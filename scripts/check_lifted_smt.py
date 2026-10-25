#!/usr/bin/env python3
"""Bounded SMT checking of the lifted RV64 integer IR against a word specification.

This is an exploratory, unverified SMT translation, NOT a Lean certificate.
The query checks return value, return to ra, and callee-saved registers for all
inputs satisfying `requires`. Failure to return within --steps is a violation,
so unsat cannot silently discard a loop, trap, or missing instruction target.
Use lift_binary.py --proof-module for a kernel-checked equivalence theorem.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from lift_binary import Instruction, read_elf


def bv(value: int, width: int = 64) -> str:
    return f"(_ bv{value % (1 << width)} {width})"


def app(op: str, *args: str) -> str:
    return f"({op} {' '.join(args)})"


def ite(condition: str, yes: str, no: str) -> str:
    return app("ite", condition, yes, no)


def select(regs: str, index: int) -> str:
    return bv(0) if index == 0 else app("select", regs, bv(index, 5))


def transition(node: Instruction, regs: str) -> tuple[str, str]:
    """Return the candidate next register array and PC expression."""
    x, y = select(regs, node.rs1), select(regs, node.rs2)
    op = node.op
    pc = bv(node.address + 4)
    result = None
    binary = {"add": "bvadd", "sub": "bvsub", "and": "bvand", "or": "bvor", "xor": "bvxor"}
    immediate = {"addi": "bvadd", "andi": "bvand", "ori": "bvor", "xori": "bvxor"}
    shifts = {"sll": "bvshl", "srl": "bvlshr", "sra": "bvashr"}
    if op in binary:
        result = app(binary[op], x, y)
    elif op in immediate:
        result = app(immediate[op], x, bv(node.imm))
    elif op in ("slt", "sltu", "slti", "sltiu"):
        comparison = "bvult" if op.endswith("u") else "bvslt"
        result = ite(app(comparison, x, bv(node.imm) if "i" in op else y), bv(1), bv(0))
    elif op in shifts:
        result = app(shifts[op], x, app("bvand", y, bv(63)))
    elif op in ("slli", "srli", "srai"):
        result = app(shifts[op[:-1]], x, bv(node.imm))
    elif op in ("addw", "subw", "addiw", "sllw", "srlw", "sraw", "slliw", "srliw", "sraiw"):
        x32 = f"((_ extract 31 0) {x})"
        y32 = f"((_ extract 31 0) {y})"
        if op in ("addw", "subw", "addiw"):
            value = app("bvsub" if op == "subw" else "bvadd", x32, bv(node.imm, 32) if op == "addiw" else y32)
        else:
            amount = bv(node.imm, 32) if "i" in op else app("bvand", y32, bv(31, 32))
            value = app(shifts[op[:3]], x32, amount)
        result = f"((_ sign_extend 32) {value})"
    elif op in ("lui", "auipc"):
        result = bv(node.imm + (node.address if op == "auipc" else 0))
    elif op in ("beq", "bne", "blt", "bge", "bltu", "bgeu"):
        predicate = {"beq": "=", "bne": "distinct", "blt": "bvslt", "bge": "bvsge", "bltu": "bvult", "bgeu": "bvuge"}[op]
        pc = ite(app(predicate, x, y), bv(node.address + node.imm), pc)
    elif op == "jal":
        result, pc = pc, bv(node.address + node.imm)
    elif op == "jalr":
        result, pc = pc, app("bvand", app("bvadd", x, bv(node.imm)), bv(-2))
    else:
        raise ValueError(f"SMT semantics unavailable for {op}")
    if result is not None and node.rd != 0:
        regs = app("store", regs, bv(node.rd, 5), result)
    return regs, pc


def contract(source: str) -> str:
    """Allow only two nullary definitions, so a spec cannot alter solver commands."""
    tokens = re.findall(r"[()]|[^\s()]+", re.sub(r";[^\n]*", "", source))
    position = 0

    def parse():
        nonlocal position
        if position >= len(tokens):
            raise ValueError("Truncated SMT specification")
        token = tokens[position]
        position += 1
        if token == ")":
            raise ValueError("Unexpected ')' in specification")
        if token != "(":
            return token
        items = []
        while position < len(tokens) and tokens[position] != ")":
            items.append(parse())
        if position == len(tokens):
            raise ValueError("Unclosed SMT expression")
        position += 1
        return items

    def render(expr):
        return "(" + " ".join(map(render, expr)) + ")" if isinstance(expr, list) else expr

    definitions = {}
    while position < len(tokens):
        form = parse()
        if not isinstance(form, list) or len(form) != 5 or form[0] != "define-fun" or form[1] not in ("expected", "requires") or form[2] != []:
            raise ValueError("Contract accepts only nullary define-fun expected / requires")
        name = form[1]
        if name in definitions or form[3] != (["_", "BitVec", "64"] if name == "expected" else "Bool"):
            raise ValueError("Duplicate definition or wrong contract type")
        definitions[name] = render(form)
    if "expected" not in definitions:
        raise ValueError("Missing (define-fun expected () (_ BitVec 64) ...)")
    return definitions["expected"] + "\n" + definitions.get("requires", "(define-fun requires () Bool true)") + "\n"


def query(nodes: list[Instruction], entry: int, spec: str, steps: int) -> str:
    if steps <= 0 or steps > 10000:
        raise ValueError("--steps must be between 1 and 10000")
    if entry not in {n.address for n in nodes}:
        raise ValueError("Entry is outside the lifted program")
    array = "(Array (_ BitVec 5) (_ BitVec 64))"
    lines = ["; Unverified bounded SMT translation; unsat is not a Lean certificate.",
             "; A timeout, trap, absent target, or bound exhaustion cannot verify.",
             "(set-logic QF_AUFBV)", "(set-option :produce-models true)",
             f"(declare-const regs_0 {array})"]
    for r in range(1, 32):
        lines.append(f"(define-fun r{r} () (_ BitVec 64) {select('regs_0', r)})")
    for r in range(8):
        lines.append(f"(define-fun a{r} () (_ BitVec 64) r{10 + r})")
    lines += ["(define-fun ra () (_ BitVec 64) r1)",
              f"(assert (= (bvand ra {bv(3)}) {bv(0)}))"]
    lines += [f"(assert (distinct ra {bv(n.address)}))" for n in nodes]
    lines += [contract(spec), "(assert requires)",
              f"(define-fun pc_0 () (_ BitVec 64) {bv(entry)})",
              "(define-fun done_0 () Bool false)", "(define-fun failed_0 () Bool false)"]
    for t in range(steps):
        regs, pc = f"regs_{t}", f"pc_{t}"
        next_regs, next_pc = regs, pc
        hits = []
        for i, node in reversed(list(enumerate(nodes))):
            hit = f"hit_{t}_{i}"
            lines.append(f"(define-fun {hit} () Bool (= {pc} {bv(node.address)}))")
            hits.append(hit)
            effect_regs, effect_pc = transition(node, regs)
            next_regs, next_pc = ite(hit, effect_regs, next_regs), ite(hit, effect_pc, next_pc)
        lines += [f"(define-fun active_{t} () Bool (not (or done_{t} failed_{t})))",
                  f"(define-fun target_{t} () (_ BitVec 64) {next_pc})",
                  f"(define-fun valid_{t} () Bool (and {app('or', *hits)} (= (bvand target_{t} {bv(3)}) {bv(0)})))",
                  f"(declare-const regs_{t+1} {array})",
                  f"(declare-const pc_{t+1} (_ BitVec 64))",
                  f"(declare-const done_{t+1} Bool)", f"(declare-const failed_{t+1} Bool)",
                  f"(assert (= regs_{t+1} (ite active_{t} {next_regs} {regs})))",
                  f"(assert (= pc_{t+1} (ite active_{t} target_{t} {pc})))",
                  f"(assert (= done_{t+1} (or done_{t} (and active_{t} valid_{t} (= target_{t} ra)))))",
                  f"(assert (= failed_{t+1} (or failed_{t} (and active_{t} (not valid_{t})))))"]
    bad = [f"failed_{steps}", f"(not done_{steps})", f"(distinct {select(f'regs_{steps}', 10)} expected)"]
    for r in [2, 8, 9, *range(18, 28)]:
        bad.append(f"(distinct {select(f'regs_{steps}', r)} r{r})")
    lines += [f"(assert {app('or', *bad)})", "(check-sat)"]
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("program", type=Path, help="program.json emitted by lift_binary.py")
    parser.add_argument("--spec", type=Path, required=True, help="SMT-LIB expected and optional requires definitions")
    parser.add_argument("--steps", type=int, default=32)
    parser.add_argument("--output", type=Path, help="SMT-LIB query path; default alongside program.json")
    parser.add_argument("--run", action="store_true", help="run installed z3; return nonzero unless unsat")
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    manifest = json.loads(args.program.read_text())
    if manifest.get("format") != "riscvc-lifted-v1":
        raise ValueError("Unsupported lifted IR format")
    nodes = [Instruction(**node) for node in manifest["nodes"]]
    data = Path(manifest["elf"]).read_bytes()
    if hashlib.sha256(data).hexdigest() != manifest["sha256"]:
        raise ValueError("ELF no longer matches the lifted manifest")
    # Re-read the actual ELF, including the selected symbol's range. A valid
    # hash alone would not bind hand-edited node addresses/encodings to the file.
    entry, decoded = read_elf(data, manifest.get("symbol"))
    if entry != manifest["entry"] or decoded != nodes:
        raise ValueError("Manifest instructions do not match the actual ELF")
    start = nodes[0].address if manifest.get("symbol") else entry
    if manifest.get("start", start) != start:
        raise ValueError("Manifest start does not match the selected function / ELF entry")
    output = args.output or args.program.with_suffix(".smt2")
    output.write_text(query(nodes, start, args.spec.read_text(), args.steps))
    print(f"SMT query: {output}\nBound: {args.steps} instructions; translation is not Lean-verified.")
    if args.run:
        result = subprocess.run(["z3", f"-T:{args.timeout}", str(output)], text=True,
                                capture_output=True, timeout=args.timeout + 5)
        answer = result.stdout.strip()
        if result.returncode or answer not in ("sat", "unsat", "unknown"):
            raise RuntimeError(f"Solver failed: {result.stdout}{result.stderr}")
        print(f"Z3: {answer}")
        if answer == "unsat":
            print("Bounded SMT check passed (not a Lean equivalence certificate).")
        else:
            print("Not verified: a result/ABI mismatch, unsupported target, or insufficient bound is possible.")
            if answer == "sat":
                with output.open("a") as file:
                    file.write(f"(get-value (a0 a1 a2 ra pc_{args.steps} done_{args.steps} failed_{args.steps}))\n")
                details = subprocess.run(["z3", f"-T:{args.timeout}", str(output)], text=True,
                                         capture_output=True, timeout=args.timeout + 5)
                print(details.stdout.strip())
            sys.exit(1)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, RuntimeError, OSError, subprocess.TimeoutExpired) as error:
        print(f"SMT check failed: {error}", file=sys.stderr)
        sys.exit(1)
