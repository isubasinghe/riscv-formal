#!/usr/bin/env python3
"""Check the scheduler's Lean proofs and inductive SMT translation validation.

Checks the actual exported DSL AST against decoded ELF instructions, including
both traversal loops, full heap equality, return value/address, and preserved
registers. Lean proves the DSL-to-Sail reference lowering and source-to-binary
equivalence for both functions. The independent SMT checks provide additional
regression coverage; their results are not premises of the Lean theorems.
"""

import argparse
from dataclasses import dataclass, replace
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from lift_binary import Instruction, ROOT, audit, read_elf, run


WORD = "(_ BitVec 64)"
HEAP = f"(Array {WORD} {WORD})"
MASK = (1 << 64) - 1
BUILD = ROOT / "build/scheduler-proof"
CALLER_SAVED = set(range(10, 18))
SOURCE_PROOF = "examples.proof.SchedulerSail"
INIT_PROOF = "examples.proof.SchedulerInit"
STEP_PROOF = "examples.proof.SchedulerStep"


def check_source_proofs(directory):
    """Check and audit both reference-lowering and optimized-program proofs."""
    print(run(["lake", "build", SOURCE_PROOF, INIT_PROOF, STEP_PROOF]), end="", flush=True)
    path = directory / "SourceToSail.lean"
    path.write_text(
        f"import {SOURCE_PROOF}\nimport {INIT_PROOF}\nimport {STEP_PROOF}\n"
        "#print axioms Riscvc.Heap.Scheduler.SailProof.init_source_to_sail\n"
        "#print axioms Riscvc.Heap.Scheduler.SailProof.step_source_to_sail\n"
        "#print axioms Riscvc.Heap.Scheduler.InitProof.refines\n"
        "#print axioms Riscvc.Heap.Scheduler.InitProof.pre_inhabited\n"
        "#print axioms Riscvc.Heap.Scheduler.StepProof.refines\n"
        "#print axioms Riscvc.Heap.Scheduler.StepProof.step_sail_equivalence\n"
        "#print axioms Riscvc.Heap.Scheduler.StepProof.pre_inhabited\n"
    )
    output = run(["lake", "env", "lean", str(path)])
    audit(output)
    (directory / "SourceToSail.axioms.txt").write_text(output)
    print("Lean checked the source-to-Sail and optimized scheduler proofs and axiom audit.", flush=True)


def bv(n):
    return f"#x{n & MASK:016x}"


def app(op, *args):
    if op in ("and", "or"):
        identity, absorbing = ("true", "false") if op == "and" else ("false", "true")
        if absorbing in args:
            return absorbing
        args = tuple(dict.fromkeys(a for a in args if a != identity))
        if not args:
            return identity
        if len(args) == 1:
            return args[0]
    if op == "not" and args[0] in ("true", "false"):
        return "false" if args[0] == "true" else "true"
    if op == "=" and args[0] == args[1]:
        return "true"
    if op == "distinct" and args[0] == args[1]:
        return "false"
    if args and all(a.startswith("#x") for a in args):
        ns = [int(a[2:], 16) for a in args]
        binary = {"bvadd": lambda a, b: a + b, "bvsub": lambda a, b: a - b,
                  "bvand": lambda a, b: a & b, "bvor": lambda a, b: a | b,
                  "bvxor": lambda a, b: a ^ b}
        if op in binary:
            return bv(binary[op](*ns))
        predicates = {"=": lambda a, b: a == b, "distinct": lambda a, b: a != b,
                      "bvult": lambda a, b: a < b, "bvule": lambda a, b: a <= b}
        if op in predicates:
            return "true" if predicates[op](*ns) else "false"
    if op == "ite":
        if args[0] in ("true", "false"):
            return args[1] if args[0] == "true" else args[2]
        if args[1] == args[2]:
            return args[1]
    return f"({op} {' '.join(args)})"


def nonzero(x):
    return app("distinct", x, bv(0))


class SMT:
    def __init__(self):
        self.lines = ["(set-logic QF_AUFBV)", "(set-option :produce-models true)"]
        self.cache = {}

    def var(self, name, sort=WORD):
        self.lines.append(f"(declare-const {name} {sort})")
        return name

    def term(self, sort, value):
        if not value.startswith("("):
            return value
        key = sort, value
        if key not in self.cache:
            name = f"v{len(self.cache)}"
            self.lines.append(f"(define-fun {name} () {sort} {value})")
            self.cache[key] = name
        return self.cache[key]

    def word(self, op, *args):
        return self.term(WORD, app(op, *args))

    def access(self, base, offset, source=False):
        address = self.word("bvadd", base, bv(offset))
        # Cell semantics agree with little-endian ld/sd only for aligned RAM.
        conditions = [app("bvule", bv(0x80001000), address),
                      app("bvule", address, bv(0x8FFFFFF8)),
                      app("=", self.word("bvand", address, bv(7)), bv(0)),
                      app("select", "mapped", address)]
        if source:
            conditions += [nonzero(base), app("bvule", base, address)]
        return address, app("and", *conditions)


@dataclass
class State:
    pc: int
    values: list[str]
    heap: str
    guards: tuple = ()
    safe: tuple = ()
    trace: tuple = ()
    result: str = ""
    destination: str = ""


class Source:
    def __init__(self, spec):
        self.nodes = {0: ("return", spec["returns"])}
        self.loops = []
        self.body_labels = {}

        def collect(cmd):
            if cmd[0] == "while":
                self.loops.append(cmd)
                collect(cmd[2])
            elif cmd[0] == "seq":
                collect(cmd[1]); collect(cmd[2])
            elif cmd[0] == "if":
                collect(cmd[2]); collect(cmd[3])

        collect(spec["body"])
        self.entry = self.compile(spec["body"], 0)
        self.params, self.locals = spec["params"], spec["locals"]

    def new(self, node):
        index = len(self.nodes)
        self.nodes[index] = node
        return index

    def compile(self, cmd, after):
        tag, *args = cmd
        if tag == "skip":
            return after
        if tag == "seq":
            return self.compile(args[0], self.compile(args[1], after))
        if tag == "if":
            return self.new(("branch", args[0], self.compile(args[1], after), self.compile(args[2], after)))
        if tag == "while":
            head = self.new(None)
            body = self.compile(args[1], head)
            self.nodes[head] = ("branch", args[0], body, after)
            loop_id = next(i for i, loop in enumerate(self.loops) if loop is cmd)
            self.body_labels[body] = loop_id
            return head
        if tag in ("assign", "store"):
            return self.new((tag, *args, after))
        raise ValueError(f"Unsupported source command {tag}")

    def expr(self, e, state, smt):
        tag, *args = e
        if tag == "var":
            return state.values[args[0]], ()
        if tag == "word":
            return bv(args[0]), ()
        if tag == "field":
            base, safe = self.expr(args[1], state, smt)
            address, access = smt.access(base, args[0], source=True)
            return smt.word("select", state.heap, address), (*safe, access)
        if tag == "ite":
            c, cs = self.expr(args[0], state, smt)
            a, sa = self.expr(args[1], state, smt)
            b, sb = self.expr(args[2], state, smt)
            return smt.word("ite", nonzero(c), a, b), (*cs,
                app("=>", nonzero(c), app("and", *sa)),
                app("=>", app("=", c, bv(0)), app("and", *sb)))
        a, sa = self.expr(args[0], state, smt)
        b, sb = self.expr(args[1], state, smt)
        if tag in ("eq", "ltu"):
            value = smt.word("ite", app("=" if tag == "eq" else "bvult", a, b), bv(1), bv(0))
        else:
            ops = {"add": "bvadd", "sub": "bvsub", "and": "bvand", "or": "bvor", "xor": "bvxor",
                   "shl": "bvshl", "shr": "bvlshr"}
            if tag not in ops:
                raise ValueError(f"Unsupported source expression {tag}")
            value = smt.word(ops[tag], a, smt.word("bvand", b, bv(63)) if tag in ("shl", "shr") else b)
        return value, (*sa, *sb)

    def paths(self, initial, smt):
        pending, ends = [initial], []
        while pending:
            s = pending.pop()
            if s.trace and s.pc in self.body_labels:
                ends.append(replace(s, destination=f"loop{self.body_labels[s.pc]}"))
                continue
            if s.pc in s.trace or len(s.trace) > 512 or len(pending) + len(ends) > 4096:
                raise ValueError("Uncovered source cycle or excessive path count")
            tag, *args = self.nodes[s.pc]
            s = replace(s, trace=(*s.trace, s.pc), values=s.values.copy())
            if tag == "return":
                value, safe = self.expr(args[0], s, smt)
                ends.append(replace(s, result=value, safe=(*s.safe, *safe), destination="return"))
            elif tag == "assign":
                value, safe = self.expr(args[1], s, smt)
                s.values[args[0]] = value
                pending.append(replace(s, pc=args[2], safe=(*s.safe, *safe)))
            elif tag == "store":
                base, bs = self.expr(args[1], s, smt)
                value, vs = self.expr(args[2], s, smt)
                address, access = smt.access(base, args[0], source=True)
                memory = smt.term(HEAP, app("store", s.heap, address, value))
                pending.append(replace(s, heap=memory, pc=args[3], safe=(*s.safe, *bs, *vs, access)))
            elif tag == "branch":
                value, safe = self.expr(args[0], s, smt)
                for condition, target in [(nonzero(value), args[1]), (app("=", value, bv(0)), args[2])]:
                    if condition != "false":
                        pending.append(replace(s, pc=target, guards=(*s.guards, condition), safe=(*s.safe, *safe)))
            else:
                raise ValueError(f"Unknown source CFG node {tag}")
        return ends


def binary_paths(nodes, initial, cuts, smt):
    program = {n.address: n for n in nodes}
    pending, ends = [initial], []
    while pending:
        s = pending.pop()
        if s.trace and s.pc in cuts:
            ends.append(replace(s, destination=cuts[s.pc]))
            continue
        if s.pc not in program or s.pc in s.trace:
            ends.append(replace(s, destination="failure"))
            continue
        if len(s.trace) > 512 or len(pending) + len(ends) > 4096:
            raise ValueError("Excessive binary segment size/path count")
        n = program[s.pc]
        s = replace(s, pc=s.pc + 4, trace=(*s.trace, s.pc), values=s.values.copy())
        x, y = s.values[n.rs1], s.values[n.rs2]
        result = None
        if n.op in ("addi", "and"):
            result = smt.word("bvadd" if n.op == "addi" else "bvand", x, bv(n.imm) if n.op == "addi" else y)
        elif n.op in ("sltu", "sltiu"):
            result = smt.word("ite", app("bvult", x, bv(n.imm) if n.op == "sltiu" else y), bv(1), bv(0))
        elif n.op in ("ld", "sd"):
            address, access = smt.access(x, n.imm)
            s.safe = (*s.safe, access)
            if n.op == "ld":
                result = smt.word("select", s.heap, address)
            else:
                s.heap = smt.term(HEAP, app("store", s.heap, address, y))
        elif n.op in ("beq", "bne"):
            condition = app("=" if n.op == "beq" else "distinct", x, y)
            for guard, target in [(condition, n.address + n.imm), (app("not", condition), s.pc)]:
                if guard != "false":
                    pending.append(replace(s, pc=target, guards=(*s.guards, guard)))
            continue
        elif n.op == "jal":
            result, s.pc = bv(s.pc), n.address + n.imm
        elif n.op == "jalr" and (n.rd, n.rs1, n.imm) == (0, 1, 0):
            ends.append(replace(s, result=smt.word("bvand", x, bv(-2)), destination="return"))
            continue
        else:
            raise ValueError(f"Unsupported instruction {n.op} at {n.address:#x}")
        if result is not None and n.rd:
            s.values[n.rd] = result
        pending.append(s)
    return ends


def relation(source, binary, original):
    if binary.destination == "failure":
        return "false"
    sv, rv = source.values, binary.values
    shared = [app("=", source.heap, binary.heap)] + [
        app("=", rv[i], original[i]) for i in range(1, 32) if i not in CALLER_SAVED]
    if source.destination == binary.destination == "return":
        return app("and", *shared, app("=", source.result, rv[10]), app("=", binary.result, original[1]))
    if source.destination == "loop0" and binary.destination == "add":
        pairs = [(0, 10), (1, 11), (2, 12), (3, 13), (4, 14), (8, 16)]
        invariant = [app("=", sv[1], bv(1)), nonzero(sv[2]), nonzero(sv[3]), nonzero(sv[4]),
                     app("or", app("=", sv[8], bv(0)), app("=", sv[8], bv(1))),
                     app("=", sv[9], bv(1)), *[app("=", sv[i], bv(0)) for i in (5, 6, 7)]]
    elif source.destination == "loop1" and binary.destination in ("remove_first", "remove_next"):
        pairs = [(0, 10), (1, 11), (2, 12), (4, 13)]
        invariant = [app("=", sv[1], bv(2)), nonzero(sv[4]), app("=", sv[9], bv(4)),
                     *[app("=", sv[i], bv(0)) for i in (6, 7, 8)]]
        if binary.destination == "remove_first":
            invariant.append(app("=", sv[5], bv(0)))
        else:
            invariant.append(nonzero(sv[5]))
            pairs.append((5, 15))
    else:
        return "false"
    return app("and", *shared, *invariant, *[app("=", sv[i], rv[j]) for i, j in pairs])


def obligation(spec, nodes, point, kind):
    if not nodes or any(n.address < 0x80000000 or n.address + 4 > 0x80001000 or n.address % 4 for n in nodes):
        raise ValueError("Scheduler text must fit in the aligned 4 KiB window below writable RAM")
    source, smt = Source(spec), SMT()
    heap = smt.var("memory", HEAP)
    smt.var("mapped", f"(Array {WORD} Bool)")
    regs = [bv(0)] + [smt.var(f"r{i}") for i in range(1, 32)]
    args = [smt.var(f"arg{i}") for i in range(source.params)]
    values = args + [bv(0)] * source.locals
    pre = [app("=", smt.word("bvand", regs[1], bv(3)), bv(0))]
    entry = nodes[0].address
    cuts = {} if kind == "init" else {
        entry + 0x3C: "add", entry + 0xAC: "remove_first", entry + 0xD0: "remove_next"}
    if kind == "step" and (len(source.loops), source.params, source.locals) != (2, 4, 6):
        raise ValueError("Scheduler source shape changed; loop invariants need updating")
    if kind == "init" and (source.loops or (source.params, source.locals) != (2, 0)):
        raise ValueError("Unexpected scheduler_init source shape")
    if not set(cuts) <= {n.address for n in nodes}:
        raise ValueError("Missing scheduler loop cutpoint")
    if point == "entry":
        for i, arg in enumerate(args):
            regs[10 + i] = arg
        spc, bpc = source.entry, entry
    else:
        values[4] = smt.var("cur")
        pre.append(nonzero(values[4]))
        regs[10], regs[12] = values[0], values[2]
        if point == "add":
            values[1] = regs[11] = bv(1)
            values[8] = smt.var("duplicate")
            values[9] = bv(1)
            regs[13], regs[14], regs[16] = values[3], values[4], values[8]
            pre += [nonzero(values[2]), nonzero(values[3]),
                    app("or", app("=", values[8], bv(0)), app("=", values[8], bv(1)))]
            loop = 0
        else:
            values[1] = regs[11] = bv(2)
            values[9] = bv(4)
            regs[13] = values[4]
            if point == "remove_next":
                values[5] = regs[15] = smt.var("prev")
                pre.append(nonzero(values[5]))
            loop = 1
        spc = next(pc for pc, i in source.body_labels.items() if i == loop)
        bpc = next(pc for pc, label in cuts.items() if label == point)
    source_paths = source.paths(State(spc, values, heap), smt)
    machine_paths = binary_paths(nodes, State(bpc, regs, heap), cuts, smt)
    violations, feasible = [], []
    for path in source_paths:
        guard = app("and", *path.guards, *path.safe)
        feasible.append(guard)
        matches = [app("and", *other.guards, *other.safe, relation(path, other, regs)) for other in machine_paths]
        violations.append(app("and", guard, app("not", app("or", *matches))))
    prefix = "\n".join([
        "; Inductive segment check, not a Lean source-to-Sail certificate.",
        "; No list-length or execution bound: all cycles must cross matched cutpoints.",
        *smt.lines, f"(assert {app('and', *pre)})", ""])
    # A satisfiable domain is checked separately to reject vacuous invariants.
    domain = prefix + f"(assert {app('or', *feasible)})\n(check-sat)\n"
    query = prefix + f"(assert {app('or', *violations)})\n(check-sat)\n"
    return query, domain, {"source_paths": len(source_paths), "binary_paths": len(machine_paths)}


def solve(path, text, timeout):
    path.write_text(text)
    result = subprocess.run(["z3", f"-T:{timeout}", str(path)], capture_output=True, text=True, timeout=timeout + 5)
    answer = result.stdout.strip()
    if result.returncode or answer not in ("sat", "unsat", "unknown"):
        raise RuntimeError(f"Solver failed for {path.name}: {result.stdout}{result.stderr}")
    if answer == "unknown":
        raise RuntimeError(f"Solver did not decide {path.name}; no proof result")
    return answer


def validate(spec, nodes, kind, directory, timeout):
    directory.mkdir(parents=True, exist_ok=True)
    results = []
    points = ["entry"] if kind == "init" else ["entry", "add", "remove_first", "remove_next"]
    for point in points:
        query, domain, counts = obligation(spec, nodes, point, kind)
        name = f"{kind}-{point}"
        if solve(directory / f"{name}-domain.smt2", domain, timeout) != "sat":
            raise RuntimeError(f"Vacuous invariant/domain at {name}")
        answer = solve(directory / f"{name}.smt2", query, timeout)
        results.append({"point": name, "result": answer, **counts,
                        "query_sha256": hashlib.sha256(query.encode()).hexdigest()})
        print(f"{name}: {answer} ({counts['source_paths']} source / {counts['binary_paths']} binary paths)", flush=True)
        if answer != "unsat":
            raise RuntimeError(f"Equivalence obligation failed at {name}; see {directory / (name + '.smt2')}")
    return results


def load_manifest(directory):
    manifest = json.loads((directory / "program.json").read_text())
    if manifest.get("format") != "riscvc-lifted-v1":
        raise ValueError("Unsupported lifting manifest")
    data = Path(manifest["elf"]).read_bytes()
    entry, nodes = read_elf(data, manifest.get("symbol"))
    if hashlib.sha256(data).hexdigest() != manifest["sha256"] or entry != manifest["entry"]:
        raise ValueError("ELF changed after lifting")
    if nodes != [Instruction(**n) for n in manifest["nodes"]]:
        raise ValueError("Manifest nodes do not match the ELF bytes")
    if manifest.get("start") != (nodes[0].address if manifest.get("symbol") else entry):
        raise ValueError("Manifest entry point does not match the ELF")
    return manifest, data, nodes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smt-only", action="store_true", help="validate existing artifacts without rerunning Lean lifting")
    parser.add_argument("--timeout", type=int, default=120, help="seconds per solver obligation")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    BUILD.mkdir(parents=True, exist_ok=True)
    (BUILD / "equivalence.json").write_text(json.dumps({"status": "in_progress"}) + "\n")
    inputs = [ROOT / path for path in (
        "examples/Scheduler.lean", "examples/proof/SchedulerExport.lean",
        "examples/proof/SchedulerSail.lean", "examples/proof/SchedulerInit.lean",
        "examples/proof/SchedulerStep.lean", "examples/proof/SchedulerStepProgram.lean",
        "examples/proof/SchedulerStepTactics.lean", "examples/proof/SchedulerStepSegments.lean",
        "Riscvc/Heap/Language.lean", "Riscvc/Heap/Syntax.lean", "Riscvc/Language.lean",
        "Riscvc/Heap/SailLowering.lean", "Riscvc/Binary/Memory.lean",
        "Riscvc/Heap/Control.lean", "Riscvc/Binary/WordMachine.lean",
        "Riscvc/Binary/Lifted.lean", "Riscvc/Binary/SailProofs.lean",
        "scripts/verify_scheduler.py", "scripts/lift_binary.py", "lean-toolchain")]
    fingerprints = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs}
    print(run(["lake", "build", "examples.Scheduler"]), end="", flush=True)
    if not args.smt_only:
        check_source_proofs(BUILD)
        for kind in ("init", "step"):
            command = [sys.executable, str(ROOT / "scripts/lift_binary.py"), "--example", f"scheduler_{kind}",
                       "--output", str(BUILD / kind)]
            command += ["--proof-module", INIT_PROOF if kind == "init" else STEP_PROOF]
            print(run(command), end="", flush=True)
    source_text = run(["lake", "env", "lean", "--run", "examples/proof/SchedulerExport.lean"])
    source = json.loads(source_text)
    if source.get("format") != "riscvc-scheduler-source-v1":
        raise ValueError("Unsupported source export format")
    (BUILD / "source.json").write_text(source_text)
    report = {"status": "passed",
              "kind": "inductive-smt-validation" if args.smt_only else "lean-translation-validation-with-smt-checks",
              "lean_source_equivalence_proved": not args.smt_only,
              "lean_lifting_checked_this_run": not args.smt_only,
              "lean_reference_lowering_checked_this_run": not args.smt_only,
              "lean_binary_equivalence_checked_this_run": {"init": not args.smt_only, "step": not args.smt_only},
              "source_sha256": hashlib.sha256(source_text.encode()).hexdigest(),
              "inputs": fingerprints, "solver": run(["z3", "--version"]).strip(),
              "smt_trusted": ["SchedulerExport.lean", "verify_scheduler.py symbolic semantics and cutpoint induction", "Z3"],
              "lean_trusted": [] if args.smt_only else
                  ["Lean kernel and standard axioms", "audited upstream Sail platform declarations", "filesystem byte ingestion"],
              "functions": {}}
    for kind in ("init", "step"):
        manifest, data, nodes = load_manifest(BUILD / kind)
        results = validate(source[kind], nodes, kind, BUILD / "equivalence", args.timeout)
        if Path(manifest["elf"]).read_bytes() != data:
            raise RuntimeError("ELF changed during validation")
        report["functions"][kind] = {"elf_sha256": manifest["sha256"], "obligations": results}
    if run(["lake", "env", "lean", "--run", "examples/proof/SchedulerExport.lean"]) != source_text:
        raise RuntimeError("DSL source changed during validation")
    if any(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest for name, digest in fingerprints.items()):
        raise RuntimeError("Validator or source files changed during validation")
    (BUILD / "equivalence.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Inductive SMT validation passed for the source DSL and decoded RV64 scheduler.")
    if not args.smt_only:
        print("Lean proved the source reference lowering and optimized binary equivalence for both scheduler functions.")
    else:
        print("This SMT-only run did not recheck the Lean proofs or ELF certificates.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, RuntimeError, KeyError, OSError, subprocess.TimeoutExpired) as error:
        if BUILD.exists():
            (BUILD / "equivalence.json").write_text(json.dumps({"status": "failed", "error": str(error)}) + "\n")
        print(f"Scheduler validation failed: {error}", file=sys.stderr)
        sys.exit(1)
