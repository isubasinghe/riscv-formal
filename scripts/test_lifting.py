#!/usr/bin/env python3
"""Integration/regression checks for Sail-certified lifting and bounded SMT."""

from dataclasses import asdict, replace
import copy
import json
from pathlib import Path
import struct
import subprocess

from lift_binary import ROOT, audit, build_example, certificate_source, decode, read_elf, run
from check_lifted_smt import contract, query


BUILD = ROOT / "build/lifting-tests"


def fixture(words: list[int], entry: int = 0x1000) -> bytes:
    result = bytearray(120 + 4 * len(words))
    result[:7] = b"\x7fELF\x02\x01\x01"
    struct.pack_into("<HHIQQQIHHHHHH", result, 16, 2, 243, 1, entry, 64, 0, 0, 64, 56, 1, 0, 0, 0)
    struct.pack_into("<IIQQQQQQ", result, 64, 1, 5, 120, entry, entry, len(words) * 4, len(words) * 4, 4)
    for i, word in enumerate(words):
        struct.pack_into("<I", result, 120 + i * 4, word)
    return bytes(result)


def rtype(f3: int, f7: int = 0, rd: int = 10, r1: int = 11, r2: int = 12, opcode: int = 0x33) -> int:
    return f7 << 25 | r2 << 20 | r1 << 15 | f3 << 12 | rd << 7 | opcode


def itype(imm: int, f3: int = 0, rd: int = 10, rs: int = 10, opcode: int = 0x13) -> int:
    return (imm & 4095) << 20 | rs << 15 | f3 << 12 | rd << 7 | opcode


def branch(imm: int, f3: int = 0, r1: int = 10, r2: int = 0) -> int:
    raw = imm & 8191
    return ((raw >> 12) << 31 | ((raw >> 11) & 1) << 7 | ((raw >> 5) & 63) << 25 |
            ((raw >> 1) & 15) << 8 | r2 << 20 | r1 << 15 | f3 << 12 | 0x63)


def jal(imm: int, rd: int = 0) -> int:
    raw = imm & 0x1fffff
    return ((raw >> 20) << 31 | ((raw >> 12) & 255) << 12 | ((raw >> 11) & 1) << 20 |
            ((raw >> 1) & 1023) << 21 | rd << 7 | 0x6f)


RET = 0x8067


def lean_check(name: str, source: str, accept: bool = True) -> str:
    path = BUILD / f"{name}.lean"
    path.write_text(source)
    checked = subprocess.run(["lake", "env", "lean", "--tstack=131072", str(path)], cwd=ROOT,
                             capture_output=True, text=True, timeout=300)
    (BUILD / f"{name}.log").write_text(checked.stdout + checked.stderr)
    if accept:
        if checked.returncode:
            raise AssertionError(f"{name}: {checked.stdout}{checked.stderr}")
        audit(checked.stdout)
    else:
        if checked.returncode == 0 or "error:" not in checked.stdout:
            raise AssertionError(f"{name}: malformed certificate was not rejected by Lean")
    return checked.stdout


def solver_check(name: str, words: list[int], expected: str, steps: int, result: str,
                 requires: str = "true") -> None:
    entry, nodes = read_elf(fixture(words))
    spec = f"(define-fun expected () (_ BitVec 64) {expected})\n(define-fun requires () Bool {requires})"
    smt_check(name, nodes, entry, spec, steps, result)


def smt_check(name, nodes, entry, spec, steps, expected_result="unsat") -> None:
    path = BUILD / f"{name}.smt2"
    path.write_text(query(nodes, entry, spec, steps))
    result = run(["z3", "-T:30", str(path)]).strip()
    if result != expected_result:
        raise AssertionError(f"{name}: expected {expected_result}, got {result}")


def cli_integrity() -> None:
    """A selected function need not be the ELF entry, and its manifest is bound
    to actual bytes rather than just a matching hash in a mutable JSON file."""
    directory = BUILD / "symbol"
    directory.mkdir(parents=True, exist_ok=True)
    source, obj, elf = [directory / f"two_functions{suffix}" for suffix in (".ll", ".o", ".elf")]
    source.write_text("define i64 @entry(i64 %x) { ret i64 %x }\n"
                      "define i64 @target(i64 %x, i64 %y) {\n"
                      "  %sum = add i64 %x, %y\n  ret i64 %sum\n}\n")
    run(["llc", "-mtriple=riscv64-unknown-elf", "-target-abi=lp64", "-filetype=obj", str(source), "-o", str(obj)])
    run(["ld.lld", "-m", "elf64lriscv", "--no-relax", "--entry=entry", "-Ttext=0x80000000", str(obj), "-o", str(elf)])
    run(["python3", "scripts/lift_binary.py", "--elf", str(elf), "--symbol", "target",
         "--import", "Riscvc.SMT", "--output", str(directory)])
    manifest_path = directory / "program.json"
    manifest = json.loads(manifest_path.read_text())
    if manifest["start"] == manifest["entry"]:
        raise AssertionError("Symbol fixture failed to select a separate function")
    spec = directory / "spec.smt2"
    spec.write_text("(define-fun expected () (_ BitVec 64) (bvadd a0 a1))\n")
    run(["python3", "scripts/check_lifted_smt.py", str(manifest_path), "--spec", str(spec), "--steps", "2", "--run"])
    changed_word = copy.deepcopy(manifest)
    node = changed_word["nodes"][0]
    changed_word["nodes"][0] = asdict(decode(node["address"], node["word"] ^ 0x40000000))
    changed_start = copy.deepcopy(manifest)
    changed_start["start"] = changed_start["entry"]
    for name, altered in [("manifest-word", changed_word), ("manifest-start", changed_start)]:
        bad = directory / f"{name}.json"
        bad.write_text(json.dumps(altered))
        result = subprocess.run(["python3", "scripts/check_lifted_smt.py", str(bad), "--spec", str(spec)],
                                cwd=ROOT, capture_output=True, text=True, timeout=30)
        if result.returncode == 0 or "Manifest" not in result.stderr:
            raise AssertionError(f"Tampered {name} was not rejected: {result.stderr}")
    print("CLI verified a non-entry function and rejected tampered manifest bytes/start.", flush=True)


def main() -> None:
    BUILD.mkdir(parents=True, exist_ok=True)
    run(["lake", "build", "riscvc", "Riscvc.Binary.Lifted", "Riscvc.Binary.CountUp",
         "Riscvc.Binary.Choose"])
    # Cross-check every supported opcode family with the independent Sail decoder,
    # including zero/high registers, negative immediates, and 32-bit word forms.
    words = [rtype(f3, f7, rd=(i * 7) % 32, r1=(i * 5) % 32, r2=(31 - i))
             for i, (f3, f7) in enumerate([(0, 0), (0, 32), (1, 0), (2, 0), (3, 0),
                                          (4, 0), (5, 0), (5, 32), (6, 0), (7, 0)])]
    words += [rtype(f3, f7, opcode=0x3b) for f3, f7 in [(0, 0), (0, 32), (1, 0), (5, 0), (5, 32)]]
    words += [itype(-2048 if f3 % 2 else 2047, f3, rd=31, rs=0) for f3 in [0, 2, 3, 4, 6, 7]]
    words += [itype(63, 1), itype(63, 5), itype(0x43f, 5), itype(-1, opcode=0x1b)]
    words += [itype(31, 1, opcode=0x1b), itype(31, 5, opcode=0x1b), itype(0x41f, 5, opcode=0x1b)]
    words += [branch(-16 if f3 % 2 else 12, f3) for f3 in [0, 1, 4, 5, 6, 7]]
    words += [jal(-20, 1), itype(-2048, rd=5, rs=31, opcode=0x67), 0xfffff537, 0x80000517, RET]
    words += [itype(8, 3, rd=0, rs=31, opcode=0x03), itype(-8, 3, rd=31, rs=0, opcode=0x03),
              0x01f03423, 0xfe003c23]  # sd x31,8(x0); sd x0,-8(x0)
    data = fixture(words, 0x4000)
    entry, nodes = read_elf(data)
    lean_check("opcode-corpus", certificate_source(data, entry, nodes))
    print(f"Sail checked {len(nodes)} instruction encodings at a different entry address.", flush=True)

    simple = fixture([rtype(0, rd=10, r1=11, r2=10), RET])
    entry, nodes = read_elf(simple)
    bad_decode = [replace(nodes[0], sail=nodes[0].sail.replace(".ADD", ".SUB")), nodes[1]]
    lean_check("wrong-decoding", certificate_source(simple, entry, bad_decode), accept=False)
    bad_bytes = bytearray(simple)
    bad_bytes[123] ^= 0x40
    lean_check("wrong-bytes", certificate_source(bytes(bad_bytes), entry, nodes), accept=False)
    for word in [0, 0x02050533, 0x00000073, 0x00000001]:
        try:
            decode(0x1000, word)
        except ValueError:
            pass
        else:
            raise AssertionError(f"Unsupported encoding accepted: {word:x}")
    print("Lean rejected wrong decoding and bytes; unsupported encodings fail closed.", flush=True)
    memory = fixture([itype(8, 3, rd=10, rs=11, opcode=0x03), 0x00a5b423, RET])
    memory_entry, memory_nodes = read_elf(memory)
    wrong_memory = [replace(memory_nodes[0], sail=memory_nodes[0].sail.replace("(8,", "(0,")), *memory_nodes[1:]]
    lean_check("wrong-memory-offset", certificate_source(memory, memory_entry, wrong_memory), accept=False)
    try:
        query(memory_nodes, memory_entry, "(define-fun expected () (_ BitVec 64) a0)", 3)
    except ValueError as error:
        if "SMT semantics unavailable" not in str(error):
            raise
    else:
        raise AssertionError("Register-only SMT checker accepted memory instructions")

    names = ["sum", "round_trip", "max_unsigned", "choose", "low_byte", "rotate_left",
             "xor_cancel", "shadow", "all_ones", "nested", "register_edge"]
    for name in names:
        directory = BUILD / name
        directory.mkdir(exist_ok=True)
        elf = build_example(name, directory)
        raw = elf.read_bytes()
        entry, nodes = read_elf(raw, name)
        proof_module = "Riscvc.Binary.Choose" if name == "choose" else None
        lean_check(name, certificate_source(raw, entry, nodes, proof_module))
        spec = run(["lake", "exe", "riscvc", "--smt", name])
        smt_check(name, nodes, entry, spec, len(nodes) + 1)
        if name == "choose":
            smt_check("choose-too-short", nodes, entry, spec, 2, "sat")
            # A valid Sail lift of a different branch must not reuse the proof.
            changed = fixture([nodes[0].word ^ 0x1000, *[n.word for n in nodes[1:]]], entry)
            changed_entry, changed_nodes = read_elf(changed)
            lean_check("choose-changed-lift", certificate_source(changed, changed_entry, changed_nodes))
            rejected = lean_check("choose-wrong-proof",
                                  certificate_source(changed, changed_entry, changed_nodes, proof_module),
                                  accept=False)
            if "program = contract.program" not in rejected:
                raise AssertionError("Changed branch was not rejected at the program equality obligation")
            run(["python3", "scripts/lift_binary.py", "--elf", str(elf),
                 "--proof-module", proof_module, "--output", str(directory)])
        print(f"{name}: certified lifting and bounded SMT passed" +
              ("; Lean proved source-IR equivalence and rejected a mismatched proof" if proof_module else ""), flush=True)

    solver_check("wrong-result", [rtype(0, 32, r1=10, r2=11), RET], "(bvadd a0 a1)", 2, "sat")
    solver_check("write-zero", [itype(123, rd=0), itype(0, rs=0), RET], "(_ bv0 64)", 3, "unsat")
    solver_check("callee-clobber", [itype(0, rd=8), RET], "a0", 2, "sat")
    solver_check("sign-extend-word", [itype(0, opcode=0x1b), RET],
                 "((_ sign_extend 32) ((_ extract 31 0) a0))", 2, "unsat")
    solver_check("negative-immediate", [itype(-1), RET], "(bvsub a0 (_ bv1 64))", 2, "unsat")
    solver_check("missing-target", [jal(8)], "a0", 3, "sat")
    solver_check("unaligned-target", [jal(2), RET], "a0", 3, "sat")
    solver_check("infinite-loop", [jal(0)], "a0", 8, "sat")
    loop = [branch(16), itype(-1), itype(1, rd=11, rs=11), jal(-12), itype(0, rs=11), RET]
    solver_check("bounded-count-up", loop, "(bvadd a0 a1)", 16, "unsat", "(bvule a0 (_ bv3 64))")
    solver_check("unbounded-count-up", loop, "(bvadd a0 a1)", 16, "sat")
    for bad in ["(assert false)", "(reset)", "(define-fun expected () Bool true)"]:
        try:
            contract(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("Unsafe/mistyped SMT contract accepted")
    print("SMT regressions passed: results, ABI, zero register, sign extension, branches, targets, and loop bounds.")
    cli_integrity()


if __name__ == "__main__":
    main()
