#!/usr/bin/env python3
"""Build and certify the LLVM-optimized count_up ELF against the DSL's proved IR.

Python and LLVM are untrusted certificate producers. Lean checks the entire ELF
literal, its loaded instruction words, and the universal Sail execution proof.
"""

import argparse
import hashlib
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
# The last four are upstream Sail platform declarations referenced by the full
# decoder/executor. The proved integer/return path never calls those primitives.
ALLOWED_AXIOMS = {
    "propext", "Classical.choice", "Quot.sound", "load_reservation",
    "match_reservation", "plat_term_write", "sys_enable_experimental_extensions",
}


def run(command: list[str], *, timeout: int = 600, **kwargs) -> str:
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout, **kwargs)
    if result.returncode:
        raise RuntimeError(f"{' '.join(command)}\n{result.stdout}")
    return result.stdout


def certificate_source(data: bytes, digest: str) -> str:
    rows = ["  " + ", ".join(str(x) for x in data[i:i + 32])
            for i in range(0, len(data), 32)]
    return (
        "import Riscvc.Binary.CountUp\n\n"
        "set_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\n"
        "namespace BinaryCertificate\nopen Riscvc.Binary\n\n"
        f"-- SHA-256 of the complete input ELF: {digest}\n"
        "def bytes : ELF.Bytes := #[\n" + ",\n".join(rows) + "\n]\n\n"
        "def image : ELF.Image := (ELF.parse bytes).getD ⟨#[], 0, []⟩\n\n"
        "theorem certificate : CountUp.Certificate bytes :=\n"
        "  ⟨image, by rfl, CountUp.correct image (by decide) (by decide) (by decide)⟩\n\n"
        "#print axioms certificate\nend BinaryCertificate\n"
    )


def check(elf: Path, output: Path, expect_failure: bool = False) -> None:
    data = elf.read_bytes()
    if len(data) > 1024 * 1024:
        raise RuntimeError("Prototype certificate size limit: 1 MiB")
    digest = hashlib.sha256(data).hexdigest()
    source = certificate_source(data, digest)
    if expect_failure:
        source = source.replace("#print axioms certificate\n", "")
    output.write_text(source)
    result = subprocess.run(
        ["lake", "env", "lean", "--tstack=131072", str(output)], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300,
    )
    if expect_failure:
        if result.returncode == 0:
            raise RuntimeError(f"Unsound certificate accepted: {elf}")
        if not any(f"Tactic `{tactic}`" in result.stdout for tactic in ["decide", "rfl"]):
            raise RuntimeError(f"Negative test did not reach the byte check:\n{result.stdout}")
        print(f"Rejected {elf.name}")
        return
    if result.returncode:
        raise RuntimeError(result.stdout)
    audit = re.search(r"depends on axioms:\s*\[([^]]*)\]", result.stdout)
    if audit is None:
        raise RuntimeError(f"Missing axiom audit:\n{result.stdout}")
    axioms = {name.strip() for name in audit[1].split(",") if name.strip()}
    if not axioms <= ALLOWED_AXIOMS:
        raise RuntimeError(f"Unexpected proof axiom:\n{result.stdout}")
    if elf.read_bytes() != data:
        raise RuntimeError("Input ELF changed while its certificate was being checked")
    (output.parent / (output.stem + ".axioms.txt")).write_text(result.stdout)
    print(f"Certified {elf}\nSHA-256: {digest}\nLean certificate: {output}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--elf", type=Path, help="certify an existing count_up executable")
    parser.add_argument("--negative-tests", action="store_true")
    args = parser.parse_args()
    for tool in ["lake"] + ([] if args.elf else ["opt", "llc", "ld.lld", "llvm-objdump"]):
        if not shutil.which(tool):
            parser.error(f"required executable not found: {tool}")
    build = ROOT / "build/binary-proof"
    build.mkdir(parents=True, exist_ok=True)
    print("Building the Sail proof library...", flush=True)
    run(["lake", "build", "riscvc", "Riscvc.Binary.CountUp"])
    elf = args.elf.resolve() if args.elf else build / "count_up.elf"
    if not args.elf:
        source = build / "count_up.ll"
        source.write_text(run(["lake", "exe", "riscvc", "--llvm", "count_up"]))
        optimized = build / "count_up.opt.ll"
        obj = build / "count_up.o"
        run(["opt", "-S", "-passes=default<O2>", "-verify-each", str(source), "-o", str(optimized)])
        run(["llc", "-mtriple=riscv64-unknown-elf", "-mattr=+m", "-target-abi=lp64",
             "-O=2", "-filetype=obj", str(optimized), "-o", str(obj)])
        run(["ld.lld", "-m", "elf64lriscv", "--no-relax", "--entry=count_up",
             "-Ttext=0x80000000", str(obj), "-o", str(elf)])
        (build / "count_up.disasm").write_text(run(["llvm-objdump", "-d", str(elf)]))
    check(elf, build / "Certificate.lean")
    if args.negative_tests:
        original = elf.read_bytes()
        # This offset selection only manufactures negative tests. It is not used
        # to generate any premise of the accepted certificate.
        phoff = struct.unpack_from("<Q", original, 32)[0]
        phnum = struct.unpack_from("<H", original, 56)[0]
        offsets = []
        for i in range(phnum):
            kind, flags, offset = struct.unpack_from("<IIQ", original, phoff + 56 * i)
            if kind == 1 and flags & 1:
                offsets.append(offset)
        if len(offsets) != 1:
            raise RuntimeError("Negative tests require exactly one executable segment")
        text = offsets[0]
        variants = {
            "wrong-add": (text + 3, original[text + 3] ^ 0x40), # add -> sub
            "wrong-return": (text + 4, 0x13),
            "wrong-isa": (18, 62),
            "bad-entry": (24, original[24] ^ 4),
        }
        for name, (offset, value) in variants.items():
            changed = bytearray(original)
            changed[offset] = value
            bad = build / f"{name}.elf"
            bad.write_bytes(changed)
            check(bad, build / f"{name}.lean", expect_failure=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.TimeoutExpired, OSError) as error:
        print(f"Binary verification failed: {error}", file=sys.stderr)
        sys.exit(1)
