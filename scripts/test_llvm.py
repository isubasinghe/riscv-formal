#!/usr/bin/env python3
"""Check LLVM IR at O0/O2 on the host and as RV64IM machine code in Sail."""

import argparse
import ctypes
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from test_sail import ROOT, run


def check_native(library: Path, cases_path: Path) -> None:
    library_handle = ctypes.CDLL(str(library.resolve()))
    cases = json.loads(cases_path.read_text())
    functions = {}
    for index, case in enumerate(cases):
        name = case["name"]
        if name not in functions:
            function = getattr(library_handle, name)
            function.argtypes = [ctypes.c_uint64] * len(case["args"])
            function.restype = ctypes.c_uint64
            functions[name] = function
        actual = functions[name](*case["args"])
        if actual != case["expected"]:
            raise RuntimeError(
                f"case {index}, {name}{tuple(case['args'])}: "
                f"got {actual}, expected {case['expected']}"
            )
    print(f"Native LLVM checks passed: {len(cases)} cases in {library.name}")


def check_optimisation(path: Path) -> None:
    # This semantic identity spans several input instructions. Checking the
    # result ensures we actually ran the optimiser rather than only codegen.
    match = re.search(
        r"define\b[^@\n]*@round_trip\([^\n]*\)[^\n]*\{\n(.*?)\n\}",
        path.read_text(), re.DOTALL,
    )
    if match is None:
        raise RuntimeError("round_trip is missing from optimised LLVM IR")
    instructions = [
        line.strip() for line in match[1].splitlines()
        if line.strip() and not line.strip().endswith(":")
        and not line.strip().startswith(";")
    ]
    if instructions != ["ret i64 %arg0"]:
        raise RuntimeError(f"LLVM did not simplify round_trip to identity: {instructions}")
    print("LLVM O2 simplified round_trip to a single return.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clang", default="clang")
    parser.add_argument("--opt", default="opt")
    parser.add_argument("--llc", default="llc")
    parser.add_argument("--skip-sail", action="store_true", help="run LLVM verification and native checks only")
    parser.add_argument("--sail", default=os.environ.get(
        "SAIL_RISCV_SIM", str(ROOT.parent / "sail-riscv/build/c_emulator/sail_riscv_sim"),
    ))
    parser.add_argument("--native-library", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--cases", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.native_library is not None:
        if args.cases is None:
            parser.error("native worker requires --cases")
        check_native(args.native_library, args.cases)
        return

    required = ["lake", args.clang, args.opt]
    if not args.skip_sail:
        required.extend([args.llc, args.sail])
    for tool in required:
        if shutil.which(tool) is None:
            parser.error(f"required executable not found: {tool}")

    build = ROOT / "build/llvm-tests"
    build.mkdir(parents=True, exist_ok=True)
    source = build / "programs.ll"
    optimised = build / "programs.opt.ll"
    run(["lake", "test", "--", "--emit-llvm-tests", str(build)])
    run([args.opt, "-passes=verify", "-disable-output", str(source)])
    run([args.opt, "-S", "-passes=default<O2>", "-verify-each", str(source), "-o", str(optimised)])
    check_optimisation(optimised)

    for level, module in [(0, source), (2, optimised)]:
        library = build / f"programs-O{level}.so"
        run([
            args.clang, "-Wno-override-module", "-shared", "-fPIC", f"-O{level}",
            str(module), "-o", str(library),
        ])
        # Isolate native execution so an unexpected infinite loop or crash is
        # reported with a timeout/exit code by the same runner used for Sail.
        run([
            sys.executable, str(Path(__file__).resolve()), "--native-library", str(library),
            "--cases", str(build / "cases.json"),
        ])
        if args.skip_sail:
            continue
        obj = build / f"programs-O{level}.o"
        elf = build / f"programs-O{level}.elf"
        run([
            args.llc, "-mtriple=riscv64-unknown-elf", "-mattr=+m", "-target-abi=lp64",
            "-code-model=medium", f"-O={level}", "-filetype=obj", str(module), "-o", str(obj),
        ])
        run([
            args.clang, "--target=riscv64-unknown-elf", "-march=rv64im", "-mabi=lp64",
            "-nostdlib", "-fuse-ld=lld", "-Wl,--no-relax", "-Wl,-T,tests/link.ld",
            str(build / "harness.S"), str(obj), "-o", str(elf),
        ])
        output = run([args.sail, "--inst-limit", "3000000", str(elf)])
        if "SUCCESS" not in output.splitlines():
            raise RuntimeError(f"Sail did not reach success for LLVM O{level}")
        print(f"LLVM O{level} Sail differential, tail-stack, and ABI checks passed.")


if __name__ == "__main__":
    try:
        main()
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, RuntimeError) as exc:
        print(f"LLVM check failed: {exc}", file=sys.stderr)
        sys.exit(1)
