#!/usr/bin/env python3
"""Build and run the linked-list scheduler compiled from the Lean heap DSL."""

import argparse
from pathlib import Path
import subprocess

from lift_binary import ROOT, pointer_flags, run


def emit(directory: Path) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    print(run(["lake", "build", "riscvc"]), end="", flush=True)
    source = directory / "scheduler.ll"
    source.write_text("\n".join(run(["lake", "exe", "riscvc", "--llvm", name])
                                for name in ("scheduler_init", "scheduler_step")))
    return source


def compile_native(source: Path, output: Path, level: int = 2, *, shared: bool = False) -> None:
    run(["clang", *pointer_flags("clang"), "-Wno-override-module", f"-O{level}",
         *(["-shared", "-fPIC"] if shared else
           ["-std=c11", "-Wall", "-Wextra", "-Werror", str(ROOT / "examples/scheduler.c")]),
         str(source), "-o", str(output)])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--demo", action="store_true", help="run a scripted process lifecycle")
    parser.add_argument("--capacity", type=int, default=8, help="number of reusable process slots (1..65536)")
    parser.add_argument("--build-only", action="store_true", help="build the standalone executable and exit")
    args = parser.parse_args()
    if not 1 <= args.capacity <= 65536:
        parser.error("capacity must be between 1 and 65536")
    directory = ROOT / "build/scheduler"
    source = emit(directory)
    binary = directory / "scheduler"
    compile_native(source, binary)
    if args.build_only:
        print(binary)
    else:
        raise SystemExit(subprocess.run([str(binary), "--capacity", str(args.capacity),
                                         *(["--demo"] if args.demo else [])], cwd=ROOT).returncode)


if __name__ == "__main__":
    main()
