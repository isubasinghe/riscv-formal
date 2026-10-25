#!/usr/bin/env python3
"""Check real RV64I assembly against source evaluation using a local Sail emulator."""

import argparse
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def run(command: list[str], *, timeout: int = 120) -> str:
    with subprocess.Popen(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True,
    ) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.communicate()
            raise
        result = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    if result.stdout:
        print(result.stdout, end="", flush=True)
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr, flush=True)
    result.check_returncode()
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sail",
        default=os.environ.get(
            "SAIL_RISCV_SIM",
            str(ROOT.parent / "sail-riscv/build/c_emulator/sail_riscv_sim"),
        ),
        help="path to an already-built sail_riscv_sim (default: sibling sail-riscv)",
    )
    parser.add_argument("--clang", default="clang")
    args = parser.parse_args()
    for tool in ("lake", args.clang, args.sail):
        if shutil.which(tool) is None:
            parser.error(f"required executable not found: {tool}")

    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    assembly = build / "sail-tests.S"
    elf = build / "sail-tests.elf"
    run(["lake", "test", "--", "--emit-sail", str(assembly)])
    run([
        args.clang,
        "--target=riscv64-unknown-elf",
        "-march=rv64i",
        "-mabi=lp64",
        "-nostdlib",
        "-fuse-ld=lld",
        "-Wl,--no-relax",
        "-Wl,-T,tests/link.ld",
        str(assembly),
        "-o", str(elf),
    ])
    output = run([args.sail, "--inst-limit", "3000000", str(elf)])
    # Sail can stop at an instruction limit without reporting a failed test.
    if "SUCCESS" not in output.splitlines():
        raise RuntimeError("Sail did not reach the harness's success exit")
    print(f"Sail differential and ABI checks passed: {elf}")


if __name__ == "__main__":
    try:
        main()
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, RuntimeError) as exc:
        print(f"Sail check failed: {exc}", file=sys.stderr)
        sys.exit(1)
