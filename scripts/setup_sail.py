#!/usr/bin/env python3
"""Generate the pinned Sail instruction semantics without changing the source checkout."""

import argparse
import io
from pathlib import Path
import re
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
# This is the source snapshot immediately preceding the published
# opencompl/sail-riscv-lean build (2026-08-20). Later models introduce unsupported
# debug-trigger types and hypervisor termination obligations in the Lean target.
REVISION = "b7d13572fcd4a87d0999eb6303652cd05a47881e"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT.parent / "sail-riscv")
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    destination = ROOT / "vendor/sail-riscv"
    if (destination / "PROVENANCE").exists() and not args.regenerate:
        print("Pinned Sail model is already present.")
        return
    version = subprocess.check_output(["sail", "--version"], text=True).strip()
    if "0.20.3" not in version:
        raise RuntimeError(f"This generation recipe requires Sail 0.20.3; found {version}")
    source = ROOT / "build/sail-source"
    source.mkdir(parents=True, exist_ok=True)
    archive = subprocess.check_output(["git", "-C", str(args.source), "archive", REVISION])
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        bundle.extractall(source, filter="data")
    build = ROOT / "build/sail-generated"
    build.mkdir(parents=True, exist_ok=True)
    values = {
        "CONFIG_ELEN_IS_64": "true", "CONFIG_XLEN_IS_32": "false",
        "CONFIG_XLEN_IS_64": "true", "CONFIG__ASID__LEN": "16",
        "CONFIG__BASE__XLEN": "64", "CONFIG__H__GEILEN": "63",
        "CONFIG__PHYSADDR__BITS": "56", "CONFIG__VMID__LEN": "14",
        "CONFIG__V__ELEN_EXP": "6", "CONFIG__V__SUPPORT": "Full",
        "CONFIG__V__VLEN_EXP": "8",
        "CONFIG_MIDELEG_DELEGATABLE_BITS_VALUE": "0x0000_0000_0000_2222",
    }
    template = (source / "config/config.json.in").read_text()
    # These are the same substitutions as upstream config/CMakeLists.txt for
    # rv64d_v256_e64. @VARIABLE@ appears only in an explanatory comment.
    config = re.sub(r"@([A-Z_0-9]+)@", lambda m: values.get(m[1], ""), template)
    config, replacements = re.subn(
        r'("Zicfilp"\s*:\s*\{\s*"supported"\s*:)\s*true', r'\1 false', config)
    if replacements != 1:
        raise RuntimeError("upstream Zicfilp configuration changed")
    (build / "rv64.json").write_text(config)
    command = [
        "sail", "--strict-var", "--strict-bitvector", "--strict-exponentials",
        "--require-version", "0.20.3", "--memo-z3-path", str(build / "sail_smt_cache"),
        "--config", str(build / "rv64.json"), "--lean", "--lean-output-dir", str(build),
        "--lean-force-output", "--lean-noncomputable",
        "--lean-import-file", "../handwritten_support/RiscvExtras.lean",
        "--lean-lib-path", str(ROOT / "vendor/lean-sail"),
    ]
    for name in ["instruction", "instr_info", "HartState", "ExecutionResult", "Step"]:
        command += ["--lean-non-beq-type", name]
    for prefix in ["encdec", "encdec_compressed"]:
        for suffix in ["forwards", "backwards", "forwards_matches", "backwards_matches"]:
            command += ["--lean-noncomputable-function", f"{prefix}_{suffix}"]
    command += ["-o", "RiscvSail", "riscv.sail_project", "I_insts", "Zicsr_insts", "postlude"]
    print(f"Generating Sail model at {REVISION}; log: {build / 'generation.log'}", flush=True)
    with (build / "generation.log").open("w") as log:
        result = subprocess.run(command, cwd=source / "model", stdout=log,
                                stderr=subprocess.STDOUT, timeout=1200)
    if result.returncode:
        raise RuntimeError((build / "generation.log").read_text()[-6000:])
    generated = build / "RiscvSail"
    for old in destination.rglob("*.lean"):
        if ".lake" not in old.parts and not (generated / old.relative_to(destination)).exists():
            old.unlink()
    shutil.copytree(generated, destination, dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"))
    # Lean 4.35 added a do-element named `assert`. Qualify Sail's existing
    # function calls, preserving string literals and the function definition.
    for path in destination.rglob("*.lean"):
        if ".lake" in path.parts or path.name == "SpecializationV1.lean":
            continue
        text = path.read_text()
        qualified = re.sub(r'"(?:[^"\\]|\\.)*"|(?<![\w.])assert\b',
                           lambda m: m[0] if m[0].startswith('"') else "RiscvSail.assert", text)
        if qualified != text:
            path.write_text(qualified)
    shutil.copy2(source / "LICENCE", destination / "LICENSE")
    shutil.copy2(build / "rv64.json", destination / "rv64.json")
    (destination / "PROVENANCE").write_text(
        f"https://github.com/riscv/sail-riscv\n{REVISION}\n{version}\n"
        "Modules: I_insts Zicsr_insts postlude (and their project dependencies)\n"
        "Zicfilp support is disabled in the configuration.\n"
        "Compatibility patch: qualify Sail assert calls for Lean 4.35.\n"
        "Configuration: rv64.json\nRegenerate: python3 scripts/setup_sail.py --regenerate\n"
    )
    # Local dependencies make the checked-in model build without network access.
    (destination / "lakefile.toml").write_text(
        'name = "riscv_sail"\ndefaultTargets = ["RiscvSail"]\n'
        'moreLeanArgs = ["--tstack=400000"]\n\n'
        '[[lean_lib]]\nname = "RiscvSail"\n\n'
        '[[require]]\nname = "lean-sail"\npath = "../lean-sail"\n'
    )
    (destination / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
    print(f"Generated {destination}")


if __name__ == "__main__":
    main()
