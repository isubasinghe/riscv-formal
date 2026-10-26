#!/usr/bin/env python3
"""Check Lean scheduler proofs and reject binary/source drift in both functions.

Requires artifacts produced by verify_scheduler.py or lift_binary.py.
The source mutation is compiled in a temporary module overlay; repository sources
and the original ELF are never edited.
"""

import os
from pathlib import Path
import re
import subprocess
import tempfile

from lift_binary import ROOT, certificate_source, read_elf, run
from test_scheduler_equivalence import immediate, patch_word, store_offset
from verify_scheduler import BUILD, INIT_PROOF, STEP_PROOF, check_source_proofs, load_manifest


def rejected(command, *, env=None):
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if result.returncode == 0:
        raise AssertionError(f"Lean accepted a deliberately false certificate: {command}")
    return result.stdout


def program_match_source(data, entry, nodes, module):
    """Focus a mutation test on the exact program-equality obligation.

    Full byte parsing and decoding are checked by the positive ELF certificate.
    Rechecking all 122 decoders is unnecessary to reject a different program.
    The node definitions and equality theorem are taken from the same generator.
    """
    source = certificate_source(data, entry, nodes, module)
    prefixes = ("import ", "set_option ", "namespace ", "open ",
                "def node", "def program :", "def contract :", "theorem program_matches", "end ")
    return "\n".join(line for line in source.splitlines() if line.startswith(prefixes)) + "\n"


def main():
    BUILD.mkdir(parents=True, exist_ok=True)
    check_source_proofs(BUILD)
    manifest, data, nodes = load_manifest(BUILD / "init")
    output = BUILD / "lean-negative-tests"
    output.mkdir(parents=True, exist_ok=True)

    changed = patch_word(data, nodes[0].address, store_offset(nodes[0].word, 16))
    entry, changed_nodes = read_elf(changed)
    source = certificate_source(changed, entry, changed_nodes, INIT_PROOF)
    wrong = output / "WrongBinary.lean"
    wrong.write_text(source)
    diagnostic = rejected(["lake", "env", "lean", "--tstack=131072", str(wrong)])
    expected_line = next(i for i, line in enumerate(source.splitlines(), 1)
                         if line.startswith("theorem program_matches"))
    if f"WrongBinary.lean:{expected_line}:" not in diagnostic:
        raise AssertionError(f"Mutation failed outside the program-equality check:\n{diagnostic}")
    (output / "WrongBinary.log").write_text(diagnostic)
    print("Lean rejected the changed ELF at program_matches.", flush=True)

    step_manifest, step_data, step_nodes = load_manifest(BUILD / "step")
    decrement = step_nodes[90]
    changed_step = patch_word(step_data, decrement.address, immediate(decrement.word, 1))
    entry, changed_nodes = read_elf(changed_step)
    source = program_match_source(changed_step, entry, changed_nodes, STEP_PROOF)
    wrong_step = output / "WrongStepBinary.lean"
    wrong_step.write_text(source)
    diagnostic = rejected(["lake", "env", "lean", str(wrong_step)])
    expected_line = next(i for i, line in enumerate(source.splitlines(), 1)
                         if line.startswith("theorem program_matches"))
    if f"WrongStepBinary.lean:{expected_line}:" not in diagnostic:
        raise AssertionError(f"Step mutation failed outside program_matches:\n{diagnostic}")
    (output / "WrongStepBinary.log").write_text(diagnostic)
    print("Lean rejected the changed step ELF at program_matches.", flush=True)

    original = (ROOT / "examples/Scheduler.lean").read_text()
    needle = "    state.count := 0;"
    if original.count(needle) != 1:
        raise AssertionError("Source mutation site changed; update this negative control")
    changed_source = original.replace(needle, "    state.count := 1;", 1)
    proof_path = ROOT / "examples/proof/SchedulerInit.lean"
    proof = proof_path.read_text()
    first = next(i for i, line in enumerate(proof.splitlines(), 1)
                 if line.startswith("theorem source_correct"))
    last = next(i for i, line in enumerate(proof.splitlines(), 1)
                if line.startswith("private def advance"))
    lean = run(["lake", "env", "which", "lean"]).strip()
    base_path = run(["lake", "env", "printenv", "LEAN_PATH"]).strip()
    with tempfile.TemporaryDirectory(prefix="scheduler-lean-source-") as temporary:
        directory = Path(temporary)
        module = directory / "examples/Scheduler.lean"
        module.parent.mkdir(parents=True)
        module.write_text(changed_source)
        run(["lake", "env", "lean", f"--root={directory}", str(module),
             "-o", str(module.with_suffix(".olean"))])
        env = os.environ.copy()
        env["LEAN_PATH"] = str(directory) + os.pathsep + base_path
        diagnostic = rejected([lean, "--tstack=131072", str(proof_path)], env=env)
    locations = [int(line) for line in re.findall(r"SchedulerInit\.lean:(\d+):\d+: error:", diagnostic)]
    if not any(first <= line < last for line in locations):
        raise AssertionError(f"Source drift failed outside source_correct:\n{diagnostic}")
    (output / "SourceDrift.log").write_text(diagnostic)
    print("Lean rejected the changed DSL initializer at source_correct.", flush=True)

    needle = "            result := 2;"
    if original.count(needle) != 1:
        raise AssertionError("Duplicate-result mutation site changed; update this negative control")
    changed_source = original.replace(needle, "            result := 6;", 1)
    with tempfile.TemporaryDirectory(prefix="scheduler-lean-step-source-") as temporary:
        directory = Path(temporary)
        env = os.environ.copy()
        env["LEAN_PATH"] = str(directory) + os.pathsep + base_path
        # Rebuild the dependency chain so no old source-dependent lemma is
        # imported while checking the mutated DSL.
        for relative in ("examples/Scheduler.lean", "examples/proof/SchedulerStepProgram.lean",
                         "examples/proof/SchedulerStepTactics.lean"):
            module = directory / relative
            module.parent.mkdir(parents=True, exist_ok=True)
            module.write_text(changed_source if relative == "examples/Scheduler.lean"
                              else (ROOT / relative).read_text())
            result = subprocess.run([lean, f"--root={directory}", str(module),
                                     "-o", str(module.with_suffix(".olean"))], cwd=ROOT, env=env,
                                    text=True, capture_output=True, timeout=180)
            if result.returncode:
                raise AssertionError(f"Failed to prepare source overlay:\n{result.stdout}{result.stderr}")
        segments = ROOT / "examples/proof/SchedulerStepSegments.lean"
        diagnostic = rejected([lean, "--tstack=131072", str(segments)], env=env)
    segment_text = segments.read_text().splitlines()
    first = next(i for i, line in enumerate(segment_text, 1) if line.startswith("theorem add_segment"))
    last = next(i for i, line in enumerate(segment_text, 1) if line.startswith("theorem remove_first_segment"))
    locations = [int(line) for line in re.findall(r"SchedulerStepSegments\.lean:(\d+):\d+: error:", diagnostic)]
    if not any(first <= line < last for line in locations):
        raise AssertionError(f"Step source drift failed outside add_segment:\n{diagnostic}")
    (output / "StepSourceDrift.log").write_text(diagnostic)
    print("Lean rejected the changed DSL duplicate result at add_segment.", flush=True)
    if (ROOT / "examples/Scheduler.lean").read_text() != original:
        raise AssertionError("Repository source changed during negative controls")
    if Path(manifest["elf"]).read_bytes() != data:
        raise AssertionError("Original ELF changed during negative controls")
    if Path(step_manifest["elf"]).read_bytes() != step_data:
        raise AssertionError("Original step ELF changed during negative controls")


if __name__ == "__main__":
    main()
