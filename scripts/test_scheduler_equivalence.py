#!/usr/bin/env python3
"""Negative controls for scheduler translation validation; mutate real ELF bytes."""

import copy
from pathlib import Path
import struct

from lift_binary import read_elf, run
from verify_scheduler import BUILD, ROOT, load_manifest, obligation, solve


def patch_word(data: bytes, address: int, word: int) -> bytes:
    result = bytearray(data)
    phoff = struct.unpack_from("<Q", data, 32)[0]
    phnum = struct.unpack_from("<H", data, 56)[0]
    for i in range(phnum):
        kind, flags, offset, start, _, size, _, _ = struct.unpack_from("<IIQQQQQQ", data, phoff + 56 * i)
        if kind == 1 and flags & 1 and start <= address and address + 4 <= start + size:
            struct.pack_into("<I", result, offset + address - start, word)
            return bytes(result)
    raise ValueError("Mutation address outside executable bytes")


def immediate(word, value):
    return (word & 0xFFFFF) | ((value & 0xFFF) << 20)


def store_offset(word, value):
    return (word & ~((0x7F << 25) | (0x1F << 7))) | (((value >> 5) & 0x7F) << 25) | ((value & 31) << 7)


def main():
    import json

    print(run(["lake", "build", "examples.Scheduler"]), end="", flush=True)
    source = json.loads(run(["lake", "env", "lean", "--run", "examples/proof/SchedulerExport.lean"]))
    output = BUILD / "negative-tests"
    output.mkdir(parents=True, exist_ok=True)
    init_manifest, init_data, init = load_manifest(BUILD / "init")
    step_manifest, step_data, step = load_manifest(BUILD / "step")
    cases = [
        ("init-wrong-field", "init", "entry", init_data, init[0], store_offset(init[0].word, 16)),
        ("tick-increments-work", "step", "entry", step_data, step[90], immediate(step[90].word, 1)),
        ("remove-wrong-tail", "step", "remove_first", step_data, step[63], store_offset(step[63].word, 16)),
        ("duplicate-reported-success", "step", "add", step_data, step[20], immediate(step[20].word, 0)),
        ("traverse-wrong-field", "step", "add", step_data, step[12], immediate(step[12].word, 8)),
        ("uncovered-infinite-loop", "step", "entry", step_data, step[11], 0x0000006F),
    ]
    for name, kind, point, data, node, word in cases:
        mutated = patch_word(data, node.address, word)
        (output / f"{name}.elf").write_bytes(mutated)
        _, nodes = read_elf(mutated)
        query, _, _ = obligation(source[kind], nodes, point, kind)
        answer = solve(output / f"{name}.smt2", query, 60)
        assert answer == "sat", f"Validator accepted {name}: {answer}"
        print(f"Rejected {name}: counterexample found.", flush=True)

    changed_source = copy.deepcopy(source["step"])
    changed_source["returns"] = ["word", 0]
    query, _, _ = obligation(changed_source, step, "entry", "step")
    assert solve(output / "source-drift.smt2", query, 60) == "sat"
    print("Rejected source drift: counterexample found.", flush=True)

    for name, word in [("unsupported-opcode", 0), ("unexpected-indirect-jump", 0x00010067)]:
        bad = patch_word(init_data, init[-1].address, word)
        try:
            _, nodes = read_elf(bad)
            obligation(source["init"], nodes, "entry", "init")
        except ValueError:
            print(f"Rejected {name}: unsupported semantics.", flush=True)
        else:
            raise AssertionError(f"Validator accepted {name}")
    # Ensure negative tests never alter the artifacts used by the real proof run.
    assert Path(init_manifest["elf"]).read_bytes() == init_data
    assert Path(step_manifest["elf"]).read_bytes() == step_data


if __name__ == "__main__":
    main()
