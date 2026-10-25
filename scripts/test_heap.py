#!/usr/bin/env python3
"""Test the typed heap DSL, LLVM O0/O2 code, and actual RV64 execution in Sail.

The append source theorem is kernel-checked. These runtime tests and the lifting
certificate are separate checks, not a whole-function binary equivalence proof.
"""

import argparse
import ctypes
from pathlib import Path
import random
import re
import subprocess
import sys

from lift_binary import ROOT, pointer_flags, run


BUILD = ROOT / "build/heap-tests"


class Node(ctypes.Structure):
    _fields_ = [("value", ctypes.c_uint64), ("next", ctypes.c_void_p)]


def native(library: Path) -> None:
    if ctypes.sizeof(ctypes.c_void_p) != 8 or ctypes.sizeof(Node) != 16:
        raise RuntimeError("Heap tests require a 64-bit host")
    lib = ctypes.CDLL(str(library))
    append = lib.list_append
    append.argtypes, append.restype = [ctypes.c_void_p, ctypes.c_void_p], ctypes.c_void_p
    set_value = lib.node_set_value
    set_value.argtypes, set_value.restype = [ctypes.c_void_p, ctypes.c_uint64], ctypes.c_uint64
    head = lib.node_head_or_zero
    head.argtypes, head.restype = [ctypes.c_void_p], ctypes.c_uint64
    if head(None) != 0:
        raise AssertionError("Null guard failed")
    rng = random.Random(7351)
    sizes = [(n, m) for n in range(9) for m in range(9)]
    sizes += [(rng.randrange(60), rng.randrange(60)) for _ in range(100)]
    sizes += [(4096, 37), (1, 4096), (4096, 0)]
    for n, m in sizes:
        arena = (Node * (n + m + 3))()
        for cell in arena:
            cell.value = rng.getrandbits(64)
            cell.next = None
        order = list(range(1, n + m + 1))
        rng.shuffle(order)
        left, right = order[:n], order[n:]
        address = lambda i: ctypes.addressof(arena[i])
        for chain in (left, right):
            for a, b in zip(chain, chain[1:]):
                arena[a].next = address(b)
        a = address(left[0]) if left else None
        b = address(right[0]) if right else None
        original = bytes(arena)
        expected = bytearray(original)
        if left:
            offset = left[-1] * ctypes.sizeof(Node) + Node.next.offset
            expected[offset:offset + 8] = int(b or 0).to_bytes(8, sys.byteorder)
        result = append(a, b)
        if result != (a or b) or bytes(arena) != expected:
            raise AssertionError(f"Append result/frame mismatch for {n}, {m}")
        cursor = result
        for index in order:
            if cursor != address(index):
                raise AssertionError("Wrong node identity/order")
            cursor = ctypes.cast(cursor, ctypes.POINTER(Node)).contents.next
        if cursor:
            raise AssertionError("Result is not null terminated")
        # Both numeric and pointer fields must use their declared offsets/types.
        old_next = arena[0].next
        if set_value(address(0), 0xffffffffffffffff) != 0xffffffffffffffff:
            raise AssertionError("Word field write/read failed")
        if arena[0].next != old_next or head(address(0)) != arena[0].value:
            raise AssertionError("Field layout mismatch")
    print(f"{library.name}: {len(sizes)} native append/frame cases passed.", flush=True)


def harness() -> str:
    text = [".option norvc", ".option norelax", ".section .text.init", ".globl _start",
            "_start:", "  la sp, stack_top"]
    data = [".section .data", ".balign 8"]
    preserved = ["s0", "s1", *[f"s{i}" for i in range(2, 12)], "gp", "tp"]
    for i, reg in enumerate(preserved):
        text.append(f"  li {reg}, {7000 + i}")
    cases = [(0, 0), (0, 3), (1, 0), (1, 1), (4, 3), (64, 17)]
    rng = random.Random(1234)
    for case, (n, m) in enumerate(cases):
        ids = list(range(n + m))
        rng.shuffle(ids)
        left, right = ids[:n], ids[n:]
        label = lambda i: f"case{case}_node{i}"
        links = {i: "0" for i in ids}
        for chain in (left, right):
            for a, b in zip(chain, chain[1:]):
                links[a] = label(b)
        data += [f"case{case}_guard: .dword 123456789"]
        for i in range(n + m):
            data += [f"{label(i)}: .dword {i + 100}, {links[i]}"]
        for reg, chain in [("a0", left), ("a1", right)]:
            text.append(f"  la {reg}, {label(chain[0])}" if chain else f"  li {reg}, 0")
        text.append("  call list_append")
        out = left or right
        text += [f"  la t0, {label(out[0])}" if out else "  li t0, 0", "  bne a0, t0, failure"]
        if left:
            links[left[-1]] = label(right[0]) if right else "0"
        for i in ids:
            text += [f"  la t0, {label(i)}", "  ld t1, 0(t0)", f"  li t2, {i + 100}",
                     "  bne t1, t2, failure", "  ld t1, 8(t0)",
                     f"  la t2, {links[i]}" if links[i] != "0" else "  li t2, 0",
                     "  bne t1, t2, failure"]
        text += [f"  la t0, case{case}_guard", "  ld t1, 0(t0)", "  li t2, 123456789",
                 "  bne t1, t2, failure"]
    for i, reg in enumerate(preserved):
        text += [f"  li t0, {7000 + i}", f"  bne {reg}, t0, failure"]
    text += ["  la t0, stack_top", "  bne sp, t0, failure", "  li a0, 1", "  j finish",
             "failure:", "  li a0, 3", "finish:", "  la t0, tohost", "  sd a0, 0(t0)",
             "halt:", "  j halt", ".section .tohost,\"aw\",@progbits", ".balign 8",
             ".globl tohost", "tohost: .dword 0", ".globl fromhost", "fromhost: .dword 0"]
    data += [".section .bss", ".balign 16", "stack: .space 8192", "stack_top:"]
    return "\n".join(text + data) + "\n"


def reject_bad_types() -> None:
    prelude = "import Riscvc.Heap.Examples\nopen Riscvc.Heap Riscvc.Heap.Examples\n"
    cases = {
        "word-as-pointer": "def bad := [riscv_mem| fun (p : u64) locals => { return p.next : ptr Node }]",
        "wrong-field-type": "def bad := [riscv_mem| fun (p : ptr Node) locals => { p.next := 42; return p : ptr Node }]",
        "wrong-pointer-type": "riscv_struct Other { value : u64 }\ndef bad := [riscv_mem| fun (p : ptr Node) (q : ptr Other) locals => { p.next := q; return p : ptr Node }]",
        "unknown-field": "def bad := [riscv_mem| fun (p : ptr Node) locals => { return p.missing : u64 }]",
        "duplicate-local": "def bad := [riscv_mem| fun (p : ptr Node) locals (p : ptr Node) => { return p : ptr Node }]",
    }
    for name, body in cases.items():
        path = BUILD / f"{name}.lean"
        path.write_text(prelude + body + "\n")
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                capture_output=True, text=True, timeout=60)
        (BUILD / f"{name}.log").write_text(result.stdout + result.stderr)
        if result.returncode == 0 or not re.search(r"\berror(?:\([^)]*\))?:", result.stdout) or "unexpected token" in result.stdout:
            raise AssertionError(f"Expected type/scope rejection for {name}: {result.stdout}")
    print("Typed frontend rejected invalid fields, assignments, pointers, and duplicate names.", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-sail", action="store_true")
    parser.add_argument("--sail", type=Path, default=ROOT.parent / "sail-riscv/build/c_emulator/sail_riscv_sim")
    parser.add_argument("--native-library", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.native_library:
        native(args.native_library.resolve())
        return
    BUILD.mkdir(parents=True, exist_ok=True)
    print(run(["lake", "test"]), end="", flush=True)
    reject_bad_types()
    source = BUILD / "heap.ll"
    source.write_text("\n".join(run(["lake", "exe", "riscvc", "--llvm", name])
                                for name in ("list_append", "node_set_value", "node_head_or_zero")))
    asm = BUILD / "harness.S"
    asm.write_text(harness())
    for level in (0, 2):
        module, library, obj, elf = [BUILD / f"heap-O{level}{ext}" for ext in (".ll", ".so", ".o", ".elf")]
        run(["opt", *pointer_flags("opt"), "-S", f"-passes=default<O{level}>", "-verify-each", str(source), "-o", str(module)])
        run(["clang", *pointer_flags("clang"), "-Wno-override-module", "-shared", "-fPIC", f"-O{level}", str(module), "-o", str(library)])
        print(run([sys.executable, str(Path(__file__).resolve()), "--native-library", str(library)], timeout=60), end="", flush=True)
        run(["llc", *pointer_flags("llc"), "-mtriple=riscv64-unknown-elf", "-target-abi=lp64",
             f"-O={level}", "-filetype=obj", str(module), "-o", str(obj)])
        run(["clang", "--target=riscv64-unknown-elf", "-march=rv64i", "-mabi=lp64", "-nostdlib", "-fuse-ld=lld",
             "-Wl,--no-relax", "-Wl,-T,tests/link.ld", str(asm), str(obj), "-o", str(elf)])
        if not args.skip_sail:
            output = run([str(args.sail), "--inst-limit", "1000000", str(elf)], timeout=120)
            (BUILD / f"sail-O{level}.log").write_text(output)
            if "SUCCESS" not in output.splitlines():
                raise AssertionError("Sail did not reach successful completion")
            print(f"O{level}: Sail checked lists, memory frame, and callee-saved registers.", flush=True)
    print(run([sys.executable, "scripts/lift_binary.py", "--example", "list_append",
               "--output", str(BUILD / "lifted")]), end="", flush=True)


if __name__ == "__main__":
    main()
