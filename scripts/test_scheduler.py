#!/usr/bin/env python3
"""Check the scheduler against a queue model in Lean, native code, and RV64 Sail."""

import argparse
import ctypes
from pathlib import Path
import random
import subprocess
import sys

from lift_binary import ROOT, pointer_flags, run
from run_scheduler import compile_native, emit


BUILD = ROOT / "build/scheduler-tests"
MASK = (1 << 64) - 1
GUARD = 0x123456789ABCDEF


class Model:
    """Queue operations on Python lists, independent of pointer rewiring."""

    def __init__(self, order: list[int]):
        self.ready: list[int] = []
        self.free = order.copy()
        self.slots = [(0, 0)] * len(order)
        self.ticks = self.last = 0

    def step(self, op: int, pid: int, work: int) -> int:
        if op == 1:
            if not pid or not work:
                return 1
            if any(self.slots[i][0] == pid for i in self.ready):
                return 2
            if not self.free:
                return 3
            i = self.free.pop(0)
            self.slots[i] = (pid, work)
            self.ready.append(i)
        elif op == 2:
            i = next((i for i in self.ready if self.slots[i][0] == pid), None)
            if i is None:
                return 4
            self.ready.remove(i)
            self.slots[i] = (0, 0)
            self.free.insert(0, i)
        elif op == 3:
            if not self.ready:
                return 5
            i = self.ready.pop(0)
            pid, work = self.slots[i]
            self.last, self.ticks = pid, (self.ticks + 1) & MASK
            if work == 1:
                self.slots[i] = (0, 0)
                self.free.insert(0, i)
            else:
                self.slots[i] = (pid, work - 1)
                self.ready.append(i)
        else:
            return 1
        return 0

    def values(self, addresses):
        def head(indices):
            return addresses[indices[0]] if indices else 0

        links = [0] * len(self.slots)
        for chain in (self.ready, self.free):
            for left, right in zip(chain, chain[1:]):
                links[left] = addresses[right]
        state = [head(self.ready), head(self.ready[-1:]), head(self.free),
                 len(self.ready), self.ticks, self.last]
        slots = [[pid, work, links[i]] for i, (pid, work) in enumerate(self.slots)]
        return state, slots


def lifecycle():
    return [
        (3, 0, 0), (2, 99, 0), (1, 0, 1), (1, 1, 0), (99, 0, 0),
        (1, 10, 3), (1, 20, 2), (1, 30, 1), (1, 40, 4),
        (1, 10, 1), (1, 50, 2),  # duplicate and exhaustion in a four-slot pool
        (2, 20, 0), (1, 50, 2),  # remove middle; reuse its slot
        (2, 50, 0), (2, 10, 0), (2, 40, 0),  # tail, head, tail
        (3, 0, 0), (3, 0, 0),  # complete the singleton; idle
        (1, 60, 2), (3, 0, 0), (3, 0, 0),  # singleton rotation and completion
        (1, 70, 3), (1, 80, 1), (1, 90, 2),
        (3, 0, 0), (3, 0, 0), (3, 0, 0), (3, 0, 0), (3, 0, 0), (3, 0, 0),
        (1, MASK, MASK), (3, 0, 0), (2, MASK, 0),  # full-width PID and work
    ]


def commands(random_count=0):
    cases = lifecycle()
    rng = random.Random(534)
    for _ in range(random_count):
        cases.append((rng.choice([1, 1, 1, 2, 2, 3, 3, 99]),
                      rng.randrange(12), rng.randrange(5)))
    # Drain, reuse every slot, and finish the processes that were newly added.
    cases += [(3, 0, 0)] * 100
    cases += [(1, i, 1) for i in range(100, 120)]
    cases += [(3, 0, 0)] * 25
    return cases


class Process(ctypes.Structure):
    _fields_ = [("pid", ctypes.c_uint64), ("remaining", ctypes.c_uint64), ("next", ctypes.c_void_p)]


class State(ctypes.Structure):
    _fields_ = [(name, ctypes.c_void_p) for name in ("head", "tail", "free")] + [
        (name, ctypes.c_uint64) for name in ("count", "ticks", "last")]


def native(library: Path):
    lib = ctypes.CDLL(str(library))
    lib.scheduler_init.argtypes = [ctypes.POINTER(State), ctypes.c_void_p]
    lib.scheduler_init.restype = ctypes.c_uint64
    lib.scheduler_step.argtypes = [ctypes.POINTER(State)] + [ctypes.c_uint64] * 3
    lib.scheduler_step.restype = ctypes.c_uint64
    total = 0
    for capacity in (0, 1, 2, 4, 17):
        class Arena(ctypes.Structure):
            _fields_ = [("guard1", ctypes.c_uint64), ("state", State),
                        ("guard2", ctypes.c_uint64), ("pool", Process * capacity),
                        ("guard3", ctypes.c_uint64)]

        arena = Arena()
        arena.guard1 = arena.guard2 = arena.guard3 = GUARD
        ctypes.memset(ctypes.byref(arena.state), 0xA5, ctypes.sizeof(State))
        addresses = [ctypes.addressof(p) for p in arena.pool]
        order = list(range(capacity))
        random.Random(capacity).shuffle(order)
        for left, right in zip(order, order[1:]):
            arena.pool[left].next = addresses[right]
        model = Model(order)

        def check():
            state, slots = model.values(addresses)
            assert [getattr(arena.state, name) or 0 for name, _ in State._fields_] == state
            assert [[p.pid, p.remaining, p.next or 0] for p in arena.pool] == slots
            assert arena.guard1 == arena.guard2 == arena.guard3 == GUARD

        assert lib.scheduler_init(ctypes.byref(arena.state), addresses[order[0]] if order else None) == 0
        check()
        # The clock is a u64 counter: its overflow must not affect queue behavior.
        arena.state.ticks = model.ticks = MASK
        for command in commands(500):
            expected = model.step(*command)
            actual = lib.scheduler_step(ctypes.byref(arena.state), *command)
            assert actual == expected, (capacity, command, actual, expected)
            check()
            total += 1
    print(f"{library.name}: {total} model comparisons, pool partitions, and memory guards passed.", flush=True)


def source_checks():
    state_address = 4096
    addresses = [8192 + i * 32 for i in range(4)]
    model = Model([2, 0, 3, 1])

    def cells():
        state, slots = model.values(addresses)
        return ([(state_address + 8 * i, v) for i, v in enumerate(state)] +
                [(address + 8 * i, v) for address, slot in zip(addresses, slots)
                 for i, v in enumerate(slot)] + [(9000, GUARD)])

    initial = [(address, GUARD if state_address <= address < state_address + 48 else value)
               for address, value in cells()]
    steps = []
    for op, pid, work in lifecycle():
        status = model.step(op, pid, work)
        steps.append(f"({op}, {pid}, {work}, {status}, {cells()})")
    step_text = ",\n".join(steps)
    text = f"""import examples.Scheduler
open Riscvc Riscvc.Heap
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def initialCells : List (Nat × Nat) := {initial}
def cases : Array (Nat × Nat × Nat × Nat × List (Nat × Nat)) := #[
{step_text}]
def check : IO Unit := do
  let before : Memory := fun address => (initialCells.lookup address).map (BitVec.ofNat 64)
  let .ok (zero, initialized) := Scheduler.init.run 64
      (fun i => if i.val = 0 then {state_address} else {addresses[2]}) before |
    throw (IO.userError "scheduler initialization failed")
  unless zero == 0 do throw (IO.userError "initialization status")
  let mut memory := initialized
  for entry in cases do
    let (op, pid, work, status, expected) : Nat × Nat × Nat × Nat × List (Nat × Nat) := entry
    let args : Array Word := #[{state_address}, BitVec.ofNat 64 op, BitVec.ofNat 64 pid, BitVec.ofNat 64 work]
    let .ok (result, after) := Scheduler.step.run 512 (fun i => args[i.val]!) memory |
      throw (IO.userError s!"scheduler source failed: {{op}} {{pid}} {{work}}")
    unless result.toNat == status do throw (IO.userError "scheduler source status mismatch")
    for (address, value) in expected do
      unless after address == some (BitVec.ofNat 64 value) do
        throw (IO.userError s!"scheduler source memory mismatch at {{address}}")
    memory := after
  IO.println "Scheduler source interpreter: lifecycle, errors, recycling, and frame checks passed."
#eval check
"""
    path = BUILD / "SourceChecks.lean"
    path.write_text(text)
    print(run(["lake", "env", "lean", str(path)]), end="", flush=True)


def harness() -> str:
    model = Model([2, 0, 3, 1])
    labels = [f"process{i}" for i in range(4)]
    _, initial_slots = model.values(labels)
    text = [".option norvc", ".option norelax", ".section .text.init", ".globl _start",
            "_start:", "  la sp, stack_top"]
    preserved = [*[f"s{i}" for i in range(12)], "gp", "tp"]
    for i, reg in enumerate(preserved):
        text.append(f"  li {reg}, {7000 + i}")

    def load(reg, value):
        return f"  la {reg}, {value}" if isinstance(value, str) else f"  li {reg}, {value if value < 1 << 63 else value - (1 << 64)}"

    def equal(left, right):
        # Conditional branches cannot reach the end of this large harness.
        text.extend([f"  beq {left}, {right}, 1f", "  j failure", "1:"])

    def check_memory(status):
        text.append(f"  li t0, {status}")
        equal("a0", "t0")
        state, slots = model.values(labels)
        for label, values in [("state", state), *zip(labels, slots), ("guard1", [GUARD]), ("guard2", [GUARD])]:
            text.append(f"  la t0, {label}")
            for i, value in enumerate(values):
                text.extend([f"  ld t1, {8 * i}(t0)", load("t2", value)])
                equal("t1", "t2")

    text += ["  la a0, state", "  la a1, process2", "  call scheduler_init"]
    check_memory(0)
    for op, pid, work in lifecycle():
        text.extend(["  la a0, state", load("a1", op), load("a2", pid), load("a3", work),
                     "  call scheduler_step"])
        check_memory(model.step(op, pid, work))
    for i, reg in enumerate(preserved):
        text.append(f"  li t0, {7000 + i}")
        equal(reg, "t0")
    text.append("  la t0, stack_top")
    equal("sp", "t0")
    text += ["  li a0, 1", "  j finish",
             "failure:", "  li a0, 3", "finish:", "  la t0, tohost", "  sd a0, 0(t0)",
             "halt:", "  j halt", ".section .tohost,\"aw\",@progbits", ".balign 8",
             ".globl tohost", "tohost: .dword 0", ".globl fromhost", "fromhost: .dword 0",
             ".section .data", ".balign 8", f"guard1: .dword {GUARD}",
             "state: .dword " + ", ".join([str(GUARD)] * 6)]
    for label, slot in zip(labels, initial_slots):
        text.append(f"{label}: .dword " + ", ".join(map(str, slot)))
    text += [f"guard2: .dword {GUARD}", ".section .bss", ".balign 16",
             "stack: .space 16384", "stack_top:"]
    return "\n".join(text) + "\n"


def cli(binary: Path):
    commands_text = "\n".join([
        "add 1 2", "add 1 3", "add 2 1", "add 3 1", "tick", "remove 1",
        "add 3 1", "tick 2", "remove 999", "add 0 1", "add -1 2",
        "add 18446744073709551616 1", "tick 0", "list", "quit", "add 99 1", "",
    ])
    result = subprocess.run([str(binary), "--capacity", "2"], input=commands_text,
                            text=True, capture_output=True, timeout=30, check=True)
    for expected in ["PID already exists", "process pool is full", "removed 1", "added 3",
                     "ran 2", "ran 3", "PID not found", "invalid command or arguments",
                     "ready: empty | processes=0 ticks=3"]:
        assert expected in result.stdout, (expected, result.stdout)
    assert "added 99" not in result.stdout
    assert result.stdout.count("error: expected") == 3, result.stdout
    demo = run([str(binary), "--demo", "--capacity", "3"])
    assert "ready: empty | processes=0 ticks=7" in demo, demo
    print(f"{binary.name}: interactive input, validation, demo, and exit checks passed.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-sail", action="store_true")
    parser.add_argument("--sail", type=Path, default=ROOT.parent / "sail-riscv/build/c_emulator/sail_riscv_sim")
    parser.add_argument("--native-library", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.native_library:
        native(args.native_library.resolve())
        return
    source = emit(BUILD)
    source_checks()
    asm = BUILD / "harness.S"
    asm.write_text(harness())
    for level in (0, 2):
        module = BUILD / f"scheduler-O{level}.ll"
        run(["opt", *pointer_flags("opt"), "-S", f"-passes=default<O{level}>", "-verify-each",
             str(source), "-o", str(module)])
        library = BUILD / f"scheduler-O{level}.so"
        compile_native(module, library, level, shared=True)
        print(run([sys.executable, str(Path(__file__).resolve()), "--native-library", str(library)]), end="", flush=True)
        binary = BUILD / f"scheduler-O{level}"
        compile_native(module, binary, level)
        cli(binary)
        obj, elf = BUILD / f"scheduler-O{level}.o", BUILD / f"scheduler-O{level}.elf"
        run(["llc", *pointer_flags("llc"), "-mtriple=riscv64-unknown-elf", "-target-abi=lp64",
             f"-O={level}", "-filetype=obj", str(module), "-o", str(obj)])
        run(["clang", "--target=riscv64-unknown-elf", "-march=rv64i", "-mabi=lp64", "-nostdlib",
             "-fuse-ld=lld", "-Wl,--no-relax", "-Wl,-T,tests/link.ld", str(asm), str(obj), "-o", str(elf)])
        if not args.skip_sail:
            output = run([str(args.sail), "--inst-limit", "3000000", str(elf)], timeout=120)
            (BUILD / f"sail-O{level}.log").write_text(output)
            assert "SUCCESS" in output.splitlines(), output
            print(f"O{level}: Sail checked the full scheduler lifecycle, memory, and preserved registers.", flush=True)


if __name__ == "__main__":
    main()
