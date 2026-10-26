import Riscvc.Heap.Syntax
import Riscvc.Heap.LLVM

namespace Riscvc.Heap.Scheduler

riscv_struct Process { pid : u64, remaining : u64, next : ptr Process }
riscv_struct State {
  head : ptr Process, tail : ptr Process, free : ptr Process,
  count : u64, ticks : u64, lastPid : u64
}

/-- The caller supplies a disjoint, null-terminated pool of process slots.
Only the pool's links need initialization. This begins a fresh scheduler. -/
def init := [riscv_mem|
  fun (state : ptr State) (pool : ptr Process) locals => {
    state.head := null;
    state.tail := null;
    state.free := pool;
    state.count := 0;
    state.ticks := 0;
    state.lastPid := 0;
    return 0 : u64
  }]

/-- Execute one scheduler command, including all queue and free-list mutations.

Operations: 1 = add(pid, remaining), 2 = remove(pid), 3 = run one time slice.
Results: 0 = success, 1 = invalid command/arguments, 2 = duplicate PID,
3 = pool exhausted, 4 = PID not found, 5 = idle. Errors leave memory unchanged.
PIDs and initial time slices must be nonzero. A successful tick records the PID,
decrements its remaining work, and either rotates it to the tail or recycles it.
The caller supplies exclusive access to the initialized state and its pool. -/
def step := [riscv_mem|
  fun (state : ptr State) (op : u64) (pid : u64) (work : u64)
  locals (cur : ptr Process) (prev : ptr Process) (node : ptr Process)
    (tail : ptr Process) (duplicate : u64) (result : u64) => {
    result := 1;
    if op == 1 {
      if pid {
        if work {
          cur := state.head;
          while cur {
            if cur.pid == pid { duplicate := 1; } else {};
            cur := cur.next;
          };
          if duplicate {
            result := 2;
          } else {
            node := state.free;
            if node {
              state.free := node.next;
              node.pid := pid;
              node.remaining := work;
              node.next := null;
              tail := state.tail;
              if tail { tail.next := node; } else { state.head := node; };
              state.tail := node;
              state.count := state.count + 1;
              result := 0;
            } else { result := 3; };
          };
        } else {};
      } else {};
    } else {};
    if op == 2 {
      result := 4;
      cur := state.head;
      while cur {
        if cur.pid == pid {
          if prev { prev.next := cur.next; } else { state.head := cur.next; };
          if state.tail == cur { state.tail := prev; } else {};
          cur.pid := 0;
          cur.remaining := 0;
          cur.next := state.free;
          state.free := cur;
          state.count := state.count - 1;
          result := 0;
          cur := null;
        } else {
          prev := cur;
          cur := cur.next;
        };
      };
    } else {};
    if op == 3 {
      cur := state.head;
      if cur {
        state.lastPid := cur.pid;
        state.ticks := state.ticks + 1;
        cur.remaining := cur.remaining - 1;
        if cur.remaining {
          if cur.next {
            state.head := cur.next;
            tail := state.tail;
            tail.next := cur;
            cur.next := null;
            state.tail := cur;
          } else {};
        } else {
          state.head := cur.next;
          if state.head {} else { state.tail := null; };
          cur.pid := 0;
          cur.next := state.free;
          state.free := cur;
          state.count := state.count - 1;
        };
        result := 0;
      } else { result := 5; };
    } else {};
    return result : u64
  }]

end Riscvc.Heap.Scheduler
