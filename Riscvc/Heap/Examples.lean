import Riscvc.Heap.Syntax
import Riscvc.Heap.LLVM

namespace Riscvc.Heap.Examples

riscv_struct Node { value : u64, next : ptr Node }

/-- Concatenate two existing lists. The inputs must be valid, acyclic, and
disjoint. No allocation or recursion stack is required. -/
def append := [riscv_mem|
  fun (xs : ptr Node) (ys : ptr Node)
  locals (cur : ptr Node) (next : ptr Node) => {
    cur := xs;
    if xs {
      next := cur.next;
      while next {
        cur := next;
        next := cur.next;
      };
      cur.next := ys;
    } else {};
    return if xs then xs else ys : ptr Node
  }]

/-- Small examples exercise both field types and conditional memory access. -/
def setValue := [riscv_mem| fun (p : ptr Node) (v : u64) locals => {
  p.value := v;
  return p.value : u64
}]

def headOrZero := [riscv_mem| fun (p : ptr Node) locals => {
  return if p then p.value else 0 : u64
}]

end Riscvc.Heap.Examples
