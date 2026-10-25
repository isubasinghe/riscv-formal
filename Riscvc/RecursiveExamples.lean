import Riscvc

namespace Riscvc.RecursiveExamples

/-- Ordinary recursion: the addition needs the result of the recursive call. -/
def sumTo : RecFn 1 := [riscv_rec| fun sumTo n =>
  if n then n + sumTo(n - 1) else 0
  termination_by n
]

/-- Tail recursion: this call becomes a jump and reuses the current frame. -/
def countUp : RecFn 2 := [riscv_rec| fun countUp n acc =>
  if n then countUp(n - 1, acc + 1) else acc
  termination_by n
]

/-- Tail calls must stage arguments simultaneously, including permutations. -/
def swapLoop : RecFn 3 := [riscv_rec| fun swapLoop n x y =>
  if n then swapLoop(n - 1, y, x) else x
  termination_by n
]

/-- Both the saved local and the other operand must survive the call. -/
def savedLocal : RecFn 2 := [riscv_rec| fun savedLocal n x =>
  let saved := x ^ 0xfedcba9876543210;
  if n then saved + savedLocal(n - 1, x + 3) else saved
  termination_by n
]

/-- Two calls in one expression exercise independent call frames and returns. -/
def binaryTree : RecFn 1 := [riscv_rec| fun binaryTree n =>
  if n then binaryTree(n - 1) + binaryTree(n - 1) else 1
  termination_by n
]

/-- A recursive result can control a later branch. -/
def recursiveCondition : RecFn 1 := [riscv_rec| fun recursiveCondition n =>
  if n then (if recursiveCondition(n - 1) then 0 else 1) else 1
  termination_by n
]

/-- An unselected recursive arm has no termination obligation. -/
def deadBranch : RecFn 1 := [riscv_rec| fun deadBranch n =>
  if 0 then deadBranch(n) else n
  termination_by n
]

def countSecond : RecFn 2 := [riscv_rec| fun countSecond acc n =>
  if n then countSecond(acc + 1, n - 1) else acc
  termination_by n
  decreasing_by word_decreasing
]

def callInLet : RecFn 2 := [riscv_rec| fun callInLet n acc =>
  if n then
    let x := callInLet(n - 1, acc + 1);
    callInLet(n - 1, x + 2)
  else acc
  termination_by n
]

theorem countUp_step (n acc : Word) : countUp.eval (Env.two n acc) =
    if n = 0 then acc else countUp.eval (Env.two (n - 1) (acc + 1)) := by
  rw [RecFn.eval_eq]
  change (if n = 0 then acc else countUp.eval _) = _
  split
  · rfl
  · congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j

/-- The invariant holds for every word, including accumulator wraparound. -/
theorem countUp_correct (n acc : Word) : countUp.eval (Env.two n acc) = n + acc := by
  rw [countUp_step]
  split
  · rename_i h
    subst n
    exact (BitVec.zero_add acc).symm
  · rw [countUp_correct (n - 1) (acc + 1)]
    calc
      (n - 1) + (acc + 1) = (n - 1 + 1) + acc := by
        rw [BitVec.add_comm acc 1, ← BitVec.add_assoc]
      _ = n + acc := by rw [BitVec.sub_add_cancel]
termination_by n.toNat
decreasing_by exact word_pred_decreases n (by assumption)

theorem countUp_compiled (n acc : Word) : countUp.execute (Env.two n acc) = n + acc := by
  rw [RecFn.execute_correct, countUp_correct]

theorem sumTo_step (n : Word) : sumTo.eval (Env.one n) =
    if n = 0 then 0 else n + sumTo.eval (Env.one (n - 1)) := by
  rw [RecFn.eval_eq]
  change (if n = 0 then 0 else n + sumTo.eval _) = _
  split
  · rfl
  · congr 2
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i

def triangle : Nat → Word
  | 0 => 0
  | n + 1 => BitVec.ofNat 64 (n + 1) + triangle n

theorem sumTo_correct (n : Word) : sumTo.eval (Env.one n) = triangle n.toNat := by
  rw [sumTo_step]
  split
  · rename_i h
    subst n
    rfl
  · rename_i h
    rw [sumTo_correct (n - 1)]
    have hpos : 0 < n.toNat := by
      have hne : n.toNat ≠ 0 := fun hz => h (BitVec.eq_of_toNat_eq hz)
      omega
    have hpred : (n - 1).toNat = n.toNat - 1 := by
      rw [BitVec.toNat_sub]
      change (2^64 - 1 + n.toNat) % 2^64 = n.toNat - 1
      have hn := n.isLt
      omega
    conv => rhs; rw [show n.toNat = (n.toNat - 1) + 1 by omega, triangle]
    rw [hpred, ← show n.toNat = (n.toNat - 1) + 1 by omega]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
termination_by n.toNat
decreasing_by exact word_pred_decreases n (by assumption)

theorem sumTo_compiled (n : Word) : sumTo.execute (Env.one n) = triangle n.toNat := by
  rw [RecFn.execute_correct, sumTo_correct]

structure Example where
  name : String
  arity : Nat
  program : RecFn arity
  inputs : List (Array Word)

private def smallCounts : List Word := [0, 1, 2, 3, 7, 16, 31]
private def payloads : List Word := [0, 1, 0x8000000000000000, 0xffffffffffffffff]

def examples : List Example := [
  ⟨"sum_to", 1, sumTo, (smallCounts ++ [128]).map (fun n => #[n])⟩,
  ⟨"count_up", 2, countUp, smallCounts.flatMap (fun n => payloads.map (fun x => #[n, x]))⟩,
  ⟨"swap_loop", 3, swapLoop, smallCounts.flatMap (fun n => payloads.map (fun x => #[n, x, x ^^^ 0x12345678]))⟩,
  ⟨"saved_local", 2, savedLocal, smallCounts.flatMap (fun n => payloads.map (fun x => #[n, x]))⟩,
  ⟨"binary_tree", 1, binaryTree, [0, 1, 2, 3, 5, 8].map (fun n => #[n])⟩,
  ⟨"recursive_condition", 1, recursiveCondition, smallCounts.map (fun n => #[n])⟩,
  ⟨"dead_branch", 1, deadBranch, payloads.map (fun n => #[n])⟩,
  ⟨"count_second", 2, countSecond, smallCounts.flatMap (fun n => payloads.map (fun x => #[x, n]))⟩,
  ⟨"call_in_let", 2, callInLet, [0, 1, 2, 3, 5].flatMap (fun n => payloads.map (fun x => #[n, x]))⟩
]

end Riscvc.RecursiveExamples
