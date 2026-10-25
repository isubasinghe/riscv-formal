import Riscvc

open Riscvc

def accumulate : RecFn 2 := [riscv_rec| fun accumulate n acc =>
  if n then accumulate(n - 1, acc + 1) else acc
  termination_by n
]

theorem accumulate_step (n acc : Word) : accumulate.eval (Env.two n acc) =
    if n = 0 then acc else accumulate.eval (Env.two (n - 1) (acc + 1)) := by
  rw [RecFn.eval_eq]
  change (if n = 0 then acc else accumulate.eval _) = _
  split
  · rfl
  · congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

/-- This specification includes accumulator overflow. -/
theorem accumulate_correct (n acc : Word) :
    accumulate.eval (Env.two n acc) = n + acc := by
  rw [accumulate_step]
  split
  · rename_i h
    subst n
    exact (BitVec.zero_add acc).symm
  · rw [accumulate_correct (n - 1) (acc + 1)]
    calc
      (n - 1) + (acc + 1) = (n - 1 + 1) + acc := by
        rw [BitVec.add_comm acc 1, ← BitVec.add_assoc]
      _ = n + acc := by rw [BitVec.sub_add_cancel]
termination_by n.toNat
decreasing_by exact word_pred_decreases n (by assumption)

theorem accumulate_compiled (n acc : Word) :
    accumulate.execute (Env.two n acc) = n + acc := by
  rw [RecFn.execute_correct, accumulate_correct]

/-- Run `lake env lean --run examples/Recursive.lean --llvm > recursive.ll`. -/
def main (args : List String) : IO Unit := do
  let output ← match args with
    | ["--llvm"] => pure (LLVM.emitRecursive "accumulate" accumulate)
    | [] => pure (emitRecursiveAssembly "accumulate" accumulate)
    | _ => throw (IO.userError "usage: Recursive.lean [--llvm]")
  match output with
  | .ok assembly => IO.print assembly
  | .error message => throw (IO.userError message)
