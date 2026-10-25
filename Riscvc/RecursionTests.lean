import Riscvc.RecursiveExamples

namespace Riscvc.RecursionTests

/-- info: 'Riscvc.RecFn.eval_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Riscvc.RecFn.eval_eq

/-- info: 'Riscvc.RecFn.execute_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Riscvc.RecFn.execute_correct

/-- info: 'Riscvc.compileTail_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Riscvc.compileTail_correct

/-- error: recursive call expects 1 arguments, got 2 -/
#guard_msgs in
#check [riscv_rec| fun loop n => loop(n, n)]

/-- error: only self-recursion is supported; expected 'loop' -/
#guard_msgs in
#check [riscv_rec| fun loop n => other(n)]

/-- error: the recursive function name cannot be shadowed -/
#guard_msgs in
#check [riscv_rec| fun loop n => let loop := n; loop]

/-- error: the recursive function name cannot be an argument -/
#guard_msgs in
#check [riscv_rec| fun loop loop => loop]

/-- error: termination_by must name a function argument -/
#guard_msgs in
#check [riscv_rec| fun loop n => n termination_by missing]

/-- error: calls require riscv_rec; call arguments must be pure (bind recursive results with let first) -/
#guard_msgs in
#check [riscv_rec| fun loop n => loop(loop(n - 1))]

/- These must fail to construct a certified function: no decrease, a wraparound
   at zero without a guard, and an increasing recursive call, respectively. -/
/--
error: unsolved goals
self✝ : Env 1 → Word
args✝ : Env 1
⊢ BitVec.toNat ((extend Fin.elim0 (Expr.var ⟨0, ⋯⟩) ⟨0, ⋯⟩).eval args✝) < BitVec.toNat (args✝ ⟨0, ⋯⟩)
-/
#guard_msgs (error, drop info) in
#check [riscv_rec| fun bad n => bad(n) termination_by n]

/--
error: unsolved goals
self✝ : Env 1 → Word
args✝ : Env 1
⊢ BitVec.toNat ((extend Fin.elim0 (Expr.bin BinOp.sub (Expr.var ⟨0, ⋯⟩) (Expr.lit 1#64)) ⟨0, ⋯⟩).eval args✝) <
    BitVec.toNat (args✝ ⟨0, ⋯⟩)
-/
#guard_msgs (error, drop info) in
#check [riscv_rec| fun bad n => bad(n - 1) termination_by n]

/--
error: unsolved goals
case hno
self✝ : Env 1 → Word
args✝ : Env 1
a✝ : ¬args✝ ⟨0, ⋯⟩ = 0
⊢ BitVec.toNat ((extend Fin.elim0 (Expr.bin BinOp.add (Expr.var ⟨0, ⋯⟩) (Expr.lit 1#64)) ⟨0, ⋯⟩).eval args✝) <
    BitVec.toNat (args✝ ⟨0, ⋯⟩)
-/
#guard_msgs (error, drop info) in
#check [riscv_rec| fun bad n => if n then bad(n + 1) else 0 termination_by n]

private def addChain : Nat → Expr 1
  | 0 => .var 0
  | n + 1 => .bin .add (addChain n) (.lit 1)

/-- A branch arm longer than the signed 12-bit branch displacement, forcing the
    backend's nearby conditional branch plus longer unconditional jump layout. -/
def longBranch : RecFn 1 where
  body := .ite (.pure (.var 0)) (.pure (addChain 700)) (.pure (.lit 777))
  measure := fun _ => 0
  decreasing := by intro self args; simp [RecExpr.CallsBelow]

def extraExamples : List RecursiveExamples.Example := [
  ⟨"long_branch", 1, longBranch, [#[0], #[1]]⟩
]

private def checkEqual (label : String) (actual expected : Word) : IO Unit := do
  if actual != expected then throw (IO.userError s!"{label}: got {actual}, expected {expected}")

def check : IO Unit := do
  for entry in RecursiveExamples.examples ++ extraExamples do
    match emitRecursiveAssembly entry.name entry.program with
    | .error message => throw (IO.userError s!"{entry.name}: {message}")
    | .ok _ => pure ()
    for values in entry.inputs do
      if values.size != entry.arity then throw (IO.userError "recursive test input arity mismatch")
      let env : Env entry.arity := fun i => values[i.val]!
      checkEqual entry.name (entry.program.execute env) (entry.program.eval env)
  checkEqual "sum_to specification" (RecursiveExamples.sumTo.eval (Env.one 10)) 55
  checkEqual "tail accumulator overflow" (RecursiveExamples.countUp.eval (Env.two 10 0xffffffffffffffff)) 9
  checkEqual "dead recursive branch" (RecursiveExamples.deadBranch.eval (Env.one 0xffffffffffffffff)) 0xffffffffffffffff
  checkEqual "multiple recursive calls" (RecursiveExamples.binaryTree.eval (Env.one 8)) 256
  checkEqual "argument permutation" (RecursiveExamples.swapLoop.eval (Env.three 3 10 20)) 20
  let tooDeep : RecFn 8 := [riscv_rec| fun f a b c d e farg g h =>
    a + (b + (c + (d + (e + (farg + (g + h)))))) termination_by a]
  match emitRecursiveAssembly "too_deep" tooDeep with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "recursive backend accepted register exhaustion")
  match emitRecursiveAssembly "bad\n.text" RecursiveExamples.sumTo with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "recursive backend accepted an invalid symbol")

end Riscvc.RecursionTests
