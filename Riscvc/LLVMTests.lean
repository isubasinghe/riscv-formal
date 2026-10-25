import Riscvc.Examples
import Riscvc.RecursionTests

namespace Riscvc.LLVMTests

/-- These exceed the handwritten backend's argument/register restrictions. -/
def wide : Expr 9 := [riscv| fun a b c d e f g h i =>
  a + (b + (c + (d + (e + (f + (g + (h + i)))))))
]

def pressure : Expr 8 := [riscv| fun a b c d e f g h =>
  a ^ (b ^ (c ^ (d ^ (e ^ (f ^ (g ^ h))))))
]

def pureExamples : List Examples.Example := [
  ⟨"llvm_wide", 9, wide⟩,
  ⟨"llvm_pressure", 8, pressure⟩
]

/-- Nested branch joins feed arithmetic and preserve a value across calls. -/
def branchJoin : RecFn 2 := [riscv_rec| fun loop n x =>
  if n then
    let y := if x < 7 then
      (if x then loop(n - 1, x + 1) else x + 2)
      else loop(n - 1, x - 1);
    y + x
  else x
  termination_by n
]

/-- A ninth argument exercises stack-passed arguments and tail-loop phi nodes. -/
def wideTail : RecFn 9 := [riscv_rec| fun loop n a b c d e f g h =>
  if n then loop(n - 1, b, c, d, e, f, g, h, a) else a
  termination_by n
]

def wideCall : RecFn 9 := [riscv_rec| fun loop n a b c d e f g h =>
  if n then h + loop(n - 1, h, a, b, c, d, e, f, g) else a
  termination_by n
]

private def wideInputs : List (Array Word) :=
  (List.range 12).map fun n =>
    #[BitVec.ofNat 64 n, 1, 17, 29, 63, 0xffffffffffffffff, 0x8000000000000000, 65, 511]

def recursiveExamples : List RecursiveExamples.Example := [
  ⟨"llvm_branch_join", 2, branchJoin,
    [0, 1, 3, 7].flatMap (fun n =>
      [0, 1, 6, 7, 10, 0xffffffffffffffff].map (fun x => #[n, x]))⟩,
  ⟨"llvm_wide_tail", 9, wideTail, wideInputs⟩,
  ⟨"llvm_wide_call", 9, wideCall, wideInputs⟩
]

def check : IO Unit := do
  for entry in pureExamples do
    match LLVM.emit entry.name entry.program with
    | .ok _ => pure ()
    | .error message => throw (IO.userError message)
  for entry in recursiveExamples do
    match LLVM.emitRecursive entry.name entry.program with
    | .ok _ => pure ()
    | .error message => throw (IO.userError message)
    for args in entry.inputs do
      let env : Env entry.arity := fun i => args[i.val]!
      if entry.program.execute env != entry.program.eval env then
        throw (IO.userError s!"recursive IR mismatch: {entry.name}")
  for name in ["", "1bad", "bad\n}", "λ"] do
    match LLVM.emit name (Expr.lit (n := 0) 0) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "LLVM emitter accepted an invalid symbol")
    match LLVM.emitRecursive name RecursiveExamples.countUp with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "recursive LLVM emitter accepted an invalid symbol")

end Riscvc.LLVMTests
