import Riscvc

open Riscvc

def addThenUndo : Expr 2 := [riscv| fun x y =>
  let z := x + y;
  z - y
]

theorem addThenUndo_correct (x y : Word) : addThenUndo.eval (Env.two x y) = x := by
  change x + y - y = x
  exact BitVec.add_sub_cancel x y

/-- Run `lake env lean --run examples/Custom.lean --llvm > custom.ll`. -/
def main (args : List String) : IO Unit := do
  let output ← match args with
    | ["--llvm"] => pure (LLVM.emit "add_then_undo" addThenUndo)
    | [] => pure (emitAssembly "add_then_undo" addThenUndo)
    | _ => throw (IO.userError "usage: Custom.lean [--llvm]")
  match output with
  | .ok assembly => IO.print assembly
  | .error message => throw (IO.userError message)
