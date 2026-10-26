import examples.Scheduler
import Lean

/-! Export the actual elaborated scheduler DSL, rather than a handwritten copy
of its algorithm, for disassembly translation validation. This serializer is
part of the validator's trusted implementation; it is not an equivalence proof. -/
namespace Riscvc.Heap.SchedulerExport

open Lean

private def tagged (tag : String) (args : List Json := []) : Json :=
  Json.arr (#[toJson tag] ++ args.toArray)

private def binName : BinOp → String
  | .add => "add" | .sub => "sub" | .band => "and" | .bor => "or"
  | .bxor => "xor" | .shl => "shl" | .shr => "shr" | .ltu => "ltu"

private def expr : Expr ctx type → Json
  | .var v => tagged "var" [toJson v.index.val]
  | .word w => tagged "word" [toJson w.toNat]
  | .null => tagged "word" [toJson (0 : Nat)]
  | .bin op a b => tagged (binName op) [expr a, expr b]
  | .eq a b => tagged "eq" [expr a, expr b]
  | .field f p => tagged "field" [toJson (8 * f.index.val), expr p]
  | .ite c a b => tagged "ite" [expr c, expr a, expr b]

private def command : Cmd ctx → Json
  | .skip => tagged "skip"
  | .seq a b => tagged "seq" [command a, command b]
  | .assign v e => tagged "assign" [toJson v.index.val, expr e]
  | .store f p e => tagged "store" [toJson (8 * f.index.val), expr p, expr e]
  | .ite c a b => tagged "if" [expr c, command a, command b]
  | .while c b => tagged "while" [expr c, command b]

private def function (fn : Function params vars result) : Json :=
  Json.mkObj [("params", toJson params.length), ("locals", toJson vars.length),
    ("body", command fn.body), ("returns", expr fn.returns)]

def spec : Json := Json.mkObj [
  ("format", toJson "riscvc-scheduler-source-v1"),
  ("init", function Scheduler.init), ("step", function Scheduler.step)]

end Riscvc.Heap.SchedulerExport

def main : IO Unit := IO.println Riscvc.Heap.SchedulerExport.spec.compress
