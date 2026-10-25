import Riscvc.Language

/-! An SMT-LIB exporter for pure source specifications. This exporter is a tool
for solver experiments, not a proved translation. An SMT result is kept separate
from the Sail/Lean certificate path. -/
namespace Riscvc.SMT

private def constant (word : Word) : String := s!"(_ bv{word.toNat} 64)"

private def bin (op : String) (x y : String) : String := s!"({op} {x} {y})"

private def operation : BinOp → String → String → String
  | .add, x, y => bin "bvadd" x y
  | .sub, x, y => bin "bvsub" x y
  | .band, x, y => bin "bvand" x y
  | .bor, x, y => bin "bvor" x y
  | .bxor, x, y => bin "bvxor" x y
  | .shl, x, y => bin "bvshl" x (bin "bvand" y (constant 63))
  | .shr, x, y => bin "bvlshr" x (bin "bvand" y (constant 63))
  | .ltu, x, y => s!"(ite (bvult {x} {y}) {constant 1} {constant 0})"

def expression : Expr n → (Fin n → String) → String
  | .var i, env => env i
  | .lit word, _ => constant word
  | .bin op x y, env => operation op (expression x env) (expression y env)
  | .letE value body, env => expression body (extend env (expression value env))
  | .ite cond yes no, env =>
    s!"(ite (= {expression cond env} {constant 0}) {expression no env} {expression yes env})"

def emit (e : Expr n) : String :=
  s!"(define-fun expected () (_ BitVec 64) {expression e (fun i => s!"a{i.val}")})\n"

end Riscvc.SMT
