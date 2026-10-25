import Std

namespace Riscvc

/-- Machine words, with arithmetic modulo 2^64. -/
abbrev Word := BitVec 64

abbrev Env (n : Nat) := Fin n → Word

def extend {α : Type} (env : Fin n → α) (value : α) : Fin (n + 1) → α :=
  Fin.cases value env

@[simp] theorem extend_zero {α : Type} (env : Fin n → α) (value : α) :
    extend env value 0 = value := rfl

@[simp] theorem extend_succ {α : Type} (env : Fin n → α) (value : α) (i : Fin n) :
    extend env value i.succ = env i := rfl

def Env.empty : Env 0 := Fin.elim0
def Env.one (x : Word) : Env 1 := extend Env.empty x
def Env.two (x y : Word) : Env 2 := extend (Env.one y) x
def Env.three (x y z : Word) : Env 3 := extend (Env.two y z) x

/-- Shifts use the low six bits of the shift amount, as on RV64. -/
inductive BinOp where
  | add | sub | band | bor | bxor | shl | shr | ltu
  deriving Repr, DecidableEq

def BinOp.eval : BinOp → Word → Word → Word
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y
  | .bxor, x, y => x ^^^ y
  | .shl, x, y => x <<< (y.toNat % 64)
  | .shr, x, y => x >>> (y.toNat % 64)
  | .ltu, x, y => if x.ult y then 1 else 0

/-- A scoped, pure expression language. Index 0 names the most recent let. -/
inductive Expr : Nat → Type where
  | var : Fin n → Expr n
  | lit : Word → Expr n
  | bin : BinOp → Expr n → Expr n → Expr n
  | letE : Expr n → Expr (n + 1) → Expr n
  | ite : Expr n → Expr n → Expr n → Expr n
  deriving Repr

/-- This is the semantics against which users state their program proofs. -/
def Expr.eval : Expr n → Env n → Word
  | .var i, env => env i
  | .lit v, _ => v
  | .bin op lhs rhs, env => op.eval (lhs.eval env) (rhs.eval env)
  | .letE value body, env => body.eval (extend env (value.eval env))
  | .ite cond yes no, env => if cond.eval env = 0 then no.eval env else yes.eval env

/-- A total-correctness specification for a pure DSL function. -/
def Expr.Satisfies (e : Expr n) (pre : Env n → Prop) (post : Env n → Word → Prop) : Prop :=
  ∀ env, pre env → post env (e.eval env)

end Riscvc
