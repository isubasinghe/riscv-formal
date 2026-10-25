import Riscvc.Language

namespace Riscvc

/-- A function body with self-calls. Recursive-call arguments are pure expressions;
    use a `let` to name a recursive result before passing it to another call. -/
inductive RecExpr (arity : Nat) : Nat → Type where
  | pure : Expr n → RecExpr arity n
  | bin : BinOp → RecExpr arity n → RecExpr arity n → RecExpr arity n
  | letE : RecExpr arity n → RecExpr arity (n + 1) → RecExpr arity n
  | ite : RecExpr arity n → RecExpr arity n → RecExpr arity n → RecExpr arity n
  | call : (Fin arity → Expr n) → RecExpr arity n

/-- Interpret a body against a supplied implementation of its recursive calls. -/
def RecExpr.eval (self : Env arity → Word) : RecExpr arity n → Env n → Word
  | .pure e, env => e.eval env
  | .bin op lhs rhs, env => op.eval (lhs.eval self env) (rhs.eval self env)
  | .letE value body, env => body.eval self (extend env (value.eval self env))
  | .ite cond yes no, env => if cond.eval self env = 0 then no.eval self env else yes.eval self env
  | .call args, env => self (fun i => (args i).eval env)

/-- Only calls on the executed path must decrease. Quantifying this predicate
    over `self` permits calls in local bindings without assuming their results. -/
def RecExpr.CallsBelow (self : Env arity → Word) (measure : Env arity → Nat)
    (bound : Nat) : RecExpr arity n → Env n → Prop
  | .pure _, _ => True
  | .bin _ lhs rhs, env => lhs.CallsBelow self measure bound env ∧ rhs.CallsBelow self measure bound env
  | .letE value body, env => value.CallsBelow self measure bound env ∧
      body.CallsBelow self measure bound (extend env (value.eval self env))
  | .ite cond yes no, env => cond.CallsBelow self measure bound env ∧
      if cond.eval self env = 0 then no.CallsBelow self measure bound env
      else yes.CallsBelow self measure bound env
  | .call args, env => measure (fun i => (args i).eval env) < bound

/-- Changing the call implementation outside the reachable decreasing calls
    cannot change a body's result. -/
theorem RecExpr.eval_congr_below (e : RecExpr arity n)
    (f g : Env arity → Word) (measure : Env arity → Nat) (bound : Nat) (env : Env n)
    (safe : e.CallsBelow f measure bound env)
    (agree : ∀ args, measure args < bound → f args = g args) :
    e.eval f env = e.eval g env := by
  induction e with
  | pure e => rfl
  | bin op lhs rhs ihl ihr =>
      simp only [RecExpr.eval]
      exact congr (congrArg op.eval (ihl env safe.1)) (ihr env safe.2)
  | letE value body ihv ihb =>
      have hv := ihv env safe.1
      exact (ihb (extend env (value.eval f env)) safe.2).trans
        (congrArg (body.eval g) (congrArg (extend env) hv))
  | ite cond yes no ihc iht ihf =>
      have hc := ihc env safe.1
      simp only [RecExpr.eval]
      rw [← hc]
      split <;> rename_i h
      · exact ihf env (by simpa only [CallsBelow, h, ite_true] using safe.2)
      · exact iht env (by simpa only [CallsBelow, h, ite_false] using safe.2)
  | call args => exact agree _ safe

/-- A total recursive DSL function. Its termination argument is checked by Lean;
    it is not emitted as fuel or a runtime check in assembly. -/
structure RecFn (arity : Nat) where
  body : RecExpr arity arity
  measure : Env arity → Nat
  decreasing : ∀ self args, body.CallsBelow self measure (measure args) args

/-- Well-founded evaluation, with a totalized recursive oracle. `eval_eq` proves
    that the fallback is unreachable for a certified function. -/
def RecFn.eval (f : RecFn arity) (args : Env arity) : Word :=
  f.body.eval (fun next => if f.measure next < f.measure args then f.eval next else 0) args
termination_by f.measure args

/-- The usable unfolding equation has ordinary recursion and no fuel or fallback. -/
theorem RecFn.eval_eq (f : RecFn arity) (args : Env arity) :
    f.eval args = f.body.eval f.eval args := by
  rw [RecFn.eval]
  apply RecExpr.eval_congr_below f.body _ _ f.measure (f.measure args) args
  · exact f.decreasing _ args
  · intro next h
    simp only [h, ite_true]

def RecFn.Satisfies (f : RecFn arity) (pre : Env arity → Prop)
    (post : Env arity → Word → Prop) : Prop :=
  ∀ args, pre args → post args (f.eval args)

/-- A common termination obligation for guarded word countdowns. -/
theorem word_pred_decreases (x : Word) (h : x ≠ 0) : (x - 1).toNat < x.toNat := by
  have hpos : 0 < x.toNat := by
    have hne : x.toNat ≠ 0 := fun hz => h (BitVec.eq_of_toNat_eq hz)
    omega
  rw [BitVec.toNat_sub]
  change ((2^64 - 1 + x.toNat) % 2^64) < x.toNat
  have hx := x.isLt
  omega

end Riscvc
