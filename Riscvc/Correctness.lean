import Riscvc.Compiler

namespace Riscvc

private theorem select_value (c t f : Word) :
    f ^^^ ((t ^^^ f) &&& (0 - BinOp.ltu.eval 0 c)) =
      if c = 0 then f else t := by
  by_cases hc : c = 0
  · simp [hc, BinOp.eval]
  · have hpos : 0 < c.toNat := by
      have hne : c.toNat ≠ 0 := by
        intro h
        apply hc
        exact BitVec.eq_of_toNat_eq h
      omega
    rw [ite_eq_right hc]
    have hlt : BinOp.ltu.eval 0 c = 1 := by simp [BinOp.eval, BitVec.ult, hpos]
    rw [hlt]
    change f ^^^ ((t ^^^ f) &&& BitVec.allOnes 64) = t
    rw [BitVec.and_allOnes, BitVec.xor_comm t f, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]

private theorem select_correct (regs : Registers) (dst : Nat) :
    run (selectCode dst) regs dst =
      (if regs dst = 0 then regs (dst + 2) else regs (dst + 1)) ∧
    ∀ i, i < dst → run (selectCode dst) regs i = regs i := by
  constructor
  · have h := select_value (regs dst) (regs (dst + 1)) (regs (dst + 2))
    simp only [selectCode, run, runState, Registers.write, Operand.read,
      BinOp.eval, ite_eq_right (show dst ≠ dst + 1 by omega),
      ite_eq_right (show dst + 1 ≠ dst by omega), ite_eq_right (show dst + 2 ≠ dst by omega),
      ite_eq_right (show dst + 2 ≠ dst + 1 by omega)]
    exact h
  · intro i hi
    simp [selectCode, run, runState, Registers.write,
      show i ≠ dst by omega, show i ≠ dst + 1 by omega]

/-- Semantic preservation and the frame property, for every source expression
    and every initial register state. No assumptions about scratch values. -/
theorem compile_correct (e : Expr n) (loc : Fin n → Nat) (dst : Nat)
    (regs : Registers) (hloc : ∀ i, loc i < dst) :
    run (compile e loc dst) regs dst = e.eval (fun i => regs (loc i)) ∧
    ∀ i, i < dst → run (compile e loc dst) regs i = regs i := by
  induction e generalizing dst regs with
  | var v =>
      simp [compile, run, runState, Instr.mov, Operand.read, BinOp.eval,
        Expr.eval, Registers.write]
      intro i hi
      simp [show i ≠ dst by omega]
  | lit v =>
      simp [compile, run, runState, Expr.eval, Registers.write]
      intro i hi
      simp [show i ≠ dst by omega]
  | bin op lhs rhs ihl ihr =>
      let r₁ := run (compile lhs loc dst) regs
      let r₂ := run (compile rhs loc (dst + 1)) r₁
      have h₁ := ihl loc dst regs hloc
      have h₂ := ihr loc (dst + 1) r₁ (fun i => Nat.lt_succ_of_lt (hloc i))
      have henv : (fun i => r₁ (loc i)) = (fun i => regs (loc i)) :=
        funext (fun i => h₁.2 _ (hloc i))
      have hkeep : r₂ dst = r₁ dst := h₂.2 dst (by omega)
      constructor
      · simp only [compile, run_append, run_cons, run_nil, Instr.exec,
          Operand.read, Registers.write_same, Expr.eval]
        change op.eval (r₂ dst) (r₂ (dst + 1)) = _
        exact congr (congrArg op.eval (hkeep.trans h₁.1))
          (h₂.1.trans (congrArg rhs.eval henv))
      · intro i hi
        simp only [compile, run_append, run_cons, run_nil, Instr.exec]
        rw [Registers.write_other _ _ _ _ (by omega)]
        exact (h₂.2 i (by omega)).trans (h₁.2 i hi)
  | letE value body ihv ihb =>
      let r₁ := run (compile value loc dst) regs
      let r₂ := run (compile body (extend loc dst) (dst + 1)) r₁
      have h₁ := ihv loc dst regs hloc
      have hbound : ∀ i, extend loc dst i < dst + 1 := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simpa using Nat.lt_succ_of_lt (hloc j)
      have h₂ := ihb (extend loc dst) (dst + 1) r₁ hbound
      have henv : (fun i => r₁ (extend loc dst i)) =
          extend (fun i => regs (loc i)) (value.eval (fun i => regs (loc i))) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact h₁.1
        · exact h₁.2 _ (hloc j)
      constructor
      · simp only [compile, run_append, run_cons, run_nil, Instr.mov,
          Instr.exec, Operand.read, BinOp.eval, Registers.write_same,
          Expr.eval]
        exact (BitVec.add_zero _).trans (h₂.1.trans (congrArg body.eval henv))
      · intro i hi
        simp only [compile, run_append, run_cons, run_nil, Instr.mov, Instr.exec]
        rw [Registers.write_other _ _ _ _ (by omega)]
        exact (h₂.2 i (by omega)).trans (h₁.2 i hi)
  | ite cond yes no ihc iht ihf =>
      let r₁ := run (compile cond loc dst) regs
      let r₂ := run (compile yes loc (dst + 1)) r₁
      let r₃ := run (compile no loc (dst + 2)) r₂
      have h₁ := ihc loc dst regs hloc
      have h₂ := iht loc (dst + 1) r₁ (fun i => by have := hloc i; omega)
      have h₃ := ihf loc (dst + 2) r₂ (fun i => by have := hloc i; omega)
      have hs := select_correct r₃ dst
      have he₁ : (fun i => r₁ (loc i)) = (fun i => regs (loc i)) :=
        funext (fun i => h₁.2 _ (hloc i))
      have he₂ : (fun i => r₂ (loc i)) = (fun i => regs (loc i)) := by
        funext i
        exact (h₂.2 _ (by have := hloc i; omega)).trans (h₁.2 _ (hloc i))
      have hc : r₃ dst = cond.eval (fun i => regs (loc i)) :=
        (h₃.2 _ (by omega)).trans ((h₂.2 _ (by omega)).trans h₁.1)
      have ht : r₃ (dst + 1) = yes.eval (fun i => regs (loc i)) := by
        exact (h₃.2 (dst + 1) (by omega)).trans
          (h₂.1.trans (congrArg yes.eval he₁))
      have hf : r₃ (dst + 2) = no.eval (fun i => regs (loc i)) := by
        exact h₃.1.trans (congrArg no.eval he₂)
      constructor
      · simpa only [compile, run_append, Expr.eval, ← hc, ← ht, ← hf] using hs.1
      · intro i hi
        simp only [compile, run_append]
        exact (hs.2 i hi).trans ((h₃.2 i (by omega)).trans
          ((h₂.2 i (by omega)).trans (h₁.2 i hi)))

theorem execute_correct (e : Expr n) (args : Env n) : execute e args = e.eval args := by
  have h := (compile_correct e Fin.val n
    (fun i => if h : i < n then args ⟨i, h⟩ else 0) (fun i => i.isLt)).1
  simpa [execute, compileFunction] using h

/-- Any source-level pre/postcondition theorem transfers to the compiled
    register-machine program. Assembly/Sail refinement is a separate obligation. -/
theorem compiled_satisfies (e : Expr n) (pre : Env n → Prop)
    (post : Env n → Word → Prop) (proof : e.Satisfies pre post) :
    ∀ args, pre args → post args (execute e args) := by
  intro args h
  rw [execute_correct]
  exact proof args h

end Riscvc
