import Riscvc.Control

namespace Riscvc

theorem compileArgs_correct (args : Fin arity → Expr n) (loc : Fin n → Nat)
    (dst : Nat) (regs : Registers) (hloc : ∀ i, loc i < dst) :
    (∀ i, run (compileArgs args loc dst) regs (dst + i.val) = (args i).eval (fun j => regs (loc j))) ∧
    (∀ i, i < dst → run (compileArgs args loc dst) regs i = regs i) := by
  induction arity generalizing dst regs with
  | zero => exact ⟨fun i => Fin.elim0 i, fun _ _ => rfl⟩
  | succ arity ih =>
      let r₁ := run (compile (args 0) loc dst) regs
      have h₁ := compile_correct (args 0) loc dst regs hloc
      have h₂ := ih (fun i => args i.succ) (dst + 1) r₁
        (fun i => Nat.lt_succ_of_lt (hloc i))
      have henv : (fun i => r₁ (loc i)) = (fun i => regs (loc i)) :=
        funext (fun i => h₁.2 _ (hloc i))
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [compileArgs, run_append, Fin.val_zero, Nat.add_zero] using
            (h₂.2 dst (by omega)).trans h₁.1
        · have h := (h₂.1 j).trans (congrArg (args j.succ).eval henv)
          simpa only [compileArgs, run_append, Fin.val_succ, Nat.add_assoc,
            Nat.add_comm 1] using h
      · intro i hi
        simpa only [compileArgs, run_append] using
          (h₂.2 i (by omega)).trans (h₁.2 i hi)

/-- Preservation for recursive expression compilation, for any call oracle. -/
theorem compileRec_correct (e : RecExpr arity n) (self : Env arity → Word)
    (loc : Fin n → Nat) (dst : Nat) (regs : Registers) (hloc : ∀ i, loc i < dst) :
    (compileRec e loc dst).run self regs dst = e.eval self (fun i => regs (loc i)) ∧
    ∀ i, i < dst → (compileRec e loc dst).run self regs i = regs i := by
  induction e generalizing dst regs with
  | pure e => exact compile_correct e loc dst regs hloc
  | bin op lhs rhs ihl ihr =>
      let r₁ := (compileRec lhs loc dst).run self regs
      let r₂ := (compileRec rhs loc (dst + 1)).run self r₁
      have h₁ := ihl loc dst regs hloc
      have h₂ := ihr loc (dst + 1) r₁ (fun i => Nat.lt_succ_of_lt (hloc i))
      have henv : (fun i => r₁ (loc i)) = (fun i => regs (loc i)) :=
        funext (fun i => h₁.2 _ (hloc i))
      constructor
      · simp only [compileRec, Control.run, Control.exec, runState_read, run_cons, run_nil, Instr.exec,
          Operand.read, Registers.write_same, RecExpr.eval]
        exact congr (congrArg op.eval ((h₂.2 dst (by omega)).trans h₁.1))
          (h₂.1.trans (congrArg (rhs.eval self) henv))
      · intro i hi
        simp only [compileRec, Control.run, Control.exec, runState_read, run_cons, run_nil, Instr.exec]
        rw [Registers.write_other _ _ _ _ (by omega)]
        exact (h₂.2 i (by omega)).trans (h₁.2 i hi)
  | letE value body ihv ihb =>
      let r₁ := (compileRec value loc dst).run self regs
      have h₁ := ihv loc dst regs hloc
      have hbound : ∀ i, extend loc dst i < dst + 1 := by
        intro i
        refine Fin.cases (by simp) (fun j => ?_) i
        simpa using Nat.lt_succ_of_lt (hloc j)
      have h₂ := ihb (extend loc dst) (dst + 1) r₁ hbound
      have henv : (fun i => r₁ (extend loc dst i)) =
          extend (fun i => regs (loc i)) (value.eval self (fun i => regs (loc i))) := by
        funext i
        exact Fin.cases h₁.1 (fun j => h₁.2 _ (hloc j)) i
      constructor
      · simp only [compileRec, Control.run, Control.exec, runState_read, run_cons, run_nil, Instr.mov,
          Instr.exec, Operand.read, BinOp.eval, Registers.write_same, RecExpr.eval]
        exact (BitVec.add_zero _).trans (h₂.1.trans (congrArg (body.eval self) henv))
      · intro i hi
        simp only [compileRec, Control.run, Control.exec, runState_read, run_cons, run_nil, Instr.mov, Instr.exec]
        rw [Registers.write_other _ _ _ _ (by omega)]
        exact (h₂.2 i (by omega)).trans (h₁.2 i hi)
  | ite cond yes no ihc iht ihf =>
      let r₁ := (compileRec cond loc dst).run self regs
      have hc := ihc loc dst regs hloc
      have ht := iht loc dst r₁ hloc
      have hf := ihf loc dst r₁ hloc
      have henv : (fun i => r₁ (loc i)) = (fun i => regs (loc i)) :=
        funext (fun i => hc.2 _ (hloc i))
      simp only [compileRec, Control.run_seq, Control.run_branch]
      constructor
      · change (if r₁ dst = 0 then (compileRec no loc dst).run self r₁
          else (compileRec yes loc dst).run self r₁) dst = _
        have hcond : r₁ dst = cond.eval self (fun i => regs (loc i)) := hc.1
        simp only [RecExpr.eval, ← hcond]
        split
        · exact hf.1.trans (congrArg (no.eval self) henv)
        · exact ht.1.trans (congrArg (yes.eval self) henv)
      · intro i hi
        change (if r₁ dst = 0 then (compileRec no loc dst).run self r₁
          else (compileRec yes loc dst).run self r₁) i = regs i
        split
        · exact (hf.2 i hi).trans (hc.2 i hi)
        · exact (ht.2 i hi).trans (hc.2 i hi)
  | call args =>
      have h := compileArgs_correct args loc dst regs hloc
      constructor
      · simp only [compileRec, Control.run, Control.exec, runState_read, Registers.write_same, RecExpr.eval]
        exact congrArg self (funext h.1)
      · intro i hi
        simp only [compileRec, Control.run, Control.exec, runState_read]
        rw [Registers.write_other _ _ _ _ (by omega)]
        exact h.2 i hi

/-- Tail-call elimination preserves the function result. -/
theorem compileTail_correct (e : RecExpr arity n) (self : Env arity → Word)
    (loc : Fin n → Nat) (dst : Nat) (regs : Registers) (hloc : ∀ i, loc i < dst) :
    (compileTail e loc dst).eval self regs = e.eval self (fun i => regs (loc i)) := by
  induction e generalizing dst regs with
  | pure e => exact (compileRec_correct (.pure e) self loc dst regs hloc).1
  | bin op lhs rhs _ _ => exact (compileRec_correct (.bin op lhs rhs) self loc dst regs hloc).1
  | letE value body _ ih =>
      let r₁ := (compileRec value loc dst).run self regs
      have h₁ := compileRec_correct value self loc dst regs hloc
      have hbound : ∀ i, extend loc dst i < dst + 1 := by
        intro i
        refine Fin.cases (by simp) (fun j => ?_) i
        simpa using Nat.lt_succ_of_lt (hloc j)
      have henv : (fun i => r₁ (extend loc dst i)) =
          extend (fun i => regs (loc i)) (value.eval self (fun i => regs (loc i))) := by
        funext i
        exact Fin.cases h₁.1 (fun j => h₁.2 _ (hloc j)) i
      exact (ih (extend loc dst) (dst + 1) r₁ hbound).trans (congrArg (body.eval self) henv)
  | ite cond yes no _ iht ihf =>
      let r₁ := (compileRec cond loc dst).run self regs
      have hc := compileRec_correct cond self loc dst regs hloc
      have henv : (fun i => r₁ (loc i)) = (fun i => regs (loc i)) :=
        funext (fun i => hc.2 _ (hloc i))
      change (if r₁ dst = 0 then (compileTail no loc dst).eval self r₁
        else (compileTail yes loc dst).eval self r₁) = _
      have hcond : r₁ dst = cond.eval self (fun i => regs (loc i)) := hc.1
      simp only [RecExpr.eval, ← hcond]
      split
      · exact (ihf loc dst r₁ hloc).trans (congrArg (no.eval self) henv)
      · exact (iht loc dst r₁ hloc).trans (congrArg (yes.eval self) henv)
  | call args =>
      exact congrArg self (funext (compileArgs_correct args loc dst regs hloc).1)

/-- Complete recursive source-to-control-IR preservation, not an oracle assumption
    about the compiler. Recursive calls execute the compiled body again. -/
theorem RecFn.execute_correct (f : RecFn arity) (args : Env arity) :
    f.execute args = f.eval args := by
  rw [RecFn.execute, RecFn.eval]
  have hc := compileTail_correct f.body
    (fun next => if f.measure next < f.measure args then f.execute next else 0)
    Fin.val arity (initialRegisters args) (fun i => i.isLt)
  simp only [initialRegisters, Fin.isLt, dite_true] at hc
  rw [hc]
  apply congrArg (fun self => f.body.eval self args)
  funext next
  split
  · exact RecFn.execute_correct f next
  · rfl
termination_by f.measure args

theorem RecFn.compiled_satisfies (f : RecFn arity) (pre : Env arity → Prop)
    (post : Env arity → Word → Prop) (h : f.Satisfies pre post) :
    ∀ args, pre args → post args (f.execute args) := by
  intro args ha
  rw [RecFn.execute_correct]
  exact h args ha

end Riscvc
