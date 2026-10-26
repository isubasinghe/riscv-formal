import Riscvc.Binary.Memory

/-! A reference lowering of the typed heap DSL into Sail computations. Loads
and stores use the generated Sail virtual-memory operations, not a second
word-memory emulator. The loop theorem quantifies over every finite source
derivation; interpreter fuel is a witness, never a bound on list length.

This is the source side of translation validation. Equating this computation
with optimized disassembly is a separate, program-specific obligation.
-/
namespace Riscvc.Heap.SailLowering

open Riscvc.Binary Riscvc.Binary.Memory
open _root_.Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Every allocated source cell lies in the configured ordinary RAM region. -/
def InRAM (mem : Heap.Memory) : Prop :=
  ∀ a v, mem a = some v → 0x80001000 ≤ a ∧ a + 8 ≤ 0x90000000 ∧ a % 8 = 0

def SameDomain (a b : Heap.Memory) : Prop :=
  ∀ p, (∃ v, a p = some v) ↔ (∃ v, b p = some v)

/-- Every byte outside the source heap is preserved, including executable text. -/
def Frame (mem : Heap.Memory) (before after : SailState) : Prop :=
  ∀ byte, (∀ a v, mem a = some v → byte < a ∨ a + 8 ≤ byte) →
    after.mem.get? byte = before.mem.get? byte

private theorem address_of_mapped (mem : Heap.Memory) (a : Nat) (v : Word)
    (hram : InRAM mem) (hm : mem a = some v) :
    (BitVec.ofNat 64 a).toNat = a ∧ Address (BitVec.ofNat 64 a) := by
  have h := hram a v hm
  have hn : a < 2 ^ 64 := by omega
  have he : (BitVec.ofNat 64 a).toNat = a := by simp [Nat.mod_eq_of_lt hn]
  exact ⟨he, by simpa only [Address, he] using h⟩

noncomputable def read (p : Word) (offset : Nat) : SailM Word := do
  if Accessible p offset then
    match ← vmem_read_addr (.Virtaddr (BitVec.ofNat 64 (p.toNat + offset)))
      8 (.Load .Data) false false false with
    | .Ok value => pure value
    | .Err _ => throw (.Assertion "DSL load failed")
  else throw (.Assertion "Invalid DSL address")

noncomputable def write (p : Word) (offset : Nat) (value : Word) : SailM Unit := do
  if Accessible p offset then
    match ← vmem_write_addr (.Virtaddr (BitVec.ofNat 64 (p.toNat + offset)))
      8 value (.Store .Data) false false false with
    | .Ok true => pure ()
    | _ => throw (.Assertion "DSL store failed")
  else throw (.Assertion "Invalid DSL address")

noncomputable def eval (env : Env ctx) : Expr ctx type → SailM Word
  | .var v => pure (env v.index)
  | .word w => pure w
  | .null => pure 0
  | .bin op a b => do return op.eval (← eval env a) (← eval env b)
  | .eq a b => do return if (← eval env a) = (← eval env b) then 1 else 0
  | .field f p => do read (← eval env p) (8 * f.index.val)
  | .ite condition yes no => do
      if (← eval env condition) = 0 then eval env no else eval env yes

noncomputable def run : Nat → Cmd ctx → Env ctx → SailM (Env ctx)
  | 0, _, _ => throw (.Assertion "DSL fuel exhausted")
  | fuel + 1, cmd, env => do
    match cmd with
    | .skip => pure env
    | .seq a b => run fuel b (← run fuel a env)
    | .assign dst value => pure (env.set dst.index (← eval env value))
    | .store field ptr value =>
        write (← eval env ptr) (8 * field.index.val) (← eval env value)
        pure env
    | .ite condition yes no =>
        if (← eval env condition) = 0 then run fuel no env else run fuel yes env
    | .while condition body =>
        if (← eval env condition) = 0 then pure env
        else run fuel (.while condition body) (← run fuel body env)

noncomputable def call (fn : Function params vars result) (fuel : Nat)
    (args : Env params) : SailM Word := do
  eval (← run fuel fn.body (initial args)) fn.returns

theorem read_correct (mem : Heap.Memory) (s : SailState)
    (p v : Word) (offset : Nat) (hr : Ready s) (hram : InRAM mem)
    (hrep : Represents mem s) (ha : Accessible p offset)
    (hm : mem (p.toNat + offset) = some v) :
    read p offset s = .ok v s := by
  obtain ⟨he, had⟩ := address_of_mapped mem (p.toNat + offset) v hram hm
  have hv : WordAt s (BitVec.ofNat 64 (p.toNat + offset)).toNat v := by
    rw [he]
    exact (hrep _ _ hm).2
  have h := vread_ok s (BitVec.ofNat 64 (p.toNat + offset)) v hr had hv
  simp only [read, ha, ite_true, bind, EStateM.bind]
  erw [h]
  rfl

theorem write_correct (mem : Heap.Memory) (s : SailState) (p v old : Word)
    (offset : Nat) (hr : Ready s) (hram : InRAM mem) (ha : Accessible p offset)
    (hm : mem (p.toNat + offset) = some old) :
    write p offset v s = .ok () (putWord s (p.toNat + offset) v) := by
  obtain ⟨he, had⟩ := address_of_mapped mem (p.toNat + offset) old hram hm
  have h := vwrite_ok s (BitVec.ofNat 64 (p.toNat + offset)) v hr had
  simp only [write, ha, ite_true, bind, EStateM.bind]
  erw [h]
  simp only [he]
  rfl

theorem eval_correct (e : Expr ctx type) (env : Env ctx) (mem : Heap.Memory)
    (s : SailState) (v : Word) (hr : Ready s) (hram : InRAM mem)
    (hrep : Represents mem s) (h : e.eval env mem = some v) :
    eval env e s = .ok v s := by
  induction e generalizing v with
  | var x => simpa [Expr.eval, eval, pure, EStateM.pure] using h
  | word w => simpa [Expr.eval, eval, pure, EStateM.pure] using h
  | null => simpa [Expr.eval, eval, pure, EStateM.pure] using h
  | bin op a b ia ib =>
      cases ha : a.eval env mem with
      | none => simp [Expr.eval, ha] at h
      | some x =>
          cases hb : b.eval env mem with
          | none => simp [Expr.eval, ha, hb] at h
          | some y =>
              have ea := ia x ha
              have eb := ib y hb
              have hv : op.eval x y = v := by simpa [Expr.eval, ha, hb] using h
              simp only [eval, bind, EStateM.bind, ea, eb, pure, EStateM.pure, hv]
  | eq a b ia ib =>
      cases ha : a.eval env mem with
      | none => simp [Expr.eval, ha] at h
      | some x =>
          cases hb : b.eval env mem with
          | none => simp [Expr.eval, ha, hb] at h
          | some y =>
              have ea := ia x ha
              have eb := ib y hb
              have hv : (if x = y then (1 : Word) else 0) = v := by
                simpa [Expr.eval, ha, hb] using h
              simp only [eval, bind, EStateM.bind, ea, eb, pure, EStateM.pure, hv]
  | field f p ip =>
      cases hp : p.eval env mem with
      | none => simp [Expr.eval, hp] at h
      | some base =>
          have ep := ip base hp
          by_cases ha : Accessible base (8 * f.index.val)
          · have hm : mem (base.toNat + 8 * f.index.val) = some v := by
              simpa [Expr.eval, hp, ha] using h
            simp only [eval, bind, EStateM.bind, ep]
            exact read_correct mem s base v _ hr hram hrep ha hm
          · simp [Expr.eval, hp, ha] at h
  | ite c a b ic ia ib =>
      cases hc : c.eval env mem with
      | none => simp [Expr.eval, hc] at h
      | some cond =>
          have ec := ic cond hc
          by_cases hz : cond = 0
          · have hb : b.eval env mem = some v := by simpa [Expr.eval, hc, hz] using h
            simpa only [eval, bind, EStateM.bind, ec, hz, ite_true] using ib v hb
          · have ha : a.eval env mem = some v := by
              simp only [Expr.eval, hc, bind, Option.bind] at h
              erw [ite_eq_right hz] at h
              exact h
            simpa only [eval, bind, EStateM.bind, ec, hz, ite_false] using ia v ha

theorem exec_domain (h : Exec cmd env mem final mem') : SameDomain mem mem' := by
  induction h with
  | skip | assign | while_zero => intro a; rfl
  | seq _ _ ia ib | while_nonzero _ _ _ _ ia ib =>
      intro a
      exact (ia a).trans (ib a)
  | if_zero _ _ ih | if_nonzero _ _ _ ih => exact ih
  | @store p v mem old layout type field ptr value env hp hv ha mapped =>
      intro a
      by_cases he : a = p.toNat + 8 * field.index.val
      · subst a
        exact ⟨fun _ => ⟨v, Heap.Memory.write_same ..⟩, fun _ => ⟨old, mapped⟩⟩
      · simp only [Heap.Memory.write_other _ _ _ _ he]

theorem exec_ram (h : Exec cmd env mem final mem') (hram : InRAM mem) : InRAM mem' := by
  intro a v hv
  obtain ⟨old, ho⟩ := (exec_domain h a).mpr ⟨v, hv⟩
  exact hram a old ho

private theorem frame_refl (mem : Heap.Memory) (s : SailState) : Frame mem s s :=
  fun _ _ => rfl

private theorem frame_trans (mem mid : Heap.Memory) (s t u : SailState)
    (hd : SameDomain mem mid) (ht : Frame mem s t) (hu : Frame mid t u) : Frame mem s u := by
  intro b hb
  rw [hu b (by
    intro a v hv
    obtain ⟨old, ho⟩ := (hd a).mpr ⟨v, hv⟩
    exact hb a old ho)]
  exact ht b hb

/-- Every terminating source derivation has a Sail execution, with the same
environment and heap, unchanged registers, and no writes outside the source
heap. The existential fuel applies to that derivation, not to the program. -/
theorem exec_correct (h : Exec cmd env mem final mem') :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ s : SailState,
      Ready s → InRAM mem → Represents mem s →
      ∃ after, run fuel cmd env s = .ok final after ∧ Ready after ∧
        Represents mem' after ∧ after.regs = s.regs ∧ Frame mem s after := by
  induction h with
  | skip =>
      refine ⟨1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ n => exact ⟨s, rfl, hr, hrep, rfl, frame_refl _ _⟩
  | seq first rest ia ib =>
      obtain ⟨n, hn⟩ := ia
      obtain ⟨m, hm⟩ := ib
      refine ⟨max n m + 1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ f =>
          obtain ⟨mid, runa, ready, rep, regs, frame⟩ := hn f (by omega) s hr hram hrep
          obtain ⟨after, runb, ready', rep', regs', frame'⟩ :=
            hm f (by omega) mid ready (exec_ram first hram) rep
          refine ⟨after, ?_, ready', rep', regs'.trans regs,
            frame_trans _ _ _ _ _ (exec_domain first) frame frame'⟩
          simpa only [run, bind, EStateM.bind, runa] using runb
  | assign hvalue =>
      refine ⟨1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ f =>
          have he := eval_correct _ _ _ s _ hr hram hrep hvalue
          refine ⟨s, ?_, hr, hrep, rfl, frame_refl _ _⟩
          simp only [run, bind, EStateM.bind, he, pure, EStateM.pure]
  | @store p v mem old layout type field ptr value env hp hv ha mapped =>
      refine ⟨1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ f =>
          have ep := eval_correct _ _ _ s _ hr hram hrep hp
          have ev := eval_correct _ _ _ s _ hr hram hrep hv
          have ew := write_correct _ s p v old _ hr hram ha mapped
          refine ⟨putWord s (p.toNat + 8 * field.index.val) v, ?_, hr,
            represents_write _ _ _ _ hrep (hram _ _ mapped).2.2, rfl, ?_⟩
          · simp only [run, bind, EStateM.bind, ep, ev, ew, pure, EStateM.pure]
          · intro byte hb
            exact putWord_frame s _ v byte (hb _ old mapped)
  | if_zero hc body ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ f =>
          obtain ⟨after, hb, ready, rep, regs, frame⟩ := hn f (by omega) s hr hram hrep
          have ec := eval_correct _ _ _ s _ hr hram hrep hc
          refine ⟨after, ?_, ready, rep, regs, frame⟩
          simpa only [run, bind, EStateM.bind, ec, ite_true] using hb
  | if_nonzero hc hv body ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ f =>
          obtain ⟨after, hb, ready, rep, regs, frame⟩ := hn f (by omega) s hr hram hrep
          have ec := eval_correct _ _ _ s _ hr hram hrep hc
          refine ⟨after, ?_, ready, rep, regs, frame⟩
          simpa only [run, bind, EStateM.bind, ec, hv, ite_false] using hb
  | while_zero hc =>
      refine ⟨1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ f =>
          have ec := eval_correct _ _ _ s _ hr hram hrep hc
          refine ⟨s, ?_, hr, hrep, rfl, frame_refl _ _⟩
          simp only [run, bind, EStateM.bind, ec, ite_true, pure, EStateM.pure]
  | while_nonzero hc hv first rest ia ib =>
      obtain ⟨n, hn⟩ := ia
      obtain ⟨m, hm⟩ := ib
      refine ⟨max n m + 1, ?_⟩
      intro fuel hf s hr hram hrep
      cases fuel with
      | zero => omega
      | succ f =>
          obtain ⟨mid, runa, ready, rep, regs, frame⟩ := hn f (by omega) s hr hram hrep
          obtain ⟨after, runb, ready', rep', regs', frame'⟩ :=
            hm f (by omega) mid ready (exec_ram first hram) rep
          have ec := eval_correct _ _ _ s _ hr hram hrep hc
          refine ⟨after, ?_, ready', rep', regs'.trans regs,
            frame_trans _ _ _ _ _ (exec_domain first) frame frame'⟩
          simpa only [run, bind, EStateM.bind, ec, hv, ite_false, runa] using runb

theorem function_correct_all_fuel (fn : Function params vars result) (args : Env params)
    (mem mem' : Heap.Memory) (value : Word) (h : fn.Evaluates args mem value mem') :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ s : SailState,
      Ready s → InRAM mem → Represents mem s →
      ∃ after, call fn fuel args s = .ok value after ∧
        Ready after ∧ Represents mem' after ∧ after.regs = s.regs ∧ Frame mem s after := by
  obtain ⟨final, hexec, hvalue⟩ := h
  obtain ⟨bound, hbound⟩ := exec_correct hexec
  refine ⟨bound, ?_⟩
  intro fuel hf s hr hram hrep
  obtain ⟨after, hrun, ready, rep, regs, frame⟩ := hbound fuel hf s hr hram hrep
  have he := eval_correct fn.returns final mem' after value ready (exec_ram hexec hram) rep hvalue
  refine ⟨after, ?_, ready, rep, regs, frame⟩
  simpa only [call, bind, EStateM.bind, hrun] using he

theorem function_correct (fn : Function params vars result) (args : Env params)
    (mem mem' : Heap.Memory) (value : Word) (h : fn.Evaluates args mem value mem')
    (s : SailState) (hr : Ready s) (hram : InRAM mem) (hrep : Represents mem s) :
    ∃ fuel after, call fn fuel args s = .ok value after ∧
      Ready after ∧ Represents mem' after ∧ after.regs = s.regs ∧ Frame mem s after := by
  obtain ⟨bound, hb⟩ := function_correct_all_fuel fn args mem mem' value h
  obtain ⟨after, ha⟩ := hb bound (Nat.le_refl _) s hr hram hrep
  exact ⟨bound, after, ha⟩

/-- The representation and frame clauses determine *every* final physical
byte, not just the cells subsequently read by the program. -/
theorem memory_unique (before after : Heap.Memory) (s t u : SailState)
    (hd : SameDomain before after) (ht : Represents after t) (hu : Represents after u)
    (ft : Frame before s t) (fu : Frame before s u) :
    ∀ byte, t.mem.get? byte = u.mem.get? byte := by
  intro byte
  classical
  by_cases owned : ∃ a v, before a = some v ∧ a ≤ byte ∧ byte < a + 8
  · obtain ⟨a, old, ho, hlo, hhi⟩ := owned
    obtain ⟨v, hv⟩ := (hd a).mp ⟨old, ho⟩
    let i : Fin 8 := ⟨byte - a, by omega⟩
    have he : a + i.val = byte := by dsimp [i]; omega
    have ht' := (ht a v hv).2 i
    have hu' := (hu a v hv).2 i
    rw [he] at ht' hu'
    exact ht'.trans hu'.symm
  · have outside : ∀ a v, before a = some v → byte < a ∨ a + 8 ≤ byte := by
      intro a v hv
      have hn : ¬ (a ≤ byte ∧ byte < a + 8) := fun h => owned ⟨a, v, hv, h⟩
      omega
    exact (ft byte outside).trans (fu byte outside).symm

end Riscvc.Heap.SailLowering
