import Riscvc.Binary.Lifted
import Riscvc.Binary.Memory
import Riscvc.Heap.SailLowering

/-! A word-level presentation of the RV64 instructions used by the scheduler.
Each transition is connected below to the generated Sail instruction semantics;
the word memory is represented by eight little-endian Sail bytes per cell. -/
namespace Riscvc.Binary.WordMachine

open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions SailProofs Lifted

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

inductive Reg where
  | ra | a0 | a1 | a2 | a3 | a4 | a5 | a6 | a7
  deriving DecidableEq, Repr

def Reg.index : Reg → regidx
  | .ra => .Regidx 1 | .a0 => .Regidx 10 | .a1 => .Regidx 11
  | .a2 => .Regidx 12 | .a3 => .Regidx 13 | .a4 => .Regidx 14
  | .a5 => .Regidx 15 | .a6 => .Regidx 16 | .a7 => .Regidx 17

def Reg.name : Reg → Register
  | .ra => .x1 | .a0 => .x10 | .a1 => .x11 | .a2 => .x12
  | .a3 => .x13 | .a4 => .x14 | .a5 => .x15 | .a6 => .x16 | .a7 => .x17

def Reg.get (s : SailState) (r : Reg) : Option Word :=
  match r with
  | .ra => s.regs.get? .x1 | .a0 => s.regs.get? .x10 | .a1 => s.regs.get? .x11
  | .a2 => s.regs.get? .x12 | .a3 => s.regs.get? .x13 | .a4 => s.regs.get? .x14
  | .a5 => s.regs.get? .x15 | .a6 => s.regs.get? .x16 | .a7 => s.regs.get? .x17

def Reg.put (s : SailState) (r : Reg) (v : Word) : SailState :=
  match r with
  | .ra => setReg s .x1 v | .a0 => setReg s .x10 v | .a1 => setReg s .x11 v
  | .a2 => setReg s .x12 v | .a3 => setReg s .x13 v | .a4 => setReg s .x14 v
  | .a5 => setReg s .x15 v | .a6 => setReg s .x16 v | .a7 => setReg s .x17 v

abbrev Registers := Reg → Word

def Registers.put (rs : Registers) (r : Reg) (v : Word) : Registers :=
  fun q => if q = r then v else rs q

inductive Src where
  | zero | reg (r : Reg)
  deriving DecidableEq, Repr

def Src.index : Src → regidx
  | .zero => .Regidx 0 | .reg r => r.index

def Src.get (rs : Registers) : Src → Word
  | .zero => 0 | .reg r => rs r

structure State where
  pc : Word
  regs : Registers
  mem : Heap.Memory

inductive Op where
  | addi (rd : Reg) (rs : Src) (imm : BitVec 12)
  | sltiu (rd : Reg) (rs : Src) (imm : BitVec 12)
  | sltu (rd : Reg) (rs1 rs2 : Src)
  | and (rd : Reg) (rs1 rs2 : Src)
  | load (rd : Reg) (rs : Src) (imm : BitVec 12)
  | store (rs1 rs2 : Src) (imm : BitVec 12)
  | branch (eq : Bool) (rs1 rs2 : Src) (imm : BitVec 13)
  | jump (imm : BitVec 21)
  | ret
  deriving DecidableEq, Repr

def Op.instruction : Op → instruction
  | .addi rd rs imm => .ITYPE (imm, rs.index, rd.index, .ADDI)
  | .sltiu rd rs imm => .ITYPE (imm, rs.index, rd.index, .SLTIU)
  | .sltu rd rs1 rs2 => .RTYPE (rs2.index, rs1.index, rd.index, .SLTU)
  | .and rd rs1 rs2 => .RTYPE (rs2.index, rs1.index, rd.index, .AND)
  | .load rd rs imm => .LOAD (imm, rs.index, rd.index, false, 8)
  | .store rs1 rs2 imm => .STORE (imm, rs2.index, rs1.index, 8)
  | .branch eq rs1 rs2 imm => .BTYPE (imm, rs2.index, rs1.index, if eq then .BEQ else .BNE)
  | .jump imm => .JAL (imm, .Regidx 0)
  | .ret => .JALR (0, .Regidx 1, .Regidx 0)

def State.write (s : State) (rd : Reg) (v : Word) : State :=
  {s with pc := s.pc + 4, regs := s.regs.put rd v}

instance (a : Word) : Decidable (Memory.Address a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Op.eval (op : Op) (s : State) : Option State :=
  match op with
  | .addi rd rs imm => some (s.write rd (rs.get s.regs + imm.signExtend 64))
  | .sltiu rd rs imm => some (s.write rd (if rs.get s.regs < imm.signExtend 64 then 1 else 0))
  | .sltu rd rs1 rs2 => some (s.write rd (if rs1.get s.regs < rs2.get s.regs then 1 else 0))
  | .and rd rs1 rs2 => some (s.write rd (rs1.get s.regs &&& rs2.get s.regs))
  | .load rd rs imm => do
      let a := rs.get s.regs + imm.signExtend 64
      if Memory.Address a then
        let v ← s.mem a.toNat
        some (s.write rd v)
      else none
  | .store rs1 rs2 imm => do
      let a := rs1.get s.regs + imm.signExtend 64
      if Memory.Address a then
        let _ ← s.mem a.toNat
        some {s with pc := s.pc + 4, mem := s.mem.write a.toNat (rs2.get s.regs)}
      else none
  | .branch eq rs1 rs2 imm =>
      let pc := if (rs1.get s.regs == rs2.get s.regs) == eq then
          s.pc + imm.signExtend 64 else s.pc + 4
      if pc &&& 3 = 0 then some {s with pc := pc} else none
  | .jump imm =>
      let pc := s.pc + imm.signExtend 64
      if pc &&& 3 = 0 then some {s with pc := pc} else none
  | .ret =>
      if s.regs .ra &&& 3 = 0 then some {s with pc := s.regs .ra} else none

def Matches (a : State) (s : SailState) : Prop :=
  Config s ∧ Memory.Ready s ∧ s.regs.get? .PC = some a.pc ∧
  (∀ r, r.get s = some (a.regs r)) ∧ Memory.Represents a.mem s

def Frame (mem : Heap.Memory) (before after : SailState) : Prop :=
  Heap.SailLowering.Frame mem before after ∧
  ∀ r, (∀ q : Reg, r ≠ q.name) → r ≠ .PC → r ≠ .nextPC →
    after.regs.get? r = before.regs.get? r

attribute [local simp] Std.ExtDHashMap.get?_insert

@[simp] theorem reg_get_put (s : SailState) (r q : Reg) (v : Word) :
    q.get (r.put s v) = if q = r then some v else q.get s := by
  cases r <;> cases q <;> simp [Reg.get, Reg.put, setReg]

@[simp] theorem reg_get_pc (s : SailState) (r : Reg) (pc : Word) :
    r.get (setReg s .PC pc) = r.get s := by
  cases r <;> simp [Reg.get, setReg]

@[simp] theorem reg_get_next (s : SailState) (r : Reg) (pc : Word) :
    r.get (setReg s .nextPC pc) = r.get s := by
  cases r <;> simp [Reg.get, setReg]

@[simp] theorem reg_get_word (s : SailState) (r : Reg) (a : Nat) (v : Word) :
    r.get (Memory.putWord s a v) = r.get s := by cases r <;> rfl

theorem read_reg (s : SailState) (r : Reg) (v : Word) (h : r.get s = some v) :
    rX_bits r.index s = .ok v s := by
  cases r <;> simp_all [Reg.get, Reg.index, rX_bits, rX, regval_from_reg,
    Sail.BitVec.toNatInt, readReg_ok, bind, EStateM.bind, pure, EStateM.pure]

theorem read_src (s : SailState) (rs : Registers) (r : Src)
    (h : ∀ q, q.get s = some (rs q)) :
    rX_bits r.index s = .ok (r.get rs) s := by
  cases r with
  | zero => rfl
  | reg r => exact read_reg s r _ (h r)

theorem write_reg (s : SailState) (r : Reg) (v : Word) :
    wX_bits r.index v s = .ok () (r.put s v) := by
  cases r <;> simp [Reg.index, Reg.put, wX_bits, wX, regval_into_reg,
    Sail.BitVec.toNatInt, writeReg_ok, bind, EStateM.bind, pure, EStateM.pure,
    xreg_write_callback, xreg_full_write_callback] <;> rfl

theorem lt_word (x y : Word) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)) =
      (if x < y then (1 : Word) else 0) := by
  by_cases h : x.toNat < y.toNat <;>
    simp [zero_extend, Sail.BitVec.zeroExtend, bool_to_bit, bool_bit_forwards,
      zopz0zI_u, Sail.BitVec.toNatInt, BitVec.lt_def, h] <;> rfl

theorem alu_addi (s : SailState) (rs : Registers) (rd : Reg) (r : Src) (imm : BitVec 12)
    (h : ∀ q, q.get s = some (rs q)) :
    execute_ITYPE imm r.index rd.index .ADDI s =
      .ok RETIRE_SUCCESS (rd.put s (r.get rs + imm.signExtend 64)) := by
  simp [execute_ITYPE, sign_extend, Sail.BitVec.signExtend, bind, EStateM.bind,
    pure, EStateM.pure, read_src s rs r h, write_reg]

theorem alu_sltiu (s : SailState) (rs : Registers) (rd : Reg) (r : Src) (imm : BitVec 12)
    (h : ∀ q, q.get s = some (rs q)) :
    execute_ITYPE imm r.index rd.index .SLTIU s =
      .ok RETIRE_SUCCESS (rd.put s (if r.get rs < imm.signExtend 64 then 1 else 0)) := by
  simp [execute_ITYPE, sign_extend, Sail.BitVec.signExtend, bind, EStateM.bind,
    pure, EStateM.pure, read_src s rs r h, lt_word, write_reg]

theorem alu_sltu (s : SailState) (rs : Registers) (rd : Reg) (x y : Src)
    (h : ∀ q, q.get s = some (rs q)) :
    execute_RTYPE y.index x.index rd.index .SLTU s =
      .ok RETIRE_SUCCESS (rd.put s (if x.get rs < y.get rs then 1 else 0)) := by
  simp [execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure,
    read_src s rs x h, read_src s rs y h, lt_word, write_reg]

theorem alu_and (s : SailState) (rs : Registers) (rd : Reg) (x y : Src)
    (h : ∀ q, q.get s = some (rs q)) :
    execute_RTYPE y.index x.index rd.index .AND s =
      .ok RETIRE_SUCCESS (rd.put s (x.get rs &&& y.get rs)) := by
  simp [execute_RTYPE, bind, EStateM.bind, pure, EStateM.pure,
    read_src s rs x h, read_src s rs y h, write_reg]

@[simp] theorem config_put (s : SailState) (r : Reg) (v : Word) :
    Config (r.put s v) ↔ Config s := by
  cases r <;> simp [Reg.put, Config, setReg]

@[simp] theorem ready_put (s : SailState) (r : Reg) (v : Word) :
    Memory.Ready (r.put s v) ↔ Memory.Ready s := by
  cases r <;> simp [Reg.put, Memory.Ready, setReg]

@[simp] theorem mem_put (s : SailState) (r : Reg) (v : Word) :
    (r.put s v).mem = s.mem := by cases r <;> rfl

@[simp] theorem next_put (s : SailState) (r : Reg) (v : Word) :
    (r.put s v).regs.get? .nextPC = s.regs.get? .nextPC := by
  cases r <;> simp [Reg.put, setReg]

theorem frame_refl (mem : Heap.Memory) (s : SailState) : Frame mem s s :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem frame_write (mem : Heap.Memory) (s : SailState) (r : Reg) (v pc : Word) :
    Frame mem s (setReg (r.put (setReg s .nextPC pc) v) .PC pc) := by
  refine ⟨?_, ?_⟩
  · intro a _
    simp [setReg]
  · intro q h hpc hn
    have hr := h r
    cases r <;> simp_all [Reg.put, Reg.name, setReg, Ne.symm]

theorem frame_pc (mem : Heap.Memory) (s : SailState) (fall target : Word) :
    Frame mem s (setReg (setReg (setReg s .nextPC fall) .nextPC target) .PC target) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro r _ hp hn
  simp [setReg, Ne.symm hp, Ne.symm hn]

theorem matches_write {a : State} {s : SailState} (h : Matches a s)
    (rd : Reg) (v : Word) :
    Matches (a.write rd v) (setReg (rd.put (setReg s .nextPC (a.pc + 4)) v) .PC (a.pc + 4)) := by
  rcases h with ⟨hc, hr, hpc, hregs, hm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Config, setReg] using (config_put (setReg s .nextPC (a.pc + 4)) rd v).mpr
      (by simpa [Config, setReg] using hc)
  · simpa [Memory.Ready, setReg] using (ready_put (setReg s .nextPC (a.pc + 4)) rd v).mpr
      (by simpa [Memory.Ready, setReg] using hr)
  · simp [State.write, setReg]
  · intro q
    simp [State.write, Registers.put, hregs]
    split <;> simp_all
  · intro b w hw
    exact ⟨(hm b w hw).1, by simpa [Memory.WordAt, setReg] using (hm b w hw).2⟩

theorem matches_pc {a : State} {s : SailState} (h : Matches a s) (fall target : Word) :
    Matches {a with pc := target}
      (setReg (setReg (setReg s .nextPC fall) .nextPC target) .PC target) := by
  rcases h with ⟨hc, hr, hpc, hregs, hm⟩
  refine ⟨?_, ?_, ?_, ?_, hm⟩
  · simpa [Config, setReg] using hc
  · simpa [Memory.Ready, setReg] using hr
  · simp [setReg]
  · intro q
    simpa using hregs q

theorem branch_taken (s : SailState) (rs : Registers) (x y : Src) (imm : BitVec 13)
    (eq : Bool) (pc : Word)
    (h : ∀ q, q.get s = some (rs q)) (hp : s.regs.get? .PC = some pc)
    (hm : s.regs.get? .misa = some 0x8000000000000100)
    (ht : ((x.get rs == y.get rs) == eq) = true)
    (ha : (pc + imm.signExtend 64) &&& 3 = 0) :
    execute_BTYPE imm y.index x.index (if eq then .BEQ else .BNE) s =
      .ok RETIRE_SUCCESS (setReg s .nextPC (pc + imm.signExtend 64)) := by
  cases eq <;> cases hb : (x.get rs == y.get rs) <;>
    simp_all [execute_BTYPE, bind, EStateM.bind, pure, EStateM.pure,
      read_src s rs x h, read_src s rs y h, readReg_ok s .PC pc hp,
      sign_extend, Sail.BitVec.signExtend, jump_to_ok s _ hm ha]

theorem branch_untaken (s : SailState) (rs : Registers) (x y : Src) (imm : BitVec 13)
    (eq : Bool) (h : ∀ q, q.get s = some (rs q))
    (ht : ((x.get rs == y.get rs) == eq) = false) :
    execute_BTYPE imm y.index x.index (if eq then .BEQ else .BNE) s = .ok RETIRE_SUCCESS s := by
  cases eq <;> cases hb : (x.get rs == y.get rs) <;>
    simp_all [execute_BTYPE, bind, EStateM.bind, pure, EStateM.pure,
      read_src s rs x h, read_src s rs y h]

theorem jump_ok (s : SailState) (imm : BitVec 21) (pc next : Word)
    (hp : s.regs.get? .PC = some pc) (hn : s.regs.get? .nextPC = some next)
    (hm : s.regs.get? .misa = some 0x8000000000000100)
    (ha : (pc + imm.signExtend 64) &&& 3 = 0) :
    execute_JAL imm (.Regidx 0) s =
      .ok RETIRE_SUCCESS (setReg s .nextPC (pc + imm.signExtend 64)) := by
  simp only [execute_JAL, get_next_pc, bind, EStateM.bind, readReg_ok s .nextPC next hn,
    readReg_ok s .PC pc hp, sign_extend, Sail.BitVec.signExtend]
  erw [jump_to_ok s _ hm ha]
  rfl

theorem store_matches {a : State} {s : SailState} (h : Matches a s)
    (addr value : Word) (ha : Memory.Address addr) :
    Matches {a with pc := a.pc + 4, mem := a.mem.write addr.toNat value}
      (setReg (Memory.putWord (setReg s .nextPC (a.pc + 4)) addr.toNat value) .PC (a.pc + 4)) := by
  rcases h with ⟨hc, hr, hp, hregs, hm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Config, setReg, Memory.putWord] using hc
  · simpa [Memory.Ready, setReg, Memory.putWord] using hr
  · simp [setReg]
  · intro q
    simpa using hregs q
  · exact Memory.represents_write a.mem s addr.toNat value hm ha.2.2

theorem store_frame (a : State) (s : SailState) (addr value : Word)
    (hm : ∃ old, a.mem addr.toNat = some old) :
    Frame a.mem s
      (setReg (Memory.putWord (setReg s .nextPC (a.pc + 4)) addr.toNat value) .PC (a.pc + 4)) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨old, ho⟩ := hm
    exact Memory.putWord_frame s addr.toNat value b (hb addr.toNat old ho)
  · intro r _ hp hn
    simp [Memory.putWord, setReg, Ne.symm hp, Ne.symm hn]

/-- Every successful word transition is an actual Sail instruction transition.
No decoder or memory behavior is replaced by an axiom. -/
theorem instruction_correct (node : Node) (op : Op) (a b : State) (s : SailState)
    (hi : node.instruction = op.instruction) (hp : node.address = a.pc)
    (hs : Matches a s) (he : op.eval a = some b) :
    ∃ after, node.run s = .ok () after ∧ Matches b after ∧ Frame a.mem s after := by
  let t := setReg s .nextPC (a.pc + 4)
  have hregs : ∀ q, q.get t = some (a.regs q) := by intro q; simpa [t] using hs.2.2.2.1 q
  have hready : Memory.Ready t := by simpa [t, Memory.Ready, setReg] using hs.2.1
  have hmisa : t.regs.get? .misa = some 0x8000000000000100 := by
    simpa [t, setReg] using hs.1.2.2
  have hpc : t.regs.get? .PC = some a.pc := by simpa [t, setReg] using hs.2.2.1
  have hn : t.regs.get? .nextPC = some (a.pc + 4) := by simp [t, setReg]
  cases op with
  | addi rd rs imm =>
    simp only [Op.eval, Option.some.injEq] at he
    subst b
    refine ⟨_, ?_, matches_write hs rd _, frame_write _ _ rd _ _⟩
    apply node_run_of node s (rd.put t _) (a.pc + 4)
    · simpa only [hi, hp, Op.instruction, RiscvSail.Functions.execute] using alu_addi t a.regs rd rs imm hregs
    · simpa using hn
  | sltiu rd rs imm =>
    simp only [Op.eval, Option.some.injEq] at he
    subst b
    refine ⟨_, ?_, matches_write hs rd _, frame_write _ _ rd _ _⟩
    apply node_run_of node s (rd.put t _) (a.pc + 4)
    · simpa only [hi, hp, Op.instruction, RiscvSail.Functions.execute] using alu_sltiu t a.regs rd rs imm hregs
    · simpa using hn
  | sltu rd rs1 rs2 =>
    simp only [Op.eval, Option.some.injEq] at he
    subst b
    refine ⟨_, ?_, matches_write hs rd _, frame_write _ _ rd _ _⟩
    apply node_run_of node s (rd.put t _) (a.pc + 4)
    · simpa only [hi, hp, Op.instruction, RiscvSail.Functions.execute] using alu_sltu t a.regs rd rs1 rs2 hregs
    · simpa using hn
  | and rd rs1 rs2 =>
    simp only [Op.eval, Option.some.injEq] at he
    subst b
    refine ⟨_, ?_, matches_write hs rd _, frame_write _ _ rd _ _⟩
    apply node_run_of node s (rd.put t _) (a.pc + 4)
    · simpa only [hi, hp, Op.instruction, RiscvSail.Functions.execute] using alu_and t a.regs rd rs1 rs2 hregs
    · simpa using hn
  | load rd rs imm =>
    simp only [Op.eval] at he
    split at he
    next ha =>
      cases hv : a.mem (rs.get a.regs + imm.signExtend 64).toNat with
      | none => simp only [hv, bind, Option.bind] at he; contradiction
      | some v =>
        simp only [hv, bind, Option.bind, Option.some.injEq] at he
        subst b
        refine ⟨_, ?_, matches_write hs rd v, frame_write _ _ rd v _⟩
        apply node_run_of node s (rd.put t v) (a.pc + 4)
        · rw [hi, hp]
          exact Memory.load64 t (rd.put t v) imm rs.index rd.index _ v hready
            (read_src t a.regs rs hregs) ha (hs.2.2.2.2 _ v hv).2 (write_reg t rd v)
        · simpa using hn
    next => contradiction
  | store rs1 rs2 imm =>
    simp only [Op.eval] at he
    split at he
    next ha =>
      cases hv : a.mem (rs1.get a.regs + imm.signExtend 64).toNat with
      | none => simp only [hv, bind, Option.bind] at he; contradiction
      | some v =>
        simp only [hv, bind, Option.bind, Option.some.injEq] at he
        subst b
        refine ⟨_, ?_, store_matches hs _ _ ha, store_frame _ _ _ _ ⟨v, hv⟩⟩
        apply node_run_of node s (Memory.putWord t _ _) (a.pc + 4)
        · rw [hi, hp]
          exact Memory.store64 t imm rs1.index rs2.index _ _ hready
            (read_src t a.regs rs1 hregs) (read_src t a.regs rs2 hregs) ha
        · simpa [Memory.putWord] using hn
    next => contradiction
  | branch eq rs1 rs2 imm =>
    cases hc : ((rs1.get a.regs == rs2.get a.regs) == eq)
    all_goals simp only [Op.eval, hc, Bool.false_eq_true, ↓reduceIte, ite_true] at he
    · split at he
      next ha =>
        cases he
        refine ⟨setReg t .PC (a.pc + 4), ?_, ?_, ?_⟩
        · apply node_run_of node s t (a.pc + 4)
          · simpa only [hi, hp, Op.instruction, RiscvSail.Functions.execute] using branch_untaken t a.regs rs1 rs2 imm eq hregs hc
          · exact hn
        · refine ⟨?_, ?_, ?_, ?_, hs.2.2.2.2⟩
          · simpa [t, Config, setReg] using hs.1
          · simpa [t, Memory.Ready, setReg] using hs.2.1
          · simp [setReg]
          · intro q
            simpa using hregs q
        · refine ⟨fun _ _ => rfl, ?_⟩
          intro r _ hp hn
          simp [t, setReg, Ne.symm hp, Ne.symm hn]
      next => contradiction
    · split at he
      next ha =>
        cases he
        refine ⟨_, ?_, matches_pc hs (a.pc + 4) _, frame_pc _ _ (a.pc + 4) _⟩
        apply node_run_of node s (setReg t .nextPC (a.pc + imm.signExtend 64)) _
        · simpa only [hi, hp, Op.instruction, RiscvSail.Functions.execute] using
            branch_taken t a.regs rs1 rs2 imm eq a.pc hregs hpc hmisa hc ha
        · simp [setReg]
      next => contradiction
  | jump imm =>
    simp only [Op.eval] at he
    split at he
    next ha =>
      cases he
      refine ⟨_, ?_, matches_pc hs (a.pc + 4) _, frame_pc _ _ (a.pc + 4) _⟩
      apply node_run_of node s (setReg t .nextPC (a.pc + imm.signExtend 64)) _
      · simpa only [hi, hp, Op.instruction, RiscvSail.Functions.execute] using jump_ok t imm a.pc _ hpc hn hmisa ha
      · simp [setReg]
    next => contradiction
  | ret =>
    simp only [Op.eval] at he
    split at he
    next ha =>
      cases he
      refine ⟨_, ?_, matches_pc hs (a.pc + 4) _, frame_pc _ _ (a.pc + 4) _⟩
      apply node_run_of node s (setReg t .nextPC (a.regs .ra)) _
      · rw [hi, hp]
        exact ret_step t (a.regs .ra) _
          (by simpa [t, setReg] using hs.1.1)
          (by simpa [t, setReg] using hs.1.2.1) hmisa (hregs .ra) hn ha
      · simp [setReg]
    next => contradiction

abbrev Program := List (Node × Op)

def Program.nodes (p : Program) : Lifted.Program := p.map Prod.fst

def Program.Valid (p : Program) : Prop :=
  ∀ pair ∈ p, pair.1.instruction = pair.2.instruction

def step (p : Program) (s : State) : Option State := do
  let pair ← p.find? (fun pair => pair.1.address == s.pc)
  pair.2.eval s

def run (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (step p s).bind (run p n)

theorem lookup_nodes (p : Program) (pc : Word) (pair : Node × Op)
    (h : p.find? (fun pair => pair.1.address == pc) = some pair) :
    Lifted.lookup p.nodes pc = some pair.1 := by
  induction p with
  | nil => simp at h
  | cons first rest ih =>
    simp only [List.find?_cons] at h
    split at h
    next hf =>
      cases h
      simp [Lifted.lookup, Program.nodes, List.find?_cons, hf]
    next hf =>
      simpa [Lifted.lookup, Program.nodes, List.find?_cons, hf] using ih h

theorem step_correct (p : Program) (valid : p.Valid) (a b : State) (s : SailState)
    (hs : Matches a s) (he : step p a = some b) :
    ∃ after, Lifted.step p.nodes s = .ok () after ∧ Matches b after ∧ Frame a.mem s after := by
  unfold step at he
  cases hf : p.find? (fun pair => pair.1.address == a.pc) with
  | none => simp [hf] at he
  | some pair =>
    simp only [hf, bind, Option.bind] at he
    have hp : pair.1.address = a.pc := by simpa using List.find?_some hf
    obtain ⟨after, hr, hm, hframe⟩ := instruction_correct pair.1 pair.2 a b s
      (valid pair (List.mem_of_find?_eq_some hf)) hp hs he
    refine ⟨after, ?_, hm, hframe⟩
    rw [step_node p.nodes pair.1 s hs.1 (by simpa [hp] using hs.2.2.1)
      (by simpa [hp] using lookup_nodes p a.pc pair hf)]
    exact hr

theorem domain_write (mem : Heap.Memory) (a : Nat) (v old : Word)
    (h : mem a = some old) : Heap.SailLowering.SameDomain mem (mem.write a v) := by
  intro b
  by_cases hb : b = a
  · subst b
    simp [h]
  · simp [Heap.Memory.write, hb]

theorem op_domain (op : Op) (a b : State) (he : op.eval a = some b) :
    Heap.SailLowering.SameDomain a.mem b.mem := by
  have refl (m : Heap.Memory) : Heap.SailLowering.SameDomain m m := fun _ => Iff.rfl
  cases op with
  | addi | sltiu | sltu | and =>
    simp only [Op.eval, Option.some.injEq] at he
    cases he
    exact refl _
  | load rd rs imm =>
    simp only [Op.eval] at he
    split at he
    next ha =>
      cases hv : a.mem (rs.get a.regs + imm.signExtend 64).toNat with
      | none => simp only [hv, bind, Option.bind] at he; contradiction
      | some v =>
        simp only [hv, bind, Option.bind, Option.some.injEq] at he
        cases he
        exact refl _
    next => contradiction
  | store rs1 rs2 imm =>
    simp only [Op.eval] at he
    split at he
    next ha =>
      cases hv : a.mem (rs1.get a.regs + imm.signExtend 64).toNat with
      | none => simp only [hv, bind, Option.bind] at he; contradiction
      | some v =>
        simp only [hv, bind, Option.bind, Option.some.injEq] at he
        cases he
        exact domain_write _ _ _ _ hv
    next => contradiction
  | branch | jump | ret =>
    simp only [Op.eval] at he
    repeat first | contradiction | (cases he; exact refl _) | split at he

theorem step_domain (p : Program) (a b : State) (he : step p a = some b) :
    Heap.SailLowering.SameDomain a.mem b.mem := by
  unfold step at he
  cases hf : p.find? (fun pair => pair.1.address == a.pc) with
  | none => simp [hf] at he
  | some pair =>
    simp only [hf, bind, Option.bind] at he
    exact op_domain pair.2 a b he

theorem run_add (p : Program) (m n : Nat) (s : State) :
    run p (m + n) s = (run p m s).bind (run p n) := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add]; rfl
  | succ m ih =>
    simp only [Nat.succ_add, run]
    cases h : step p s <;> simp [ih]

theorem run_domain (p : Program) (n : Nat) (a b : State) (he : run p n a = some b) :
    Heap.SailLowering.SameDomain a.mem b.mem := by
  induction n generalizing a with
  | zero => cases he; exact fun _ => Iff.rfl
  | succ n ih =>
    simp only [run] at he
    cases hs : step p a with
    | none => simp [hs] at he
    | some mid =>
      simp only [hs, Option.bind_some] at he
      exact fun addr => (step_domain p a mid hs addr).trans (ih mid he addr)

theorem run_ram (p : Program) (n : Nat) (a b : State) (he : run p n a = some b)
    (hr : Heap.SailLowering.InRAM a.mem) : Heap.SailLowering.InRAM b.mem := by
  intro addr value hm
  obtain ⟨old, ho⟩ := (run_domain p n a b he addr).mpr ⟨value, hm⟩
  exact hr addr old ho

theorem frame_trans (mem mem' : Heap.Memory) (a b c : SailState)
    (hd : Heap.SailLowering.SameDomain mem mem')
    (hab : Frame mem a b) (hbc : Frame mem' b c) : Frame mem a c := by
  refine ⟨?_, ?_⟩
  · intro byte hbyte
    rw [hbc.1 byte, hab.1 byte hbyte]
    intro addr val hv
    obtain ⟨v, h⟩ := (hd addr).mpr ⟨val, hv⟩
    exact hbyte addr v h
  · intro r hr hp hn
    rw [hbc.2 r hr hp hn, hab.2 r hr hp hn]

/-- Transfer an arbitrarily long successful word execution, including loops,
to the original Sail semantics of the decoded program. -/
theorem run_correct (p : Program) (valid : p.Valid) (n : Nat) (a b : State) (s : SailState)
    (hs : Matches a s) (he : run p n a = some b) :
    ∃ after, Lifted.run p.nodes n s = .ok () after ∧ Matches b after ∧ Frame a.mem s after := by
  induction n generalizing a s with
  | zero =>
    cases he
    exact ⟨s, rfl, hs, frame_refl _ _⟩
  | succ n ih =>
    simp only [run] at he
    cases hf : step p a with
    | none => simp [hf] at he
    | some mid =>
      simp only [hf, Option.bind_some] at he
      obtain ⟨next, hn, hmatch, hframe⟩ := step_correct p valid a mid s hs hf
      obtain ⟨after, hr, hma, hfr⟩ := ih mid next hmatch he
      exact ⟨after, run_cons_of hn hr, hma,
        frame_trans _ _ _ _ _ (step_domain p a mid hf) hframe hfr⟩

end Riscvc.Binary.WordMachine
