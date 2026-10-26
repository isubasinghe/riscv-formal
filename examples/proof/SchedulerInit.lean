import examples.Scheduler
import Riscvc.Binary.Lifted
import Riscvc.Binary.Memory

/-! Source-to-disassembly refinement for `scheduler_init`. The program is
matched against the decoded ELF by `lift_binary.py --proof-module`.
The postcondition contains execution of the actual quoted DSL definition.
-/
namespace Riscvc.Heap.Scheduler.InitProof

open Riscvc.Binary Riscvc.Binary.Lifted Riscvc.Binary.SailProofs
open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

attribute [local simp] Std.ExtDHashMap.get?_insert

def node0 : Node := ⟨0x80000000, 0x00053423, .STORE (8, .Regidx 0, .Regidx 10, 8)⟩
def node1 : Node := ⟨0x80000004, 0x00053023, .STORE (0, .Regidx 0, .Regidx 10, 8)⟩
def node2 : Node := ⟨0x80000008, 0x00b53823, .STORE (16, .Regidx 11, .Regidx 10, 8)⟩
def node3 : Node := ⟨0x8000000c, 0x00053c23, .STORE (24, .Regidx 0, .Regidx 10, 8)⟩
def node4 : Node := ⟨0x80000010, 0x02053023, .STORE (32, .Regidx 0, .Regidx 10, 8)⟩
def node5 : Node := ⟨0x80000014, 0x02053423, .STORE (40, .Regidx 0, .Regidx 10, 8)⟩
def node6 : Node := ⟨0x80000018, 0x00000513, .ITYPE (0, .Regidx 0, .Regidx 10, .ADDI)⟩
def node7 : Node := ⟨0x8000001c, 0x00008067, .JALR (0, .Regidx 1, .Regidx 0)⟩
def program : Program := [node0, node1, node2, node3, node4, node5, node6, node7]

def args (p pool : Word) : Env [.ptr State.name, .ptr Process.name] :=
  fun i => if i.val = 0 then p else pool

def heapAfter (mem : Heap.Memory) (p pool : Word) : Heap.Memory :=
  (((((mem.write p.toNat 0).write (p.toNat + 8) 0).write (p.toNat + 16) pool).write
    (p.toNat + 24) 0).write (p.toNat + 32) 0).write (p.toNat + 40) 0

def StateSpace (mem : Heap.Memory) (p : Word) : Prop :=
  Accessible p 40 ∧
  (∀ j : Fin 6, Binary.Memory.Address (p + BitVec.ofNat 64 (8 * j.val))) ∧
  (∀ j : Fin 6, ∃ v, mem (p.toNat + 8 * j.val) = some v)

private theorem access (mem : Heap.Memory) (p : Word) (h : StateSpace mem p)
    (n : Nat) (hn : n ≤ 40) : Accessible p n :=
  ⟨h.1.1, h.1.2.1, by have := h.1.2.2; omega⟩

theorem source_correct (mem : Heap.Memory) (p pool : Word) (h : StateSpace mem p) :
    init.Evaluates (args p pool) mem 0 (heapAfter mem p pool) := by
  obtain ⟨v0, h0⟩ := h.2.2 ⟨0, by decide⟩
  obtain ⟨v1, h1⟩ := h.2.2 ⟨1, by decide⟩
  obtain ⟨v2, h2⟩ := h.2.2 ⟨2, by decide⟩
  obtain ⟨v3, h3⟩ := h.2.2 ⟨3, by decide⟩
  obtain ⟨v4, h4⟩ := h.2.2 ⟨4, by decide⟩
  obtain ⟨v5, h5⟩ := h.2.2 ⟨5, by decide⟩
  simp only [Fin.val_mk, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.add_zero] at h0 h1 h2 h3 h4 h5
  refine ⟨initial (args p pool), ?_, rfl⟩
  apply Exec.seq
  · exact Exec.store rfl rfl (access mem p h 0 (by decide)) h0
  apply Exec.seq
  · exact Exec.store rfl rfl (access mem p h 8 (by decide))
      (by simpa [Heap.Memory.write, initial, args, State.head, State.tail] using h1)
  apply Exec.seq
  · exact Exec.store rfl rfl (access mem p h 16 (by decide))
      (by simpa [Heap.Memory.write, initial, args, State.head, State.tail, State.free] using h2)
  apply Exec.seq
  · exact Exec.store rfl rfl (access mem p h 24 (by decide))
      (by simpa [Heap.Memory.write, initial, args, State.head, State.tail, State.free, State.count] using h3)
  apply Exec.seq
  · exact Exec.store rfl rfl (access mem p h 32 (by decide))
      (by simpa [Heap.Memory.write, initial, args, State.head, State.tail, State.free, State.count, State.ticks] using h4)
  apply Exec.seq
  · exact Exec.store rfl rfl (access mem p h 40 (by decide))
      (by simpa [Heap.Memory.write, initial, args, State.head, State.tail, State.free, State.count,
        State.ticks, State.lastPid] using h5)
  exact Exec.skip

private def advance (s : SailState) (pc : Word) : SailState :=
  setReg (setReg s .nextPC pc) .PC pc

private def stored (s : SailState) (pc : Word) (a : Nat) (v : Word) : SailState :=
  advance (Binary.Memory.putWord s a v) pc

private theorem store_step (node : Node) (s : SailState) (imm : BitVec 12)
    (rs : regidx) (p v : Word)
    (hi : node.instruction = .STORE (imm, rs, .Regidx 10, 8))
    (hn : lookup program node.address = some node)
    (hc : Config s) (hr : Binary.Memory.Ready s)
    (hpc : s.regs.get? .PC = some node.address)
    (hp : s.regs.get? .x10 = some p)
    (hv : rX_bits rs (setReg s .nextPC (node.address + 4)) =
      .ok v (setReg s .nextPC (node.address + 4)))
    (ha : Binary.Memory.Address (p + imm.signExtend 64)) :
    Lifted.step program s =
      .ok () (stored s (node.address + 4) (p + imm.signExtend 64).toNat v) := by
  rw [step_node program node s hc hpc hn]
  apply node_run_of node s
    (Binary.Memory.putWord (setReg s .nextPC (node.address + 4))
      (p + imm.signExtend 64).toNat v) (node.address + 4)
  · rw [hi]
    apply Binary.Memory.store64 _ imm (.Regidx 10) rs p v
    · simpa [Binary.Memory.Ready, setReg] using hr
    · simp [rX_bits, rX, regval_from_reg, Sail.BitVec.toNatInt,
        readReg_ok, setReg, hp]
    · exact hv
    · exact ha
  · simp [Binary.Memory.putWord, setReg]

private theorem zero_step (s : SailState) (hc : Config s)
    (hpc : s.regs.get? .PC = some node6.address) :
    Lifted.step program s = .ok ()
      (setReg (setReg (setReg s .nextPC 0x8000001c) .x10 0) .PC 0x8000001c) := by
  rw [step_node program node6 s hc hpc (by rfl)]
  apply node_run_of node6 s (setReg (setReg s .nextPC 0x8000001c) .x10 0) 0x8000001c
  · simp [node6, RiscvSail.Functions.execute, execute_ITYPE, rX_bits, rX,
      wX_bits, wX, regval_from_reg, regval_into_reg, zero_reg, zeros,
      Sail.BitVec.toNatInt, sign_extend, Sail.BitVec.signExtend,
      bind, EStateM.bind, pure, EStateM.pure, xreg_write_callback,
      xreg_full_write_callback, writeReg_ok]
    rfl
  · simp [setReg]

private theorem return_step (s : SailState) (ra : Word) (hc : Config s)
    (hpc : s.regs.get? .PC = some node7.address)
    (hr : s.regs.get? .x1 = some ra) (ha : ra &&& 3 = 0) :
    Lifted.step program s = .ok ()
      (setReg (setReg (setReg s .nextPC 0x80000020) .nextPC ra) .PC ra) := by
  rw [step_node program node7 s hc hpc (by rfl)]
  apply node_run_of node7 s (setReg (setReg s .nextPC 0x80000020) .nextPC ra) ra
  · apply ret_step _ ra 0x80000020
    · simpa [setReg] using hc.1
    · simpa [setReg] using hc.2.1
    · simpa [setReg] using hc.2.2
    · simpa [setReg] using hr
    · simp [setReg, node7]
    · exact ha
  · simp [setReg]


private theorem offset_nat (mem : Heap.Memory) (p : Word) (h : StateSpace mem p)
    (n : Nat) (hn : n ≤ 40) : (p + BitVec.ofNat 64 n).toNat = p.toNat + n := by
  have hb : p.toNat + n < 2 ^ 64 := by have := h.1.2.2; omega
  have hn' : n < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn',
    Nat.mod_eq_of_lt hb]

private theorem write_comm (m : Heap.Memory) (a b : Nat) (v w : Word) (h : a ≠ b) :
    (m.write a v).write b w = (m.write b w).write a v := by
  funext x
  by_cases ha : x = a <;> by_cases hb : x = b <;> simp_all [Heap.Memory.write]

/-- Universal refinement of the eight decoded instructions to the actual DSL.
The only restrictions concern valid memory and the explicitly configured Sail
platform. Initial field values, the pool pointer, and return address are arbitrary. -/
theorem refines (s : SailState) (mem : Heap.Memory) (p pool ra : Word)
    (hc : Config s) (hr : Binary.Memory.Ready s)
    (hpc : s.regs.get? .PC = some 0x80000000)
    (hp : s.regs.get? .x10 = some p) (hpool : s.regs.get? .x11 = some pool)
    (hra : s.regs.get? .x1 = some ra) (halign : ra &&& 3 = 0)
    (hs : StateSpace mem p) (hmem : Binary.Memory.Represents mem s) :
    ∃ after, Lifted.run program 8 s = .ok () after ∧
      init.Evaluates (args p pool) mem 0 (heapAfter mem p pool) ∧
      after.regs.get? .x10 = some 0 ∧ after.regs.get? .PC = some ra ∧
      Binary.Memory.Represents (heapAfter mem p pool) after ∧
      (∀ a, a < p.toNat ∨ p.toNat + 48 ≤ a → after.mem.get? a = s.mem.get? a) ∧
      (∀ r, r ≠ .x10 → r ≠ .PC → r ≠ .nextPC → after.regs.get? r = s.regs.get? r) := by
  let s1 := stored s 0x80000004 (p.toNat + 8) 0
  have h0 : Lifted.step program s = .ok () s1 := by
    have h := store_step node0 s 8 (.Regidx 0) p 0 rfl (by rfl)
      (by simpa [stored, advance, Binary.Memory.putWord, Config, setReg] using hc)
      (by simpa [stored, advance, Binary.Memory.putWord, Binary.Memory.Ready, setReg] using hr)
      hpc
      (by simpa [stored, advance, Binary.Memory.putWord, setReg] using hp)
      (by rfl)
      (by simpa using hs.2.1 ⟨1, by decide⟩)
    simpa [s1, node0, offset_nat mem p hs 8 (by decide)] using h
  have rep1 : Binary.Memory.Represents ((mem).write (p.toNat + 8) 0) s1 :=
    Binary.Memory.represents_write (mem) s (p.toNat + 8) 0
      hmem (by have := hs.1.2.1; omega)
  let s2 := stored s1 0x80000008 (p.toNat + 0) 0
  have h1 : Lifted.step program s1 = .ok () s2 := by
    have h := store_step node1 s1 0 (.Regidx 0) p 0 rfl (by rfl)
      (by simpa [s1, stored, advance, Binary.Memory.putWord, Config, setReg] using hc)
      (by simpa [s1, stored, advance, Binary.Memory.putWord, Binary.Memory.Ready, setReg] using hr)
      (by simp [s1, stored, advance, setReg, node1])
      (by simpa [s1, stored, advance, Binary.Memory.putWord, setReg] using hp)
      (by rfl)
      (by simpa using hs.2.1 ⟨0, by decide⟩)
    simpa [s2, node1, offset_nat mem p hs 0 (by decide)] using h
  have rep2 : Binary.Memory.Represents (((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0) s2 :=
    Binary.Memory.represents_write ((mem).write (p.toNat + 8) 0) s1 (p.toNat + 0) 0
      rep1 (by have := hs.1.2.1; omega)
  let s3 := stored s2 0x8000000c (p.toNat + 16) pool
  have h2 : Lifted.step program s2 = .ok () s3 := by
    have h := store_step node2 s2 16 (.Regidx 11) p pool rfl (by rfl)
      (by simpa [s2, s1, stored, advance, Binary.Memory.putWord, Config, setReg] using hc)
      (by simpa [s2, s1, stored, advance, Binary.Memory.putWord, Binary.Memory.Ready, setReg] using hr)
      (by simp [s2, stored, advance, setReg, node2])
      (by simpa [s2, s1, stored, advance, Binary.Memory.putWord, setReg] using hp)
      (by simp [s2, s1, stored, advance, Binary.Memory.putWord, rX_bits, rX,
        regval_from_reg, Sail.BitVec.toNatInt, readReg_ok, setReg, hpool])
      (by simpa using hs.2.1 ⟨2, by decide⟩)
    simpa [s3, node2, offset_nat mem p hs 16 (by decide)] using h
  have rep3 : Binary.Memory.Represents ((((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0).write (p.toNat + 16) pool) s3 :=
    Binary.Memory.represents_write (((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0) s2 (p.toNat + 16) pool
      rep2 (by have := hs.1.2.1; omega)
  let s4 := stored s3 0x80000010 (p.toNat + 24) 0
  have h3 : Lifted.step program s3 = .ok () s4 := by
    have h := store_step node3 s3 24 (.Regidx 0) p 0 rfl (by rfl)
      (by simpa [s3, s2, s1, stored, advance, Binary.Memory.putWord, Config, setReg] using hc)
      (by simpa [s3, s2, s1, stored, advance, Binary.Memory.putWord, Binary.Memory.Ready, setReg] using hr)
      (by simp [s3, stored, advance, setReg, node3])
      (by simpa [s3, s2, s1, stored, advance, Binary.Memory.putWord, setReg] using hp)
      (by rfl)
      (by simpa using hs.2.1 ⟨3, by decide⟩)
    simpa [s4, node3, offset_nat mem p hs 24 (by decide)] using h
  have rep4 : Binary.Memory.Represents (((((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0).write (p.toNat + 16) pool).write (p.toNat + 24) 0) s4 :=
    Binary.Memory.represents_write ((((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0).write (p.toNat + 16) pool) s3 (p.toNat + 24) 0
      rep3 (by have := hs.1.2.1; omega)
  let s5 := stored s4 0x80000014 (p.toNat + 32) 0
  have h4 : Lifted.step program s4 = .ok () s5 := by
    have h := store_step node4 s4 32 (.Regidx 0) p 0 rfl (by rfl)
      (by simpa [s4, s3, s2, s1, stored, advance, Binary.Memory.putWord, Config, setReg] using hc)
      (by simpa [s4, s3, s2, s1, stored, advance, Binary.Memory.putWord, Binary.Memory.Ready, setReg] using hr)
      (by simp [s4, stored, advance, setReg, node4])
      (by simpa [s4, s3, s2, s1, stored, advance, Binary.Memory.putWord, setReg] using hp)
      (by rfl)
      (by simpa using hs.2.1 ⟨4, by decide⟩)
    simpa [s5, node4, offset_nat mem p hs 32 (by decide)] using h
  have rep5 : Binary.Memory.Represents ((((((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0).write (p.toNat + 16) pool).write (p.toNat + 24) 0).write (p.toNat + 32) 0) s5 :=
    Binary.Memory.represents_write (((((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0).write (p.toNat + 16) pool).write (p.toNat + 24) 0) s4 (p.toNat + 32) 0
      rep4 (by have := hs.1.2.1; omega)
  let s6 := stored s5 0x80000018 (p.toNat + 40) 0
  have h5 : Lifted.step program s5 = .ok () s6 := by
    have h := store_step node5 s5 40 (.Regidx 0) p 0 rfl (by rfl)
      (by simpa [s5, s4, s3, s2, s1, stored, advance, Binary.Memory.putWord, Config, setReg] using hc)
      (by simpa [s5, s4, s3, s2, s1, stored, advance, Binary.Memory.putWord, Binary.Memory.Ready, setReg] using hr)
      (by simp [s5, stored, advance, setReg, node5])
      (by simpa [s5, s4, s3, s2, s1, stored, advance, Binary.Memory.putWord, setReg] using hp)
      (by rfl)
      (by simpa using hs.2.1 ⟨5, by decide⟩)
    simpa [s6, node5, offset_nat mem p hs 40 (by decide)] using h
  have rep6 : Binary.Memory.Represents (((((((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0).write (p.toNat + 16) pool).write (p.toNat + 24) 0).write (p.toNat + 32) 0).write (p.toNat + 40) 0) s6 :=
    Binary.Memory.represents_write ((((((mem).write (p.toNat + 8) 0).write (p.toNat + 0) 0).write (p.toNat + 16) pool).write (p.toNat + 24) 0).write (p.toNat + 32) 0) s5 (p.toNat + 40) 0
      rep5 (by have := hs.1.2.1; omega)
  let s7 := setReg (setReg (setReg s6 .nextPC 0x8000001c) .x10 0) .PC 0x8000001c
  have h6 : Lifted.step program s6 = .ok () s7 := zero_step s6
    (by simpa [s6, s5, s4, s3, s2, s1, stored, advance, Binary.Memory.putWord,
      Config, setReg] using hc)
    (by simp [s6, stored, advance, setReg, node6])
  let s8 := setReg (setReg (setReg s7 .nextPC 0x80000020) .nextPC ra) .PC ra
  have h7 : Lifted.step program s7 = .ok () s8 := return_step s7 ra
    (by simpa [s7, s6, s5, s4, s3, s2, s1, stored, advance, Binary.Memory.putWord,
      Config, setReg] using hc)
    (by simp [s7, setReg, node7])
    (by simpa [s7, s6, s5, s4, s3, s2, s1, stored, advance, Binary.Memory.putWord,
      setReg] using hra) halign
  refine ⟨s8, run_cons_of h0 (run_cons_of h1 (run_cons_of h2 (run_cons_of h3
    (run_cons_of h4 (run_cons_of h5 (run_cons_of h6 (run_cons_of h7 rfl))))))),
    source_correct mem p pool hs, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s8, s7, setReg]
  · simp [s8, setReg]
  · have he : (mem.write (p.toNat + 8) 0).write p.toNat 0 =
        (mem.write p.toNat 0).write (p.toNat + 8) 0 :=
      write_comm mem (p.toNat + 8) p.toNat 0 0 (by omega)
    change Binary.Memory.Represents (heapAfter mem p pool) s6
    simpa only [Nat.add_zero, he, heapAfter] using rep6
  · intro a ha
    change (Binary.Memory.putWord (Binary.Memory.putWord (Binary.Memory.putWord
      (Binary.Memory.putWord (Binary.Memory.putWord (Binary.Memory.putWord s
      (p.toNat + 8) 0) (p.toNat + 0) 0) (p.toNat + 16) pool) (p.toNat + 24) 0)
      (p.toNat + 32) 0) (p.toNat + 40) 0).mem.get? a = s.mem.get? a
    repeat rw [Binary.Memory.putWord_frame _ _ _ a (by omega)]
  · intro r h10 hpc hnext
    simp [s8, s7, s6, s5, s4, s3, s2, s1, stored, advance, Binary.Memory.putWord,
      setReg, Ne.symm h10, Ne.symm hpc, Ne.symm hnext]

def pre (s : SailState) : Prop :=
  Config s ∧ Binary.Memory.Ready s ∧ s.regs.get? .PC = some 0x80000000 ∧
  ∃ mem p pool ra,
    s.regs.get? .x10 = some p ∧ s.regs.get? .x11 = some pool ∧
    s.regs.get? .x1 = some ra ∧ ra &&& 3 = 0 ∧
    StateSpace mem p ∧ Binary.Memory.Represents mem s

def post (before after : SailState) : Prop :=
  ∃ mem p pool ra,
    before.regs.get? .x10 = some p ∧ before.regs.get? .x11 = some pool ∧
    before.regs.get? .x1 = some ra ∧ StateSpace mem p ∧ Binary.Memory.Represents mem before ∧
    init.Evaluates (args p pool) mem 0 (heapAfter mem p pool) ∧
    after.regs.get? .x10 = some 0 ∧ after.regs.get? .PC = some ra ∧
    Binary.Memory.Represents (heapAfter mem p pool) after ∧
    (∀ a, a < p.toNat ∨ p.toNat + 48 ≤ a → after.mem.get? a = before.mem.get? a) ∧
    (∀ r, r ≠ .x10 → r ≠ .PC → r ≠ .nextPC → after.regs.get? r = before.regs.get? r)

theorem ir_correct : Hoare program pre post := by
  intro s hs
  obtain ⟨hc, hr, hpc, mem, p, pool, ra, hp, hpool, hra, halign, hspace, hmem⟩ := hs
  obtain ⟨after, run, source, value, pc, rep, frame, regs⟩ :=
    refines s mem p pool ra hc hr hpc hp hpool hra halign hspace hmem
  exact ⟨8, after, run, mem, p, pool, ra, hp, hpool, hra, hspace, hmem,
    source, value, pc, rep, frame, regs⟩

def contract : Contract := ⟨program, pre, post, ir_correct⟩

/-- A concrete satisfying input prevents the initializer contract from passing
only because its platform and memory premises are inconsistent. -/
theorem pre_inhabited : ∃ s, pre s := by
  let regs : SailState :=
    setReg (setReg (setReg (setReg (setReg (setReg (setReg (setReg
      (setReg (setReg (setReg (setReg (default : SailState)
      .cur_privilege .Machine) .mseccfg 0) .misa 0x8000000000000100) .mstatus 0)
      .pma_regions [Binary.Memory.ram]) .pmpcfg_n (Vector.replicate 64 0))
      .pmpaddr_n (Vector.replicate 64 0)) .htif_tohost_base none)
      .PC 0x80000000) .x10 0x80001000) .x11 0) .x1 0x80000400
  let mem : Heap.Memory := heapAfter (fun _ => none) 0x80001000 0
  let s := Binary.Memory.putWord (Binary.Memory.putWord (Binary.Memory.putWord
    (Binary.Memory.putWord (Binary.Memory.putWord (Binary.Memory.putWord regs
    0x80001000 0) 0x80001008 0) 0x80001010 0) 0x80001018 0) 0x80001020 0) 0x80001028 0
  have hrep : Binary.Memory.Represents mem s := by
    apply Binary.Memory.represents_write
    · apply Binary.Memory.represents_write
      · apply Binary.Memory.represents_write
        · apply Binary.Memory.represents_write
          · apply Binary.Memory.represents_write
            · apply Binary.Memory.represents_write
              · intro a v h
                cases h
              · decide
            · decide
          · decide
        · decide
      · decide
    · decide
  have space : StateSpace mem 0x80001000 := by
    refine ⟨by decide, by unfold Binary.Memory.Address; decide, ?_⟩
    have hm : ∀ j : Fin 6, mem (0x80001000 + 8 * j.val) = some 0 := by decide
    intro j
    exact ⟨0, hm j⟩
  refine ⟨s, ?_, ?_, ?_, mem, 0x80001000, 0, 0x80000400, ?_, ?_, ?_,
    by decide, space, hrep⟩
  all_goals simp [s, regs, Config, Binary.Memory.Ready, Binary.Memory.putWord, setReg]

end Riscvc.Heap.Scheduler.InitProof

/-- Module-name entry point expected by the ELF certificate generator. -/
def examples.proof.SchedulerInit.contract : Riscvc.Binary.Lifted.Contract :=
  Riscvc.Heap.Scheduler.InitProof.contract
