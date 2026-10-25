import Riscvc.Binary.Lifted
import Riscvc.Examples

/- Check this module independently with `lake build Riscvc.Binary.Choose`.
To bind the proof to a concrete ELF:
python3 scripts/lift_binary.py --example choose --proof-module Riscvc.Binary.Choose

The program below records the layout this proof handles. The lifter imports
`contract` and proves that the decoded binary has exactly this program, in
addition to checking its bytes and Sail decoding.
-/
namespace Riscvc.Binary.Choose

open Riscvc.Binary.Lifted Riscvc.Binary.SailProofs
open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

attribute [local simp] Std.ExtDHashMap.get?_insert

def node0 : Node :=
  ⟨0x80000000, 0x00050463, .BTYPE (8, (.Regidx 0), (.Regidx 10), .BEQ)⟩
def node1 : Node :=
  ⟨0x80000004, 0x00058613, .ITYPE (0, (.Regidx 11), (.Regidx 12), .ADDI)⟩
def node2 : Node :=
  ⟨0x80000008, 0x00060513, .ITYPE (0, (.Regidx 12), (.Regidx 10), .ADDI)⟩
def node3 : Node :=
  ⟨0x8000000c, 0x00008067, .JALR (0, (.Regidx 1), (.Regidx 0))⟩

def program : Program := [node0, node1, node2, node3]

def pre (s : SailState) : Prop :=
  Config s ∧ s.regs.get? .PC = some 0x80000000 ∧
  ∃ flag x y ra : Word,
    s.regs.get? .x10 = some flag ∧ s.regs.get? .x11 = some x ∧
    s.regs.get? .x12 = some y ∧ s.regs.get? .x1 = some ra ∧ ra &&& 3 = 0

def post (before after : SailState) : Prop :=
  after.regs.get? .x10 = some (Riscvc.execute Examples.choose
    (Env.three ((before.regs.get? .x10).getD 0)
      ((before.regs.get? .x11).getD 0) ((before.regs.get? .x12).getD 0))) ∧
  after.regs.get? .PC = before.regs.get? .x1 ∧
  after.mem = before.mem ∧
  ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .PC → r ≠ .nextPC →
    after.regs.get? r = before.regs.get? r

private def branchState (s : SailState) (flag : Word) : SailState :=
  let start := setReg s .nextPC 0x80000004
  if flag = 0 then setReg (setReg start .nextPC 0x80000008) .PC 0x80000008
  else setReg start .PC 0x80000004

private theorem branchState_of_zero (s : SailState) (flag : Word) (h : flag = 0) :
    branchState s flag = setReg (setReg (setReg s .nextPC 0x80000004) .nextPC 0x80000008) .PC 0x80000008 := by
  unfold branchState
  rw [ite_eq_left h]

private theorem branchState_of_ne (s : SailState) (flag : Word) (h : flag ≠ 0) :
    branchState s flag = setReg (setReg s .nextPC 0x80000004) .PC 0x80000004 := by
  unfold branchState
  rw [ite_eq_right h]

private theorem branch_run (s : SailState) (flag : Word) (hc : Config s)
    (hpc : s.regs.get? .PC = some 0x80000000)
    (hflag : s.regs.get? .x10 = some flag) :
    node0.run s = .ok () (branchState s flag) := by
  obtain ⟨hp, hz, hm⟩ := hc
  by_cases hf : flag = 0
  · rw [branchState_of_zero s flag hf]
    subst flag
    apply node_run_of node0 s (setReg (setReg s .nextPC 0x80000004) .nextPC 0x80000008) 0x80000008
    · change execute_BTYPE 8 (.Regidx 0) (.Regidx 10) .BEQ _ = _
      simp [execute_BTYPE, rX_bits, rX, zero_reg, zeros, regval_from_reg, Sail.BitVec.toNatInt,
        readReg, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, pure, EStateM.pure, hflag, hpc, setReg, sign_extend, Sail.BitVec.signExtend]
      simpa [setReg, node0] using jump_to_ok (setReg s .nextPC 0x80000004) 0x80000008
        (by simpa [setReg] using hm) (by decide)
    · simp [setReg]
  · rw [branchState_of_ne s flag hf]
    apply node_run_of node0 s (setReg s .nextPC 0x80000004) 0x80000004
    · simp [node0, RiscvSail.Functions.execute, execute_BTYPE, rX_bits, rX, zero_reg, zeros, regval_from_reg,
        Sail.BitVec.toNatInt, readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
        EStateM.get, bind, EStateM.bind, pure, EStateM.pure, hflag, setReg, hf]
      erw [ite_eq_right hf]
      rfl
    · simp [setReg]

private def moveState (node : Node) (s : SailState) (dst : Register)
    (value : RegisterType dst) : SailState :=
  setReg (setReg (setReg s .nextPC (node.address + 4)) dst value) .PC (node.address + 4)

private theorem move_left (s : SailState) (x : Word) (hx : s.regs.get? .x11 = some x) :
    node1.run s = .ok () (moveState node1 s .x12 x) := by
  apply node_run_of node1 s (setReg (setReg s .nextPC 0x80000008) .x12 x) 0x80000008
  · simp [node1, RiscvSail.Functions.execute, execute_ITYPE, rX_bits, rX, wX_bits, wX, regval_from_reg,
      regval_into_reg, Sail.BitVec.toNatInt, readReg, PreSail.readReg, get, getThe,
      MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
      hx, setReg, sign_extend, Sail.BitVec.signExtend, xreg_write_callback, xreg_full_write_callback]
    rfl
  · simp [setReg]

private theorem move_result (s : SailState) (y : Word) (hy : s.regs.get? .x12 = some y) :
    node2.run s = .ok () (moveState node2 s .x10 y) := by
  apply node_run_of node2 s (setReg (setReg s .nextPC 0x8000000c) .x10 y) 0x8000000c
  · simp [node2, RiscvSail.Functions.execute, execute_ITYPE, rX_bits, rX, wX_bits, wX, regval_from_reg,
      regval_into_reg, Sail.BitVec.toNatInt, readReg, PreSail.readReg, get, getThe,
      MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
      hy, setReg, sign_extend, Sail.BitVec.signExtend, xreg_write_callback, xreg_full_write_callback]
    rfl
  · simp [setReg]

private def returnState (s : SailState) (ra : Word) : SailState :=
  setReg (setReg (setReg s .nextPC 0x80000010) .nextPC ra) .PC ra

private theorem return_run (s : SailState) (ra : Word) (hc : Config s)
    (hr : s.regs.get? .x1 = some ra) (ha : ra &&& 3 = 0) :
    node3.run s = .ok () (returnState s ra) := by
  obtain ⟨hp, hz, hm⟩ := hc
  apply node_run_of node3 s (setReg (setReg s .nextPC 0x80000010) .nextPC ra) ra
  · apply ret_step _ ra 0x80000010
    · simpa [setReg] using hp
    · simpa [setReg] using hz
    · simpa [setReg] using hm
    · simpa [setReg] using hr
    · simp [setReg, node3]
    · exact ha
  · simp [setReg]

theorem ir_correct : Hoare program pre post := by
  intro s hs
  obtain ⟨hc, hpc, flag, x, y, ra, hf, hx, hy, hr, ha⟩ := hs
  have first : Lifted.step program s = .ok () (branchState s flag) := by
    rw [step_node program node0 s hc hpc (by rfl)]
    exact branch_run s flag hc hpc hf
  have spec : Riscvc.execute Examples.choose (Env.three flag x y) =
      (if flag = 0 then y else x) := by rw [Riscvc.execute_correct]; rfl
  by_cases hzero : flag = 0
  · let s1 := branchState s flag
    let s2 := moveState node2 s1 .x10 y
    let s3 := returnState s2 ra
    have second : Lifted.step program s1 = .ok () s2 := by
      rw [step_node program node2 s1
        (by simpa [s1, branchState_of_zero _ _ hzero, Config, setReg] using hc)
        (by simp [s1, branchState_of_zero _ _ hzero, setReg, node2]) (by rfl)]
      exact move_result s1 y (by simpa [s1, branchState_of_zero _ _ hzero, setReg] using hy)
    have third : Lifted.step program s2 = .ok () s3 := by
      rw [step_node program node3 s2
        (by simpa [s2, s1, moveState, branchState_of_zero _ _ hzero, Config, setReg] using hc)
        (by simp [s2, moveState, setReg, node2, node3]) (by rfl)]
      exact return_run s2 ra
        (by simpa [s2, s1, moveState, branchState_of_zero _ _ hzero, Config, setReg] using hc)
        (by simpa [s2, s1, moveState, branchState_of_zero _ _ hzero, setReg] using hr) ha
    refine ⟨3, s3, ?_, ?_⟩
    · exact run_cons_of first (run_cons_of second (run_cons_of third rfl))
    · unfold post
      rw [hf, hx, hy, hr]
      change _ = some (Riscvc.execute Examples.choose (Env.three flag x y)) ∧ _
      rw [spec, ite_eq_left hzero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [s3, s2, returnState, moveState, setReg]
      · simp [s3, returnState, setReg]
      · simp [s3, s2, s1, returnState, moveState, branchState_of_zero _ _ hzero, setReg]
      · intro r h10 h12 hpc hnext
        simp [s3, s2, s1, returnState, moveState, branchState_of_zero _ _ hzero, setReg,
          Ne.symm h10, Ne.symm h12, Ne.symm hpc, Ne.symm hnext]
  · let s1 := branchState s flag
    let s2 := moveState node1 s1 .x12 x
    let s3 := moveState node2 s2 .x10 x
    let s4 := returnState s3 ra
    have second : Lifted.step program s1 = .ok () s2 := by
      rw [step_node program node1 s1
        (by simpa [s1, branchState_of_ne _ _ hzero, Config, setReg] using hc)
        (by simp [s1, branchState_of_ne _ _ hzero, setReg, node1]) (by rfl)]
      exact move_left s1 x (by simpa [s1, branchState_of_ne _ _ hzero, setReg] using hx)
    have third : Lifted.step program s2 = .ok () s3 := by
      rw [step_node program node2 s2
        (by simpa [s2, s1, moveState, branchState_of_ne _ _ hzero, Config, setReg] using hc)
        (by simp [s2, moveState, setReg, node1, node2]) (by rfl)]
      exact move_result s2 x (by simp [s2, moveState, setReg])
    have fourth : Lifted.step program s3 = .ok () s4 := by
      rw [step_node program node3 s3
        (by simpa [s3, s2, s1, moveState, branchState_of_ne _ _ hzero, Config, setReg] using hc)
        (by simp [s3, moveState, setReg, node2, node3]) (by rfl)]
      exact return_run s3 ra
        (by simpa [s3, s2, s1, moveState, branchState_of_ne _ _ hzero, Config, setReg] using hc)
        (by simpa [s3, s2, s1, moveState, branchState_of_ne _ _ hzero, setReg] using hr) ha
    refine ⟨4, s4, ?_, ?_⟩
    · exact run_cons_of first (run_cons_of second (run_cons_of third (run_cons_of fourth rfl)))
    · unfold post
      rw [hf, hx, hy, hr]
      change _ = some (Riscvc.execute Examples.choose (Env.three flag x y)) ∧ _
      rw [spec, ite_eq_right hzero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [s4, s3, returnState, moveState, setReg]
      · simp [s4, returnState, setReg]
      · simp [s4, s3, s2, s1, returnState, moveState, branchState_of_ne _ _ hzero, setReg]
      · intro r h10 h12 hpc hnext
        simp [s4, s3, s2, s1, returnState, moveState, branchState_of_ne _ _ hzero, setReg,
          Ne.symm h10, Ne.symm h12, Ne.symm hpc, Ne.symm hnext]

/-- Interface consumed by `lift_binary.py --proof-module Riscvc.Binary.Choose`. -/
def contract : Contract := ⟨program, pre, post, ir_correct⟩

end Riscvc.Binary.Choose
