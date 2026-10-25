import Riscvc.Binary.Sail
import Riscvc.Language

namespace Riscvc.Binary.SailProofs

open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

attribute [local simp] Std.ExtDHashMap.get?_insert

def setReg (s : SailState) (r : Register) (value : RegisterType r) : SailState :=
  { s with regs := s.regs.insert r value }

theorem readReg_ok (s : SailState) (r : Register) (value : RegisterType r)
    (h : s.regs.get? r = some value) : readReg r s = .ok value s := by
  simp [readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind, pure, EStateM.pure, h]

theorem writeReg_ok (s : SailState) (r : Register) (value : RegisterType r) :
    writeReg r value s = .ok ⟨⟩ (setReg s r value) := rfl

theorem enabled_zicsr : currentlyEnabled .Ext_Zicsr = pure true := by
  rw [currentlyEnabled]
  simp [hartSupports]

theorem enabled_zicfilp (s : SailState)
    (hp : s.regs.get? .cur_privilege = some .Machine)
    (hc : s.regs.get? .mseccfg = some 0) :
    currentlyEnabled .Ext_Zicfilp s = .ok false s := by
  rw [currentlyEnabled]
  simp only [enabled_zicsr, pure_bind]
  simp [get_xLPE, readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind, pure, EStateM.pure, hp, hc, hartSupports]

theorem decode_add (s : SailState)
    (hp : s.regs.get? .cur_privilege = some .Machine)
    (hc : s.regs.get? .mseccfg = some 0) :
    encdec_backwards 0x00a58533 s =
      .ok (.RTYPE (.Regidx 10, .Regidx 11, .Regidx 10, .ADD)) s := by
  simp [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind, pure, EStateM.pure, hp, hc]
  rfl

theorem decode_ret (s : SailState)
    (hp : s.regs.get? .cur_privilege = some .Machine)
    (hc : s.regs.get? .mseccfg = some 0) :
    encdec_backwards 0x00008067 s = .ok (.JALR (0, .Regidx 1, .Regidx 0)) s := by
  simp [encdec_backwards, currentlyEnabled, get_xLPE, hartSupports,
    readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind, pure, EStateM.pure, hp, hc]
  rfl

theorem add_step (s : SailState) (n acc : Word)
    (h0 : s.regs.get? .x10 = some n) (h1 : s.regs.get? .x11 = some acc) :
    execute_RTYPE (.Regidx 10) (.Regidx 11) (.Regidx 10) .ADD s =
      .ok RETIRE_SUCCESS (setReg s .x10 (acc + n)) := by
  simp [execute_RTYPE, rX_bits, rX, wX_bits, wX, regval_from_reg, regval_into_reg,
    Sail.BitVec.toNatInt, readReg, PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind, pure, EStateM.pure, h0, h1,
    writeReg_ok, xreg_write_callback, xreg_full_write_callback]
  rfl

theorem enabled_zca (s : SailState) (hm : s.regs.get? .misa = some 0x8000000000000100) :
    currentlyEnabled .Ext_Zca s = .ok false s := by
  simp [currentlyEnabled, hartSupports, readReg, PreSail.readReg, get, getThe,
    MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure, hm,
    _get_Misa_C, Sail.BitVec.extractLsb]
  rfl

/-- Aligned integer control transfers cannot take Sail's alignment trap. -/
theorem jump_to_ok (s : SailState) (target : Word)
    (hm : s.regs.get? .misa = some 0x8000000000000100)
    (halign : target &&& 3 = 0) :
    jump_to target s = .ok RETIRE_SUCCESS (setReg s .nextPC target) := by
  have h0 : Sail.BitVec.access target 0 = 0#1 := by
    have h := congrArg (fun x : Word => x.getLsbD 0) halign
    change BitVec.ofBool (target.getLsbD 0) = 0#1
    have hz : target.getLsbD 0 = false := by simpa using h
    rw [hz]
    rfl
  have h1 : Sail.BitVec.access target 1 = 0#1 := by
    have h := congrArg (fun x : Word => x.getLsbD 1) halign
    change BitVec.ofBool (target.getLsbD 1) = 0#1
    have hz : target.getLsbD 1 = false := by simpa using h
    rw [hz]
    rfl
  simp [jump_to, ext_control_check_pc, h0, h1, bit_to_bool, bool_bit_backwards,
    enabled_zca s hm, set_next_pc,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift, ExceptT.mk, Functor.map, EStateM.map,
    liftM, monadLift, MonadLift.monadLift, RiscvSail.assert, PreSail.assert,
    bind, EStateM.bind, pure, EStateM.pure, writeReg_ok]

theorem ret_step (s : SailState) (ra next : Word)
    (hp : s.regs.get? .cur_privilege = some .Machine)
    (hc : s.regs.get? .mseccfg = some 0)
    (hm : s.regs.get? .misa = some 0x8000000000000100)
    (hr : s.regs.get? .x1 = some ra)
    (hn : s.regs.get? .nextPC = some next)
    (halign : ra &&& 3 = 0) :
    execute_JALR 0 (.Regidx 1) (.Regidx 0) s =
      .ok RETIRE_SUCCESS (setReg s .nextPC ra) := by
  have h0 : ra.getLsbD 0 = false := by
    have h := congrArg (fun x : Word => x.getLsbD 0) halign
    simpa using h
  have h1 : ra.getLsbD 1 = false := by
    have h := congrArg (fun x : Word => x.getLsbD 1) halign
    simpa using h
  have hbit0 : Sail.BitVec.access ra 0 = 0#1 := by
    change BitVec.ofBool (ra.getLsbD 0) = 0#1
    rw [h0]
    rfl
  have hbit1 : Sail.BitVec.access ra 1 = 0#1 := by
    change BitVec.ofBool (ra.getLsbD 1) = 0#1
    rw [h1]
    rfl
  have htarget : Sail.BitVec.update ra 0 0#1 = ra := by
    change ((~~~(1#64) &&& ra) ||| 0#64) = ra
    rw [BitVec.or_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
    by_cases hz : i = 0
    · subst i
      simp [h0]
      exact h0
    · simp [hz, hi]
  simp [execute_JALR, update_elp_state, get_next_pc, rX_bits, rX,
    sign_extend, Sail.BitVec.signExtend, jump_to, ext_control_check_pc,
    htarget, hbit0, hbit1, bit_to_bool, set_next_pc,
    enabled_zicfilp s hp hc, enabled_zca s hm, readReg, PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, hp, hc, hm, hr, hn, Sail.BitVec.toNatInt, regval_from_reg,
    SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    liftM, monadLift, MonadLift.monadLift, RiscvSail.assert, PreSail.assert, bool_bit_backwards,
    wX_bits, wX, writeReg_ok, ExceptT.mk, Functor.map, EStateM.map]
  rfl

theorem set_next_pc_ok (s : SailState) (pc : Word) :
    set_next_pc pc s = .ok () (setReg s .nextPC pc) := rfl

theorem tick_pc_ok (s : SailState) (pc : Word)
    (h : s.regs.get? .nextPC = some pc) :
    tick_pc () s = .ok () (setReg s .PC pc) := by
  have hpc : (setReg s .PC pc).regs.get? .PC = some pc := by simp [setReg]
  simp [tick_pc, bind, EStateM.bind, readReg_ok s _ _ h,
    writeReg_ok, readReg_ok _ _ _ hpc, pure, EStateM.pure]

/-- Compose fetch, Sail decode, Sail execute, and Sail PC commit. -/
theorem step_of (image : ELF.Image) (s after : SailState) (pc next : Word)
    (word : BitVec 32) (instruction : RiscvSail.instruction)
    (hpc : s.regs.get? .PC = some pc)
    (hfetch : image.fetchWord pc.toNat = some word)
    (hdecode : encdec_backwards word (setReg s .nextPC (pc + (4 : BitVec 64))) =
      .ok instruction (setReg s .nextPC (pc + (4 : BitVec 64))))
    (hexec : RiscvSail.Functions.execute instruction (setReg s .nextPC (pc + (4 : BitVec 64))) = .ok RETIRE_SUCCESS after)
    (hnext : after.regs.get? .nextPC = some next) :
    step image s = .ok () (setReg after .PC next) := by
  simp [step, bind, EStateM.bind, readReg_ok s _ _ hpc, hfetch,
    set_next_pc_ok, hdecode, hexec, RETIRE_SUCCESS, tick_pc_ok after next hnext]
  erw [hdecode]
  dsimp only
  erw [hexec]
  exact tick_pc_ok after next hnext

end Riscvc.Binary.SailProofs
