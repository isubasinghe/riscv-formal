import Riscvc.Binary.SailProofs
import Riscvc.RecursiveExamples

namespace Riscvc.Binary.CountUp

open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions SailProofs

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

attribute [local simp] Std.ExtDHashMap.get?_insert

structure Ready (s : SailState) (entry n acc ra : Word) : Prop where
  pc : s.regs.get? .PC = some entry
  arg0 : s.regs.get? .x10 = some n
  arg1 : s.regs.get? .x11 = some acc
  returnAddress : s.regs.get? .x1 = some ra
  aligned : ra &&& 3 = 0
  privilege : s.regs.get? .cur_privilege = some .Machine
  security : s.regs.get? .mseccfg = some 0
  isa : s.regs.get? .misa = some 0x8000000000000100

/-- Observable function result, return, and preservation of the caller's state.
Only a0 and the two PC registers may change. -/
structure Returned (before after : SailState) (n acc ra : Word) : Prop where
  result : after.regs.get? .x10 = some (RecursiveExamples.countUp.execute (Env.two n acc))
  pc : after.regs.get? .PC = some ra
  registers : ∀ r, r ≠ .x10 → r ≠ .PC → r ≠ .nextPC → after.regs.get? r = before.regs.get? r
  memory : after.mem = before.mem
  choices : after.choiceState = before.choiceState
  tags : after.tags = before.tags
  cycles : after.cycleCount = before.cycleCount
  output : after.sailOutput = before.sailOutput

def RefinesIR (image : ELF.Image) : Prop :=
  ∀ (s : SailState) (n acc ra : Word),
    Ready s (BitVec.ofNat 64 image.entry) n acc ra →
    TextLoaded image s →
    ∃ after, run image 2 s = .ok () after ∧ Returned s after n acc ra ∧ TextLoaded image after

/-- The reusable translation-validation theorem. LLVM and the linker need not
be trusted: the three image premises are checked against each concrete ELF. -/
theorem correct (image : ELF.Image)
    (hentry : image.entry = 0x80000000)
    (hadd : image.fetchWord 0x80000000 = some 0x00a58533)
    (hret : image.fetchWord 0x80000004 = some 0x00008067) : RefinesIR image := by
  intro s n acc ra ready loaded
  rw [hentry] at ready
  let s0 := setReg s .nextPC 0x80000004
  let s1 := setReg s0 .x10 (acc + n)
  let s2 := setReg s1 .PC 0x80000004
  let s3 := setReg s2 .nextPC 0x80000008
  let s4 := setReg s3 .nextPC ra
  let s5 := setReg s4 .PC ra
  have d0 : encdec_backwards 0x00a58533 s0 =
      .ok (.RTYPE (.Regidx 10, .Regidx 11, .Regidx 10, .ADD)) s0 :=
    decode_add s0 (by simpa [s0, setReg] using ready.privilege)
      (by simpa [s0, setReg] using ready.security)
  have e0 : RiscvSail.Functions.execute (.RTYPE (.Regidx 10, .Regidx 11, .Regidx 10, .ADD)) s0 =
      .ok RETIRE_SUCCESS s1 :=
    add_step s0 n acc (by simpa [s0, setReg] using ready.arg0)
      (by simpa [s0, setReg] using ready.arg1)
  have first : step image s = .ok () s2 :=
    step_of image s s1 0x80000000 0x80000004 _ _ ready.pc hadd d0 e0
      (by simp [s1, s0, setReg])
  have d1 : encdec_backwards 0x00008067 s3 = .ok (.JALR (0, .Regidx 1, .Regidx 0)) s3 :=
    decode_ret s3 (by simpa [s3, s2, s1, s0, setReg] using ready.privilege)
      (by simpa [s3, s2, s1, s0, setReg] using ready.security)
  have e1 : RiscvSail.Functions.execute (.JALR (0, .Regidx 1, .Regidx 0)) s3 =
      .ok RETIRE_SUCCESS s4 :=
    ret_step s3 ra 0x80000008
      (by simpa [s3, s2, s1, s0, setReg] using ready.privilege)
      (by simpa [s3, s2, s1, s0, setReg] using ready.security)
      (by simpa [s3, s2, s1, s0, setReg] using ready.isa)
      (by simpa [s3, s2, s1, s0, setReg] using ready.returnAddress)
      (by simp [s3, setReg]) ready.aligned
  have second : step image s2 = .ok () s5 :=
    step_of image s2 s4 0x80000004 ra _ _ (by simp [s2, setReg]) hret d1 e1
      (by simp [s4, setReg])
  refine ⟨s5, ?_, ?_, ?_⟩
  · simp [run, SeqRight.seqRight, EStateM.seqRight, bind, EStateM.bind,
      first, second, pure, EStateM.pure]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, setReg, RecursiveExamples.countUp_compiled,
        BitVec.add_comm]
    · simp [s5, setReg]
    · intro r h0 hp hn
      simp [s5, s4, s3, s2, s1, s0, setReg, h0, hp, hn, Ne.symm h0,
        Ne.symm hp, Ne.symm hn]
    all_goals rfl
  · exact loaded

/-- A certificate binds the universal theorem to the entire executable file. -/
def Certificate (bytes : ELF.Bytes) : Prop :=
  ∃ image, ELF.parse bytes = some image ∧ RefinesIR image

/- The four platform declarations belong to the upstream Sail model. This
   guard rejects accidental admissions or native proof-checking assumptions. -/
/--
info: 'Riscvc.Binary.CountUp.correct' depends on axioms: [load_reservation,
 match_reservation,
 plat_term_write,
 propext,
 sys_enable_experimental_extensions,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms correct

end Riscvc.Binary.CountUp
