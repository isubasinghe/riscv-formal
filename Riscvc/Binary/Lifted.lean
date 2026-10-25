import Riscvc.Binary.SailProofs

/-! A decoded, addressed IR with Sail semantics. The lifter is untrusted: every
node carries an obligation connecting its instruction to bytes fetched by the
Lean ELF loader and decoded by Sail. Successful lifted executions refine the
binary harness, for arbitrary control flow and any finite number of steps.

The configuration guard makes the decoder's assumptions explicit at *each*
step. A proof cannot silently run past an unsupported instruction, a missing
target, a changed configuration, or a Sail exception.
-/
namespace Riscvc.Binary.Lifted

open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions SailProofs

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def Config (s : SailState) : Prop :=
  s.regs.get? .cur_privilege = some .Machine ∧
  s.regs.get? .mseccfg = some 0 ∧
  s.regs.get? .misa = some 0x8000000000000100

noncomputable instance (s : SailState) : Decidable (Config s) := Classical.propDecidable _

structure Node where
  address : Word
  word : BitVec 32
  instruction : RiscvSail.instruction

abbrev Program := List Node

def lookup (program : Program) (pc : Word) : Option Node :=
  program.find? fun node => node.address == pc

/-- Instruction effects and PC commit are the original generated Sail functions. -/
noncomputable def Node.run (node : Node) : SailM Unit := do
  set_next_pc (node.address + 4)
  match ← execute node.instruction with
  | .Retire_Success () => tick_pc ()
  | _ => throw (.Assertion "Instruction did not retire successfully")

noncomputable def step (program : Program) (s : SailState) :
    EStateM.Result (Sail.Error exception) SailState Unit :=
  if Config s then
    match s.regs.get? .PC with
    | none => .error (.Assertion "Missing PC") s
    | some pc => match lookup program pc with
      | none => .error (.Assertion "PC outside lifted program") s
      | some node => node.run s
  else .error (.Assertion "Unsupported machine configuration") s

noncomputable def run (program : Program) : Nat → SailM Unit
  | 0 => pure ()
  | n + 1 => step program *> run program n

structure Node.Valid (image : ELF.Image) (node : Node) : Prop where
  fetch : image.fetchWord node.address.toNat = some node.word
  decode : ∀ s : SailState, Config s →
    encdec_backwards node.word s = .ok node.instruction s

def Certified (image : ELF.Image) (program : Program) : Prop :=
  ∀ node ∈ program, node.Valid image

theorem config_next (s : SailState) (pc : Word) (h : Config s) :
    Config (setReg s .nextPC pc) := by
  simpa [Config, setReg, Std.ExtDHashMap.get?_insert] using h

theorem node_correct (node : Node) (image : ELF.Image) (h : node.Valid image)
    (s : SailState) (hc : Config s) (hp : s.regs.get? .PC = some node.address) :
    Binary.step image s = node.run s := by
  have hd := h.decode (setReg s .nextPC (node.address + 4))
    (config_next s _ hc)
  simp [Binary.step, Node.run, bind, EStateM.bind, readReg_ok s _ _ hp,
    h.fetch, set_next_pc_ok]
  erw [hd]
  rfl

theorem lookup_mem {program : Program} {pc : Word} {node : Node}
    (h : lookup program pc = some node) : node ∈ program ∧ node.address = pc := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  exact ⟨hm, by simpa using hp⟩

theorem step_node (program : Program) (node : Node) (s : SailState)
    (hc : Config s) (hp : s.regs.get? .PC = some node.address)
    (hn : lookup program node.address = some node) : step program s = node.run s := by
  simp [step, hc, hp, hn]

theorem node_run_of (node : Node) (s after : SailState) (next : Word)
    (he : execute node.instruction (setReg s .nextPC (node.address + 4)) =
      .ok RETIRE_SUCCESS after)
    (hn : after.regs.get? .nextPC = some next) :
    node.run s = .ok () (setReg after .PC next) := by
  simp only [Node.run, bind, EStateM.bind, set_next_pc_ok]
  erw [he]
  exact tick_pc_ok after next hn

/-- A successful lifted step has exactly the same full Sail state transition. -/
theorem step_correct {image : ELF.Image} {program : Program}
    (cert : Certified image program) {s after : SailState}
    (h : step program s = .ok () after) : Binary.step image s = .ok () after := by
  unfold step at h
  split at h
  next hc =>
    split at h
    next => contradiction
    next pc hp =>
      split at h
      next => contradiction
      next node hn =>
        obtain ⟨hm, ha⟩ := lookup_mem hn
        rw [← ha] at hp
        rw [node_correct node image (cert node hm) s hc hp]
        exact h
  next => contradiction

/-- This theorem is independent of program length, instruction shape, entry
address, branches, loops, and calls. The premise proves successful execution. -/
theorem run_correct {image : ELF.Image} {program : Program}
    (cert : Certified image program) (steps : Nat) {s after : SailState}
    (h : run program steps s = .ok () after) :
    Binary.run image steps s = .ok () after := by
  induction steps generalizing s with
  | zero => exact h
  | succ n ih =>
    simp only [run, SeqRight.seqRight, EStateM.seqRight, bind, EStateM.bind] at h
    cases hs : step program s with
    | error error state => simp [hs] at h
    | ok value state =>
      cases value
      have ht := step_correct cert hs
      simp only [hs] at h
      simpa only [Binary.run, SeqRight.seqRight, EStateM.seqRight, bind,
        EStateM.bind, ht] using ih h

theorem run_add (program : Program) (m n : Nat) (s : SailState) :
    run program (m + n) s = (run program m *> run program n) s := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add]; rfl
  | succ m ih =>
    simp only [Nat.succ_add, run, SeqRight.seqRight, EStateM.seqRight, bind, EStateM.bind]
    cases h : step program s with
    | error error state => rfl
    | ok value state => exact ih state

theorem run_cons_of {program : Program} {n : Nat} {s next after : SailState}
    (first : step program s = .ok () next)
    (rest : run program n next = .ok () after) : run program (n + 1) s = .ok () after := by
  simpa only [run, SeqRight.seqRight, EStateM.seqRight, first] using rest

def Hoare (program : Program) (pre : SailState → Prop)
    (post : SailState → SailState → Prop) : Prop :=
  ∀ s, pre s → ∃ steps after, run program steps s = .ok () after ∧ post s after

/-- A checked program contract exported by an ordinary Lean proof module.
The lifter checks equality with `program` before transferring `correct`. -/
structure Contract where
  program : Program
  pre : SailState → Prop
  post : SailState → SailState → Prop
  correct : Hoare program pre post

def BinaryHoare (image : ELF.Image) (pre : SailState → Prop)
    (post : SailState → SailState → Prop) : Prop :=
  ∀ s, pre s → TextLoaded image s →
    ∃ steps after, Binary.run image steps s = .ok () after ∧ post s after

theorem transfer {image : ELF.Image} {program : Program}
    (cert : Certified image program) {pre post} (proof : Hoare program pre post) :
    BinaryHoare image pre post := by
  intro s hs _
  obtain ⟨n, after, hr, hp⟩ := proof s hs
  exact ⟨n, after, run_correct cert n hr, hp⟩

/-- Prove unbounded loops at cutpoints. A segment may execute many instructions;
the rank must decrease between cutpoints. No fixed unrolling bound is assumed. -/
theorem loop (program : Program) (inv done : SailState → Prop)
    (rank : SailState → Nat)
    (progress : ∀ s, inv s → ¬done s →
      ∃ n next, run program n s = .ok () next ∧ inv next ∧ rank next < rank s)
    (s : SailState) (hs : inv s) :
    ∃ n after, run program n s = .ok () after ∧ inv after ∧ done after := by
  by_cases hd : done s
  · exact ⟨0, s, rfl, hs, hd⟩
  · obtain ⟨n, next, hr, hi, hlt⟩ := progress s hs hd
    obtain ⟨m, after, hm, ha⟩ := loop program inv done rank progress next hi
    refine ⟨n + m, after, ?_, ha⟩
    rw [run_add]
    simpa only [SeqRight.seqRight, EStateM.seqRight, bind, EStateM.bind, hr] using hm
termination_by rank s

end Riscvc.Binary.Lifted
