import examples.proof.SchedulerStepSegments
namespace Riscvc.Heap.Scheduler.StepProof
open Riscvc.Binary
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem values_eta (env : Env Ctx) :
    values (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) (env 9) = env := by
  funext ⟨i, hi⟩
  change i < 10 at hi
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | n + 10 => omega

theorem sourceAdd_eq (s : Control.State Ctx) (b : WordMachine.State) (h : AtAdd s b) :
    s = sourceAdd (s.env 0) (s.env 2) (s.env 3) (s.env 4) (s.env 8) s.mem := by
  rcases h with ⟨hs, _, hop, _, _, _, hprev, hnode, htail, _, hresult, _⟩
  rcases s with ⟨stack, env, mem⟩
  dsimp at *
  subst stack
  unfold sourceAdd
  congr 1
  calc
    env = values (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) (env 9) := (values_eta env).symm
    _ = _ := by rw [hop, hprev, hnode, htail, hresult]; rfl

theorem add_chunk (ra : Word) (s : Control.State Ctx) (b : WordMachine.State)
    (hm : b.mem = s.mem) (hr : b.regs .ra = ra) (h : AtAdd s b)
    (hram : SailLowering.InRAM s.mem) (hra : ra &&& 3 = 0)
    (k : Nat) (t : Control.State Ctx) (hc : Control.chunk s = some (k,t)) :
    Reaches b (Related ra t) := by
  have he := sourceAdd_eq s b h
  rcases h with ⟨_, hpc, hop, hp, hw, hcur, _, _, _, hd, _, h0, h1, h2, h3, h4, h6⟩
  have ht := add_segment (s.env 0) (s.env 2) (s.env 3) (s.env 4) (s.env 8)
    s.mem b.regs hp hw hcur hd h0 (h1.trans hop) h2 h3 h4 h6 hram
    (by simpa [hr] using hra) k t (by simpa only [← he] using hc)
  simpa only [← hm, ← hpc, hr] using ht


theorem sourceRemove_eq (s : Control.State Ctx) (b : WordMachine.State) (h : AtRemove s b) :
    s = sourceRemove (s.env 0) (s.env 2) (s.env 3) (s.env 4) (s.env 5) s.mem := by
  rcases h with ⟨hs, hop, _, hnode, htail, hdup, hresult, _⟩
  rcases s with ⟨stack, env, mem⟩
  dsimp at *
  subst stack
  unfold sourceRemove
  congr 1
  calc
    env = values (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7) (env 8) (env 9) := (values_eta env).symm
    _ = _ := by rw [hop, hnode, htail, hdup, hresult]; rfl

theorem remove_chunk (ra : Word) (s : Control.State Ctx) (b : WordMachine.State)
    (hm : b.mem = s.mem) (hr : b.regs .ra = ra) (h : AtRemove s b)
    (hram : SailLowering.InRAM s.mem) (hra : ra &&& 3 = 0)
    (k : Nat) (t : Control.State Ctx) (hc : Control.chunk s = some (k,t)) :
    Reaches b (Related ra t) := by
  have he := sourceRemove_eq s b h
  rcases h with ⟨_, hop, hcur, _, _, _, _, h0, h1, h2, h3, first | next⟩
  · obtain ⟨hpc, hprev⟩ := first
    have ht := remove_first_segment (s.env 0) (s.env 2) (s.env 3) (s.env 4)
      s.mem b.regs hcur h0 (h1.trans hop) h2 h3 hram
      (by simpa [hr] using hra) k t (by have hh := hc; rw [he] at hh; simpa only [hprev] using hh)
    simpa only [← hm, ← hpc, hr] using ht
  · obtain ⟨hpc, hprev, h5⟩ := next
    have ht := remove_next_segment (s.env 0) (s.env 2) (s.env 3) (s.env 4) (s.env 5)
      s.mem b.regs hcur hprev h0 (h1.trans hop) h2 h3 h5 hram
      (by simpa [hr] using hra) k t (by simpa only [← he] using hc)
    simpa only [← hm, ← hpc, hr] using ht

theorem related_chunk (ra : Word) (s : Control.State Ctx) (b : WordMachine.State)
    (h : Related ra s b) (hn : s.stack ≠ [])
    (hram : SailLowering.InRAM s.mem) (hra : ra &&& 3 = 0)
    (k : Nat) (t : Control.State Ctx) (hc : Control.chunk s = some (k,t)) :
    Reaches b (Related ra t) := by
  rcases h with ⟨hm, hr, hf | ha | hrm⟩
  · exact False.elim (hn hf.1)
  · exact add_chunk ra s b hm hr ha hram hra k t hc
  · exact remove_chunk ra s b hm hr hrm hram hra k t hc

theorem related_return (ra : Word) (env : Env Ctx) (mem : Heap.Memory) (b : WordMachine.State)
    (h : Related ra ⟨[], env, mem⟩ b) :
    b.mem = mem ∧ b.regs .ra = ra ∧ b.pc = ra ∧ b.regs .a0 = env 9 := by
  rcases h with ⟨hm, hr, hf | ha | hrm⟩
  · exact ⟨hm, hr, hf.2⟩
  · cases ha.1
  · cases hrm.1

/-- Induction is on the terminating source derivation's execution length.
Each loop segment consumes a positive number of source transitions. There is
no fixed bound on the number of visits to either linked-list loop. -/
theorem simulate (n : Nat) (s final : Control.State Ctx) (b : WordMachine.State) (ra : Word)
    (hf : final.stack = []) (hs : Control.run n s = some final)
    (h : Related ra s b) (hram : SailLowering.InRAM s.mem) (hra : ra &&& 3 = 0) :
    Reaches b (Related ra final) := by
  induction n using Nat.strongRecOn generalizing s b with
  | ind n ih =>
    by_cases hn : s.stack = []
    · cases n with
      | zero => cases hs; exact reaches_done _ _ h
      | succ n => simp [Control.run, Control.step, hn] at hs
    · obtain ⟨k, t, hchunk, hk, hkn, _, _, hrest⟩ := Control.chunk_complete n s final hn hf hs
      obtain ⟨m, c, hbc, hc⟩ := related_chunk ra s b h hn hram hra k t hchunk
      have hram' : SailLowering.InRAM t.mem := by
        rw [← hc.1]
        exact WordMachine.run_ram program m b c hbc (by simpa only [h.1] using hram)
      obtain ⟨q, d, hcd, hd⟩ := ih (n - k) (by omega) t c hrest hc hram'
      exact ⟨m + q, d, by simp only [WordMachine.run_add, hbc, Option.bind_some, hcd], hd⟩

abbrev Params : Context := [.ptr State.name, .u64, .u64, .u64]

def args (p op pid work : Word) : Env Params :=
  fun i => match i.val with | 0 => p | 1 => op | 2 => pid | _ => work

theorem initial_args (p op pid work : Word) :
    initial («locals» := [.ptr Process.name, .ptr Process.name, .ptr Process.name, .ptr Process.name, .u64, .u64]) (args p op pid work) =
      values p op pid work 0 0 0 0 0 0 := by
  funext ⟨i, hi⟩
  change i < 10 at hi
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | n + 10 => omega

/-- The actual typed scheduler and the exact optimized word-level program
agree for every valid terminating source execution and every register input. -/
theorem word_refines (p op pid work value : Word) (mem mem' : Heap.Memory)
    (rs : WordMachine.Registers)
    (h0 : rs .a0 = p) (h1 : rs .a1 = op) (h2 : rs .a2 = pid) (h3 : rs .a3 = work)
    (hram : SailLowering.InRAM mem) (hra : rs .ra &&& 3 = 0)
    (source : Scheduler.step.Evaluates (args p op pid work) mem value mem') :
    ∃ n b, WordMachine.run program n ⟨0x80000000, rs, mem⟩ = some b ∧
      b.mem = mem' ∧ b.regs .ra = rs .ra ∧ b.pc = rs .ra ∧ b.regs .a0 = value := by
  obtain ⟨env, ⟨n, hn⟩, hv⟩ := Control.function_finishes Scheduler.step
    (args p op pid work) mem mem' value source
  have he : (⟨[Control.Frame.cmd Scheduler.step.body 1],
      initial (args p op pid work), mem⟩ : Control.State Ctx) = sourceEntry p op pid work mem := by
    rw [initial_args]; rfl
  rw [he] at hn
  obtain ⟨k, t, hchunk, _, _, _, _, hrest⟩ := Control.chunk_complete n
    (sourceEntry p op pid work mem) ⟨[], env, mem'⟩ (by simp [sourceEntry, entryStack]) rfl hn
  obtain ⟨m, b, hab, hb⟩ := entry_segment p op pid work mem rs h0 h1 h2 h3 hram hra k t hchunk
  have hram' : SailLowering.InRAM t.mem := by
    rw [← hb.1]
    exact WordMachine.run_ram program m _ b hab hram
  obtain ⟨q, c, hbc, hc⟩ := simulate (n - k) t ⟨[], env, mem'⟩ b (rs .ra) rfl hrest hb hram' hra
  have hreturn := related_return (rs .ra) env mem' c hc
  have hv' : env (9 : Fin Ctx.length) = value := Option.some.inj hv
  exact ⟨m + q, c, by simp only [WordMachine.run_add, hab, Option.bind_some, hbc],
    hreturn.1, hreturn.2.1, hreturn.2.2.1, hreturn.2.2.2.trans hv'⟩



open _root_.Sail.ConcurrencyInterfaceV1 RiscvSail

/-- Transfer the full scheduler proof to the generated Sail instruction
semantics. The source execution premise asserts defined behavior and
termination; it does not assume any property of the compiled program. -/
theorem refines (s : SailState) (rs : WordMachine.Registers)
    (mem mem' : Heap.Memory) (value : Word)
    (hm : WordMachine.Matches ⟨0x80000000, rs, mem⟩ s)
    (hram : SailLowering.InRAM mem) (hra : rs .ra &&& 3 = 0)
    (source : Scheduler.step.Evaluates
      (args (rs .a0) (rs .a1) (rs .a2) (rs .a3)) mem value mem') :
    ∃ n after, Lifted.run program.nodes n s = .ok () after ∧
      after.regs.get? .x10 = some value ∧ after.regs.get? .PC = some (rs .ra) ∧
      after.regs.get? .x1 = some (rs .ra) ∧ Binary.Memory.Represents mem' after ∧
      WordMachine.Frame mem s after := by
  obtain ⟨n, b, hr, hmem, hreturn, hpc, hvalue⟩ := word_refines
    (rs .a0) (rs .a1) (rs .a2) (rs .a3) value mem mem' rs rfl rfl rfl rfl hram hra source
  obtain ⟨after, hrun, hmatch, hframe⟩ := WordMachine.run_correct program program_valid
    n _ b s hm hr
  refine ⟨n, after, hrun, ?_, ?_, ?_, ?_, hframe⟩
  · simpa only [WordMachine.Reg.get, hvalue] using hmatch.2.2.2.1 .a0
  · simpa only [hpc] using hmatch.2.2.1
  · simpa only [WordMachine.Reg.get, hreturn] using hmatch.2.2.2.1 .ra
  · simpa only [hmem] using hmatch.2.2.2.2

/-- Both translations execute the actual Sail memory primitives and agree on
the returned value and every physical memory byte. Scratch registers and the
reference interpreter's control state are intentionally not observables. -/
theorem step_sail_equivalence (s : SailState) (rs : WordMachine.Registers)
    (mem mem' : Heap.Memory) (value : Word)
    (hm : WordMachine.Matches ⟨0x80000000, rs, mem⟩ s)
    (hram : SailLowering.InRAM mem) (hra : rs .ra &&& 3 = 0)
    (source : Scheduler.step.Evaluates
      (args (rs .a0) (rs .a1) (rs .a2) (rs .a3)) mem value mem') :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ n native reference,
      Lifted.run program.nodes n s = .ok () native ∧
      SailLowering.call Scheduler.step fuel
        (args (rs .a0) (rs .a1) (rs .a2) (rs .a3)) s = .ok value reference ∧
      native.regs.get? .x10 = some value ∧ native.regs.get? .PC = some (rs .ra) ∧
      native.regs.get? .x1 = some (rs .ra) ∧
      (∀ byte, native.mem.get? byte = reference.mem.get? byte) ∧
      WordMachine.Frame mem s native := by
  obtain ⟨n, native, hn, hv, hp, hr, hrep, hframe⟩ := refines s rs mem mem' value hm hram hra source
  obtain ⟨bound, hb⟩ := SailLowering.function_correct_all_fuel Scheduler.step
    (args (rs .a0) (rs .a1) (rs .a2) (rs .a3)) mem mem' value source
  refine ⟨bound, ?_⟩
  intro fuel hf
  obtain ⟨reference, he, _, href, _, hfr⟩ := hb fuel hf s hm.2.1 hram hm.2.2.2.2
  refine ⟨n, native, reference, hn, he, hv, hp, hr, ?_, hframe⟩
  obtain ⟨env, hexec, _⟩ := source
  exact SailLowering.memory_unique mem mem' s native reference
    (SailLowering.exec_domain hexec) hrep href hframe.1 hfr

def pre (s : SailState) : Prop :=
  ∃ mem rs value mem', WordMachine.Matches ⟨0x80000000, rs, mem⟩ s ∧
    SailLowering.InRAM mem ∧ rs .ra &&& 3 = 0 ∧
    Scheduler.step.Evaluates (args (rs .a0) (rs .a1) (rs .a2) (rs .a3)) mem value mem'

def post (before after : SailState) : Prop :=
  ∃ mem rs value mem', WordMachine.Matches ⟨0x80000000, rs, mem⟩ before ∧
    SailLowering.InRAM mem ∧
    Scheduler.step.Evaluates (args (rs .a0) (rs .a1) (rs .a2) (rs .a3)) mem value mem' ∧
    after.regs.get? .x10 = some value ∧ after.regs.get? .PC = some (rs .ra) ∧
    after.regs.get? .x1 = some (rs .ra) ∧ Binary.Memory.Represents mem' after ∧
    WordMachine.Frame mem before after

theorem ir_correct : Lifted.Hoare program.nodes pre post := by
  intro s hs
  obtain ⟨mem, rs, value, mem', hm, hram, hra, source⟩ := hs
  obtain ⟨n, after, hn, hv, hp, hr, hmem, hframe⟩ := refines s rs mem mem' value hm hram hra source
  exact ⟨n, after, hn, mem, rs, value, mem', hm, hram, source, hv, hp, hr, hmem, hframe⟩

def contract : Lifted.Contract := ⟨program.nodes, pre, post, ir_correct⟩

/-- The contract has a concrete configured input. Command zero returns the
DSL's invalid-command status without touching memory. -/
theorem pre_inhabited : ∃ s, pre s := by
  let rs : WordMachine.Registers := fun r => if r = .ra then 0x80000400 else 0
  let mem : Heap.Memory := fun _ => none
  let s : SailState :=
    Binary.SailProofs.setReg (Binary.SailProofs.setReg (Binary.SailProofs.setReg
    (Binary.SailProofs.setReg (Binary.SailProofs.setReg (Binary.SailProofs.setReg
    (Binary.SailProofs.setReg (Binary.SailProofs.setReg (Binary.SailProofs.setReg
    (Binary.SailProofs.setReg (Binary.SailProofs.setReg (Binary.SailProofs.setReg
    (Binary.SailProofs.setReg (Binary.SailProofs.setReg (Binary.SailProofs.setReg
    (Binary.SailProofs.setReg (Binary.SailProofs.setReg (Binary.SailProofs.setReg
      (default : SailState) .cur_privilege .Machine) .mseccfg 0)
      .misa 0x8000000000000100) .mstatus 0) .pma_regions [Binary.Memory.ram])
      .pmpcfg_n (Vector.replicate 64 0)) .pmpaddr_n (Vector.replicate 64 0)) .htif_tohost_base none)
      .PC 0x80000000) .x1 0x80000400) .x10 0) .x11 0) .x12 0) .x13 0)
      .x14 0) .x15 0) .x16 0) .x17 0
  have hm : WordMachine.Matches ⟨0x80000000, rs, mem⟩ s := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [s, Lifted.Config, Binary.SailProofs.setReg, Std.ExtDHashMap.get?_insert]
    · simp [s, Binary.Memory.Ready, Binary.SailProofs.setReg, Std.ExtDHashMap.get?_insert]
    · simp [s, Binary.SailProofs.setReg, Std.ExtDHashMap.get?_insert]
    · intro r
      cases r <;> simp [s, rs, WordMachine.Reg.get, Binary.SailProofs.setReg, Std.ExtDHashMap.get?_insert]
    · intro a v h; cases h
  refine ⟨s, mem, rs, 1, mem, hm, ?_, by decide, ?_⟩
  · intro a v h; cases h
  · change Scheduler.step.Evaluates (args 0 0 0 0) mem 1 mem
    refine ⟨(values 0 0 0 0 0 0 0 0 0 0).set 9 1, ?_, rfl⟩
    rw [initial_args]
    repeat first | apply Exec.seq | apply Exec.assign rfl | apply Exec.if_zero rfl | exact Exec.skip

end Riscvc.Heap.Scheduler.StepProof

/-- Module entry point used by the certificate that checks the decoded ELF. -/
def examples.proof.SchedulerStep.contract : Riscvc.Binary.Lifted.Contract :=
  Riscvc.Heap.Scheduler.StepProof.contract
