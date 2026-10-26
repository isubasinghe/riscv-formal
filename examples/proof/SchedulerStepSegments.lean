import examples.proof.SchedulerStepTactics
namespace Riscvc.Heap.Scheduler.StepProof
open Riscvc.Binary
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem add_segment (p pid work cur dup : Word) (mem : Heap.Memory) (rs : WordMachine.Registers)
    (hp : pid ≠ 0) (hw : work ≠ 0) (_hc : cur ≠ 0) (hd : dup = 0 ∨ dup = 1)
    (h0 : rs .a0 = p) (h1 : rs .a1 = 1) (h2 : rs .a2 = pid)
    (h3 : rs .a3 = work) (h4 : rs .a4 = cur) (h6 : rs .a6 = dup)
    (hram : SailLowering.InRAM mem) (hra : rs .ra &&& 3 = 0)
    (k : Nat) (t : Control.State Ctx)
    (h : Control.chunk (sourceAdd p pid work cur dup mem) = some (k,t)) :
    Reaches ⟨0x8000003c, rs, mem⟩ (Related (rs .ra) t) := by
  source_cases h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals memory_facts
  all_goals try normalize_memory
  machine_run
theorem remove_first_segment (p pid work cur : Word) (mem : Heap.Memory) (rs : WordMachine.Registers)
    (hc : cur ≠ 0)
    (h0 : rs .a0 = p) (h1 : rs .a1 = 2) (h2 : rs .a2 = pid)
    (h3 : rs .a3 = cur)
    (hram : SailLowering.InRAM mem) (hra : rs .ra &&& 3 = 0)
    (k : Nat) (t : Control.State Ctx)
    (h : Control.chunk (sourceRemove p pid work cur 0 mem) = some (k,t)) :
    Reaches ⟨0x800000ac, rs, mem⟩ (Related (rs .ra) t) := by
  source_cases h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals memory_facts
  all_goals try normalize_memory
  machine_run
theorem remove_next_segment (p pid work cur prev : Word) (mem : Heap.Memory) (rs : WordMachine.Registers)
    (hc : cur ≠ 0) (_hp : prev ≠ 0)
    (h0 : rs .a0 = p) (h1 : rs .a1 = 2) (h2 : rs .a2 = pid)
    (h3 : rs .a3 = cur) (h5 : rs .a5 = prev)
    (hram : SailLowering.InRAM mem) (hra : rs .ra &&& 3 = 0)
    (k : Nat) (t : Control.State Ctx)
    (h : Control.chunk (sourceRemove p pid work cur prev mem) = some (k,t)) :
    Reaches ⟨0x800000d0, rs, mem⟩ (Related (rs .ra) t) := by
  source_cases h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals memory_facts
  all_goals try normalize_memory
  machine_run

set_option maxHeartbeats 64000000 in
theorem entry_segment (p op pid work : Word) (mem : Heap.Memory) (rs : WordMachine.Registers)
    (h0 : rs .a0 = p) (h1 : rs .a1 = op) (h2 : rs .a2 = pid) (h3 : rs .a3 = work)
    (hram : SailLowering.InRAM mem) (hra : rs .ra &&& 3 = 0)
    (k : Nat) (t : Control.State Ctx)
    (h : Control.chunk (sourceEntry p op pid work mem) = some (k,t)) :
    Reaches ⟨0x80000000, rs, mem⟩ (Related (rs .ra) t) := by
  source_cases h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals memory_facts
  all_goals try normalize_memory
  machine_run

end Riscvc.Heap.Scheduler.StepProof
