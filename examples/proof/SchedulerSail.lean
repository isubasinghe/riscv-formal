import examples.Scheduler
import Riscvc.Heap.SailLowering

/-! Reference source-to-Sail theorems for the actual scheduler DSL. These prove
the source lowering, including arbitrary finite traversals of both linked-list
loops. They do not assert equivalence with LLVM's optimized instruction stream;
that additional binary obligation is separate from this reference lowering.
-/
namespace Riscvc.Heap.Scheduler.SailProof

open Riscvc.Binary Riscvc.Binary.Memory SailLowering
open _root_.Sail.ConcurrencyInterfaceV1

abbrev InitArgs := Env [.ptr State.name, .ptr Process.name]
abbrev StepArgs := Env [.ptr State.name, .u64, .u64, .u64]

theorem init_source_to_sail (args : InitArgs) (before after : Heap.Memory) (result : Word)
    (source : init.Evaluates args before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ s : SailState,
      Ready s → InRAM before → Represents before s →
      ∃ t, call init fuel args s = .ok result t ∧
        Ready t ∧ Represents after t ∧ t.regs = s.regs ∧ Frame before s t :=
  function_correct_all_fuel init args before after result source

/-- Includes add, remove, tick, all error returns, and both traversal loops.
No fixed capacity, command value, PID, work count, or loop bound is assumed.
As for the source semantics, an execution premise establishes termination and
valid accesses; the RAM/platform premises make the target setup explicit. -/
theorem step_source_to_sail (args : StepArgs) (before after : Heap.Memory) (result : Word)
    (source : step.Evaluates args before result after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ s : SailState,
      Ready s → InRAM before → Represents before s →
      ∃ t, call step fuel args s = .ok result t ∧
        Ready t ∧ Represents after t ∧ t.regs = s.regs ∧ Frame before s t :=
  function_correct_all_fuel step args before after result source

end Riscvc.Heap.Scheduler.SailProof
