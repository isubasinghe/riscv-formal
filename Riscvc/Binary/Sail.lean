import RiscvSail.InstsEnd
import Riscvc.Binary.ELF

/-! Instruction execution uses the generated Sail decoder and execute function.
This is an instruction-level harness with immutable executable text. The caller
supplies a valid mapped text image; MMU translation and interrupt delivery are
outside this harness. No instruction semantics are reimplemented here.
-/
namespace Riscvc.Binary

open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions

abbrev SailState := SequentialState RegisterType trivialChoiceSource

/-- The executable text image agrees with the bytes loaded in Sail memory. -/
def TextLoaded (image : ELF.Image) (state : SailState) : Prop :=
  ∀ address byte, image.fetchByte address = some byte →
    state.mem.get? address = some (BitVec.ofNat 8 byte.toNat)

noncomputable def step (image : ELF.Image) : SailM Unit := do
  let pc ← readReg Register.PC
  let some word := image.fetchWord pc.toNat
    | throw (.Assertion "Instruction fetch outside executable text")
  set_next_pc (pc + 4)
  let instruction ← encdec_backwards word
  match ← execute instruction with
  | .Retire_Success () => tick_pc ()
  | _ => throw (.Assertion "Instruction did not retire successfully")

noncomputable def run (image : ELF.Image) : Nat → SailM Unit
  | 0 => pure ()
  | n + 1 => step image *> run image n

end Riscvc.Binary
