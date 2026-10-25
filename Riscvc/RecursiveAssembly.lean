import Riscvc.Control
import Riscvc.Assembly

namespace Riscvc

/-- Fifteen saved virtual slots plus the function's incoming return address.
    The frame remains 16-byte aligned at every ordinary call. -/
def recursiveFrameSize : Nat := 128

private abbrev EmitM := StateT Nat (Except String)

private def freshLabel (name : String) : EmitM String := do
  let n ← get
  set (n + 1)
  return s!".L{name}_{n}"

private def savedSlots : List Nat := List.range registerNames.size

private def emitCall (name : String) (dst : Nat) (args : Fin arity → Nat) : EmitM (List String) := do
  let _ ← registerName dst
  let mut lines := []
  for i in savedSlots do
    lines := lines ++ [s!"  sd {← registerName i}, {8 * i}(sp)"]
  -- Read all arguments from the saved snapshot: ABI argument permutations must
  -- not overwrite values that a later argument still needs.
  for i in List.finRange arity do
    let _ ← registerName (args i)
    lines := lines ++ [s!"  ld a{i.val}, {8 * args i}(sp)"]
  lines := lines ++ [s!"  call {name}", s!"  sd a0, {8 * dst}(sp)"]
  for i in savedSlots do
    lines := lines ++ [s!"  ld {← registerName i}, {8 * i}(sp)"]
  return lines

private def emitControl (name : String) : Control arity → EmitM (List String)
  | .block code => code.mapM (fun i => do return ← emitInstr i)
  | .seq first second => do return (← emitControl name first) ++ (← emitControl name second)
  | .call dst args => emitCall name dst args
  | .branch cond yes no => do
      let yesLabel ← freshLabel name
      let noLabel ← freshLabel name
      let doneLabel ← freshLabel name
      let reg ← registerName cond
      return [s!"  bne {reg}, zero, {yesLabel}", s!"  j {noLabel}", s!"{yesLabel}:"] ++
        (← emitControl name yes) ++ [s!"  j {doneLabel}", s!"{noLabel}:"] ++
        (← emitControl name no) ++ [s!"{doneLabel}:"]

private def emitTail (name : String) : Tail arity → EmitM (List String)
  | .ret code dst => do
      return (← emitControl name code) ++ [s!"  add a0, {← registerName dst}, zero",
        "  ld ra, 120(sp)", s!"  addi sp, sp, {recursiveFrameSize}", "  jalr zero, 0(ra)"]
  | .seq code next => do return (← emitControl name code) ++ (← emitTail name next)
  | .branch cond yes no => do
      let yesLabel ← freshLabel name
      let noLabel ← freshLabel name
      let reg ← registerName cond
      return [s!"  bne {reg}, zero, {yesLabel}", s!"  j {noLabel}", s!"{yesLabel}:"] ++
        (← emitTail name yes) ++ [s!"{noLabel}:"] ++ (← emitTail name no)
  | .recur args => do
      let mut lines := []
      for i in List.finRange arity do
        lines := lines ++ [s!"  sd {← registerName (args i)}, {8 * i.val}(sp)"]
      for i in List.finRange arity do
        lines := lines ++ [s!"  ld a{i.val}, {8 * i.val}(sp)"]
      return lines ++ [s!"  j .L{name}_body"]

/-- Emit a certified self-recursive RV64I function. Termination proofs and
    measures are erased; tail jumps reuse the existing 128-byte frame. -/
def emitRecursiveAssembly (name : String) (f : RecFn arity) : Except String String := do
  if !validSymbol name then throw "invalid assembly symbol"
  if arity > 8 then throw "the RV64 calling convention backend supports at most eight arguments"
  let (body, _) ← (emitTail name (compileTail f.body Fin.val arity)).run 0
  -- Conditional branches only cross the immediately following jump. Bound the
  -- function size conservatively so every remaining `j` fits its signed offset,
  -- even after full-width `li` pseudoinstructions are expanded.
  if body.length > 16384 then throw "recursive function exceeds the supported branch-layout size (16384 assembly lines)"
  return String.intercalate "\n" ([".option norvc", ".option norelax", ".text", ".balign 4",
    s!".globl {name}", s!".type {name}, @function", s!"{name}:",
    s!"  addi sp, sp, -{recursiveFrameSize}", "  sd ra, 120(sp)", s!".L{name}_body:"] ++
    body ++ [s!".size {name}, .-{name}", ""])

end Riscvc
