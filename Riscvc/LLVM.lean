import Riscvc.Control
import Riscvc.Assembly

namespace Riscvc.LLVM

/- Lower the existing, proved register/control IR into LLVM SSA. Virtual slots
   become SSA values, with phi nodes at branch joins. Physical registers, frame
   layout, and instruction selection belong to LLVM's selected target backend.

   This renderer is tested against LLVM and Sail; it is not yet covered by a
   semantic-preservation theorem relating our IR to LLVM's semantics. -/

private structure EmitState where
  next : Nat := 0
  block : String := "body"
  lines : Array String := #[]
  backEdges : Array (String × Array String) := #[]

private abbrev EmitM := StateM EmitState
private abbrev Slots := Array String

private def line (text : String) : EmitM Unit :=
  modify fun s => { s with lines := s.lines.push text }

private def fresh (stem : String) : EmitM String := do
  let s ← get
  set { s with next := s.next + 1 }
  return s!"{stem}{s.next}"

private def value (rhs : String) : EmitM String := do
  let name ← fresh "v"
  line s!"  %{name} = {rhs}"
  return s!"%{name}"

private def beginBlock (label : String) : EmitM Unit := do
  modify fun s => { s with block := label }
  line s!"{label}:"

private def Slots.read (slots : Slots) (i : Nat) : String := slots[i]?.getD "0"

private def Slots.write (slots : Slots) (i : Nat) (v : String) : Slots :=
  let slots := slots ++ Array.replicate (i + 1 - slots.size) "0"
  slots.set! i v

private def operand (slots : Slots) : Operand → String
  | .zero => "0"
  | .reg i => slots.read i

private def binary (op : BinOp) (lhs rhs : String) : EmitM String := do
  match op with
  | .add => value s!"add i64 {lhs}, {rhs}"
  | .sub => value s!"sub i64 {lhs}, {rhs}"
  | .band => value s!"and i64 {lhs}, {rhs}"
  | .bor => value s!"or i64 {lhs}, {rhs}"
  | .bxor => value s!"xor i64 {lhs}, {rhs}"
  | .shl | .shr =>
      -- LLVM shifts by >= 64 produce poison. The DSL masks the count, and its
      -- modular arithmetic must not be annotated with nsw/nuw/exact flags.
      let count ← value s!"and i64 {rhs}, 63"
      let mnemonic := if op == .shl then "shl" else "lshr"
      value s!"{mnemonic} i64 {lhs}, {count}"
  | .ltu =>
      let cond ← value s!"icmp ult i64 {lhs}, {rhs}"
      value s!"zext i1 {cond} to i64"

private def instructions (code : List Instr) (slots : Slots) : EmitM Slots := do
  let mut slots := slots
  for instr in code do
    match instr with
    | .li dst v => slots := slots.write dst (toString v.toInt)
    | .alu op dst lhs rhs =>
        let result ← binary op (operand slots lhs) (operand slots rhs)
        slots := slots.write dst result
  return slots

private def arguments (slots : Slots) (args : Fin arity → Nat) : String :=
  String.intercalate ", " ((List.finRange arity).map fun i => s!"i64 {slots.read (args i)}")

private def merge (yes no : Slots) (yesBlock noBlock : String) : EmitM Slots := do
  let mut slots := #[]
  for i in [:max yes.size no.size] do
    let a := yes.read i
    let b := no.read i
    let v ← if a == b then pure a else
      value s!"phi i64 [ {a}, %{yesBlock} ], [ {b}, %{noBlock} ]"
    slots := slots.push v
  return slots

private def control (name : String) : Control arity → Slots → EmitM Slots
  | .block code, slots => instructions code slots
  | .seq first second, slots => do
      let next ← control name first slots
      control name second next
  | .call dst args, slots => do
      let result ← value s!"call i64 @{name}({arguments slots args})"
      return slots.write dst result
  | .branch cond yes no, slots => do
      let yesLabel ← fresh "bb"
      let noLabel ← fresh "bb"
      let doneLabel ← fresh "bb"
      let test ← value s!"icmp ne i64 {slots.read cond}, 0"
      line s!"  br i1 {test}, label %{yesLabel}, label %{noLabel}"
      beginBlock yesLabel
      let yesSlots ← control name yes slots
      let yesEnd := (← get).block
      line s!"  br label %{doneLabel}"
      beginBlock noLabel
      let noSlots ← control name no slots
      let noEnd := (← get).block
      line s!"  br label %{doneLabel}"
      beginBlock doneLabel
      merge yesSlots noSlots yesEnd noEnd

private def tail (name : String) : Tail arity → Slots → EmitM Unit
  | .ret code dst, slots => do
      let result ← control name code slots
      line s!"  ret i64 {result.read dst}"
  | .seq code next, slots => do
      let slots ← control name code slots
      tail name next slots
  | .branch cond yes no, slots => do
      let yesLabel ← fresh "bb"
      let noLabel ← fresh "bb"
      let test ← value s!"icmp ne i64 {slots.read cond}, 0"
      line s!"  br i1 {test}, label %{yesLabel}, label %{noLabel}"
      beginBlock yesLabel
      tail name yes slots
      beginBlock noLabel
      tail name no slots
  | .recur args, slots => do
      -- Record simultaneous incoming arguments for the loop header's phi nodes.
      -- An explicit back edge works even when the target cannot implement an
      -- ABI tail call with stack-passed arguments, and needs no optimiser pass.
      let values := ((List.finRange arity).map fun i => slots.read (args i)).toArray
      modify fun s => { s with backEdges := s.backEdges.push (s.block, values) }
      line "  br label %body"

private def function (name : String) (code : Tail arity) : Except String String := do
  if !validSymbol name then throw "invalid LLVM symbol (use ASCII letters, digits, and underscores; no initial digit)"
  let args := (List.range arity).map fun i => s!"i64 %arg{i}"
  let slots := ((List.range arity).map fun i => s!"%param{i}").toArray
  let (_, state) := (tail name code slots).run {}
  let header := (List.range arity).map fun i =>
    let incoming := [s!"[ %arg{i}, %entry ]"] ++
      state.backEdges.toList.map (fun (block, values) => s!"[ {values[i]!}, %{block} ]")
    s!"  %param{i} = phi i64 {String.intercalate ", " incoming}"
  return String.intercalate "\n" (
    [s!"define i64 @{name}({String.intercalate ", " args}) \{", "entry:",
      "  br label %body", "body:"] ++ header ++ state.lines.toList ++ ["}", ""])

/-- Emit a target-independent LLVM function, without a physical-register or
    eight-argument limit. Concatenate definitions to form a module. -/
def emit (name : String) (e : Expr n) : Except String String :=
  function name (Tail.ret (arity := n) (.block (compileFunction e)) n)

/-- Emit a certified recursive function using LLVM calls and explicit tail loops.
    Termination measures and proofs are not emitted. -/
def emitRecursive (name : String) (f : RecFn arity) : Except String String :=
  function name (compileTail f.body Fin.val arity)

end Riscvc.LLVM
