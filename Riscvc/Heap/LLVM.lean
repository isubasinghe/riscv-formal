import Riscvc.Heap.Language
import Riscvc.Assembly

namespace Riscvc.Heap.LLVM

private def typeName : Ty → String
  | .u64 => "i64"
  | .ptr _ => "ptr"

private def zero : Ty → String
  | .u64 => "0"
  | .ptr _ => "null"

private structure EmitState where
  next : Nat := 0
  block : String := "entry"
  lines : Array String := #[]

private abbrev EmitM := StateM EmitState

private def line (s : String) : EmitM Unit := modify fun st => { st with lines := st.lines.push s }

private def fresh (stem : String) : EmitM String := do
  let n := (← get).next
  modify fun st => { st with next := n + 1 }
  return s!"{stem}{n}"

private def value (rhs : String) : EmitM String := do
  let v ← fresh "v"
  line s!"  %{v} = {rhs}"
  return s!"%{v}"

private def block (label : String) : EmitM Unit := do
  line s!"{label}:"
  modify fun st => { st with block := label }

private def nonzero (type : Ty) (v : String) : EmitM String :=
  value s!"icmp ne {typeName type} {v}, {zero type}"

private def address (base : String) (index : Nat) : EmitM String :=
  -- No inbounds assertion: safety is a program precondition, not an unchecked
  -- promise about intermediate addresses made by the renderer.
  value s!"getelementptr i8, ptr {base}, i64 {8 * index}"

private def expr : {type : Ty} → Expr ctx type → EmitM String
  | type, .var v => value s!"load {typeName type}, ptr %slot{v.index.val}, align 8"
  | _, .word w => pure (toString w.toInt)
  | _, .null => pure "null"
  | _, .bin op a b => do
      let x ← expr a
      let y ← expr b
      match op with
      | .ltu =>
          let c ← value s!"icmp ult i64 {x}, {y}"
          value s!"zext i1 {c} to i64"
      | .shl | .shr =>
          let y ← value s!"and i64 {y}, 63"
          value s!"{if op == .shl then "shl" else "lshr"} i64 {x}, {y}"
      | _ =>
          let mnemonic := match op with
            | .add => "add" | .sub => "sub" | .band => "and" | .bor => "or" | _ => "xor"
          value s!"{mnemonic} i64 {x}, {y}"
  | _, @Expr.eq _ type a b => do
      let x ← expr a
      let y ← expr b
      let c ← value s!"icmp eq {typeName type} {x}, {y}"
      value s!"zext i1 {c} to i64"
  | type, .field f p => do
      let p ← expr p
      let p ← address p f.index.val
      value s!"load {typeName type}, ptr {p}, align 8"
  | type, @Expr.ite _ condType _ condition yes no => do
      let c ← expr condition
      let c ← nonzero condType c
      let yesLabel ← fresh "yes"
      let noLabel ← fresh "no"
      let endLabel ← fresh "join"
      line s!"  br i1 {c}, label %{yesLabel}, label %{noLabel}"
      block yesLabel
      let y ← expr yes
      let ye := (← get).block
      line s!"  br label %{endLabel}"
      block noLabel
      let n ← expr no
      let ne := (← get).block
      line s!"  br label %{endLabel}"
      block endLabel
      value s!"phi {typeName type} [ {y}, %{ye} ], [ {n}, %{ne} ]"

private def command : Cmd ctx → EmitM Unit
  | .skip => pure ()
  | .seq a b => command a *> command b
  | @Cmd.assign _ type dst e => do
      let v ← expr e
      line s!"  store {typeName type} {v}, ptr %slot{dst.index.val}, align 8"
  | @Cmd.store _ _ type f p e => do
      let p ← expr p
      let v ← expr e
      let p ← address p f.index.val
      line s!"  store {typeName type} {v}, ptr {p}, align 8"
  | @Cmd.ite _ type condition yes no => do
      let c ← expr condition
      let c ← nonzero type c
      let y ← fresh "then"
      let n ← fresh "else"
      let doneLabel ← fresh "done"
      line s!"  br i1 {c}, label %{y}, label %{n}"
      block y
      command yes
      line s!"  br label %{doneLabel}"
      block n
      command no
      line s!"  br label %{doneLabel}"
      block doneLabel
  | @Cmd.while _ type condition body => do
      let check ← fresh "check"
      let loopLabel ← fresh "loop"
      let doneLabel ← fresh "done"
      line s!"  br label %{check}"
      block check
      let c ← expr condition
      let c ← nonzero type c
      line s!"  br i1 {c}, label %{loopLabel}, label %{doneLabel}"
      block loopLabel
      command body
      line s!"  br label %{check}"
      block doneLabel

/-- Lower typed heap programs to LLVM on 64-bit targets. Local variables are
promoted by LLVM's mem2reg/SROA passes. Program proofs must establish valid,
aligned accesses; this renderer is not a proved LLVM semantic translation. -/
def emit (name : String) (fn : Function params localTypes result) : Except String String := do
  if !validSymbol name then throw "invalid LLVM symbol"
  let args := params.zipIdx |>.map fun (t, i) => s!"{typeName t} %arg{i}"
  let action : EmitM Unit := do
    for (type, i) in (params ++ localTypes).zipIdx do
      line s!"  %slot{i} = alloca {typeName type}, align 8"
      let v := if i < params.length then s!"%arg{i}" else zero type
      line s!"  store {typeName type} {v}, ptr %slot{i}, align 8"
    command fn.body
    let v ← expr fn.returns
    line s!"  ret {typeName result} {v}"
  let (_, state) := action.run {}
  return String.intercalate "\n" (
    ["; Heap DSL: 64-bit words and pointers, 8-byte fields.",
     s!"define {typeName result} @{name}({String.intercalate ", " args}) \{", "entry:"] ++
    state.lines.toList ++ ["}", ""])

end Riscvc.Heap.LLVM
