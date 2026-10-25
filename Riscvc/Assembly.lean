import Riscvc.Compiler

namespace Riscvc

/-- Inputs occupy a0..a7 in order. Everything in this pool is caller-saved. -/
def registerNames : Array String :=
  #["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4", "t5", "t6"]

def registerName (slot : Nat) : Except String String :=
  match registerNames[slot]? with
  | some name => .ok name
  | none => .error s!"register pressure exceeds {registerNames.size} caller-saved registers (slot {slot}); stack spilling is not implemented"

private def operandName : Operand → Except String String
  | .zero => .ok "zero"
  | .reg slot => registerName slot

def BinOp.mnemonic : BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .band => "and"
  | .bor => "or"
  | .bxor => "xor"
  | .shl => "sll"
  | .shr => "srl"
  | .ltu => "sltu"

def emitInstr : Instr → Except String String
  | .li dst value => do
      return s!"  li {← registerName dst}, {value.toInt}"
  | .alu op dst lhs rhs => do
      return s!"  {op.mnemonic} {← registerName dst}, {← operandName lhs}, {← operandName rhs}"

def validSymbol (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      (first.isAlpha && first.toNat < 128 || first == '_') &&
        rest.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))

/-- Emit a callable RV64I leaf function. The checked backend is deliberately
    fallible: unsupported arity/register pressure never produces partial code. -/
def emitAssembly (name : String) (e : Expr n) : Except String String := do
  if !validSymbol name then throw "invalid assembly symbol (use ASCII letters, digits, and underscores; no initial digit)"
  if n > 8 then throw "the RV64 calling convention backend supports at most eight arguments"
  let body ← (compileFunction e).mapM emitInstr
  let result ← registerName n
  let returnMove := if n = 0 then [] else [s!"  add a0, {result}, zero"]
  return String.intercalate "\n" (
    [".option norvc", ".option norelax", ".text", ".balign 4",
     s!".globl {name}", s!".type {name}, @function", s!"{name}:"] ++
    body ++ returnMove ++ ["  jalr zero, 0(ra)", s!".size {name}, .-{name}", ""])

end Riscvc
