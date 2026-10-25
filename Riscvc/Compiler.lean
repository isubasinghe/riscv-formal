import Riscvc.Machine

namespace Riscvc

/-- A nonzero condition becomes an all-ones mask. Both arms are pure and total,
    so selecting with XOR/AND preserves the source conditional's meaning. -/
def selectCode (dst : Nat) : List Instr := [
  .alu .ltu dst .zero (.reg dst),
  .alu .sub dst .zero (.reg dst),
  .alu .bxor (dst + 1) (.reg (dst + 1)) (.reg (dst + 2)),
  .alu .band (dst + 1) (.reg (dst + 1)) (.reg dst),
  .alu .bxor dst (.reg (dst + 2)) (.reg (dst + 1))
]

/-- Compile into `dst`, using slots above it as scratch and preserving all
    slots below it. Locals are mapped explicitly to their register slots. -/
def compile : Expr n → (Fin n → Nat) → Nat → List Instr
  | .var i, loc, dst => [.mov dst (loc i)]
  | .lit v, _, dst => [.li dst v]
  | .bin op lhs rhs, loc, dst =>
      compile lhs loc dst ++ compile rhs loc (dst + 1) ++
        [.alu op dst (.reg dst) (.reg (dst + 1))]
  | .letE value body, loc, dst =>
      compile value loc dst ++ compile body (extend loc dst) (dst + 1) ++
        [.mov dst (dst + 1)]
  | .ite cond yes no, loc, dst =>
      compile cond loc dst ++ compile yes loc (dst + 1) ++
        compile no loc (dst + 2) ++ selectCode dst

def compileFunction (e : Expr n) : List Instr := compile e Fin.val n

/-- The modeled result is in slot `n`; the ABI return move is added by the
    assembly backend. The initial scratch registers can contain any values. -/
def execute (e : Expr n) (args : Env n) : Word :=
  let regs : Registers := fun i => if h : i < n then args ⟨i, h⟩ else 0
  run (compileFunction e) regs n

end Riscvc
