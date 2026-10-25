import Riscvc.Language

namespace Riscvc.Heap

/-- All supported fields occupy eight bytes on the 64-bit targets. Pointer
types are nominal: a pointer to one struct cannot access another's fields. -/
inductive Ty where
  | u64
  | ptr (name : String)
  deriving DecidableEq, Repr

structure Layout where
  name : String
  fields : List Ty
  deriving Repr

def Layout.size (layout : Layout) : Nat := 8 * layout.fields.length

structure Field (layout : Layout) (type : Ty) where
  index : Fin layout.fields.length
  typed : layout.fields[index] = type

abbrev Context := List Ty
abbrev Env (ctx : Context) := Fin ctx.length → Word

structure Var (ctx : Context) (type : Ty) where
  index : Fin ctx.length
  typed : ctx[index] = type

def Env.set (env : Env ctx) (i : Fin ctx.length) (value : Word) : Env ctx :=
  fun j => if j = i then value else env j

/-- A partial heap of aligned 8-byte cells, indexed by byte address. An absent
cell cannot be read or written. Allocation is supplied by the caller. -/
abbrev Memory := Nat → Option Word

def Memory.write (mem : Memory) (address : Nat) (value : Word) : Memory :=
  fun a => if a = address then some value else mem a

@[simp] theorem Memory.write_same (mem : Memory) (a : Nat) (v : Word) :
    mem.write a v a = some v := by simp [Memory.write]

@[simp] theorem Memory.write_other (mem : Memory) (a b : Nat) (v : Word) (h : b ≠ a) :
    mem.write a v b = mem b := by simp [Memory.write, h]

/-- No null dereference, unaligned access, or address wraparound. -/
def Accessible (base : Word) (offset : Nat) : Prop :=
  base ≠ 0 ∧ base.toNat % 8 = 0 ∧ base.toNat + offset + 8 ≤ 2^64

instance (p : Word) (n : Nat) : Decidable (Accessible p n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

inductive Expr (ctx : Context) : Ty → Type where
  | var : Var ctx type → Expr ctx type
  | word : Word → Expr ctx .u64
  | null : Expr ctx (.ptr name)
  | bin : BinOp → Expr ctx .u64 → Expr ctx .u64 → Expr ctx .u64
  | eq : Expr ctx type → Expr ctx type → Expr ctx .u64
  | field : Field layout type → Expr ctx (.ptr layout.name) → Expr ctx type
  | ite : Expr ctx condType → Expr ctx type → Expr ctx type → Expr ctx type

def Expr.eval (env : Env ctx) (mem : Memory) : Expr ctx type → Option Word
  | .var v => some (env v.index)
  | .word w => some w
  | .null => some 0
  | .bin op a b => do return op.eval (← a.eval env mem) (← b.eval env mem)
  | .eq a b => do return if (← a.eval env mem) = (← b.eval env mem) then 1 else 0
  | .field f p => do
      let base ← p.eval env mem
      if Accessible base (8 * f.index.val) then mem (base.toNat + 8 * f.index.val) else none
  | .ite condition yes no => do
      if (← condition.eval env mem) = 0 then no.eval env mem else yes.eval env mem

inductive Cmd (ctx : Context) where
  | skip
  | seq : Cmd ctx → Cmd ctx → Cmd ctx
  | assign : Var ctx type → Expr ctx type → Cmd ctx
  | store : Field layout type → Expr ctx (.ptr layout.name) → Expr ctx type → Cmd ctx
  | ite : Expr ctx type → Cmd ctx → Cmd ctx → Cmd ctx
  | while : Expr ctx type → Cmd ctx → Cmd ctx

/-- Big-step semantics has no unrolling bound. A derivation establishes both
termination and absence of invalid memory accesses along the executed path. -/
inductive Exec : Cmd ctx → Env ctx → Memory → Env ctx → Memory → Prop where
  | skip : Exec .skip env mem env mem
  | seq : Exec a env mem mid mem' → Exec b mid mem' final mem'' →
      Exec (.seq a b) env mem final mem''
  | assign (h : value.eval env mem = some v) :
      Exec (.assign dst value) env mem (env.set dst.index v) mem
  | store (hp : ptr.eval env mem = some p) (hv : value.eval env mem = some v)
      (ha : Accessible p (8 * field.index.val))
      (mapped : mem (p.toNat + 8 * field.index.val) = some old) :
      Exec (.store field ptr value) env mem env (mem.write (p.toNat + 8 * field.index.val) v)
  | if_zero (hc : condition.eval env mem = some 0) (h : Exec no env mem final mem') :
      Exec (.ite condition yes no) env mem final mem'
  | if_nonzero (hc : condition.eval env mem = some v) (hv : v ≠ 0)
      (h : Exec yes env mem final mem') : Exec (.ite condition yes no) env mem final mem'
  | while_zero (hc : condition.eval env mem = some 0) : Exec (.while condition body) env mem env mem
  | while_nonzero (hc : condition.eval env mem = some v) (hv : v ≠ 0)
      (first : Exec body env mem mid mem')
      (rest : Exec (.while condition body) mid mem' final mem'') :
      Exec (.while condition body) env mem final mem''

inductive Error where
  | fuelExhausted
  | invalidAccess
  deriving Repr, DecidableEq

/-- Executable interpreter for testing. Fuel is a recursion-depth bound in this
interpreter only; it is absent from the language and generated machine code. -/
def Cmd.run : Nat → Cmd ctx → Env ctx → Memory → Except Error (Env ctx × Memory)
  | 0, _, _, _ => .error .fuelExhausted
  | fuel + 1, cmd, env, mem => do
    match cmd with
    | .skip => return (env, mem)
    | .seq a b =>
        let (mid, mem') ← a.run fuel env mem
        b.run fuel mid mem'
    | .assign dst value =>
        let some v := value.eval env mem | throw .invalidAccess
        return (env.set dst.index v, mem)
    | .store field ptr value =>
        let some p := ptr.eval env mem | throw .invalidAccess
        let some v := value.eval env mem | throw .invalidAccess
        if !decide (Accessible p (8 * field.index.val)) then throw .invalidAccess
        let address := p.toNat + 8 * field.index.val
        let some _ := mem address | throw .invalidAccess
        return (env, mem.write address v)
    | .ite condition yes no =>
        let some v := condition.eval env mem | throw .invalidAccess
        (if v = 0 then no else yes).run fuel env mem
    | .while condition body =>
        let some v := condition.eval env mem | throw .invalidAccess
        if v = 0 then return (env, mem)
        let (mid, mem') ← body.run fuel env mem
        (Cmd.while condition body).run fuel mid mem'

structure Function (params locals : Context) (result : Ty) where
  body : Cmd (params ++ locals)
  returns : Expr (params ++ locals) result

def initial (args : Env params) : Env (params ++ locals) :=
  fun i => if h : i.val < params.length then args ⟨i.val, h⟩ else 0

def Function.Evaluates (fn : Function params locals result)
    (args : Env params) (before : Memory) (value : Word) (after : Memory) : Prop :=
  ∃ final, Exec fn.body (initial args) before final after ∧ fn.returns.eval final after = some value

def Function.run (fn : Function params locals result) (fuel : Nat)
    (args : Env params) (before : Memory) : Except Error (Word × Memory) := do
  let (final, after) ← fn.body.run fuel (initial args) before
  let some value := fn.returns.eval final after | throw .invalidAccess
  return (value, after)

end Riscvc.Heap
