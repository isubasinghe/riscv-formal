import Riscvc.Language

namespace Riscvc

/-- Virtual register slots. The assembly backend checks that slots fit in the
    fifteen caller-saved RV64 registers before emitting any assembly. -/
abbrev Registers := Nat → Word

/-- Keep state transitions eager even though register reads are functions. -/
structure RegisterState where
  read : Registers

inductive Operand where
  | zero
  | reg (slot : Nat)
  deriving Repr, DecidableEq

def Operand.read : Operand → Registers → Word
  | .zero, _ => 0
  | .reg i, regs => regs i

def Registers.write (regs : Registers) (dst : Nat) (value : Word) : Registers :=
  fun i => if i = dst then value else regs i

@[simp] theorem Registers.write_same (regs : Registers) (dst : Nat) (value : Word) :
    regs.write dst value dst = value := by simp [Registers.write]

@[simp] theorem Registers.write_other (regs : Registers) (dst i : Nat) (value : Word)
    (h : i ≠ dst) : regs.write dst value i = regs i := by simp [Registers.write, h]

/-- `li` has assembler-pseudoinstruction semantics. Other operations correspond
    to individual RV64I register instructions. This is not the Sail ISA model. -/
inductive Instr where
  | li (dst : Nat) (value : Word)
  | alu (op : BinOp) (dst : Nat) (lhs rhs : Operand)
  deriving Repr

def Instr.mov (dst src : Nat) : Instr := .alu .add dst (.reg src) .zero

def Instr.exec : Instr → Registers → Registers
  | .li dst value, regs => regs.write dst value
  | .alu op dst lhs rhs, regs => regs.write dst (op.eval (lhs.read regs) (rhs.read regs))

def runState : List Instr → RegisterState → RegisterState
  | [], state => state
  | .li dst value :: rest, state => runState rest ⟨state.read.write dst value⟩
  | .alu op dst lhs rhs :: rest, state =>
      -- Return a state record so Lean does not eta-expand this interpreter into
      -- a register reader and repeat previous instructions on every read.
      let value := op.eval (lhs.read state.read) (rhs.read state.read)
      runState rest ⟨state.read.write dst value⟩

def run (code : List Instr) (regs : Registers) : Registers :=
  (runState code ⟨regs⟩).read

theorem runState_read (code : List Instr) (state : RegisterState) :
    (runState code state).read = run code state.read := rfl

@[simp] theorem run_nil (regs : Registers) : run [] regs = regs := rfl
@[simp] theorem run_cons (i : Instr) (code : List Instr) (regs : Registers) :
    run (i :: code) regs = run code (i.exec regs) := by cases i <;> rfl

@[simp] theorem run_append (a b : List Instr) (regs : Registers) :
    run (a ++ b) regs = run b (run a regs) := by
  induction a generalizing regs with
  | nil => rfl
  | cons i rest ih => simpa only [List.cons_append, run_cons] using ih (i.exec regs)

end Riscvc
