import Riscvc.Recursion
import Riscvc.Correctness

namespace Riscvc

/-- Structured control-flow IR. A call's contract restores the caller's slots,
    replacing only its destination. The assembly backend implements this with
    a stack frame; physical-memory refinement remains outside this IR proof. -/
inductive Control (arity : Nat) where
  | block (code : List Instr)
  | seq (first second : Control arity)
  | branch (condition : Nat) (yes no : Control arity)
  | call (dst : Nat) (arguments : Fin arity → Nat)

def Control.exec (self : Env arity → Word) : Control arity → RegisterState → RegisterState
  | .block code, state => runState code state
  | .seq first second, state => second.exec self (first.exec self state)
  | .branch cond yes no, state => if state.read cond = 0 then no.exec self state else yes.exec self state
  | .call dst arguments, state => ⟨state.read.write dst (self (fun i => state.read (arguments i)))⟩

def Control.run (self : Env arity → Word) (code : Control arity) (regs : Registers) : Registers :=
  (code.exec self ⟨regs⟩).read

theorem Control.run_seq (self : Env arity → Word) (first second : Control arity) (regs : Registers) :
    (Control.seq first second).run self regs = second.run self (first.run self regs) := rfl

theorem Control.run_branch (self : Env arity → Word) (cond : Nat)
    (yes no : Control arity) (regs : Registers) :
    (Control.branch cond yes no).run self regs =
      if regs cond = 0 then no.run self regs else yes.run self regs := by
  simp only [Control.run, Control.exec]
  split <;> rfl

/-- A function's tail positions end in a return or a jump to its own body.
    There is no caller continuation to preserve at a tail jump. -/
inductive Tail (arity : Nat) where
  | ret (code : Control arity) (result : Nat)
  | seq (code : Control arity) (next : Tail arity)
  | branch (condition : Nat) (yes no : Tail arity)
  | recur (arguments : Fin arity → Nat)

def Tail.exec (self : Env arity → Word) : Tail arity → RegisterState → Word
  | .ret code result, state => (code.exec self state).read result
  | .seq code next, state => next.exec self (code.exec self state)
  | .branch cond yes no, state => if state.read cond = 0 then no.exec self state else yes.exec self state
  | .recur arguments, state => self (fun i => state.read (arguments i))

def Tail.eval (self : Env arity → Word) (code : Tail arity) (regs : Registers) : Word :=
  code.exec self ⟨regs⟩

/-- Stage arguments left-to-right in distinct slots before changing ABI inputs. -/
def compileArgs : {arity : Nat} → (Fin arity → Expr n) → (Fin n → Nat) → Nat → List Instr
  | 0, _, _, _ => []
  | arity + 1, args, loc, dst =>
      compile (args 0) loc dst ++ compileArgs (fun i : Fin arity => args i.succ) loc (dst + 1)

def compileRec : RecExpr arity n → (Fin n → Nat) → Nat → Control arity
  | .pure e, loc, dst => .block (compile e loc dst)
  | .bin op lhs rhs, loc, dst =>
      .seq (compileRec lhs loc dst) (.seq (compileRec rhs loc (dst + 1))
        (.block [.alu op dst (.reg dst) (.reg (dst + 1))]))
  | .letE value body, loc, dst =>
      .seq (compileRec value loc dst) (.seq (compileRec body (extend loc dst) (dst + 1))
        (.block [.mov dst (dst + 1)]))
  | .ite cond yes no, loc, dst =>
      .seq (compileRec cond loc dst) (.branch dst (compileRec yes loc dst) (compileRec no loc dst))
  | .call args, loc, dst =>
      .seq (.block (compileArgs args loc dst)) (.call dst (fun i => dst + i.val))

/-- Tail position propagates through lets and selected branches, but not through
    arithmetic operands or conditions which still need their call's result. -/
def compileTail : RecExpr arity n → (Fin n → Nat) → Nat → Tail arity
  | .letE value body, loc, dst =>
      .seq (compileRec value loc dst) (compileTail body (extend loc dst) (dst + 1))
  | .ite cond yes no, loc, dst =>
      .seq (compileRec cond loc dst) (.branch dst (compileTail yes loc dst) (compileTail no loc dst))
  | .call args, loc, dst =>
      .seq (.block (compileArgs args loc dst)) (.recur (fun i => dst + i.val))
  | e, loc, dst => .ret (compileRec e loc dst) dst

def initialRegisters (args : Env arity) : Registers :=
  fun i => if h : i < arity then args ⟨i, h⟩ else 0

/-- Closed execution of the compiled recursive IR. Calls execute this same
    compiled function, including non-tail calls; the source evaluator is not used. -/
def RecFn.execute (f : RecFn arity) (args : Env arity) : Word :=
  (compileTail f.body Fin.val arity).eval
    (fun next => if f.measure next < f.measure args then f.execute next else 0)
    (initialRegisters args)
termination_by f.measure args

end Riscvc
