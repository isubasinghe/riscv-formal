import Riscvc.Syntax
import Riscvc.Recursion

namespace Riscvc

private theorem termination_branch {p yes no : Prop} [Decidable p]
    (hyes : p → yes) (hno : ¬p → no) : if p then yes else no := by
  split
  · exact hyes ‹p›
  · exact hno ‹¬p›

/-- Automation for guarded countdown recursion. More involved measures can use
    an explicit `decreasing_by` proof or the `RecFn` structure directly. -/
macro "word_decreasing" : tactic => `(tactic|
  (intro self args
   simp only [RecExpr.CallsBelow, RecExpr.eval, Expr.eval, BinOp.eval,
     extend_zero, extend_succ, true_and, and_true, ite_self]
   repeat' first
     | exact True.intro
     | apply And.intro
     | (apply termination_branch <;> intro)
     | exact word_pred_decreases _ (by assumption)
     | assumption
     | omega))

syntax "[riscv_rec| " "fun " ident ident* " => " rvExpr "]" : term
syntax "[riscv_rec| " "fun " ident ident* " => " rvExpr
  " termination_by " ident "]" : term
syntax "[riscv_rec| " "fun " ident ident* " => " rvExpr
  " termination_by " ident " decreasing_by " tacticSeq "]" : term

open Lean Elab Term in
private partial def quoteRecursive (self : Name) (arity : Nat) (names : List Name)
    (stx : Syntax) : TermElabM (TSyntax `term) := do
  match stx with
  | `(rvExpr| $callee:ident($args:rvExpr,*)) =>
      if callee.getId != self then throwErrorAt callee "only self-recursion is supported; expected '{self}'"
      if args.getElems.size != arity then
        throwErrorAt stx "recursive call expects {arity} arguments, got {args.getElems.size}"
      let mut values ← `(Fin.elim0)
      for arg in args.getElems.toList.reverse do
        values ← `(Riscvc.extend $values $(← quoteExpr names arg))
      `(Riscvc.RecExpr.call $values)
  | `(rvExpr| ($e:rvExpr)) => quoteRecursive self arity names e
  | `(rvExpr| let $v:ident := $a:rvExpr; $b:rvExpr) =>
      if v.getId == self then throwErrorAt v "the recursive function name cannot be shadowed"
      `(Riscvc.RecExpr.letE $(← quoteRecursive self arity names a)
        $(← quoteRecursive self arity (v.getId :: names) b))
  | `(rvExpr| if $c:rvExpr then $t:rvExpr else $f:rvExpr) =>
      `(Riscvc.RecExpr.ite $(← quoteRecursive self arity names c)
        $(← quoteRecursive self arity names t) $(← quoteRecursive self arity names f))
  | `(rvExpr| $a:rvExpr + $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .add $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | `(rvExpr| $a:rvExpr - $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .sub $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | `(rvExpr| $a:rvExpr & $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .band $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | `(rvExpr| $a:rvExpr | $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .bor $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | `(rvExpr| $a:rvExpr ^ $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .bxor $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | `(rvExpr| $a:rvExpr << $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .shl $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | `(rvExpr| $a:rvExpr >> $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .shr $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | `(rvExpr| $a:rvExpr < $b:rvExpr) =>
      `(Riscvc.RecExpr.bin .ltu $(← quoteRecursive self arity names a) $(← quoteRecursive self arity names b))
  | _ => `(Riscvc.RecExpr.pure $(← quoteExpr names stx))

open Lean Elab Term in
private def recursiveBody (self : TSyntax `ident) (args : Array (TSyntax `ident))
    (body : TSyntax `rvExpr) : TermElabM (TSyntax `term) := do
  let names := args.toList.map (fun arg => arg.getId)
  if names.eraseDups.length != names.length then throwError "duplicate DSL argument name"
  if names.contains self.getId then throwError "the recursive function name cannot be an argument"
  let quoted ← quoteRecursive self.getId names.length names body
  `(show Riscvc.RecExpr $(quote names.length) $(quote names.length) from $quoted)

open Lean Elab Term in
private def recursiveFunction (self : TSyntax `ident) (args : Array (TSyntax `ident))
    (body : TSyntax `rvExpr) (decreasingArg : TSyntax `ident) (proof : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
    TermElabM Lean.Expr := do
  let quoted ← recursiveBody self args body
  let names := args.toList.map (fun arg => arg.getId)
  let some index := names.idxOf? decreasingArg.getId
    | throwErrorAt decreasingArg "termination_by must name a function argument"
  let result ← `(show Riscvc.RecFn $(quote names.length) from
    Riscvc.RecFn.mk $quoted (fun env => (env ⟨$(quote index), by decide⟩).toNat) (by $proof))
  elabTerm result none

open Lean Elab Term in
elab_rules : term
  | `([riscv_rec| fun $self:ident $args:ident* => $body:rvExpr]) => do
      elabTerm (← recursiveBody self args body) none
  | `([riscv_rec| fun $self:ident $args:ident* => $body:rvExpr termination_by $arg:ident]) => do
      recursiveFunction self args body arg (← `(tacticSeq| word_decreasing))
  | `([riscv_rec| fun $self:ident $args:ident* => $body:rvExpr termination_by $arg:ident decreasing_by $proof:tacticSeq]) => do
      recursiveFunction self args body arg proof

end Riscvc
