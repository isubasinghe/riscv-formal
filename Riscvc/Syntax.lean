import Lean
import Riscvc.Language

namespace Riscvc

declare_syntax_cat rvExpr
syntax num : rvExpr
syntax ident : rvExpr
syntax ident "(" rvExpr,* ")" : rvExpr
syntax "(" rvExpr ")" : rvExpr
syntax:65 rvExpr:65 " + " rvExpr:66 : rvExpr
syntax:65 rvExpr:65 " - " rvExpr:66 : rvExpr
syntax:60 rvExpr:60 " << " rvExpr:61 : rvExpr
syntax:60 rvExpr:60 " >> " rvExpr:61 : rvExpr
syntax:55 rvExpr:56 " < " rvExpr:56 : rvExpr
syntax:50 rvExpr:50 " & " rvExpr:51 : rvExpr
syntax:45 rvExpr:45 " ^ " rvExpr:46 : rvExpr
syntax:40 rvExpr:40 " | " rvExpr:41 : rvExpr
syntax:10 "let " ident " := " rvExpr "; " rvExpr : rvExpr
syntax:10 "if " rvExpr " then " rvExpr " else " rvExpr : rvExpr
syntax "[riscv| " "fun " ident* " => " rvExpr "]" : term

open Lean Elab Term in
partial def quoteExpr (names : List Name) (stx : Syntax) : TermElabM (TSyntax `term) := do
  match stx with
  | `(rvExpr| $v:num) =>
      if v.getNat ≥ 2^64 then
        throwErrorAt v "literal does not fit in a 64-bit word"
      `(Riscvc.Expr.lit (BitVec.ofNat 64 $v))
  | `(rvExpr| $v:ident) =>
      match names.idxOf? v.getId with
      | none => throwErrorAt v "unknown DSL variable '{v.getId}'"
      | some i => `(Riscvc.Expr.var ⟨$(quote i), by decide⟩)
  | `(rvExpr| ($e:rvExpr)) => quoteExpr names e
  | `(rvExpr| let $v:ident := $a:rvExpr; $b:rvExpr) =>
      `(Riscvc.Expr.letE $(← quoteExpr names a) $(← quoteExpr (v.getId :: names) b))
  | `(rvExpr| if $c:rvExpr then $t:rvExpr else $f:rvExpr) =>
      `(Riscvc.Expr.ite $(← quoteExpr names c) $(← quoteExpr names t) $(← quoteExpr names f))
  | `(rvExpr| $a:rvExpr + $b:rvExpr) =>
      `(Riscvc.Expr.bin .add $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $a:rvExpr - $b:rvExpr) =>
      `(Riscvc.Expr.bin .sub $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $a:rvExpr & $b:rvExpr) =>
      `(Riscvc.Expr.bin .band $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $a:rvExpr | $b:rvExpr) =>
      `(Riscvc.Expr.bin .bor $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $a:rvExpr ^ $b:rvExpr) =>
      `(Riscvc.Expr.bin .bxor $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $a:rvExpr << $b:rvExpr) =>
      `(Riscvc.Expr.bin .shl $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $a:rvExpr >> $b:rvExpr) =>
      `(Riscvc.Expr.bin .shr $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $a:rvExpr < $b:rvExpr) =>
      `(Riscvc.Expr.bin .ltu $(← quoteExpr names a) $(← quoteExpr names b))
  | `(rvExpr| $_f:ident($_args:rvExpr,*)) =>
      throwErrorAt stx "calls require riscv_rec; call arguments must be pure (bind recursive results with let first)"
  | _ => throwErrorAt stx "unsupported DSL expression"

open Lean Elab Term in
elab_rules : term
  | `([riscv| fun $args:ident* => $body:rvExpr]) => do
      let names := args.toList.map (fun arg => arg.getId)
      if names.eraseDups.length ≠ names.length then
        throwError "duplicate DSL argument name"
      let quoted ← quoteExpr names body
      let typed ← `(show Riscvc.Expr $(quote names.length) from $quoted)
      elabTerm typed none

end Riscvc
