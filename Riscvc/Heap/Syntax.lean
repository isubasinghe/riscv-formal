import Lean
import Riscvc.Heap.Language

namespace Riscvc.Heap

declare_syntax_cat heapTy
syntax "u64" : heapTy
syntax "ptr " ident : heapTy
syntax "riscv_struct " ident " { " (ident " : " heapTy),* " }" : command

open Lean Elab Command Term

private def quoteType (ty : Syntax) : TermElabM (TSyntax `term) := do
  match ty with
  | `(heapTy| u64) => `(Riscvc.Heap.Ty.u64)
  | `(heapTy| ptr $name:ident) => `(Riscvc.Heap.Ty.ptr ($name).name)
  | _ => throwErrorAt ty "expected u64 or ptr StructName"

elab_rules : command
  | `(riscv_struct $name:ident { $[$fields:ident : $types:heapTy],* }) => do
      let fullName := (← getCurrNamespace) ++ name.getId
      if fields.isEmpty then throwErrorAt name "a struct must have at least one field"
      if (fields.toList.map (·.getId)).eraseDups.length ≠ fields.size then
        throwErrorAt name "duplicate struct field name"
      let tys ← liftTermElabM do types.mapM fun ty => do
        match ty with
        | `(heapTy| ptr $target:ident) =>
            if target.getId == name.getId then `(Riscvc.Heap.Ty.ptr $(quote fullName.toString))
            else quoteType ty
        | _ => quoteType ty
      elabCommand (← `(def $name : Riscvc.Heap.Layout :=
        ⟨$(quote fullName.toString), [$tys,*]⟩))
      for i in [:fields.size] do
        let fieldName := mkIdent (name.getId ++ fields[i]!.getId)
        elabCommand (← `(def $fieldName : Riscvc.Heap.Field $name $(tys[i]!) :=
          ⟨⟨$(quote i), by decide⟩, rfl⟩))

declare_syntax_cat heapExpr
syntax num : heapExpr
syntax ident : heapExpr
syntax "null" : heapExpr
syntax "(" heapExpr ")" : heapExpr
syntax:65 heapExpr:65 " + " heapExpr:66 : heapExpr
syntax:65 heapExpr:65 " - " heapExpr:66 : heapExpr
syntax:50 heapExpr:51 " == " heapExpr:51 : heapExpr
syntax:10 "if " heapExpr " then " heapExpr " else " heapExpr : heapExpr

declare_syntax_cat heapCmd
syntax ident " := " heapExpr ";" : heapCmd
syntax "if " heapExpr " { " heapCmd* " } " "else" " { " heapCmd* " }" ";" : heapCmd
syntax "while " heapExpr " { " heapCmd* " }" ";" : heapCmd
declare_syntax_cat heapBinder
syntax "(" ident " : " heapTy ")" : heapBinder
syntax "[riscv_mem| " "fun " heapBinder*
  " locals " heapBinder* " => " "{ " heapCmd*
  " return " heapExpr " : " heapTy " }" "]" : term

private def varIndex (names : List Name) (name : Syntax) : TermElabM Nat := do
  match names.idxOf? name.getId with
  | some i => return i
  | none => throwErrorAt name "unknown heap DSL variable '{name.getId}'"

private def quoteVar (names : List Name) (name : Syntax) : TermElabM (TSyntax `term) := do
  let i ← varIndex names name
  `(Riscvc.Heap.Var.mk ⟨$(quote i), by decide⟩ (by rfl))

/-- Field notation is resolved from the variable's declared struct type. -/
private def fieldAccess (names : List Name) (types : List Syntax) (name : Syntax) :
    TermElabM (TSyntax `term × TSyntax `term) := do
  let base := mkIdent name.getId.getPrefix
  let i ← varIndex names base
  let `(heapTy| ptr $layout:ident) := types[i]! |
    throwErrorAt name "field access requires a struct pointer"
  let field := mkIdent (layout.getId ++ .str .anonymous name.getId.getString!)
  let p ← `(Riscvc.Heap.Expr.var $(← quoteVar names base))
  return (field, p)

private partial def quoteExpr (names : List Name) (types : List Syntax) (e : Syntax) :
    TermElabM (TSyntax `term) := do
  match e with
  | `(heapExpr| null) => `(Riscvc.Heap.Expr.null)
  | `(heapExpr| $n:num) =>
      if n.getNat ≥ 2^64 then throwErrorAt n "literal does not fit in a 64-bit word"
      `(Riscvc.Heap.Expr.word (BitVec.ofNat 64 $n))
  | `(heapExpr| $v:ident) =>
      if names.contains v.getId then `(Riscvc.Heap.Expr.var $(← quoteVar names v))
      else
        let (field, pointer) ← fieldAccess names types v
        `(Riscvc.Heap.Expr.field $field $pointer)
  | `(heapExpr| ($a:heapExpr)) => quoteExpr names types a
  | `(heapExpr| $a:heapExpr + $b:heapExpr) =>
      `(Riscvc.Heap.Expr.bin .add $(← quoteExpr names types a) $(← quoteExpr names types b))
  | `(heapExpr| $a:heapExpr - $b:heapExpr) =>
      `(Riscvc.Heap.Expr.bin .sub $(← quoteExpr names types a) $(← quoteExpr names types b))
  | `(heapExpr| $a:heapExpr == $b:heapExpr) =>
      `(Riscvc.Heap.Expr.eq $(← quoteExpr names types a) $(← quoteExpr names types b))
  | `(heapExpr| if $c:heapExpr then $a:heapExpr else $b:heapExpr) =>
      `(Riscvc.Heap.Expr.ite $(← quoteExpr names types c)
        $(← quoteExpr names types a) $(← quoteExpr names types b))
  | _ => throwErrorAt e "unsupported heap expression"

private partial def quoteCmds (names : List Name) (types : List Syntax) (cmds : List Syntax) :
    TermElabM (TSyntax `term) := do
  match cmds with
  | [] => `(Riscvc.Heap.Cmd.skip)
  | cmd :: rest =>
    let first ← match cmd with
    | `(heapCmd| $dst:ident := $value:heapExpr;) => do
        let value ← quoteExpr names types value
        if names.contains dst.getId then
          `(Riscvc.Heap.Cmd.assign $(← quoteVar names dst) $value)
        else
          let (field, pointer) ← fieldAccess names types dst
          `(Riscvc.Heap.Cmd.store $field $pointer $value)
    | `(heapCmd| if $condition:heapExpr { $yes:heapCmd* } else { $no:heapCmd* };) =>
        `(Riscvc.Heap.Cmd.ite $(← quoteExpr names types condition)
          $(← quoteCmds names types (yes.toList.map (·.raw))) $(← quoteCmds names types (no.toList.map (·.raw))))
    | `(heapCmd| while $condition:heapExpr { $body:heapCmd* };) =>
        `(Riscvc.Heap.Cmd.while $(← quoteExpr names types condition)
          $(← quoteCmds names types (body.toList.map (·.raw))))
    | _ => throwErrorAt cmd "unsupported heap command"
    `(Riscvc.Heap.Cmd.seq $first $(← quoteCmds names types rest))

elab_rules : term
  | `([riscv_mem| fun $args:heapBinder* locals $vars:heapBinder* => {
       $cmds:heapCmd* return $result:heapExpr : $resultType:heapTy }]) => do
      let binders ← (args ++ vars).mapM fun binder => do
        let `(heapBinder| ($name:ident : $ty:heapTy)) := binder | throwError "invalid binder"
        pure (name.getId, ty.raw)
      let names := binders.toList.map Prod.fst
      let types := binders.toList.map Prod.snd
      if names.eraseDups.length ≠ names.length then throwError "duplicate heap DSL variable name"
      let params ← (types.take args.size).toArray.mapM quoteType
      let localTys ← (types.drop args.size).toArray.mapM quoteType
      let body ← quoteCmds names types (cmds.toList.map (·.raw))
      let returns ← quoteExpr names types result
      let ty ← quoteType resultType
      elabTerm (← `(show Riscvc.Heap.Function [$params,*] [$localTys,*] $ty from
        ⟨$body, $returns⟩)) none

end Riscvc.Heap
