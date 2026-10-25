import Riscvc.Examples
import Riscvc.RecursiveExamples
import Riscvc.SMT
import Riscvc.Heap.Examples

open Riscvc Riscvc.Examples

private def emit (entry : Example) (llvm : Bool) : IO Unit :=
  match (if llvm then LLVM.emit else emitAssembly) entry.name entry.program with
  | .ok asm => IO.print asm
  | .error message => throw (IO.userError s!"{entry.name}: {message}")

private def emitRecursive (entry : RecursiveExamples.Example) (llvm : Bool) : IO Unit :=
  match (if llvm then LLVM.emitRecursive else emitRecursiveAssembly) entry.name entry.program with
  | .ok asm => IO.print asm
  | .error message => throw (IO.userError s!"{entry.name}: {message}")

private def heapExamples : List (String × Except String String) :=
  [("list_append", Heap.LLVM.emit "list_append" Heap.Examples.append),
   ("node_set_value", Heap.LLVM.emit "node_set_value" Heap.Examples.setValue),
   ("node_head_or_zero", Heap.LLVM.emit "node_head_or_zero" Heap.Examples.headOrZero)]

private def emitHeap (code : Except String String) : IO Unit :=
  match code with
  | .ok text => IO.print text
  | .error message => throw (IO.userError message)

def main (args : List String) : IO UInt32 := do
  if let ["--smt", name] := args then
    if let some e := examples.find? (fun e => e.name == name) then
      IO.print (SMT.emit e.program)
      return 0
    IO.eprintln "SMT export requires a pure example; recursive functions need a supplied specification/invariant"
    return 1
  let (llvm, args) := match args with
    | "--llvm" :: rest => (true, rest)
    | _ => (false, args)
  match args with
  | ["--list"] =>
      for e in examples do IO.println s!"{e.name} ({e.arity} arguments)"
      for e in RecursiveExamples.examples do IO.println s!"{e.name} ({e.arity} arguments, recursive)"
      for (name, _) in heapExamples do IO.println s!"{name} (heap program, LLVM backend)"
      return 0
  | ["--all"] =>
      for e in examples do emit e llvm
      for e in RecursiveExamples.examples do emitRecursive e llvm
      if llvm then
        for (_, code) in heapExamples do emitHeap code
      return 0
  | [name] =>
      if let some (_, code) := heapExamples.find? (fun e => e.1 == name) then
        if !llvm then
          IO.eprintln "heap programs require --llvm"
          return 1
        emitHeap code
        return 0
      if let some e := examples.find? (fun e => e.name == name) then
        emit e llvm
        return 0
      if let some e := RecursiveExamples.examples.find? (fun e => e.name == name) then
        emitRecursive e llvm
        return 0
      IO.eprintln s!"unknown example '{name}'; use --list"
      return 1
  | _ =>
      IO.eprintln "usage: lake exe riscvc [--llvm] <example-name | --all | --list> | --smt <pure-example>"
      return 1
