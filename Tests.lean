import Riscvc.Examples
import Riscvc.RecursionTests
import Riscvc.LLVMTests
import Riscvc.Binary.ELFTests
import Riscvc.Heap.Tests

open Riscvc Riscvc.Examples

/- Audit the proof boundary: these should depend only on Lean's standard axioms. -/
/-- info: 'Riscvc.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Riscvc.compile_correct

/-- info: 'Riscvc.execute_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Riscvc.execute_correct

/-- info: 'Riscvc.compiled_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Riscvc.compiled_satisfies

/- Frontend errors must be diagnosed at the DSL boundary. -/
/-- error: unknown DSL variable 'missing' -/
#guard_msgs in
#check [riscv| fun x => x + missing]

/-- error: duplicate DSL argument name -/
#guard_msgs in
#check [riscv| fun x x => x]

/-- error: literal does not fit in a 64-bit word -/
#guard_msgs in
#check [riscv| fun => 18446744073709551616]

/- Scope, associativity, and precedence affect the meaning users prove. -/
example : ([riscv| fun x y => x - y - 1] : Expr 2).eval (Env.two 9 3) = 5 := by decide
example : ([riscv| fun x => x + 1 << 2] : Expr 1).eval (Env.one 2) = 12 := by decide
example : ([riscv| fun x => let x := x + 1; let x := x + 2; x] : Expr 1).eval
    (Env.one 10) = 13 := by decide
example : ([riscv| fun x y => if x then if y then 1 else 2 else 3] : Expr 2).eval
    (Env.two 1 0) = 2 := by decide
example : ([riscv| fun x n => x >> n] : Expr 2).eval (Env.two 8 64) = 8 := by decide
example : ([riscv| fun x n => x << n] : Expr 2).eval (Env.two 8 65) = 16 := by decide

/-- Each overflowing case requires a slot outside the physical register pool. -/
private def tooDeep : Expr 8 := [riscv| fun a b c d e f g h =>
  a + (b + (c + (d + (e + (f + (g + h))))))
]

private def assertOk {α : Type} (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok x => pure x
  | .error message => throw (IO.userError s!"{label}: {message}")

private def assertError {α : Type} (label : String) (value : Except String α) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: expected rejection")

private def next (seed : Word) : Word := seed * 6364136223846793005 + 1442695040888963407

/-- Deterministic expression generation exercises compiler shapes beyond the
    handwritten examples, including locals, constants, and nested selections. -/
private def randomExpr {n : Nat} : Nat → Word → Expr n
  | 0, seed =>
      if h : n > 0 then
        if seed.toNat % 2 = 0 then .var ⟨seed.toNat % n, Nat.mod_lt _ h⟩ else .lit seed
      else .lit seed
  | depth + 1, seed =>
      let a := next seed
      let b := next a
      match seed.toNat % 5 with
      | 0 => .lit seed
      | 1 => .letE (randomExpr depth a) (randomExpr depth b)
      | 2 => .ite (randomExpr depth a) (randomExpr depth b) (randomExpr depth (next b))
      | _ =>
          let op := #[BinOp.add, .sub, .band, .bor, .bxor, .shl, .shr, .ltu].getD
            (a.toNat % 8) .add
          .bin op (randomExpr depth a) (randomExpr depth b)

private def generated : List Example := (List.range 32).map fun i =>
  ⟨s!"generated_{i}", 3, randomExpr 4 (next (BitVec.ofNat 64 (i + 1)))⟩

private def cases (arity : Nat) : List (Array Word) := Id.run do
  let edges : Array Word := #[0, 1, 2, 63, 64, 65, 255, 0x7fffffffffffffff,
    0x8000000000000000, 0xfffffffffffffffe, 0xffffffffffffffff]
  let mut vectors := []
  for x in edges do
    for y in edges do
      vectors := vectors ++ [(List.range arity).toArray.map fun i =>
        if i % 3 = 0 then x else if i % 3 = 1 then y else x ^^^ y]
  let mut seed : Word := 0x123456789abcdef0
  for _ in [:24] do
    let mut vector := #[]
    for _ in [:arity] do
      seed := next seed
      vector := vector.push seed
    vectors := vectors ++ [vector]
  return vectors

private def preserved : List (String × Word) :=
  [("sp", 0x81000000), ("gp", 0x12340), ("tp", 0x56780)] ++
    (List.range 12).map (fun i => (s!"s{i}", BitVec.ofNat 64 (0x1000 + i)))

private def sailCase (lines : Array String) (count : Nat) (name : String)
    (args : Array Word) (expected : Word) : Array String := Id.run do
  let mut lines := lines.push s!"  # case {count}: {name}"
  -- LLVM also supports arguments beyond a0..a7. Keep the outgoing stack area
  -- 16-byte aligned and restore it before checking the preserved stack pointer.
  let stackBytes := ((args.size - 8 + 1) / 2) * 16
  if stackBytes > 0 then lines := lines.push s!"  addi sp, sp, -{stackBytes}"
  for i in [:args.size] do
    if i < 8 then
      lines := lines.push s!"  li a{i}, {args[i]!.toInt}"
    else
      lines := lines ++ #[s!"  li t0, {args[i]!.toInt}", s!"  sd t0, {8 * (i - 8)}(sp)"]
  lines := lines.push s!"  call {name}"
  if stackBytes > 0 then lines := lines.push s!"  addi sp, sp, {stackBytes}"
  return lines ++ #[s!"  li t0, {expected.toInt}",
    s!"  beq a0, t0, .Lcase_{count}_ok", s!"  li a0, {2 * (count + 1) + 1}",
    "  tail .Lfinish", s!".Lcase_{count}_ok:"]

/-- Generate a bare-metal ELF test's assembly. Expected results come from the
    source evaluator; the executable instructions are checked by Sail. -/
private def sailHarness (llvm : Bool := false) : IO (String × Nat) := do
  let entries := examples ++ generated ++ (if llvm then LLVMTests.pureExamples else [])
  let mut lines := #[".option norvc", ".option norelax", ".section .text.init",
    ".globl _start", "_start:"]
  for (reg, value) in preserved do
    lines := lines.push s!"  li {reg}, {value.toInt}"
  let mut count := 0
  for entry in entries do
    for args in cases entry.arity do
      let env : Env entry.arity := fun i => args[i.val]!
      let expected := entry.program.eval env
      if execute entry.program env != expected then
        throw (IO.userError s!"modeled execution mismatch: {entry.name}, case {count}")
      lines := sailCase lines count entry.name args expected
      count := count + 1
  let recursiveEntries := RecursiveExamples.examples ++ RecursionTests.extraExamples ++
    (if llvm then LLVMTests.recursiveExamples else [])
  for entry in recursiveEntries do
    for args in entry.inputs do
      let env : Env entry.arity := fun i => args[i.val]!
      let expected := entry.program.eval env
      lines := sailCase lines count entry.name args expected
      count := count + 1
  -- Tail recursion must not consume another frame on each iteration. A canary
  -- below the one permitted frame detects stack growth even if the result is right.
  lines := lines ++ #[s!"  # case {count}: deep tail recursion and stack canary",
    "  li t0, 0x13579bdf2468ace0", "  sd t0, -256(sp)",
    "  li a0, 10000", "  li a1, -1", "  call count_up", "  li t0, 9999",
    "  beq a0, t0, .Ldeep_result_ok", s!"  li a0, {2 * (count + 1) + 1}",
    "  tail .Lfinish", ".Ldeep_result_ok:", "  li t0, 0x13579bdf2468ace0",
    "  ld t1, -256(sp)", "  beq t0, t1, .Ldeep_canary_ok", s!"  li a0, {2 * (count + 1) + 1}",
    "  tail .Lfinish", ".Ldeep_canary_ok:"]
  count := count + 1
  for (reg, value) in preserved do
    lines := lines ++ #[s!"  li t0, {value.toInt}", s!"  beq {reg}, t0, .Lpreserved_{reg}",
      s!"  li a0, {2 * (count + 1) + 1}", "  tail .Lfinish", s!".Lpreserved_{reg}:"]
  lines := lines ++ #["  li a0, 1", ".Lfinish:", "  la t0, tohost", "  sd a0, 0(t0)",
    ".Lhalt:", "  j .Lhalt", ".section .tohost,\"aw\",@progbits", ".balign 8",
    ".globl tohost", "tohost: .dword 0", ".globl fromhost", "fromhost: .dword 0"]
  if !llvm then
    for entry in entries do
      lines := lines.push (← assertOk entry.name (emitAssembly entry.name entry.program))
    for entry in recursiveEntries do
      lines := lines.push (← assertOk entry.name (emitRecursiveAssembly entry.name entry.program))
  return (String.intercalate "\n" lines.toList ++ "\n", count)

private def llvmCase (name : String) (args : Array Word) (expected : Word) : Lean.Json :=
  Lean.Json.mkObj [("name", Lean.toJson name),
    ("args", Lean.toJson (args.map BitVec.toNat)), ("expected", Lean.toJson expected.toNat)]

/-- One source-evaluated corpus is used for native LLVM execution and Sail. -/
private def llvmArtifacts (directory : System.FilePath) : IO Unit := do
  let mut definitions := #[]
  let mut inputs := #[]
  for entry in examples ++ generated ++ LLVMTests.pureExamples do
    definitions := definitions.push (← assertOk entry.name (LLVM.emit entry.name entry.program))
    for args in cases entry.arity do
      let env : Env entry.arity := fun i => args[i.val]!
      inputs := inputs.push (llvmCase entry.name args (entry.program.eval env))
  for entry in RecursiveExamples.examples ++ RecursionTests.extraExamples ++ LLVMTests.recursiveExamples do
    definitions := definitions.push (← assertOk entry.name (LLVM.emitRecursive entry.name entry.program))
    for args in entry.inputs do
      let env : Env entry.arity := fun i => args[i.val]!
      inputs := inputs.push (llvmCase entry.name args (entry.program.eval env))
  -- The deep countdown uses countUp_correct's arithmetic specification.
  inputs := inputs.push (llvmCase "count_up" #[10000, 0xffffffffffffffff] 9999)
  let (harness, count) ← sailHarness true
  if count != inputs.size then throw (IO.userError "LLVM/native and Sail corpus sizes disagree")
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "programs.ll") (String.intercalate "\n" definitions.toList)
  IO.FS.writeFile (directory / "cases.json") (Lean.Json.arr inputs).compress
  IO.FS.writeFile (directory / "harness.S") harness
  IO.println s!"Generated {count} LLVM differential cases and ABI checks in {directory}."

def main (args : List String) : IO UInt32 := do
  Heap.Tests.check
  RecursionTests.check
  LLVMTests.check
  assertError "invalid symbol" (emitAssembly "bad\n.text" sum)
  assertError "empty symbol" (emitAssembly "" sum)
  assertError "non-ASCII symbol" (emitAssembly "λ" sum)
  assertError "initial digit" (emitAssembly "1bad" sum)
  assertError "register exhaustion" (emitAssembly "too_deep" tooDeep)
  assertError "too many arguments" (emitAssembly "arity" (Expr.lit (n := 9) 0))
  for entry in examples ++ generated do
    let _ ← assertOk entry.name (emitAssembly entry.name entry.program)
  match args with
  | [] =>
      IO.println "Frontend and backend checks passed."
  | ["--emit-sail", path] =>
      let (assembly, count) ← sailHarness
      IO.FS.writeFile path assembly
      IO.println s!"Generated {count} source/assembly differential cases and ABI preservation checks in {path}."
  | ["--emit-llvm-tests", directory] => llvmArtifacts directory
  | _ =>
      IO.eprintln "usage: lake test [-- --emit-sail <assembly-path> | -- --emit-llvm-tests <directory>]"
      return 1
  return 0
