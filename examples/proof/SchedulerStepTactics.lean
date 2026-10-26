import examples.proof.SchedulerStepProgram
import Lean

namespace Riscvc.Heap.Scheduler.StepProof

open Riscvc.Binary

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem index0 : (0 : Fin Ctx.length).val = 0 := rfl
theorem index1 : (1 : Fin Ctx.length).val = 1 := rfl
theorem index2 : (2 : Fin Ctx.length).val = 2 := rfl
theorem index3 : (3 : Fin Ctx.length).val = 3 := rfl
theorem index4 : (4 : Fin Ctx.length).val = 4 := rfl
theorem index5 : (5 : Fin Ctx.length).val = 5 := rfl
theorem index6 : (6 : Fin Ctx.length).val = 6 := rfl
theorem index7 : (7 : Fin Ctx.length).val = 7 := rfl
theorem index8 : (8 : Fin Ctx.length).val = 8 := rfl
theorem index9 : (9 : Fin Ctx.length).val = 9 := rfl

def values (p op pid work cur prev node tail duplicate result : Word) : Env Ctx :=
  fun i => match i.val with
  | 0 => p | 1 => op | 2 => pid | 3 => work | 4 => cur | 5 => prev
  | 6 => node | 7 => tail | 8 => duplicate | _ => result

def sourceEntry (p op pid work : Word) (mem : Heap.Memory) : Control.State Ctx :=
  ⟨entryStack, values p op pid work 0 0 0 0 0 0, mem⟩

def sourceAdd (p pid work cur duplicate : Word) (mem : Heap.Memory) : Control.State Ctx :=
  ⟨addStack, values p 1 pid work cur 0 0 0 duplicate 1, mem⟩

def sourceRemove (p pid work cur prev : Word) (mem : Heap.Memory) : Control.State Ctx :=
  ⟨removeStack, values p 2 pid work cur prev 0 0 0 4, mem⟩

def AtAdd (s : Control.State Ctx) (b : WordMachine.State) : Prop :=
  s.stack = addStack ∧ b.pc = 0x8000003c ∧
  s.env 1 = 1 ∧ s.env 2 ≠ 0 ∧ s.env 3 ≠ 0 ∧ s.env 4 ≠ 0 ∧
  s.env 5 = 0 ∧ s.env 6 = 0 ∧ s.env 7 = 0 ∧ (s.env 8 = 0 ∨ s.env 8 = 1) ∧ s.env 9 = 1 ∧
  b.regs .a0 = s.env 0 ∧ b.regs .a1 = s.env 1 ∧ b.regs .a2 = s.env 2 ∧
  b.regs .a3 = s.env 3 ∧ b.regs .a4 = s.env 4 ∧ b.regs .a6 = s.env 8

def AtRemove (s : Control.State Ctx) (b : WordMachine.State) : Prop :=
  s.stack = removeStack ∧ s.env 1 = 2 ∧ s.env 4 ≠ 0 ∧
  s.env 6 = 0 ∧ s.env 7 = 0 ∧ s.env 8 = 0 ∧ s.env 9 = 4 ∧
  b.regs .a0 = s.env 0 ∧ b.regs .a1 = s.env 1 ∧ b.regs .a2 = s.env 2 ∧ b.regs .a3 = s.env 4 ∧
  ((b.pc = 0x800000ac ∧ s.env 5 = 0) ∨
   (b.pc = 0x800000d0 ∧ s.env 5 ≠ 0 ∧ b.regs .a5 = s.env 5))

def Related (ra : Word) (s : Control.State Ctx) (b : WordMachine.State) : Prop :=
  b.mem = s.mem ∧ b.regs .ra = ra ∧
  ((s.stack = [] ∧ b.pc = ra ∧ b.regs .a0 = s.env 9) ∨ AtAdd s b ∨ AtRemove s b)

def Reaches (a : WordMachine.State) (post : WordMachine.State → Prop) : Prop :=
  ∃ n b, WordMachine.run program n a = some b ∧ post b

theorem reaches_done (a : WordMachine.State) (post : WordMachine.State → Prop) (h : post a) :
    Reaches a post := ⟨0, a, rfl, h⟩

theorem reaches_step (a b : WordMachine.State) (post : WordMachine.State → Prop)
    (h : WordMachine.step program a = some b) (rest : Reaches b post) : Reaches a post := by
  obtain ⟨n, final, hn, hp⟩ := rest
  exact ⟨n + 1, final, by simp only [WordMachine.run, h, Option.bind_some, hn], hp⟩

def Bounds (a : Nat) : Prop := 0x80001000 ≤ a ∧ a + 8 ≤ 0x90000000 ∧ a % 8 = 0

theorem mapped_bounds (mem : Heap.Memory) (a : Nat) (v : Word)
    (hr : SailLowering.InRAM mem) (hm : mem a = some v) : Bounds a := hr a v hm

theorem ram_write (mem : Heap.Memory) (a : Nat) (v : Word)
    (hr : SailLowering.InRAM mem) (ha : Bounds a) : SailLowering.InRAM (mem.write a v) := by
  intro b w hw
  by_cases hb : b = a
  · subst b; exact ha
  · exact hr b w (by simpa [Heap.Memory.write, hb] using hw)

theorem offset_nat (p : Word) (n : Nat) (ha : Accessible p n) :
    (p + BitVec.ofNat 64 n).toNat = p.toNat + n := by
  have hn : n < 2 ^ 64 := by have := ha.2.2; omega
  have hb : p.toNat + n < 2 ^ 64 := by have := ha.2.2; omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hb]

theorem less_one (v : Word) : (v < 1#64) = (v = 0#64) := by
  apply propext
  change v.toNat < 1 ↔ v = 0
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    change v.toNat = 0
    omega
  · intro h; subst v; decide

theorem zero_less (v : Word) : (0#64 < v) = (v ≠ 0#64) := by
  apply propext
  change 0 < v.toNat ↔ v ≠ 0
  constructor
  · intro h he; subst v; contradiction
  · intro h
    have : v.toNat ≠ 0 := by
      intro he
      exact h (BitVec.eq_of_toNat_eq he)
    omega

theorem sub_one_zero (v : Word) : (v + 18446744073709551615#64 = 0#64) = (v = 1#64) := by
  apply propext
  constructor
  · intro h
    have := congrArg (fun x : Word => x + 1) h
    simpa [BitVec.add_assoc] using this
  · intro h; subst v; rfl

theorem sub_one (v : Word) : v + 18446744073709551615#64 = v - 1#64 := by
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem sub_one_eq_zero (v : Word) : (v - 1#64 = 0#64) = (v = 1#64) := by
  rw [← sub_one, sub_one_zero]

theorem write_order (mem : Heap.Memory) (a : Nat) (x y : Word) :
    (mem.write (a + 8) x).write a y = (mem.write a y).write (a + 8) x := by
  funext b
  by_cases ha : b = a <;> by_cases hb : b = a + 8 <;> simp_all [Heap.Memory.write]

macro "normalize_memory" : tactic => `(tactic|
  simp (disch := omega) only [write_order, Heap.Memory.write_same,
    Heap.Memory.write_other, Nat.add_zero] at *)

open Lean Meta Elab Tactic in
elab "source_split " h:ident : tactic => withMainContext do
  let decl ← getLocalDeclFromUserName h.getId
  let type ← instantiateMVars decl.type
  let guard? := type.find? fun e =>
    (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !(e.getArg! 1).hasLooseBVars
  if let some expr := guard? then
    let g ← getMainGoal
    let (yes, no) ← g.byCases (expr.getArg! 1) (← mkFreshUserName `guard)
    replaceMainGoal [yes.mvarId, no.mvarId]
  else
    let lookup? := type.find? fun e =>
      !e.hasLooseBVars && e.isApp &&
      ((e.getAppFn.isFVar && e.getAppNumArgs == 1) ||
        e.isAppOfArity ``Heap.Memory.write 4)
    let some expr := lookup? | throwError "no source guard or memory read remains"
    unless ← isDefEq (← inferType expr) (← mkAppM ``Option #[mkConst ``Word]) do
      throwError "not a memory read: {expr}"
    let g ← getMainGoal
    let (_, ids, g) ← g.generalizeHyp #[{expr, hName? := some (← mkFreshUserName `mapped)}] #[decl.fvarId]
    let goals ← g.cases ids[0]!
    replaceMainGoal (goals.toList.map (·.mvarId))

macro "source_simp " h:ident : tactic => `(tactic|
  simp (config := { maxSteps := 100000 }) [sourceEntry, sourceAdd, sourceRemove,
    entryStack, addStack, removeStack, cmd1540, cmd770, cmd771, cmd97, cmd25, cmd7,
    cmd460, cmd230, cmd231, cmd15, descend, Scheduler.step,
    Control.chunk, Control.untilCut_cmd, Control.untilCut_nil, Control.untilCut_mark,
    Control.step, Expr.eval, values, Env.set, bind, Option.bind, pure, BinOp.eval,
    State.head, State.tail, State.free, State.count, State.ticks, State.lastPid,
    Process.pid, Process.next, Process.remaining,
    index0, index1, index2, index3, index4, index5, index6, index7, index8, index9, *] at $h:ident)

open Lean Meta Elab Tactic in
elab "source_cases " h:ident : tactic => do
  let mut pending ← getGoals
  let mut leaves := []
  let mut count := 0
  while !pending.isEmpty do
    count := count + 1
    if count > 2000 then throwError "source segment exceeded 2000 proof branches"
    let g := pending.head!
    pending := pending.tail!
    setGoals [g]
    try evalTactic (← `(tactic| source_simp $h)) catch _ => pure ()
    if (← getGoals).isEmpty then continue
    try
      evalTactic (← `(tactic| source_split $h))
      pending := (← getGoals) ++ pending
    catch _ =>
      leaves := leaves ++ (← getGoals)
  setGoals leaves

private partial def collectWrites (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : Array Lean.Expr :=
  let acc := if e.isAppOfArity ``Heap.Memory.write 3 && !e.hasLooseBVars && !acc.contains e
    then acc.push e else acc
  match e with
  | .app f a => collectWrites a (collectWrites f acc)
  | .lam _ t b _ | .forallE _ t b _ => collectWrites b (collectWrites t acc)
  | .letE _ t v b _ => collectWrites b (collectWrites v (collectWrites t acc))
  | .proj _ _ b | .mdata _ b => collectWrites b acc
  | _ => acc

open Lean Meta Elab Tactic in
elab "memory_facts" : tactic => withMainContext do
  let mut ram : Array (Lean.Expr × Lean.Expr) := #[]
  let mut bounds : Array (Lean.Expr × Lean.Expr) := #[]
  let mut reads : Array (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  let mut writes : Array Lean.Expr := #[]
  let mut facts : Array Lean.Expr := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      writes := writes ++ collectWrites type
      if type.isAppOfArity ``SailLowering.InRAM 1 then
        ram := ram.push (type.getArg! 0, mkFVar decl.fvarId)
      if type.isAppOfArity ``Accessible 2 then
        facts := facts.push (← mkAppM ``offset_nat #[type.getArg! 0, type.getArg! 1, mkFVar decl.fvarId])
      if let some (_, lhs, rhs) := type.eq? then
        if rhs.isAppOfArity ``Option.some 2 && lhs.isApp then
          if ← isDefEq (← inferType lhs) (← mkAppM ``Option #[mkConst ``Word]) then
            reads := reads.push (lhs.appFn!, lhs.appArg!, rhs.getArg! 1, mkFVar decl.fvarId)
  writes := writes ++ collectWrites (← getMainTarget)
  let mut changed := true
  while changed do
    changed := false
    for (mem, addr, v, proof) in reads do
      unless ← bounds.anyM (fun (a, _) => isDefEq a addr) do
        if let some (_, hr) ← ram.findM? (fun (m, _) => isDefEq m mem) then
          let hb ← mkAppM ``mapped_bounds #[mem, addr, v, hr, proof]
          bounds := bounds.push (addr, hb)
          facts := facts.push (← mkAppM ``And.left #[hb])
          let tail ← mkAppM ``And.right #[hb]
          facts := facts.push (← mkAppM ``And.left #[tail])
          facts := facts.push (← mkAppM ``And.right #[tail])
          changed := true
    for w in writes do
      unless ← ram.anyM (fun (m, _) => isDefEq m w) do
        let mem := w.getArg! 0
        let addr := w.getArg! 1
        let value := w.getArg! 2
        if let some (_, hr) ← ram.findM? (fun (m, _) => isDefEq m mem) then
          if let some (_, hb) ← bounds.findM? (fun (a, _) => isDefEq a addr) then
            ram := ram.push (w, ← mkAppM ``ram_write #[mem, addr, value, hr, hb])
            changed := true
  let mut g ← getMainGoal
  for proof in facts do
    let (_, next) ← g.note (← mkFreshUserName `memoryFact) proof
    g := next
  replaceMainGoal [g]

macro "machine_simp" : tactic => `(tactic|
  simp (config := { maxSteps := 100000 }) (disch := first | assumption | omega)
    [instructions, WordMachine.Op.eval, WordMachine.State.write, WordMachine.Src.get,
     WordMachine.Registers.put, Binary.Memory.Address, less_one, zero_less, sub_one_zero,
     sub_one, sub_one_eq_zero, write_order, bind, Option.bind, *])

macro "machine_done" : tactic => `(tactic|
  (apply reaches_done
   simp (config := { maxSteps := 100000 }) (disch := first | assumption | omega)
     [Related, AtAdd, AtRemove, entryStack, addStack, removeStack,
      cmd1540, cmd770, cmd771, cmd97, cmd25, cmd7, cmd460, cmd230, cmd231, cmd15,
      descend, Scheduler.step, values, Env.set, WordMachine.Registers.put,
      State.head, State.tail, State.free, State.count, State.ticks, State.lastPid,
      Process.pid, Process.next, Process.remaining,
      index0, index1, index2, index3, index4, index5, index6, index7, index8, index9,
      sub_one, write_order, *]
   repeat first | assumption | rfl | apply And.intro))

open Lean Meta Elab Tactic in
elab "instruction_step" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.isAppOfArity ``Reaches 2 do throwError "expected a scheduler reachability goal"
  let state := target.getArg! 0
  let pc ← mkAppM ``WordMachine.State.pc #[state]
  let pcNat ← mkAppM ``BitVec.toNat #[pc]
  let pcNat ← withTransparency .all <| whnf pcNat
  let .lit (.natVal addr) := pcNat | throwError "PC is not a concrete instruction address: {pcNat}"
  unless 0x80000000 ≤ addr && addr < 0x800001e8 && addr % 4 == 0 do
    throwError "PC is outside the scheduler: {addr}"
  let lemma := mkIdent <| ``instruction0 |>.getPrefix |>.str s!"instruction{(addr - 0x80000000) / 4}"
  evalTactic (← `(tactic| apply reaches_step))
  evalTactic (← `(tactic| erw [$lemma:ident]))
  evalTactic (← `(tactic| machine_simp))
  if (← getGoals).length > 1 then
    evalTactic (← `(tactic| first | rfl | exact ⟨by assumption, rfl⟩))

open Lean Meta Elab Tactic in
elab "machine_run" : tactic => do
  let goals ← getGoals
  let mut left := []
  for g in goals do
    setGoals [g]
    let mut done := false
    for i in [:160] do
      let finish ← withMainContext do
        let target ← getMainTarget
        let pc ← mkAppM ``WordMachine.State.pc #[target.getArg! 0]
        let pcNat ← withTransparency .all <| whnf (← mkAppM ``BitVec.toNat #[pc])
        pure <| match pcNat with
          | .lit (.natVal n) => i > 0 && [0x8000003c, 0x800000ac, 0x800000d0].contains n
          | _ => true
      if finish then
        evalTactic (← `(tactic| machine_done))
        unless (← getGoals).isEmpty do
          throwError "unproved cutpoint relation: {← getMainTarget}"
        done := true
        break
      evalTactic (← `(tactic| instruction_step))
    unless done do throwError "binary segment did not reach the source cutpoint in 160 instructions"
    left := left ++ (← getGoals)
  setGoals left

end Riscvc.Heap.Scheduler.StepProof
