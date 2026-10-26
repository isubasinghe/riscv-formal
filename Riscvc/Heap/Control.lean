import Riscvc.Heap.Language
import Riscvc.Heap.SailLowering

/-! Continuations for the actual typed heap DSL. Loop-entry markers carry the
syntactic path of the loop; they have no effect on the source program. This
small-step presentation lets translation certificates stop at loop cutpoints.
`of_exec` connects it to the unbounded big-step semantics, without a list bound.
-/
namespace Riscvc.Heap.Control

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

inductive Frame (ctx : Context) where
  | cmd (body : Cmd ctx) (path : Nat)
  | mark (path : Nat)

structure State (ctx : Context) where
  stack : List (Frame ctx)
  env : Env ctx
  mem : Memory

def step (s : State ctx) : Option (State ctx) :=
  match s.stack with
  | [] => none
  | .mark _ :: rest => some {s with stack := rest}
  | .cmd body path :: rest =>
    match body with
    | .skip => some {s with stack := rest}
    | .seq a b => some {s with stack := .cmd a (2 * path) :: .cmd b (2 * path + 1) :: rest}
    | .assign dst value => do
        let v ← value.eval s.env s.mem
        some {s with stack := rest, env := s.env.set dst.index v}
    | .store field ptr value => do
        let p ← ptr.eval s.env s.mem
        let v ← value.eval s.env s.mem
        if Accessible p (8 * field.index.val) then
          let _ ← s.mem (p.toNat + 8 * field.index.val)
          some {s with stack := rest, mem := s.mem.write (p.toNat + 8 * field.index.val) v}
        else none
    | .ite cond yes no => do
        let v ← cond.eval s.env s.mem
        some {s with stack :=
          if v = 0 then .cmd no (2 * path + 1) :: rest else .cmd yes (2 * path) :: rest}
    | .while cond body => do
        let v ← cond.eval s.env s.mem
        some {s with stack := (if v = 0 then rest else
          .mark path :: .cmd body (2 * path) :: .cmd (.while cond body) path :: rest)}

def run : Nat → State ctx → Option (State ctx)
  | 0, s => some s
  | n + 1, s => (step s).bind (run n)

theorem run_add (m n : Nat) (s : State ctx) :
    run (m + n) s = (run m s).bind (run n) := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add]; rfl
  | succ m ih =>
    simp only [Nat.succ_add, run]
    cases h : step s <;> simp [ih]

def Reaches (a b : State ctx) : Prop := ∃ n, run n a = some b

theorem Reaches.refl (s : State ctx) : Reaches s s := ⟨0, rfl⟩

theorem Reaches.cons (a b c : State ctx) (h : step a = some b) (rest : Reaches b c) :
    Reaches a c := by
  obtain ⟨n, hn⟩ := rest
  exact ⟨n + 1, by simpa only [run, h, Option.bind_some] using hn⟩

theorem Reaches.trans (a b c : State ctx) (first : Reaches a b) (rest : Reaches b c) :
    Reaches a c := by
  obtain ⟨n, hn⟩ := first
  obtain ⟨m, hm⟩ := rest
  exact ⟨n + m, by simp only [run_add, hn, Option.bind_some, hm]⟩

theorem of_exec {cmd : Cmd ctx} {env final : Env ctx} {mem mem' : Memory}
    (h : Exec cmd env mem final mem') (path : Nat) (rest : List (Frame ctx)) :
    Reaches ⟨.cmd cmd path :: rest, env, mem⟩ ⟨rest, final, mem'⟩ := by
  induction h generalizing path rest with
  | skip => exact ⟨1, rfl⟩
  | @seq a env mem mid mem' b final mem'' ha hb iha ihb =>
    apply Reaches.cons _ _ _ rfl
    exact Reaches.trans _ _ _ (iha (2 * path) (.cmd b (2 * path + 1) :: rest))
      (ihb (2 * path + 1) rest)
  | assign hv =>
    refine ⟨1, ?_⟩
    simp [run, step, hv]
  | store hp hv ha hm =>
    refine ⟨1, ?_⟩
    simp [run, step, hp, hv, ha, hm]
  | if_zero hc h ih =>
    refine Reaches.cons _ _ _ ?_ (ih (2 * path + 1) rest)
    simp [step, hc]
  | if_nonzero hc hv h ih =>
    refine Reaches.cons _ _ _ ?_ (ih (2 * path) rest)
    simp only [step, hc, bind, Option.bind, ite_eq_right hv]
  | while_zero hc =>
    refine ⟨1, ?_⟩
    simp [run, step, hc]
  | @while_nonzero v body env mem mid mem' type cond final mem'' hc hv first last ihf ihl =>
    refine Reaches.cons _ ⟨.mark path :: .cmd body (2 * path) ::
      .cmd (.while cond body) path :: rest, env, mem⟩ _ ?_ (Reaches.cons _ _ _ rfl
      (Reaches.trans _ _ _ (ihf (2 * path) (.cmd (.while cond body) path :: rest))
        (ihl path rest)))
    simp only [step, hc, bind, Option.bind, ite_eq_right hv]

def Finishes (s : State ctx) (final : Env ctx) (mem : Memory) : Prop :=
  Reaches s ⟨[], final, mem⟩

theorem function_finishes (fn : Function params vars type) (args : Env params)
    (mem mem' : Memory) (v : Word) (h : fn.Evaluates args mem v mem') :
    ∃ final, Finishes ⟨[.cmd fn.body 1], initial args, mem⟩ final mem' ∧
      fn.returns.eval final mem' = some v := by
  obtain ⟨final, he, hv⟩ := h
  exact ⟨final, of_exec he 1 [], hv⟩

def weight : Cmd ctx → Nat
  | .skip | .assign _ _ | .store _ _ _ | .while _ _ => 1
  | .seq a b => 1 + weight a + weight b
  | .ite _ a b => 1 + max (weight a) (weight b)

def stackWeight : List (Frame ctx) → Nat
  | [] | .mark _ :: _ => 0
  | .cmd c _ :: rest => weight c + stackWeight rest

def IsCut (s : State ctx) : Bool :=
  match s.stack with
  | [] | .mark _ :: _ => true
  | _ => false

theorem weight_decreases (s t : State ctx) (hc : IsCut s = false) (h : step s = some t) :
    stackWeight t.stack < stackWeight s.stack := by
  rcases s with ⟨stack, env, mem⟩
  cases stack with
  | nil => cases hc
  | cons frame rest =>
    cases frame with
    | mark => cases hc
    | cmd cmd path =>
      cases cmd with
      | skip => cases h; simp [stackWeight, weight]
      | seq a b => cases h; simp [stackWeight, weight]; omega
      | assign dst value =>
        simp only [step] at h
        cases he : value.eval env mem with
        | none => simp [he] at h
        | some v =>
          simp only [he, bind, Option.bind, Option.some.injEq] at h
          cases h
          simp [stackWeight, weight]
      | store f ptr value =>
        simp only [step] at h
        cases hp : ptr.eval env mem with
        | none => simp [hp] at h
        | some p =>
          simp only [hp, bind, Option.bind] at h
          cases hv : value.eval env mem with
          | none => simp [hv] at h
          | some v =>
            simp only [hv, bind, Option.bind] at h
            split at h
            next ha =>
              cases hm : mem (p.toNat + 8 * f.index.val) with
              | none => simp [hm] at h
              | some old =>
                simp only [hm, bind, Option.bind, Option.some.injEq] at h
                cases h
                simp [stackWeight, weight]
            next => contradiction
      | ite cond yes no =>
        simp only [step] at h
        cases he : cond.eval env mem with
        | none => simp [he] at h
        | some v =>
          simp only [he, bind, Option.bind, Option.some.injEq] at h
          cases h
          split <;> simp [stackWeight, weight] <;> omega
      | «while» cond body =>
        simp only [step] at h
        cases he : cond.eval env mem with
        | none => simp [he] at h
        | some v =>
          simp only [he, bind, Option.bind, Option.some.injEq] at h
          cases h
          split <;> simp [stackWeight, weight] <;> omega

/-- Stop at the next marker or return. Structural descent, rather than an
execution-fuel assumption, guarantees that the segment itself is finite. -/
def untilCut (s : State ctx) : Option (Nat × State ctx) :=
  if hc : IsCut s then some (0, s)
  else match ht : step s with
    | none => none
    | some t => do
      let (n, final) ← untilCut t
      some (n + 1, final)
termination_by stackWeight s.stack
decreasing_by exact weight_decreases s t (by simpa using hc) ht

def chunk (s : State ctx) : Option (Nat × State ctx) := do
  let t ← step s
  let (n, final) ← untilCut t
  some (n + 1, final)

theorem untilCut_eq (s : State ctx) :
    untilCut s = if IsCut s then some (0, s) else
      (step s).bind (fun t => (untilCut t).bind (fun (n, final) => some (n + 1, final))) := by
  rw [untilCut]
  split
  · rfl
  · split <;> simp_all only [Option.bind_none, Option.bind_some] <;> rfl

theorem untilCut_nil (env : Env ctx) (mem : Memory) :
    untilCut ⟨[], env, mem⟩ = some (0, ⟨[], env, mem⟩) := by
  rw [untilCut_eq]; rfl

theorem untilCut_mark (path : Nat) (rest : List (Frame ctx)) (env : Env ctx) (mem : Memory) :
    untilCut ⟨.mark path :: rest, env, mem⟩ = some (0, ⟨.mark path :: rest, env, mem⟩) := by
  rw [untilCut_eq]; rfl

theorem untilCut_cmd (cmd : Cmd ctx) (path : Nat) (rest : List (Frame ctx))
    (env : Env ctx) (mem : Memory) :
    untilCut ⟨.cmd cmd path :: rest, env, mem⟩ =
      (step ⟨.cmd cmd path :: rest, env, mem⟩).bind
        (fun t => (untilCut t).bind (fun (n, final) => some (n + 1, final))) := by
  rw [untilCut_eq]; rfl

theorem untilCut_complete (n : Nat) (s final : State ctx)
    (hf : final.stack = []) (h : run n s = some final) :
    ∃ k t, untilCut s = some (k, t) ∧ k ≤ n ∧ run k s = some t ∧
      IsCut t = true ∧ run (n - k) t = some final := by
  induction n generalizing s with
  | zero =>
    cases h
    refine ⟨0, final, ?_, Nat.le_refl _, rfl, ?_, rfl⟩
    · rw [untilCut]; simp [IsCut, hf]
    · simp [IsCut, hf]
  | succ n ih =>
    by_cases hc : IsCut s = true
    · exact ⟨0, s, by rw [untilCut]; simp [hc], by omega, rfl, hc, h⟩
    · have hc' : IsCut s = false := by simpa using hc
      simp only [run] at h
      cases hs : step s with
      | none => simp [hs] at h
      | some next =>
        simp only [hs, Option.bind_some] at h
        obtain ⟨k, t, hu, hk, hr, hcut, hrest⟩ := ih next h
        refine ⟨k + 1, t, ?_, by omega, ?_, hcut, ?_⟩
        · rw [untilCut]
          simp only [hc', Bool.false_eq_true, ↓reduceDIte]
          split
          next he => simp_all
          next t' he =>
            have ht : t' = next := Option.some.inj (he.symm.trans hs)
            subst t'
            simp only [hu, bind, Option.bind]
        · simp only [run, hs, Option.bind_some, hr]
        · simpa using hrest

theorem chunk_complete (n : Nat) (s final : State ctx)
    (hn : s.stack ≠ []) (hf : final.stack = []) (h : run n s = some final) :
    ∃ k t, chunk s = some (k, t) ∧ 0 < k ∧ k ≤ n ∧ run k s = some t ∧
      IsCut t = true ∧ run (n - k) t = some final := by
  cases n with
  | zero => cases h; contradiction
  | succ n =>
    simp only [run] at h
    cases hs : step s with
    | none => simp [hs] at h
    | some next =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨k, t, hu, hk, hr, hcut, hrest⟩ := untilCut_complete n next final hf h
      refine ⟨k + 1, t, ?_, by omega, by omega, ?_, hcut, ?_⟩
      · simp [chunk, hs, hu]
      · simp [run, hs, hr]
      · simpa using hrest

end Riscvc.Heap.Control
