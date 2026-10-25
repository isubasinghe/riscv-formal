import Riscvc.Heap.Examples

namespace Riscvc.Heap.AppendProof

open Examples

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Ghost nodes record addresses and payloads; they are never emitted. -/
abbrev Nodes := List (Word × Word)

def head : Nodes → Word
  | [] => 0
  | (p, _) :: _ => p

def footprint : Nodes → List Nat
  | [] => []
  | (p, _) :: rest => p.toNat :: (p.toNat + 8) :: footprint rest

/-- A null-terminated list with specified node identities and values. Pairwise
disjoint cells are a separate ownership condition, used by `append_correct`. -/
def ListRep (mem : Memory) : Nodes → Prop
  | [] => True
  | (p, v) :: rest => Accessible p 8 ∧ mem p.toNat = some v ∧
      mem (p.toNat + 8) = some (head rest) ∧ ListRep mem rest

/-- The sole heap change is to the last node's next field. -/
def link (mem : Memory) : Nodes → Word → Memory
  | [], _ => mem
  | [(p, _)], suffix => mem.write (p.toNat + 8) suffix
  | _ :: q :: rest, suffix => link mem (q :: rest) suffix

theorem link_frame (mem : Memory) (xs : Nodes) (suffix : Word) (a : Nat)
    (h : a ∉ footprint xs) : link mem xs suffix a = mem a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨p, v⟩
      cases xs with
      | nil =>
          apply Memory.write_other
          intro eq
          apply h
          simp [footprint, eq]
      | cons q rest =>
          apply ih
          intro ha
          apply h
          simp only [footprint, List.mem_cons] at *
          exact Or.inr (Or.inr ha)

theorem rep_frame (mem other : Memory) (xs : Nodes)
    (agree : ∀ a ∈ footprint xs, other a = mem a) (h : ListRep mem xs) : ListRep other xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      rcases x with ⟨p, v⟩
      exact ⟨h.1, (agree _ (by simp [footprint])).trans h.2.1,
        (agree _ (by simp [footprint])).trans h.2.2.1,
        ih (fun a ha => agree a (by simp [footprint, ha])) h.2.2.2⟩

theorem footprint_append (xs ys : Nodes) : footprint (xs ++ ys) = footprint xs ++ footprint ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨p, v⟩; simp [footprint, ih]

theorem link_correct (mem : Memory) (xs ys : Nodes)
    (hx : ListRep mem xs) (hy : ListRep mem ys)
    (owned : (footprint xs ++ footprint ys).Nodup) :
    ListRep (link mem xs (head ys)) (xs ++ ys) := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
      rcases x with ⟨p, v⟩
      have own : p.toNat ∉ (p.toNat + 8) :: (footprint xs ++ footprint ys) ∧
          (p.toNat + 8) ∉ (footprint xs ++ footprint ys) ∧
          (footprint xs ++ footprint ys).Nodup := by simpa [footprint] using owned
      cases xs with
      | nil =>
          refine ⟨hx.1, ?_, ?_, ?_⟩
          · simpa [link, Memory.write] using hx.2.1
          · simp [link, Memory.write]
          · apply rep_frame mem _ ys _ hy
            intro a ha
            apply Memory.write_other
            intro eq
            subst a
            exact own.2.1 (by simp [footprint, ha])
      | cons q rest =>
          have ih' := ih hx.2.2.2 own.2.2
          refine ⟨hx.1, ?_, ?_, ih'⟩
          · rw [show link mem ((p, v) :: q :: rest) (head ys) =
                link mem (q :: rest) (head ys) from rfl,
                link_frame mem (q :: rest) (head ys) p.toNat (by intro ha; exact own.1 (by simp [ha]))]
            exact hx.2.1
          · rw [show link mem ((p, v) :: q :: rest) (head ys) =
                link mem (q :: rest) (head ys) from rfl,
                link_frame mem (q :: rest) (head ys) (p.toNat + 8) (by intro ha; exact own.2.1 (by simp [ha]))]
            exact hx.2.2.1

abbrev Ctx : Context := [.ptr Node.name, .ptr Node.name, .ptr Node.name, .ptr Node.name]
def vx : Var Ctx (.ptr Node.name) := ⟨0, rfl⟩
def vy : Var Ctx (.ptr Node.name) := ⟨1, rfl⟩
def vc : Var Ctx (.ptr Node.name) := ⟨2, rfl⟩
def vn : Var Ctx (.ptr Node.name) := ⟨3, rfl⟩

def state (x y c n : Word) : Env Ctx := fun i =>
  match i.val with | 0 => x | 1 => y | 2 => c | _ => n

theorem set_cur (x y c n v : Word) : (state x y c n).set vc.index v = state x y v n := by
  funext ⟨i, hi⟩
  change i < 4 at hi
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | i + 4 => omega

theorem set_next (x y c n v : Word) : (state x y c n).set vn.index v = state x y c v := by
  funext ⟨i, hi⟩
  change i < 4 at hi
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | i + 4 => omega

def scanBody : Cmd Ctx := .seq (.assign vc (.var vn))
  (.seq (.assign vn (.field Node.next (.var vc))) .skip)
def scan : Cmd Ctx := .while (.var vn) scanBody

def last : Nodes → Word
  | [] => 0
  | [(p, _)] => p
  | _ :: q :: rest => last (q :: rest)

theorem scan_correct (mem : Memory) (p v x y : Word) (rest : Nodes)
    (h : ListRep mem ((p, v) :: rest)) :
    Exec scan (state x y p (head rest)) mem
      (state x y (last ((p, v) :: rest)) 0) mem := by
  induction rest generalizing p v with
  | nil => exact Exec.while_zero rfl
  | cons q rest ih =>
      rcases q with ⟨q, w⟩
      have hq := h.2.2.2
      apply Exec.while_nonzero (v := q) rfl hq.1.1
      · apply Exec.seq (Exec.assign rfl)
        rw [set_cur]
        apply Exec.seq
        · apply Exec.assign (v := head rest)
          change (if Accessible q 8 then mem (q.toNat + 8) else none) = some (head rest)
          simp [hq.1, hq.2.2.1]
        · exact Exec.skip
      · rw [set_next]
        exact ih q w hq

theorem last_access (mem : Memory) (p v : Word) (rest : Nodes)
    (h : ListRep mem ((p, v) :: rest)) :
    Accessible (last ((p, v) :: rest)) 8 ∧
    mem ((last ((p, v) :: rest)).toNat + 8) = some 0 := by
  induction rest generalizing p v with
  | nil => exact ⟨h.1, h.2.2.1⟩
  | cons q rest ih => exact ih q.1 q.2 h.2.2.2

theorem link_last (mem : Memory) (p v : Word) (rest : Nodes) (suffix : Word) :
    link mem ((p, v) :: rest) suffix = mem.write ((last ((p, v) :: rest)).toNat + 8) suffix := by
  induction rest generalizing p v with
  | nil => rfl
  | cons q rest ih => exact ih q.1 q.2

/-- Total correctness of the actual quoted DSL program, for lists of arbitrary
length. Its proof follows the remaining list, not a numeric pointer measure. -/
theorem append_exec (mem : Memory) (xs ys : Nodes) (hx : ListRep mem xs) :
    append.Evaluates (fun i => if i.val = 0 then head xs else head ys) mem
      (head (xs ++ ys)) (link mem xs (head ys)) := by
  have init : initial (params := [.ptr Node.name, .ptr Node.name]) («locals» := [.ptr Node.name, .ptr Node.name])
      (fun i : Fin 2 => if i.val = 0 then head xs else head ys) = state (head xs) (head ys) 0 0 := by
    funext ⟨i, hi⟩
    change i < 4 at hi
    match i with
    | 0 | 1 | 2 | 3 => rfl
    | i + 4 => omega
  unfold Function.Evaluates
  erw [init]
  cases xs with
  | nil =>
      refine ⟨state 0 (head ys) 0 0, ?_, ?_⟩
      · apply Exec.seq (Exec.assign rfl)
        erw [show (state 0 (head ys) 0 0).set vc.index 0 = state 0 (head ys) 0 0 from set_cur ..]
        exact Exec.seq (Exec.if_zero rfl Exec.skip) Exec.skip
      · rfl
  | cons x xs =>
      rcases x with ⟨p, v⟩
      let endState := state p (head ys) (last ((p, v) :: xs)) 0
      refine ⟨endState, ?_, ?_⟩
      · apply Exec.seq (Exec.assign rfl)
        erw [show (state p (head ys) 0 0).set vc.index p = state p (head ys) p 0 from set_cur ..]
        apply Exec.seq (mid := endState) (mem' := link mem ((p, v) :: xs) (head ys))
        · apply Exec.if_nonzero (v := p) rfl hx.1.1
          apply Exec.seq
          · apply Exec.assign (v := head xs)
            change (if Accessible p 8 then mem (p.toNat + 8) else none) = some (head xs)
            simp [hx.1, hx.2.2.1]
          · erw [show (state p (head ys) p 0).set vn.index (head xs) =
                state p (head ys) p (head xs) from set_next ..]
            apply Exec.seq (scan_correct mem p v p (head ys) xs hx)
            erw [link_last]
            exact Exec.seq (Exec.store rfl rfl (last_access mem p v xs hx).1
              (last_access mem p v xs hx).2) Exec.skip
        · exact Exec.skip
      · change (if p = 0 then some (head ys) else some p) = some p
        have hp : p ≠ 0 := hx.1.1
        exact ite_eq_right hp

/-- The input lists' cells are owned exclusively. The output has the same node
identities and payloads in concatenation order; all other memory is unchanged. -/
theorem append_correct (mem : Memory) (xs ys : Nodes)
    (hx : ListRep mem xs) (hy : ListRep mem ys)
    (owned : (footprint xs ++ footprint ys).Nodup) :
    ∃ after, append.Evaluates (fun i => if i.val = 0 then head xs else head ys) mem
      (head (xs ++ ys)) after ∧ ListRep after (xs ++ ys) ∧
      ∀ a, a ∉ footprint xs → after a = mem a := by
  exact ⟨link mem xs (head ys), append_exec mem xs ys hx,
    link_correct mem xs ys hx hy owned, fun a ha => link_frame mem xs (head ys) a ha⟩

end Riscvc.Heap.AppendProof
