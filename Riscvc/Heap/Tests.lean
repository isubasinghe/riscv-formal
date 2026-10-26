import examples.proof.AppendProof

namespace Riscvc.Heap.Tests

open Examples AppendProof

/-- info: 'Riscvc.Heap.AppendProof.append_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Riscvc.Heap.AppendProof.append_correct

private def expect (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"heap DSL: {label}")

private def allocated (nodes : Nodes) (suffix : Word := 0) : Memory :=
  match nodes with
  | [] => fun _ => none
  | (p, v) :: rest =>
      let tail := allocated rest suffix
      (tail.write p.toNat v).write (p.toNat + 8) (if rest.isEmpty then suffix else head rest)

private def combine (a b : Memory) : Memory := fun p => (a p).or (b p)

def check : IO Unit := do
  for n in [:8] do
    for m in [:8] do
      -- Interleaved, descending addresses exercise actual links rather than
      -- relying on adjacency or pointer ordering for termination.
      let xs : Nodes := (List.range n).map fun i => (BitVec.ofNat 64 (4096 + 32 * (8-i)), BitVec.ofNat 64 i)
      let ys : Nodes := (List.range m).map fun i => (BitVec.ofNat 64 (4112 + 32 * (8-i)), BitVec.ofNat 64 (100+i))
      let before := (combine (allocated xs) (allocated ys)).write 8192 0x12345678
      let result := append.run 100 (fun i => if i.val = 0 then head xs else head ys) before
      let .ok (p, after) := result | throw (IO.userError "append interpreter failed")
      expect "returned head" (p == head (xs ++ ys))
      let mut cursor := p
      for (address, value) in xs ++ ys do
        expect "node identity" (cursor == address)
        expect "payload preservation" (after cursor.toNat == some value)
        let some next := after (cursor.toNat + 8) | throw (IO.userError "missing next cell")
        cursor := next
      expect "null termination" (cursor == 0)
      expect "unrelated memory" (after 8192 == some 0x12345678)
      for address in footprint ys do
        expect "second list unchanged" (after address == before address)
  let empty : Memory := fun _ => none
  let .ok (v, _) := headOrZero.run 10 (fun _ => 0) empty |
    throw (IO.userError "guarded null dereference")
  expect "lazy conditional" (v == 0)
  match setValue.run 10 (fun i => if i.val = 0 then 4096 else 7) empty with
  | .error .invalidAccess => pure ()
  | _ => throw (IO.userError "unmapped write was not rejected")
  let mapped := (empty.write 4096 9).write 4104 0
  for invalid in [0, 4097, 0xfffffffffffffff8] do
    match append.run 20 (fun i => if i.val = 0 then invalid else 0) mapped with
    | .error .invalidAccess => expect "null is a valid empty list" (invalid != 0)
    | .ok _ => expect "invalid pointer accepted" (invalid == 0)
    | _ => throw (IO.userError "unexpected fuel exhaustion")
  let cycle := mapped.write 4104 4096
  match append.run 20 (fun i => if i.val = 0 then 4096 else 0) cycle with
  | .error .fuelExhausted => pure ()
  | _ => throw (IO.userError "cyclic list terminated unexpectedly")
  IO.println "Heap DSL: append contents, identity, frame, faults, and loop checks passed."

end Riscvc.Heap.Tests
