import Std

/-! A deliberately small ELF64 loader for static little-endian RISC-V executables.
The certificate contains the entire file. Neither objdump nor the Python driver
chooses the instruction bytes used by the proof: this loader does that in Lean.
-/
namespace Riscvc.Binary.ELF

abbrev Bytes := Array UInt8

def readLE (bytes : Bytes) (offset width : Nat) : Option Nat := do
  if offset + width > bytes.size then none else
    some ((List.range width).foldl
      (fun acc i => acc + bytes[offset + i]!.toNat * 256 ^ i) 0)

structure Segment where
  offset : Nat
  address : Nat
  fileSize : Nat
  memorySize : Nat
  flags : Nat
  deriving Repr, DecidableEq

structure Image where
  bytes : Bytes
  entry : Nat
  segments : List Segment
  deriving Repr

private def readSegment (bytes : Bytes) (header : Nat) : Option Segment := do
  let flags ← readLE bytes (header + 4) 4
  let offset ← readLE bytes (header + 8) 8
  let address ← readLE bytes (header + 16) 8
  let fileSize ← readLE bytes (header + 32) 8
  let memorySize ← readLE bytes (header + 40) 8
  if fileSize > memorySize || offset + fileSize > bytes.size ||
      address + memorySize > 2^64 then none
  else some ⟨offset, address, fileSize, memorySize, flags⟩

private def disjoint (a b : Segment) : Bool :=
  a.address + a.memorySize ≤ b.address || b.address + b.memorySize ≤ a.address

/-- Reject dynamic linking, malformed/truncated headers, and overlapping loads. -/
def parse (bytes : Bytes) : Option Image := do
  if (← readLE bytes 0 7) != 0x010102464c457f then none else do
  if (← readLE bytes 16 2) != 2 || (← readLE bytes 18 2) != 243 ||
      (← readLE bytes 20 4) != 1 || (← readLE bytes 48 4) != 0 ||
      (← readLE bytes 52 2) != 64 || (← readLE bytes 54 2) != 56 then none else do
  let entry ← readLE bytes 24 8
  let phoff ← readLE bytes 32 8
  let phnum ← readLE bytes 56 2
  if phoff < 64 || phoff + 56 * phnum > bytes.size then none else do
  let mut segments := []
  for i in List.range phnum do
    let header := phoff + 56 * i
    let kind ← readLE bytes header 4
    if kind == 2 || kind == 3 then none else do
    if kind == 1 then
      let segment ← readSegment bytes header
      if !segments.all (disjoint segment) then none else
        segments := segments ++ [segment]
  if entry % 4 != 0 then none else some ⟨bytes, entry, segments⟩

/-- Instruction fetch from the executable, file-backed part of a load segment.
Zero-filled data and non-executable segments are intentionally not executable. -/
def Image.fetchByte (image : Image) (address : Nat) : Option UInt8 := do
  let segment ← image.segments.find? fun s =>
    s.flags % 2 == 1 && s.address ≤ address && address < s.address + s.fileSize
  image.bytes[segment.offset + address - segment.address]?

def Image.fetchWord (image : Image) (address : Nat) : Option (BitVec 32) := do
  if address % 4 != 0 then none else do
  let b0 ← image.fetchByte address
  let b1 ← image.fetchByte (address + 1)
  let b2 ← image.fetchByte (address + 2)
  let b3 ← image.fetchByte (address + 3)
  some (BitVec.ofNat 32
    (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216))

/-- A code certificate is checked against the loaded entry point, not a text
disassembly or an externally supplied file offset. -/
def entryWords (bytes : Bytes) (count : Nat) : Option (Nat × List (BitVec 32)) := do
  let image ← parse bytes
  let words ← (List.range count).mapM fun i => image.fetchWord (image.entry + 4 * i)
  some (image.entry, words)

end Riscvc.Binary.ELF
