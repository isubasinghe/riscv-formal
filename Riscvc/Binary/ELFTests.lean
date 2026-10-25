import Riscvc.Binary.ELF

namespace Riscvc.Binary.ELF.Tests

private def put (b : Bytes) (offset value width : Nat) : Bytes :=
  (List.range width).foldl (fun b i => b.set! (offset + i) (UInt8.ofNat (value / 256^i))) b

private def fixture : Bytes := Id.run do
  let mut b := Array.replicate 128 0
  for (offset, value, width) in [
      (0, 0x010102464c457f, 7), (16, 2, 2), (18, 243, 2), (20, 1, 4),
      (24, 0x1000, 8), (32, 64, 8), (52, 64, 2), (54, 56, 2), (56, 1, 2),
      (64, 1, 4), (68, 5, 4), (72, 120, 8), (80, 0x1000, 8),
      (96, 8, 8), (104, 8, 8), (120, 0x00a58533, 4), (124, 0x00008067, 4)] do
    b := put b offset value width
  return b

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

example : entryWords fixture 2 = some (0x1000, [0x00a58533, 0x00008067]) := by decide
example : entryWords (fixture.set! 0 0) 2 = none := by decide
example : entryWords (fixture.set! 5 2) 2 = none := by decide -- big endian
example : entryWords (fixture.set! 18 62) 2 = none := by decide -- wrong ISA
example : entryWords (fixture.set! 16 3) 2 = none := by decide -- shared object
example : entryWords (fixture.set! 48 1) 2 = none := by decide -- compressed ABI
example : entryWords (fixture.set! 68 4) 2 = none := by decide -- no execute permission
example : entryWords (fixture.set! 64 3) 2 = none := by decide -- PT_INTERP
example : entryWords (fixture.set! 96 9) 2 = none := by decide -- filesz > memsz
example : entryWords (fixture.set! 72 121) 2 = none := by decide -- truncated segment
example : entryWords (fixture.set! 24 1) 2 = none := by decide -- unaligned entry
example : entryWords (fixture.set! 120 0xff) 2 ≠ entryWords fixture 2 := by decide

end Riscvc.Binary.ELF.Tests
