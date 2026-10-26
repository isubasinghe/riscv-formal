import examples.Scheduler
import Riscvc.Binary.WordMachine
import Riscvc.Heap.Control

/-! The exact optimized scheduler instruction sequence. Its addresses, words,
and Sail instructions are checked against the ELF by the lifting certificate.
Source continuations below select subterms of the quoted DSL itself. -/
namespace Riscvc.Heap.Scheduler.StepProof

open Riscvc.Binary

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def instructions : List (Word × BitVec 32 × WordMachine.Op) := [
  (0x80000000, 0xfff58713, .addi .a4 (.reg .a1) 4095),
  (0x80000004, 0x00173713, .sltiu .a4 (.reg .a4) 1),
  (0x80000008, 0x00c037b3, .sltu .a5 .zero (.reg .a2)),
  (0x8000000c, 0x00f77733, .and .a4 (.reg .a4) (.reg .a5)),
  (0x80000010, 0x00d037b3, .sltu .a5 .zero (.reg .a3)),
  (0x80000014, 0x00f777b3, .and .a5 (.reg .a4) (.reg .a5)),
  (0x80000018, 0x00100713, .addi .a4 .zero 1),
  (0x8000001c, 0x08078063, .branch true (.reg .a5) .zero 128),
  (0x80000020, 0x00053703, .load .a4 (.reg .a0) 0),
  (0x80000024, 0x02070a63, .branch true (.reg .a4) .zero 52),
  (0x80000028, 0x00000813, .addi .a6 .zero 0),
  (0x8000002c, 0x0100006f, .jump 16),
  (0x80000030, 0x01073703, .load .a4 (.reg .a4) 16),
  (0x80000034, 0x00078813, .addi .a6 (.reg .a5) 0),
  (0x80000038, 0x00070c63, .branch true (.reg .a4) .zero 24),
  (0x8000003c, 0x00073883, .load .a7 (.reg .a4) 0),
  (0x80000040, 0x00100793, .addi .a5 .zero 1),
  (0x80000044, 0xfec886e3, .branch true (.reg .a7) (.reg .a2) 8172),
  (0x80000048, 0x00080793, .addi .a5 (.reg .a6) 0),
  (0x8000004c, 0xfe5ff06f, .jump 2097124),
  (0x80000050, 0x00200713, .addi .a4 .zero 2),
  (0x80000054, 0x04079463, .branch false (.reg .a5) .zero 72),
  (0x80000058, 0x01053783, .load .a5 (.reg .a0) 16),
  (0x8000005c, 0x0c078a63, .branch true (.reg .a5) .zero 212),
  (0x80000060, 0x0107b703, .load .a4 (.reg .a5) 16),
  (0x80000064, 0x00e53823, .store (.reg .a0) (.reg .a4) 16),
  (0x80000068, 0x00c7b023, .store (.reg .a5) (.reg .a2) 0),
  (0x8000006c, 0x00d7b423, .store (.reg .a5) (.reg .a3) 8),
  (0x80000070, 0x0007b823, .store (.reg .a5) .zero 16),
  (0x80000074, 0x00853703, .load .a4 (.reg .a0) 8),
  (0x80000078, 0x00050693, .addi .a3 (.reg .a0) 0),
  (0x8000007c, 0x00070463, .branch true (.reg .a4) .zero 8),
  (0x80000080, 0x01070693, .addi .a3 (.reg .a4) 16),
  (0x80000084, 0x00f6b023, .store (.reg .a3) (.reg .a5) 0),
  (0x80000088, 0x01853683, .load .a3 (.reg .a0) 24),
  (0x8000008c, 0x00000713, .addi .a4 .zero 0),
  (0x80000090, 0x00f53423, .store (.reg .a0) (.reg .a5) 8),
  (0x80000094, 0x00168693, .addi .a3 (.reg .a3) 1),
  (0x80000098, 0x00d53c23, .store (.reg .a0) (.reg .a3) 24),
  (0x8000009c, 0x00200693, .addi .a3 .zero 2),
  (0x800000a0, 0x08d59e63, .branch false (.reg .a1) (.reg .a3) 156),
  (0x800000a4, 0x00053683, .load .a3 (.reg .a0) 0),
  (0x800000a8, 0x00068a63, .branch true (.reg .a3) .zero 20),
  (0x800000ac, 0x0006b703, .load .a4 (.reg .a3) 0),
  (0x800000b0, 0x00c71a63, .branch false (.reg .a4) (.reg .a2) 20),
  (0x800000b4, 0x00000713, .addi .a4 .zero 0),
  (0x800000b8, 0x0280006f, .jump 40),
  (0x800000bc, 0x00400513, .addi .a0 .zero 4),
  (0x800000c0, 0x00008067, .ret),
  (0x800000c4, 0x00068793, .addi .a5 (.reg .a3) 0),
  (0x800000c8, 0x0107b683, .load .a3 (.reg .a5) 16),
  (0x800000cc, 0x10068063, .branch true (.reg .a3) .zero 256),
  (0x800000d0, 0x0006b803, .load .a6 (.reg .a3) 0),
  (0x800000d4, 0x00078713, .addi .a4 (.reg .a5) 0),
  (0x800000d8, 0x00068793, .addi .a5 (.reg .a3) 0),
  (0x800000dc, 0xfec816e3, .branch false (.reg .a6) (.reg .a2) 8172),
  (0x800000e0, 0x0106b603, .load .a2 (.reg .a3) 16),
  (0x800000e4, 0x00050793, .addi .a5 (.reg .a0) 0),
  (0x800000e8, 0x00070463, .branch true (.reg .a4) .zero 8),
  (0x800000ec, 0x01070793, .addi .a5 (.reg .a4) 16),
  (0x800000f0, 0x00c7b023, .store (.reg .a5) (.reg .a2) 0),
  (0x800000f4, 0x00853603, .load .a2 (.reg .a0) 8),
  (0x800000f8, 0x00d61463, .branch false (.reg .a2) (.reg .a3) 8),
  (0x800000fc, 0x00e53423, .store (.reg .a0) (.reg .a4) 8),
  (0x80000100, 0x0006b423, .store (.reg .a3) .zero 8),
  (0x80000104, 0x0006b023, .store (.reg .a3) .zero 0),
  (0x80000108, 0x01053603, .load .a2 (.reg .a0) 16),
  (0x8000010c, 0x00c6b823, .store (.reg .a3) (.reg .a2) 16),
  (0x80000110, 0x01853603, .load .a2 (.reg .a0) 24),
  (0x80000114, 0x00000713, .addi .a4 .zero 0),
  (0x80000118, 0x00d53823, .store (.reg .a0) (.reg .a3) 16),
  (0x8000011c, 0xfff60613, .addi .a2 (.reg .a2) 4095),
  (0x80000120, 0x00c53c23, .store (.reg .a0) (.reg .a2) 24),
  (0x80000124, 0x00300613, .addi .a2 .zero 3),
  (0x80000128, 0x00c58e63, .branch true (.reg .a1) (.reg .a2) 28),
  (0x8000012c, 0x0ac0006f, .jump 172),
  (0x80000130, 0x00300713, .addi .a4 .zero 3),
  (0x80000134, 0x00200693, .addi .a3 .zero 2),
  (0x80000138, 0xf6d586e3, .branch true (.reg .a1) (.reg .a3) 8044),
  (0x8000013c, 0x00300613, .addi .a2 .zero 3),
  (0x80000140, 0x08c59c63, .branch false (.reg .a1) (.reg .a2) 152),
  (0x80000144, 0x00053583, .load .a1 (.reg .a0) 0),
  (0x80000148, 0x04058663, .branch true (.reg .a1) .zero 76),
  (0x8000014c, 0x0005b603, .load .a2 (.reg .a1) 0),
  (0x80000150, 0x02053683, .load .a3 (.reg .a0) 32),
  (0x80000154, 0x02c53423, .store (.reg .a0) (.reg .a2) 40),
  (0x80000158, 0x00168613, .addi .a2 (.reg .a3) 1),
  (0x8000015c, 0x02c53023, .store (.reg .a0) (.reg .a2) 32),
  (0x80000160, 0x0085b683, .load .a3 (.reg .a1) 8),
  (0x80000164, 0x0105b603, .load .a2 (.reg .a1) 16),
  (0x80000168, 0xfff68693, .addi .a3 (.reg .a3) 4095),
  (0x8000016c, 0x00d5b423, .store (.reg .a1) (.reg .a3) 8),
  (0x80000170, 0x02068663, .branch true (.reg .a3) .zero 44),
  (0x80000174, 0x06060663, .branch true (.reg .a2) .zero 108),
  (0x80000178, 0x00853683, .load .a3 (.reg .a0) 8),
  (0x8000017c, 0x00c53023, .store (.reg .a0) (.reg .a2) 0),
  (0x80000180, 0x00b6b823, .store (.reg .a3) (.reg .a1) 16),
  (0x80000184, 0x0005b823, .store (.reg .a1) .zero 16),
  (0x80000188, 0x00b53423, .store (.reg .a0) (.reg .a1) 8),
  (0x8000018c, 0x00000513, .addi .a0 .zero 0),
  (0x80000190, 0x00008067, .ret),
  (0x80000194, 0x00500513, .addi .a0 .zero 5),
  (0x80000198, 0x00008067, .ret),
  (0x8000019c, 0x00c53023, .store (.reg .a0) (.reg .a2) 0),
  (0x800001a0, 0x00061463, .branch false (.reg .a2) .zero 8),
  (0x800001a4, 0x00053423, .store (.reg .a0) .zero 8),
  (0x800001a8, 0x0005b023, .store (.reg .a1) .zero 0),
  (0x800001ac, 0x01053603, .load .a2 (.reg .a0) 16),
  (0x800001b0, 0x00c5b823, .store (.reg .a1) (.reg .a2) 16),
  (0x800001b4, 0x01853603, .load .a2 (.reg .a0) 24),
  (0x800001b8, 0x00000713, .addi .a4 .zero 0),
  (0x800001bc, 0x00b53823, .store (.reg .a0) (.reg .a1) 16),
  (0x800001c0, 0xfff60593, .addi .a1 (.reg .a2) 4095),
  (0x800001c4, 0x00b53c23, .store (.reg .a0) (.reg .a1) 24),
  (0x800001c8, 0x0100006f, .jump 16),
  (0x800001cc, 0x00400713, .addi .a4 .zero 4),
  (0x800001d0, 0x00300613, .addi .a2 .zero 3),
  (0x800001d4, 0xf6c588e3, .branch true (.reg .a1) (.reg .a2) 8048),
  (0x800001d8, 0x00070513, .addi .a0 (.reg .a4) 0),
  (0x800001dc, 0x00008067, .ret),
  (0x800001e0, 0x00000513, .addi .a0 .zero 0),
  (0x800001e4, 0x00008067, .ret)]

def program : WordMachine.Program := instructions.map fun (pc, bits, op) =>
  (⟨pc, bits, op.instruction⟩, op)

theorem program_valid : program.Valid := by
  intro pair hp
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem instruction0 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000000, rs, mem⟩ =
      some ⟨0x80000004, rs.put .a4 (rs .a1 + 18446744073709551615), mem⟩ := by rfl

theorem instruction1 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000004, rs, mem⟩ =
      (instructions[1]'(by decide)).2.2.eval ⟨0x80000004, rs, mem⟩ := by rfl

theorem instruction2 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000008, rs, mem⟩ =
      (instructions[2]'(by decide)).2.2.eval ⟨0x80000008, rs, mem⟩ := by rfl

theorem instruction3 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000000c, rs, mem⟩ =
      (instructions[3]'(by decide)).2.2.eval ⟨0x8000000c, rs, mem⟩ := by rfl

theorem instruction4 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000010, rs, mem⟩ =
      (instructions[4]'(by decide)).2.2.eval ⟨0x80000010, rs, mem⟩ := by rfl

theorem instruction5 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000014, rs, mem⟩ =
      (instructions[5]'(by decide)).2.2.eval ⟨0x80000014, rs, mem⟩ := by rfl

theorem instruction6 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000018, rs, mem⟩ =
      (instructions[6]'(by decide)).2.2.eval ⟨0x80000018, rs, mem⟩ := by rfl

theorem instruction7 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000001c, rs, mem⟩ =
      some ⟨if rs .a5 == 0 then 0x8000009c else 0x80000020, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a5) .zero 128).eval ⟨0x8000001c, rs, mem⟩ = _
  cases h : rs .a5 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction8 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000020, rs, mem⟩ =
      (instructions[8]'(by decide)).2.2.eval ⟨0x80000020, rs, mem⟩ := by rfl

theorem instruction9 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000024, rs, mem⟩ =
      some ⟨if rs .a4 == 0 then 0x80000058 else 0x80000028, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a4) .zero 52).eval ⟨0x80000024, rs, mem⟩ = _
  cases h : rs .a4 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction10 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000028, rs, mem⟩ =
      (instructions[10]'(by decide)).2.2.eval ⟨0x80000028, rs, mem⟩ := by rfl

theorem instruction11 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000002c, rs, mem⟩ =
      some ⟨0x8000003c, rs, mem⟩ := by
  change (WordMachine.Op.jump 16).eval ⟨0x8000002c, rs, mem⟩ = _
  simp only [WordMachine.Op.eval]
  change (if (0x8000003c : Word) &&& 3 = 0 then some (WordMachine.State.mk 0x8000003c rs mem) else none) = _
  exact ite_eq_left (by decide)

theorem instruction12 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000030, rs, mem⟩ =
      (instructions[12]'(by decide)).2.2.eval ⟨0x80000030, rs, mem⟩ := by rfl

theorem instruction13 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000034, rs, mem⟩ =
      (instructions[13]'(by decide)).2.2.eval ⟨0x80000034, rs, mem⟩ := by rfl

theorem instruction14 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000038, rs, mem⟩ =
      some ⟨if rs .a4 == 0 then 0x80000050 else 0x8000003c, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a4) .zero 24).eval ⟨0x80000038, rs, mem⟩ = _
  cases h : rs .a4 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction15 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000003c, rs, mem⟩ =
      (instructions[15]'(by decide)).2.2.eval ⟨0x8000003c, rs, mem⟩ := by rfl

theorem instruction16 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000040, rs, mem⟩ =
      (instructions[16]'(by decide)).2.2.eval ⟨0x80000040, rs, mem⟩ := by rfl

theorem instruction17 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000044, rs, mem⟩ =
      some ⟨if rs .a7 == rs .a2 then 0x80000030 else 0x80000048, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a7) (.reg .a2) 8172).eval ⟨0x80000044, rs, mem⟩ = _
  cases h : rs .a7 == rs .a2 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction18 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000048, rs, mem⟩ =
      (instructions[18]'(by decide)).2.2.eval ⟨0x80000048, rs, mem⟩ := by rfl

theorem instruction19 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000004c, rs, mem⟩ =
      some ⟨0x80000030, rs, mem⟩ := by
  change (WordMachine.Op.jump 2097124).eval ⟨0x8000004c, rs, mem⟩ = _
  simp only [WordMachine.Op.eval]
  change (if (0x80000030 : Word) &&& 3 = 0 then some (WordMachine.State.mk 0x80000030 rs mem) else none) = _
  exact ite_eq_left (by decide)

theorem instruction20 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000050, rs, mem⟩ =
      (instructions[20]'(by decide)).2.2.eval ⟨0x80000050, rs, mem⟩ := by rfl

theorem instruction21 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000054, rs, mem⟩ =
      some ⟨if rs .a5 == 0 then 0x80000058 else 0x8000009c, rs, mem⟩ := by
  change (WordMachine.Op.branch false (.reg .a5) .zero 72).eval ⟨0x80000054, rs, mem⟩ = _
  cases h : rs .a5 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction22 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000058, rs, mem⟩ =
      (instructions[22]'(by decide)).2.2.eval ⟨0x80000058, rs, mem⟩ := by rfl

theorem instruction23 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000005c, rs, mem⟩ =
      some ⟨if rs .a5 == 0 then 0x80000130 else 0x80000060, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a5) .zero 212).eval ⟨0x8000005c, rs, mem⟩ = _
  cases h : rs .a5 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction24 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000060, rs, mem⟩ =
      (instructions[24]'(by decide)).2.2.eval ⟨0x80000060, rs, mem⟩ := by rfl

theorem instruction25 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000064, rs, mem⟩ =
      (instructions[25]'(by decide)).2.2.eval ⟨0x80000064, rs, mem⟩ := by rfl

theorem instruction26 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000068, rs, mem⟩ =
      (instructions[26]'(by decide)).2.2.eval ⟨0x80000068, rs, mem⟩ := by rfl

theorem instruction27 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000006c, rs, mem⟩ =
      (instructions[27]'(by decide)).2.2.eval ⟨0x8000006c, rs, mem⟩ := by rfl

theorem instruction28 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000070, rs, mem⟩ =
      (instructions[28]'(by decide)).2.2.eval ⟨0x80000070, rs, mem⟩ := by rfl

theorem instruction29 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000074, rs, mem⟩ =
      (instructions[29]'(by decide)).2.2.eval ⟨0x80000074, rs, mem⟩ := by rfl

theorem instruction30 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000078, rs, mem⟩ =
      (instructions[30]'(by decide)).2.2.eval ⟨0x80000078, rs, mem⟩ := by rfl

theorem instruction31 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000007c, rs, mem⟩ =
      some ⟨if rs .a4 == 0 then 0x80000084 else 0x80000080, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a4) .zero 8).eval ⟨0x8000007c, rs, mem⟩ = _
  cases h : rs .a4 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction32 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000080, rs, mem⟩ =
      (instructions[32]'(by decide)).2.2.eval ⟨0x80000080, rs, mem⟩ := by rfl

theorem instruction33 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000084, rs, mem⟩ =
      (instructions[33]'(by decide)).2.2.eval ⟨0x80000084, rs, mem⟩ := by rfl

theorem instruction34 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000088, rs, mem⟩ =
      (instructions[34]'(by decide)).2.2.eval ⟨0x80000088, rs, mem⟩ := by rfl

theorem instruction35 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000008c, rs, mem⟩ =
      (instructions[35]'(by decide)).2.2.eval ⟨0x8000008c, rs, mem⟩ := by rfl

theorem instruction36 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000090, rs, mem⟩ =
      (instructions[36]'(by decide)).2.2.eval ⟨0x80000090, rs, mem⟩ := by rfl

theorem instruction37 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000094, rs, mem⟩ =
      (instructions[37]'(by decide)).2.2.eval ⟨0x80000094, rs, mem⟩ := by rfl

theorem instruction38 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000098, rs, mem⟩ =
      (instructions[38]'(by decide)).2.2.eval ⟨0x80000098, rs, mem⟩ := by rfl

theorem instruction39 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000009c, rs, mem⟩ =
      (instructions[39]'(by decide)).2.2.eval ⟨0x8000009c, rs, mem⟩ := by rfl

theorem instruction40 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000a0, rs, mem⟩ =
      some ⟨if rs .a1 == rs .a3 then 0x800000a4 else 0x8000013c, rs, mem⟩ := by
  change (WordMachine.Op.branch false (.reg .a1) (.reg .a3) 156).eval ⟨0x800000a0, rs, mem⟩ = _
  cases h : rs .a1 == rs .a3 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction41 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000a4, rs, mem⟩ =
      (instructions[41]'(by decide)).2.2.eval ⟨0x800000a4, rs, mem⟩ := by rfl

theorem instruction42 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000a8, rs, mem⟩ =
      some ⟨if rs .a3 == 0 then 0x800000bc else 0x800000ac, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a3) .zero 20).eval ⟨0x800000a8, rs, mem⟩ = _
  cases h : rs .a3 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction43 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000ac, rs, mem⟩ =
      (instructions[43]'(by decide)).2.2.eval ⟨0x800000ac, rs, mem⟩ := by rfl

theorem instruction44 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000b0, rs, mem⟩ =
      some ⟨if rs .a4 == rs .a2 then 0x800000b4 else 0x800000c4, rs, mem⟩ := by
  change (WordMachine.Op.branch false (.reg .a4) (.reg .a2) 20).eval ⟨0x800000b0, rs, mem⟩ = _
  cases h : rs .a4 == rs .a2 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction45 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000b4, rs, mem⟩ =
      (instructions[45]'(by decide)).2.2.eval ⟨0x800000b4, rs, mem⟩ := by rfl

theorem instruction46 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000b8, rs, mem⟩ =
      some ⟨0x800000e0, rs, mem⟩ := by
  change (WordMachine.Op.jump 40).eval ⟨0x800000b8, rs, mem⟩ = _
  simp only [WordMachine.Op.eval]
  change (if (0x800000e0 : Word) &&& 3 = 0 then some (WordMachine.State.mk 0x800000e0 rs mem) else none) = _
  exact ite_eq_left (by decide)

theorem instruction47 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000bc, rs, mem⟩ =
      (instructions[47]'(by decide)).2.2.eval ⟨0x800000bc, rs, mem⟩ := by rfl

theorem instruction48 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000c0, rs, mem⟩ =
      (instructions[48]'(by decide)).2.2.eval ⟨0x800000c0, rs, mem⟩ := by rfl

theorem instruction49 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000c4, rs, mem⟩ =
      (instructions[49]'(by decide)).2.2.eval ⟨0x800000c4, rs, mem⟩ := by rfl

theorem instruction50 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000c8, rs, mem⟩ =
      (instructions[50]'(by decide)).2.2.eval ⟨0x800000c8, rs, mem⟩ := by rfl

theorem instruction51 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000cc, rs, mem⟩ =
      some ⟨if rs .a3 == 0 then 0x800001cc else 0x800000d0, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a3) .zero 256).eval ⟨0x800000cc, rs, mem⟩ = _
  cases h : rs .a3 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction52 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000d0, rs, mem⟩ =
      (instructions[52]'(by decide)).2.2.eval ⟨0x800000d0, rs, mem⟩ := by rfl

theorem instruction53 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000d4, rs, mem⟩ =
      (instructions[53]'(by decide)).2.2.eval ⟨0x800000d4, rs, mem⟩ := by rfl

theorem instruction54 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000d8, rs, mem⟩ =
      (instructions[54]'(by decide)).2.2.eval ⟨0x800000d8, rs, mem⟩ := by rfl

theorem instruction55 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000dc, rs, mem⟩ =
      some ⟨if rs .a6 == rs .a2 then 0x800000e0 else 0x800000c8, rs, mem⟩ := by
  change (WordMachine.Op.branch false (.reg .a6) (.reg .a2) 8172).eval ⟨0x800000dc, rs, mem⟩ = _
  cases h : rs .a6 == rs .a2 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction56 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000e0, rs, mem⟩ =
      (instructions[56]'(by decide)).2.2.eval ⟨0x800000e0, rs, mem⟩ := by rfl

theorem instruction57 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000e4, rs, mem⟩ =
      (instructions[57]'(by decide)).2.2.eval ⟨0x800000e4, rs, mem⟩ := by rfl

theorem instruction58 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000e8, rs, mem⟩ =
      some ⟨if rs .a4 == 0 then 0x800000f0 else 0x800000ec, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a4) .zero 8).eval ⟨0x800000e8, rs, mem⟩ = _
  cases h : rs .a4 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction59 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000ec, rs, mem⟩ =
      (instructions[59]'(by decide)).2.2.eval ⟨0x800000ec, rs, mem⟩ := by rfl

theorem instruction60 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000f0, rs, mem⟩ =
      (instructions[60]'(by decide)).2.2.eval ⟨0x800000f0, rs, mem⟩ := by rfl

theorem instruction61 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000f4, rs, mem⟩ =
      (instructions[61]'(by decide)).2.2.eval ⟨0x800000f4, rs, mem⟩ := by rfl

theorem instruction62 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000f8, rs, mem⟩ =
      some ⟨if rs .a2 == rs .a3 then 0x800000fc else 0x80000100, rs, mem⟩ := by
  change (WordMachine.Op.branch false (.reg .a2) (.reg .a3) 8).eval ⟨0x800000f8, rs, mem⟩ = _
  cases h : rs .a2 == rs .a3 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction63 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800000fc, rs, mem⟩ =
      (instructions[63]'(by decide)).2.2.eval ⟨0x800000fc, rs, mem⟩ := by rfl

theorem instruction64 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000100, rs, mem⟩ =
      (instructions[64]'(by decide)).2.2.eval ⟨0x80000100, rs, mem⟩ := by rfl

theorem instruction65 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000104, rs, mem⟩ =
      (instructions[65]'(by decide)).2.2.eval ⟨0x80000104, rs, mem⟩ := by rfl

theorem instruction66 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000108, rs, mem⟩ =
      (instructions[66]'(by decide)).2.2.eval ⟨0x80000108, rs, mem⟩ := by rfl

theorem instruction67 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000010c, rs, mem⟩ =
      (instructions[67]'(by decide)).2.2.eval ⟨0x8000010c, rs, mem⟩ := by rfl

theorem instruction68 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000110, rs, mem⟩ =
      (instructions[68]'(by decide)).2.2.eval ⟨0x80000110, rs, mem⟩ := by rfl

theorem instruction69 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000114, rs, mem⟩ =
      (instructions[69]'(by decide)).2.2.eval ⟨0x80000114, rs, mem⟩ := by rfl

theorem instruction70 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000118, rs, mem⟩ =
      (instructions[70]'(by decide)).2.2.eval ⟨0x80000118, rs, mem⟩ := by rfl

theorem instruction71 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000011c, rs, mem⟩ =
      some ⟨0x80000120, rs.put .a2 (rs .a2 + 18446744073709551615), mem⟩ := by rfl

theorem instruction72 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000120, rs, mem⟩ =
      (instructions[72]'(by decide)).2.2.eval ⟨0x80000120, rs, mem⟩ := by rfl

theorem instruction73 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000124, rs, mem⟩ =
      (instructions[73]'(by decide)).2.2.eval ⟨0x80000124, rs, mem⟩ := by rfl

theorem instruction74 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000128, rs, mem⟩ =
      some ⟨if rs .a1 == rs .a2 then 0x80000144 else 0x8000012c, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a1) (.reg .a2) 28).eval ⟨0x80000128, rs, mem⟩ = _
  cases h : rs .a1 == rs .a2 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction75 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000012c, rs, mem⟩ =
      some ⟨0x800001d8, rs, mem⟩ := by
  change (WordMachine.Op.jump 172).eval ⟨0x8000012c, rs, mem⟩ = _
  simp only [WordMachine.Op.eval]
  change (if (0x800001d8 : Word) &&& 3 = 0 then some (WordMachine.State.mk 0x800001d8 rs mem) else none) = _
  exact ite_eq_left (by decide)

theorem instruction76 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000130, rs, mem⟩ =
      (instructions[76]'(by decide)).2.2.eval ⟨0x80000130, rs, mem⟩ := by rfl

theorem instruction77 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000134, rs, mem⟩ =
      (instructions[77]'(by decide)).2.2.eval ⟨0x80000134, rs, mem⟩ := by rfl

theorem instruction78 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000138, rs, mem⟩ =
      some ⟨if rs .a1 == rs .a3 then 0x800000a4 else 0x8000013c, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a1) (.reg .a3) 8044).eval ⟨0x80000138, rs, mem⟩ = _
  cases h : rs .a1 == rs .a3 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction79 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000013c, rs, mem⟩ =
      (instructions[79]'(by decide)).2.2.eval ⟨0x8000013c, rs, mem⟩ := by rfl

theorem instruction80 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000140, rs, mem⟩ =
      some ⟨if rs .a1 == rs .a2 then 0x80000144 else 0x800001d8, rs, mem⟩ := by
  change (WordMachine.Op.branch false (.reg .a1) (.reg .a2) 152).eval ⟨0x80000140, rs, mem⟩ = _
  cases h : rs .a1 == rs .a2 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction81 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000144, rs, mem⟩ =
      (instructions[81]'(by decide)).2.2.eval ⟨0x80000144, rs, mem⟩ := by rfl

theorem instruction82 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000148, rs, mem⟩ =
      some ⟨if rs .a1 == 0 then 0x80000194 else 0x8000014c, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a1) .zero 76).eval ⟨0x80000148, rs, mem⟩ = _
  cases h : rs .a1 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction83 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000014c, rs, mem⟩ =
      (instructions[83]'(by decide)).2.2.eval ⟨0x8000014c, rs, mem⟩ := by rfl

theorem instruction84 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000150, rs, mem⟩ =
      (instructions[84]'(by decide)).2.2.eval ⟨0x80000150, rs, mem⟩ := by rfl

theorem instruction85 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000154, rs, mem⟩ =
      (instructions[85]'(by decide)).2.2.eval ⟨0x80000154, rs, mem⟩ := by rfl

theorem instruction86 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000158, rs, mem⟩ =
      (instructions[86]'(by decide)).2.2.eval ⟨0x80000158, rs, mem⟩ := by rfl

theorem instruction87 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000015c, rs, mem⟩ =
      (instructions[87]'(by decide)).2.2.eval ⟨0x8000015c, rs, mem⟩ := by rfl

theorem instruction88 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000160, rs, mem⟩ =
      (instructions[88]'(by decide)).2.2.eval ⟨0x80000160, rs, mem⟩ := by rfl

theorem instruction89 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000164, rs, mem⟩ =
      (instructions[89]'(by decide)).2.2.eval ⟨0x80000164, rs, mem⟩ := by rfl

theorem instruction90 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000168, rs, mem⟩ =
      some ⟨0x8000016c, rs.put .a3 (rs .a3 + 18446744073709551615), mem⟩ := by rfl

theorem instruction91 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000016c, rs, mem⟩ =
      (instructions[91]'(by decide)).2.2.eval ⟨0x8000016c, rs, mem⟩ := by rfl

theorem instruction92 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000170, rs, mem⟩ =
      some ⟨if rs .a3 == 0 then 0x8000019c else 0x80000174, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a3) .zero 44).eval ⟨0x80000170, rs, mem⟩ = _
  cases h : rs .a3 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction93 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000174, rs, mem⟩ =
      some ⟨if rs .a2 == 0 then 0x800001e0 else 0x80000178, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a2) .zero 108).eval ⟨0x80000174, rs, mem⟩ = _
  cases h : rs .a2 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction94 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000178, rs, mem⟩ =
      (instructions[94]'(by decide)).2.2.eval ⟨0x80000178, rs, mem⟩ := by rfl

theorem instruction95 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000017c, rs, mem⟩ =
      (instructions[95]'(by decide)).2.2.eval ⟨0x8000017c, rs, mem⟩ := by rfl

theorem instruction96 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000180, rs, mem⟩ =
      (instructions[96]'(by decide)).2.2.eval ⟨0x80000180, rs, mem⟩ := by rfl

theorem instruction97 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000184, rs, mem⟩ =
      (instructions[97]'(by decide)).2.2.eval ⟨0x80000184, rs, mem⟩ := by rfl

theorem instruction98 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000188, rs, mem⟩ =
      (instructions[98]'(by decide)).2.2.eval ⟨0x80000188, rs, mem⟩ := by rfl

theorem instruction99 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000018c, rs, mem⟩ =
      (instructions[99]'(by decide)).2.2.eval ⟨0x8000018c, rs, mem⟩ := by rfl

theorem instruction100 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000190, rs, mem⟩ =
      (instructions[100]'(by decide)).2.2.eval ⟨0x80000190, rs, mem⟩ := by rfl

theorem instruction101 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000194, rs, mem⟩ =
      (instructions[101]'(by decide)).2.2.eval ⟨0x80000194, rs, mem⟩ := by rfl

theorem instruction102 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x80000198, rs, mem⟩ =
      (instructions[102]'(by decide)).2.2.eval ⟨0x80000198, rs, mem⟩ := by rfl

theorem instruction103 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x8000019c, rs, mem⟩ =
      (instructions[103]'(by decide)).2.2.eval ⟨0x8000019c, rs, mem⟩ := by rfl

theorem instruction104 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001a0, rs, mem⟩ =
      some ⟨if rs .a2 == 0 then 0x800001a4 else 0x800001a8, rs, mem⟩ := by
  change (WordMachine.Op.branch false (.reg .a2) .zero 8).eval ⟨0x800001a0, rs, mem⟩ = _
  cases h : rs .a2 == 0 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction105 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001a4, rs, mem⟩ =
      (instructions[105]'(by decide)).2.2.eval ⟨0x800001a4, rs, mem⟩ := by rfl

theorem instruction106 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001a8, rs, mem⟩ =
      (instructions[106]'(by decide)).2.2.eval ⟨0x800001a8, rs, mem⟩ := by rfl

theorem instruction107 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001ac, rs, mem⟩ =
      (instructions[107]'(by decide)).2.2.eval ⟨0x800001ac, rs, mem⟩ := by rfl

theorem instruction108 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001b0, rs, mem⟩ =
      (instructions[108]'(by decide)).2.2.eval ⟨0x800001b0, rs, mem⟩ := by rfl

theorem instruction109 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001b4, rs, mem⟩ =
      (instructions[109]'(by decide)).2.2.eval ⟨0x800001b4, rs, mem⟩ := by rfl

theorem instruction110 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001b8, rs, mem⟩ =
      (instructions[110]'(by decide)).2.2.eval ⟨0x800001b8, rs, mem⟩ := by rfl

theorem instruction111 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001bc, rs, mem⟩ =
      (instructions[111]'(by decide)).2.2.eval ⟨0x800001bc, rs, mem⟩ := by rfl

theorem instruction112 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001c0, rs, mem⟩ =
      some ⟨0x800001c4, rs.put .a1 (rs .a2 + 18446744073709551615), mem⟩ := by rfl

theorem instruction113 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001c4, rs, mem⟩ =
      (instructions[113]'(by decide)).2.2.eval ⟨0x800001c4, rs, mem⟩ := by rfl

theorem instruction114 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001c8, rs, mem⟩ =
      some ⟨0x800001d8, rs, mem⟩ := by
  change (WordMachine.Op.jump 16).eval ⟨0x800001c8, rs, mem⟩ = _
  simp only [WordMachine.Op.eval]
  change (if (0x800001d8 : Word) &&& 3 = 0 then some (WordMachine.State.mk 0x800001d8 rs mem) else none) = _
  exact ite_eq_left (by decide)

theorem instruction115 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001cc, rs, mem⟩ =
      (instructions[115]'(by decide)).2.2.eval ⟨0x800001cc, rs, mem⟩ := by rfl

theorem instruction116 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001d0, rs, mem⟩ =
      (instructions[116]'(by decide)).2.2.eval ⟨0x800001d0, rs, mem⟩ := by rfl

theorem instruction117 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001d4, rs, mem⟩ =
      some ⟨if rs .a1 == rs .a2 then 0x80000144 else 0x800001d8, rs, mem⟩ := by
  change (WordMachine.Op.branch true (.reg .a1) (.reg .a2) 8048).eval ⟨0x800001d4, rs, mem⟩ = _
  cases h : rs .a1 == rs .a2 <;>
    simp only [WordMachine.Op.eval, WordMachine.Src.get, h] <;> rfl

theorem instruction118 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001d8, rs, mem⟩ =
      (instructions[118]'(by decide)).2.2.eval ⟨0x800001d8, rs, mem⟩ := by rfl

theorem instruction119 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001dc, rs, mem⟩ =
      (instructions[119]'(by decide)).2.2.eval ⟨0x800001dc, rs, mem⟩ := by rfl

theorem instruction120 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001e0, rs, mem⟩ =
      (instructions[120]'(by decide)).2.2.eval ⟨0x800001e0, rs, mem⟩ := by rfl

theorem instruction121 (rs : WordMachine.Registers) (mem : Heap.Memory) :
    WordMachine.step program ⟨0x800001e4, rs, mem⟩ =
      (instructions[121]'(by decide)).2.2.eval ⟨0x800001e4, rs, mem⟩ := by rfl

abbrev Ctx : Context := [.ptr State.name, .u64, .u64, .u64,
  .ptr Process.name, .ptr Process.name, .ptr Process.name, .ptr Process.name, .u64, .u64]

def descend : Cmd Ctx → List Bool → Cmd Ctx
  | c, [] => c
  | .seq a b, side :: rest | .ite _ a b, side :: rest =>
      descend (if side then b else a) rest
  | .while _ b, _ :: rest => descend b rest
  | _, _ => .skip

def cmd770 : Cmd Ctx := descend Scheduler.step.body [true, false, false, false, false, false, false, true, false]
def cmd1540 : Cmd Ctx := descend Scheduler.step.body [true, false, false, false, false, false, false, true, false, false]
def cmd771 : Cmd Ctx := descend Scheduler.step.body [true, false, false, false, false, false, false, true, true]
def cmd97 : Cmd Ctx := descend Scheduler.step.body [true, false, false, false, false, true]
def cmd25 : Cmd Ctx := descend Scheduler.step.body [true, false, false, true]
def cmd7 : Cmd Ctx := descend Scheduler.step.body [true, true]
def cmd230 : Cmd Ctx := descend Scheduler.step.body [true, true, false, false, true, true, false]
def cmd460 : Cmd Ctx := descend Scheduler.step.body [true, true, false, false, true, true, false, false]
def cmd231 : Cmd Ctx := descend Scheduler.step.body [true, true, false, false, true, true, true]
def cmd15 : Cmd Ctx := descend Scheduler.step.body [true, true, true]

def entryStack : List (Control.Frame Ctx) := [.cmd Scheduler.step.body 1]
def addStack : List (Control.Frame Ctx) :=
  [.mark 770, .cmd cmd1540 1540, .cmd cmd770 770, .cmd cmd771 771,
   .cmd cmd97 97, .cmd cmd25 25, .cmd cmd7 7]
def removeStack : List (Control.Frame Ctx) :=
  [.mark 230, .cmd cmd460 460, .cmd cmd230 230, .cmd cmd231 231, .cmd cmd15 15]

end Riscvc.Heap.Scheduler.StepProof
