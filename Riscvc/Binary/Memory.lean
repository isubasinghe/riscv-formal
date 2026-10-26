import Riscvc.Binary.SailProofs
import Riscvc.Heap.Language

/-! Byte-level refinement of the heap DSL's aligned 64-bit cells to Sail RAM.
The instruction lemmas below use the generated Sail memory system, including
address translation, PMA/PMP checks, and the sequential byte-memory interface.
-/
namespace Riscvc.Binary.Memory

open Sail.ConcurrencyInterfaceV1 RiscvSail RiscvSail.Functions SailProofs

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

attribute [local simp] Std.ExtDHashMap.get?_insert

private theorem get_insert (m : Std.ExtHashMap Nat (BitVec 8)) (a b : Nat) (v : BitVec 8) :
    (m.insert a v).get? b = if a = b then some v else m.get? b := by
  simpa only [beq_iff_eq, Std.ExtHashMap.get?_eq_getElem?] using (Std.ExtHashMap.getElem?_insert (m := m) (k := a) (a := b) (v := v))


/-- Little-endian representation of one source word in physical memory. -/
def WordAt (s : SailState) (a : Nat) (v : Word) : Prop :=
  ∀ i : Fin 8, s.mem.get? (a + i.val) = some (v.extractLsb' (8 * i.val) 8)

/-- Source cells are aligned and represented by eight actual Sail bytes. -/
def Represents (mem : Heap.Memory) (s : SailState) : Prop :=
  ∀ a v, mem a = some v → a % 8 = 0 ∧ WordAt s a v

def putWord (s : SailState) (a : Nat) (v : Word) : SailState :=
  let m0 := s.mem.insert a (v.extractLsb' 0 8)
  let m1 := m0.insert (a+1) (v.extractLsb' 8 8)
  let m2 := m1.insert (a+2) (v.extractLsb' 16 8)
  let m3 := m2.insert (a+3) (v.extractLsb' 24 8)
  let m4 := m3.insert (a+4) (v.extractLsb' 32 8)
  let m5 := m4.insert (a+5) (v.extractLsb' 40 8)
  let m6 := m5.insert (a+6) (v.extractLsb' 48 8)
  { s with mem := m6.insert (a+7) (v.extractLsb' 56 8) }

theorem readBytes_ok (s : SailState) (a : Nat) (v : Word) (h : WordAt s a v) :
    PreSail.readBytes (ue := exception) 8 a s = .ok (v, none) s := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  have h4 := h ⟨4, by decide⟩
  have h5 := h ⟨5, by decide⟩
  have h6 := h ⟨6, by decide⟩
  have h7 := h ⟨7, by decide⟩
  simp only [Fin.val_mk, Nat.add_zero, Nat.mul_zero, Nat.mul_one] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [PreSail.readBytes, PreSail.readByte, get, getThe, MonadStateOf.get,
    EStateM.get, bind, EStateM.bind, pure, EStateM.pure, Nat.add_assoc,
    h0, h1, h2, h3, h4, h5, h6, h7, Nat.reduceAdd, Nat.reduceMul]
  congr 1
  apply Prod.ext
  · bv_normalize
  · rfl

theorem writeBytes_ok (s : SailState) (a : Nat) (v : Word) :
    PreSail.writeBytes (ue := exception) (n := 8) a v s = .ok true (putWord s a v) := by
  rfl

theorem putWord_at (s : SailState) (a : Nat) (v : Word) :
    WordAt (putWord s a v) a v := by
  intro i
  rcases i with ⟨i, hi⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> subst i <;> simp only [putWord, get_insert, Fin.val_mk]
  all_goals simp

theorem putWord_frame (s : SailState) (a : Nat) (v : Word) (b : Nat)
    (h : b < a ∨ a + 8 ≤ b) :
    (putWord s a v).mem.get? b = s.mem.get? b := by
  have h0 : a ≠ b := by omega
  have h1 : a+1 ≠ b := by omega
  have h2 : a+2 ≠ b := by omega
  have h3 : a+3 ≠ b := by omega
  have h4 : a+4 ≠ b := by omega
  have h5 : a+5 ≠ b := by omega
  have h6 : a+6 ≠ b := by omega
  have h7 : a+7 ≠ b := by omega
  simp only [putWord, get_insert, ite_eq_right, h0, h1, h2, h3, h4, h5, h6, h7, ite_false]

theorem represents_write (mem : Heap.Memory) (s : SailState) (a : Nat) (v : Word)
    (h : Represents mem s) (ha : a % 8 = 0) :
    Represents (mem.write a v) (putWord s a v) := by
  intro b w hw
  by_cases eq : b = a
  · subst b
    have : w = v := by simpa [Heap.Memory.write] using hw.symm
    subst w
    exact ⟨ha, putWord_at s a v⟩
  · have old : mem b = some w := by simpa [Heap.Memory.write, eq] using hw
    obtain ⟨hb, hword⟩ := h b w old
    refine ⟨hb, ?_⟩
    intro (i : Fin 8)
    rw [putWord_frame s a v (b + i.val) (by have := i.isLt; omega)]
    exact hword i

/-- A writable RAM region; executable text is outside this data-only region. -/
def ram : PMA_Region :=
  { base := 0x80001000, size := 0x0ffff000,
    attributes := { (default : PMA) with readable := true, writable := true },
    include_in_device_tree := false }

/-- Aligned 8-byte accesses in the 256 MiB RAM window above the text. -/
def Address (a : Word) : Prop :=
  0x80001000 ≤ a.toNat ∧ a.toNat + 8 ≤ 0x90000000 ∧ a.toNat % 8 = 0

/-- Concrete platform setup, not an assumption about the result of a load/store. -/
def Ready (s : SailState) : Prop :=
  s.regs.get? .cur_privilege = some .Machine ∧
  s.regs.get? .mseccfg = some 0 ∧
  s.regs.get? .mstatus = some 0 ∧
  s.regs.get? .pma_regions = some [ram] ∧
  s.regs.get? .pmpcfg_n = some (Vector.replicate 64 0) ∧
  s.regs.get? .pmpaddr_n = some (Vector.replicate 64 0) ∧
  s.regs.get? .htif_tohost_base = some none

attribute [local simp] readReg PreSail.readReg get getThe MonadStateOf.get
  EStateM.get bind EStateM.bind pure EStateM.pure
  SailME.run PreSail.PreSailME.run ExceptT.run ExceptT.bind ExceptT.bindCont
  ExceptT.pure ExceptT.lift ExceptT.mk Functor.map EStateM.map
  liftM monadLift MonadLift.monadLift RiscvSail.assert PreSail.assert
  BEq.beq instBEqPrivilege.beq instBEqSATPMode.beq instBEqMemoryAccessType.beq instBEqMem_payload.beq
  instBEqSplittability.beq mem_payload.ctorIdx Splittability.ctorIdx

theorem aligned (a : Word) (h : Address a) :
    is_aligned_paddr (.Physaddr a) 8 = true := by
  simp only [is_aligned_paddr, Sail.BitVec.toNatInt, beq_iff_eq]
  change (a.toNat : Int) % (8 : Nat) = 0
  rw [← Int.natCast_emod, h.2.2]
  rfl

private theorem replicate_int {α : Type} [Inhabited α] (v : α) (i : Int)
    (h : 0 ≤ i) (h' : i < 64) : (Vector.replicate 64 v)[i]! = v := by
  change (Vector.replicate 64 v)[i.toNat]! = v
  simp [show i.toNat < 64 by omega]

private theorem replicate_int_get {α : Type} [Inhabited α] (v : α) (i : Int)
    (h : i.toNat < 64) : (Vector.replicate 64 v)[i]'h = v := by
  change (Vector.replicate 64 v)[i.toNat] = v
  simp

theorem pmp_ok (s : SailState) (a : Word) (access : MemoryAccessType mem_payload)
    (hc : s.regs.get? .pmpcfg_n = some (Vector.replicate 64 0))
    (ha : s.regs.get? .pmpaddr_n = some (Vector.replicate 64 0)) :
    pmpCheck (.Physaddr a) 8 access .Machine s = .ok none s := by
  simp [pmpCheck, sys_pmp_count, pmpReadAddrReg, sys_pmp_grain,
    pmpMatchAddr, pmpAddrMatchType_encdec_backwards, _get_Pmpcfg_ent_A,
    hc, ha, Membership.mem, IntRange.instMemIntRange, Sail.BitVec.extractLsb, Sail.BitVec.access, replicate_int, replicate_int_get,
    ForIn.forIn, ForIn'.forIn', IntRange.forIn', IntRange.forIn'.loop]

theorem ram_read (s : SailState) (a v : Word) (h : WordAt s a.toNat v) :
    read_ram .Read_plain (.Physaddr a) 8 false s = .ok (v, ()) s := by
  simp [read_ram, PreSail.sail_mem_read, readBytes_ok s a.toNat v h, default_meta]

theorem ram_write (s : SailState) (a v : Word) :
    write_ram .Write_plain (.Physaddr a) 8 v () s = .ok true (putWord s a.toNat v) := by
  simp [write_ram, PreSail.sail_mem_write, writeBytes_ok]

theorem in_ram (a : Word) (h : Address a) :
    matching_pma_region [ram] (.Physaddr a) 8 = some ram := by
  have lo : (0x80001000 : Word) ≤ a := h.1
  have hi : a ≤ (0x8ffffff8 : Word) := by change a.toNat ≤ 0x8ffffff8; have := h.2.1; omega
  have range : range_subset a 8 0x80001000 0x0ffff000 = true := by
    have ule (x y : Word) : zopz0zIzJ_u x y = true ↔ x ≤ y := by
      simp only [zopz0zIzJ_u, Sail.BitVec.toNatInt, decide_eq_true_eq]
      exact Int.ofNat_le
    simp only [range_subset, Bool.and_eq_true, ule]
    simp [BitVec.le_def, BitVec.toNat_sub, BitVec.toNat_add] at *
    omega
  simpa [matching_pma_region, matching_pma_region_bits_range, ram,
    bits_of_physaddr, zero_extend, Sail.BitVec.zeroExtend, to_bits, Sail.get_slice_int] using congrArg (fun b => if b then some ram else none) range

theorem page_ok (a : Word) (h : Address a) :
    split_on_page_boundary a 8 = pure (8, 0) := by
  have hm : a &&& 7 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    change a.toNat &&& (2^3-1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod, h.2.2]
  have hp : a &&& 0xfffffffffffff000 = (a + 8 - 1) &&& 0xfffffffffffff000 := by
    have mask_eq (x : Word) : x &&& 0xfffffffffffff000 = (x >>> 12) <<< 12 := by
      exact (BitVec.shiftLeft_ushiftRight (x := x) (n := 12)).symm
    erw [mask_eq, mask_eq]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hn : (a + 8 - 1).toNat = a.toNat + 7 := by
      simp [BitVec.toNat_sub, BitVec.toNat_add]
      have := h.1
      have := h.2.1
      omega
    simp only [BitVec.toNat_ushiftRight, hn, Nat.shiftRight_eq_div_pow]
    have := h.2.2
    omega
  have mask : Sail.BitVec.updateSubrange (ones (n := 64)) 11 0 (zeros (n := 12)) =
      0xfffffffffffff000#64 := by decide
  unfold split_on_page_boundary
  change (if (a &&& Sail.BitVec.updateSubrange (ones (n := 64)) 11 0 (zeros (n := 12)) ==
    (a + 8 - 1) &&& Sail.BitVec.updateSubrange (ones (n := 64)) 11 0 (zeros (n := 12)))
    then (pure (8, 0) : SailM (Int × Int)) else _) = _
  rw [mask]
  erw [show (a &&& 0xfffffffffffff000 == (a + 8 - 1) &&& 0xfffffffffffff000) = true
    from beq_iff_eq.mpr hp]
  rfl

theorem mmio_read_false (s : SailState) (a : Word) (h : Address a)
    (ht : s.regs.get? .htif_tohost_base = some none) :
    within_mmio_readable (.Physaddr a) 8 s = .ok false s := by
  have hc : ¬ ((a.toNat : Int) + 8 ≤ 34340864) := by have := h.1; omega
  have hs : ¬ ((a.toNat : Int) + 8 ≤ 201326624) := by have := h.1; omega
  have cb : plat_clint_base = 33554432#64 := rfl
  have cs : plat_clint_size = 786432#64 := rfl
  have sb : plat_sig_base = 201326592#64 := rfl
  have ss : plat_sig_size = 32#64 := rfl
  simp [within_mmio_readable, get_config_rvfi, within_clint, within_sig,
    within_htif_readable, within_htif_writable, ht, plat_have_clint, plat_have_sig,
    cb, cs, sb, ss, Functions.not, Sail.BitVec.toNatInt, hc, hs]

theorem mmio_write_false (s : SailState) (a : Word) (h : Address a)
    (ht : s.regs.get? .htif_tohost_base = some none) :
    within_mmio_writable (.Physaddr a) 8 s = .ok false s := by
  have hc : ¬ ((a.toNat : Int) + 8 ≤ 34340864) := by have := h.1; omega
  have hs : ¬ ((a.toNat : Int) + 8 ≤ 201326624) := by have := h.1; omega
  have cb : plat_clint_base = 33554432#64 := rfl
  have cs : plat_clint_size = 786432#64 := rfl
  have sb : plat_sig_base = 201326592#64 := rfl
  have ss : plat_sig_size = 32#64 := rfl
  simp [within_mmio_writable, get_config_rvfi, within_clint, within_sig,
    within_htif_writable, ht, plat_have_clint, plat_have_sig,
    cb, cs, sb, ss, Functions.not, Sail.BitVec.toNatInt, hc, hs]

def dataAccess (writing : Bool) : MemoryAccessType mem_payload :=
  if writing then .Store .Data else .Load .Data

theorem pma_ok (s : SailState) (a : Word) (writing : Bool) (h : Address a)
    (hr : s.regs.get? .pma_regions = some [ram]) :
    pmaCheck (.Physaddr a) 8 (dataAccess writing) .PBMT_PMA false s =
      .ok (.Ok ⟨.CannotSplit, 0⟩) s := by
  cases writing <;>
    simp [dataAccess, pmaCheck, hr, in_ram a h, override_PMA,
      mag_pma_check, is_mag_applicable_access, aligned a h, Functions.not]
  all_goals simp [ram, Functions.xlen_bytes]

theorem transform_ok (s : SailState) (a : Word) (writing : Bool) (h : Ready s) :
    transform_effective_address (.Virtaddr a) (dataAccess writing) s =
      .ok (.Virtaddr a) s := by
  obtain ⟨hp, hc, hm, _⟩ := h
  cases writing <;>
    simp [dataAccess, transform_effective_address, effectivePrivilege, hp, hc, hm,
      get_pmlen, is_pmm_applicable, get_pmm, translationMode, _get_Mstatus_MPRV,
      _get_Mstatus_MXR, _get_Seccfg_PMM, pmm_mode_backwards, pm_transform_PA,
      Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend, Functions.xlen, bne, BitVec.extractLsb]
  all_goals rfl

theorem translate_ok (s : SailState) (a : Word) (writing : Bool) (h : Ready s) :
    translateAddr (.Virtaddr a) (dataAccess writing) s =
      .ok (.Ok (.Physaddr a, .PBMT_PMA, ())) s := by
  obtain ⟨hp, _, hm, _⟩ := h
  cases writing <;>
    simp [dataAccess, translateAddr, effectivePrivilege, translationMode, hp, hm,
      _get_Mstatus_MPRV, is_shadow_stack_access, bits_of_virtaddr, zero_extend,
      Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, init_ext_ptw, bne]

@[simp] theorem update_all (x y : Word) :
    Sail.BitVec.updateSubrange x 63 0 y = y := by
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

theorem mem_read_ok (s : SailState) (a v : Word) (ready : Ready s)
    (ha : Address a) (hv : WordAt s a.toNat v) :
    mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) 8 false false false s =
      .ok (.Ok v) s := by
  obtain ⟨hp, _, hm, hr, hpc, hpa, ht⟩ := ready
  have pma := pma_ok s a false ha hr
  simp only [dataAccess, Bool.false_eq_true, ite_false, ite_true] at pma
  have pmp := pmp_ok s a (.Load .Data) hpc hpa
  simp [mem_read, mem_read_priv, mem_read_priv_meta, checked_mem_read,
    effectivePrivilege, hp, hm, _get_Mstatus_MPRV, Sail.BitVec.extractLsb,
    check_pma_with_pmp_priority, pma, dataAccess, split_misaligned,
    misaligned_order, sys_misaligned_order_decreasing, read_kind_of_flags,
    untilFuelM, untilFuelM.go, bits_of_physaddr, Sail.BitVec.addInt,
    pmp, mmio_read_false s a ha ht, ram_read s a v hv, default_meta,
    MemoryOpResult_drop_meta]

theorem mem_ea_ok (s : SailState) (a : Word) (ready : Ready s) (ha : Address a) :
    mem_write_ea (.Physaddr a) 8 (.Store .Data) .PBMT_PMA false false false s =
      .ok (.Ok ()) s := by
  obtain ⟨hp, _, hm, hr, hpc, hpa, _⟩ := ready
  have pma := pma_ok s a true ha hr
  simp only [dataAccess, Bool.false_eq_true, ite_false, ite_true] at pma
  have pmp := pmp_ok s a (.Store .Data) hpc hpa
  simp [mem_write_ea, effectivePrivilege, hp, hm, _get_Mstatus_MPRV,
    Sail.BitVec.extractLsb, check_pma_with_pmp_priority, pma, dataAccess,
    split_misaligned, misaligned_order, sys_misaligned_order_decreasing,
    write_kind_of_flags, untilFuelM, untilFuelM.go, bits_of_physaddr,
    Sail.BitVec.addInt, pmp, write_ram_ea]

theorem mem_write_ok (s : SailState) (a v : Word) (ready : Ready s) (ha : Address a) :
    mem_write_value (.Physaddr a) 8 v (.Store .Data) .PBMT_PMA false false false s =
      .ok (.Ok true) (putWord s a.toNat v) := by
  obtain ⟨hp, _, hm, hr, hpc, hpa, ht⟩ := ready
  have pma := pma_ok s a true ha hr
  simp only [dataAccess, Bool.false_eq_true, ite_false, ite_true] at pma
  have pmp := pmp_ok s a (.Store .Data) hpc hpa
  simp [mem_write_value, mem_write_value_meta, mem_write_value_priv_meta,
    checked_mem_write, effectivePrivilege, hp, hm, _get_Mstatus_MPRV,
    Sail.BitVec.extractLsb, check_pma_with_pmp_priority, pma, dataAccess,
    split_misaligned, misaligned_order, sys_misaligned_order_decreasing,
    write_kind_of_flags, untilFuelM, untilFuelM.go, bits_of_physaddr,
    Sail.BitVec.addInt, pmp, mmio_write_false s a ha ht, ram_write, default_meta, BitVec.extractLsb]

theorem vread_ok (s : SailState) (a v : Word) (ready : Ready s)
    (ha : Address a) (hv : WordAt s a.toNat v) :
    vmem_read_addr (.Virtaddr a) 8 (.Load .Data) false false false s =
      .ok (.Ok v) s := by
  have hp := ready.1
  have hm := ready.2.2.1
  have halign : is_aligned_vaddr (.Virtaddr a) 8 = true := aligned a ha
  have tr := translate_ok s a false ready
  simp only [dataAccess, Bool.false_eq_true, ite_false] at tr
  simp [vmem_read_addr, halign, bits_of_virtaddr, page_ok a ha,
    effectivePrivilege, hp, hm, _get_Mstatus_MPRV, Sail.BitVec.extractLsb,
    translationMode, bne, Functions.not, translate_and_read_value, tr,
    mem_read_ok s a v ready ha hv, sys_misaligned_order_decreasing]

theorem vwrite_ok (s : SailState) (a v : Word) (ready : Ready s) (ha : Address a) :
    vmem_write_addr (.Virtaddr a) 8 v (.Store .Data) false false false s =
      .ok (.Ok true) (putWord s a.toNat v) := by
  have hp := ready.1
  have hm := ready.2.2.1
  have halign : is_aligned_vaddr (.Virtaddr a) 8 = true := aligned a ha
  have tr := translate_ok s a true ready
  simp only [dataAccess, ite_true] at tr
  simp [vmem_write_addr, halign, bits_of_virtaddr, page_ok a ha,
    effectivePrivilege, hp, hm, _get_Mstatus_MPRV, Sail.BitVec.extractLsb,
    translationMode, bne, Functions.not, tr, mem_ea_ok s a ready ha,
    mem_write_ok s a v ready ha, sys_misaligned_order_decreasing,
    is_store_conditional, BitVec.extractLsb]

/-- The actual Sail instruction used to traverse `Node.next`. -/
theorem ld_next (s : SailState) (p v : Word) (ready : Ready s)
    (hp : s.regs.get? .x13 = some p) (ha : Address (p + 8))
    (hv : WordAt s (p + 8).toNat v) :
    execute_LOAD 8 (.Regidx 13) (.Regidx 13) false 8 s =
      .ok RETIRE_SUCCESS (setReg s .x13 v) := by
  have tr := transform_ok s (p + 8) false ready
  simp only [dataAccess, Bool.false_eq_true, ite_false] at tr
  simp [execute_LOAD, vmem_read, get_transformed_data_addr, ext_data_get_addr,
    rX_bits, rX, wX_bits, wX, regval_from_reg, regval_into_reg,
    Sail.BitVec.toNatInt, hp, sign_extend, Sail.BitVec.signExtend,
    tr, vread_ok s (p + 8) v ready ha hv, Functions.xlen_bytes,
    extend_value, writeReg_ok, xreg_write_callback, xreg_full_write_callback]
  erw [tr]
  simp only [EStateM.pure, EStateM.map, bind, EStateM.bind]
  erw [vread_ok s (p + 8) v ready ha hv]
  simp [writeReg_ok, reg_name_forwards, encdec_reg_forwards_matches,
    encdec_reg_forwards, get_config_use_abi_names, reg_arch_name_raw_forwards]
  rfl

/-- The actual Sail instruction that links the last node to the suffix. -/
theorem sd_next (s : SailState) (p v : Word) (ready : Ready s)
    (hp : s.regs.get? .x12 = some p) (hv : s.regs.get? .x11 = some v)
    (ha : Address (p + 8)) :
    execute_STORE 8 (.Regidx 11) (.Regidx 12) 8 s =
      .ok RETIRE_SUCCESS (putWord s (p + 8).toNat v) := by
  have tr := transform_ok s (p + 8) true ready
  simp only [dataAccess, ite_true] at tr
  simp [execute_STORE, vmem_write, get_transformed_data_addr, ext_data_get_addr,
    rX_bits, rX, regval_from_reg, Sail.BitVec.toNatInt, hp, hv,
    sign_extend, Sail.BitVec.signExtend, tr, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, BitVec.extractLsb, vwrite_ok s (p + 8) v ready ha]
  erw [tr]
  simp only [EStateM.pure, EStateM.map, bind, EStateM.bind]
  erw [vwrite_ok s (p + 8) v ready ha]
  rfl

/-- The register operands are read by Sail itself; the effective address uses
the signed 12-bit immediate from the decoded instruction. -/
theorem store64 (s : SailState) (imm : BitVec 12) (rs1 rs2 : regidx)
    (p v : Word) (ready : Ready s)
    (hp : rX_bits rs1 s = .ok p s) (hv : rX_bits rs2 s = .ok v s)
    (ha : Address (p + imm.signExtend 64)) :
    execute_STORE imm rs2 rs1 8 s =
      .ok RETIRE_SUCCESS (putWord s (p + imm.signExtend 64).toNat v) := by
  have tr := transform_ok s (p + imm.signExtend 64) true ready
  simp only [dataAccess, ite_true] at tr
  simp [execute_STORE, vmem_write, get_transformed_data_addr, ext_data_get_addr,
    sign_extend, Sail.BitVec.signExtend, hp, hv, Functions.xlen_bytes,
    Sail.BitVec.extractLsb, BitVec.extractLsb]
  erw [tr]
  simp only [EStateM.pure, EStateM.map, bind, EStateM.bind]
  erw [vwrite_ok s (p + imm.signExtend 64) v ready ha]
  rfl

theorem load64 (s after : SailState) (imm : BitVec 12) (rs1 rd : regidx)
    (p v : Word) (ready : Ready s)
    (hp : rX_bits rs1 s = .ok p s)
    (ha : Address (p + imm.signExtend 64))
    (hv : WordAt s (p + imm.signExtend 64).toNat v)
    (hw : wX_bits rd v s = .ok () after) :
    execute_LOAD imm rs1 rd false 8 s = .ok RETIRE_SUCCESS after := by
  have tr := transform_ok s (p + imm.signExtend 64) false ready
  simp only [dataAccess, Bool.false_eq_true, ite_false] at tr
  simp [execute_LOAD, vmem_read, get_transformed_data_addr, ext_data_get_addr,
    hp, sign_extend, Sail.BitVec.signExtend, Functions.xlen_bytes, extend_value]
  erw [tr]
  simp only [EStateM.pure, EStateM.map, bind, EStateM.bind]
  erw [vread_ok s (p + imm.signExtend 64) v ready ha hv]
  simp only [EStateM.pure, EStateM.map, bind, EStateM.bind, BitVec.signExtend_eq]
  erw [hw]

end Riscvc.Binary.Memory
