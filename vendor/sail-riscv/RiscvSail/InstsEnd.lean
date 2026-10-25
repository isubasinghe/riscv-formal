import RiscvSail.Flow
import RiscvSail.Prelude
import RiscvSail.Errors
import RiscvSail.Xlen
import RiscvSail.PlatformConfig
import RiscvSail.Types
import RiscvSail.Callbacks
import RiscvSail.Regs
import RiscvSail.PcAccess
import RiscvSail.SysRegs
import RiscvSail.SysExceptions
import RiscvSail.ZicfilpRegs
import RiscvSail.SysControl
import RiscvSail.VmemTlb
import RiscvSail.InstsBegin
import RiscvSail.VmemUtils
import RiscvSail.ZicfilpInsts
import RiscvSail.BaseInsts
import RiscvSail.ZicsrInsts

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

noncomputable section
namespace RiscvSail

open ConcurrencyInterfaceV1

namespace Functions

open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vstart_class
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open stateen_bit
open sopw
open sop
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open page_based_mem_type
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_exception
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extension
open exception
open csrop
open cregidx
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cacheop
open breakpoint_cause
open bop
open barrier_kind
open amoop
open agtype
open XtvecModeReservedBehavior
open XipReadType
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Splittability
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privileged_ISA_Version
open Privilege
open PointerMaskingMode
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open PM_Ext
open OOBVstartReservedBehavior
open MemoryRegionType
open MemoryAccessType
open InterruptType
open IllegalVtypeReservedBehavior
open ISA_Format
open HartState
open FflagsDirtyPolicy
open FetchResult
open FetchBytes_Result
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open CSRCheckResult
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

noncomputable def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__169 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__169 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then
      (let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__169 31 12)
      let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__169 31 12)
      (pure (some (LPAD lpl))))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__169 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__169 31 12)
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__169 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 11 7)
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__169 31 12)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__167 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__167 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__167 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__167 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__167 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__167 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__167 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__167 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__167 20 20)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (let imm := (((imm_19_19_ +++ imm_18_11_) +++ imm_10_10_) +++ imm_9_0_)
                  (JAL ((imm +++ 0#1), rd))))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__164 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__164 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__164 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__164 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__164 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__164 31 20)
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__164 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__164 19 15)
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__164 31 20)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some (JALR (imm, rs1, rd)))))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__162 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__162 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__162 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__162 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__162 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__162 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__162 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__162 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__162 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__162 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__162 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__162 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__162 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (let imm := (((imm_11_11_ +++ imm_10_10_) +++ imm_9_4_) +++ imm_3_0_)
                          (BTYPE ((imm +++ 0#1), rs2, rs1, op))))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__160 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__160 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__160 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__160 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__160 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__160 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__160 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__160 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__160 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__160 31 20)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__156 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__156 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__156 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__156 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__156 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__156 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__156 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__156 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__156 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some (SHIFTIOP (shamt, rs1, rd, SLLI))))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__152 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__152 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__152 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__152 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__152 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__152 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__152 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__152 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__152 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some (SHIFTIOP (shamt, rs1, rd, SRLI))))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__148 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__148 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__148 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__148 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__148 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__148 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__148 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__148 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__148 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some (SHIFTIOP (shamt, rs1, rd, SRAI))))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__144 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__144 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__144 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__144 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__144 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__144 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__144 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__144 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__144 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__144 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) =>
                                          (pure (some (RTYPE (rs2, rs1, rd, ADD)))))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__140 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__140 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__140 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__140 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__140 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__140 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__140 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__140 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__140 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__140 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) =>
                                              (pure (some (RTYPE (rs2, rs1, rd, SLT)))))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__136 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__136 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__136 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__136 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__136 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__136 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__136 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__136 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__136 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__136 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) =>
                                                  (pure (some (RTYPE (rs2, rs1, rd, SLTU)))))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__132 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__132 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__132 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__132 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__132 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__132 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__132 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__132 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__132 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__132 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) =>
                                                      (pure (some (RTYPE (rs2, rs1, rd, AND)))))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__128 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__128 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__128 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__128 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__128 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__128 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__128 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__128 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__128 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__128 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) =>
                                                          (pure (some (RTYPE (rs2, rs1, rd, OR)))))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__124 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__124 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__124 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__124 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__124 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__124 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__124 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__124 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__124 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__124 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) =>
                                                              (pure (some
                                                                  (RTYPE (rs2, rs1, rd, XOR)))))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__120 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__120 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__120 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__120 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__120 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__120 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__120 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__120 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__120 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__120 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some
                                                                      (RTYPE (rs2, rs1, rd, SLL)))))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__116 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__116 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__116 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__116 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__116 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__116 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__116 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__116
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__116
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__116
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some
                                                                          (RTYPE (rs2, rs1, rd, SRL)))))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__112 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__112 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__112 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__112 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__112 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__112 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__112 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__112 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__112 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__112 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some
                                                                              (RTYPE
                                                                                (rs2, rs1, rd, SUB)))))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__108 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__108 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__108 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__108 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__108 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__108 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__108 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__108 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__108 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__108 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some
                                                                                  (RTYPE
                                                                                    (rs2, rs1, rd, SRA)))))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__106 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__106 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__106 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__106 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__106 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__106 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__106 31 20)
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__106 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__106 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__106 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__106 19 15)
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__106 31 20)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bit_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some
                                                                                        (LOAD
                                                                                          (imm, rs1, rd, is_unsigned, width))))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__103 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__103 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__103 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__103 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__103 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__103 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__103 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__103 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__103 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__103 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__103 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__103 31 25)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((let imm :=
                                                                                           (imm_11_5_ +++ imm_4_0_)
                                                                                         (width ≤b xlen_bytes)) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (let imm :=
                                                                                              (imm_11_5_ +++ imm_4_0_)
                                                                                            (STORE
                                                                                              (imm, rs2, rs1, width)))))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__100 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__100
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__100
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__100
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__100
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__100
                                                                                            31 20)
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__100
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__100
                                                                                            19 15)
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__100
                                                                                            31 20)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                (ADDIW
                                                                                                  (imm, rs1, rd))))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__96 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__96
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__96
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__96
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__96
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__96
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__96
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__96
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__96
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__96
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    (RTYPEW
                                                                                                      (rs2, rs1, rd, ADDW))))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__92 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__92
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__92
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__92
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__92
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__92
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__92
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__92
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__92
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__92
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        (RTYPEW
                                                                                                          (rs2, rs1, rd, SUBW))))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__88 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__88
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__88
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__88
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__88
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__88
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__88
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__88
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__88
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__88
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            (RTYPEW
                                                                                                              (rs2, rs1, rd, SLLW))))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__84 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__84
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__84
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__84
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__84
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__84
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__84
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__84
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__84
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__84
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                (RTYPEW
                                                                                                                  (rs2, rs1, rd, SRLW))))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__80 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__80
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__80
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__80
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__80
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__80
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__80
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__80
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__80
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__80
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    (RTYPEW
                                                                                                                      (rs2, rs1, rd, SRAW))))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__76 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__76
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__76
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__76
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__76
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__76
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let shamt : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__76
                                                                                                                    24
                                                                                                                    20)
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__76
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__76
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        (SHIFTIWOP
                                                                                                                          (shamt, rs1, rd, SLLIW))))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__72 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__72
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__72
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__72
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__72
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__72
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let shamt : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__72
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__72
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__72
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            (SHIFTIWOP
                                                                                                                              (shamt, rs1, rd, SRLIW))))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__68 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__68
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__68
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__68
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__68
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__68
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let shamt : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__68
                                                                                                                            24
                                                                                                                            20)
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__68
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__68
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                (SHIFTIWOP
                                                                                                                                  (shamt, rs1, rd, SRAIW))))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__57 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__57 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (FENCE_TSO
                                                                                                                                ())))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__57
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__57
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__57
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__57
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__57
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                let succ : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__57
                                                                                                                                    23
                                                                                                                                    20)
                                                                                                                                let pred : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__57
                                                                                                                                    27
                                                                                                                                    24)
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__57
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__57
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__57
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping77_)), (← (encdec_reg_backwards
                                                                                                                                    mapping78_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (pure (some
                                                                                                                                      (FENCE
                                                                                                                                        (fm, pred, succ, rs, rd)))))
                                                                                                                            else
                                                                                                                              (pure none))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__20 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__20 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  (ECALL
                                                                                                                                    ())))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__20 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (MRET
                                                                                                                                        ())))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__20 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          (SRET
                                                                                                                                            ())))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__20 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (EBREAK
                                                                                                                                                ())))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__20 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (WFI
                                                                                                                                                    ())))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__20
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__20
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__20
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__20
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__20
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__20
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping79_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping80_))) with
                                                                                                                                                    | (rs2, rs1) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((← (virtual_memory_supported
                                                                                                                                                                 ())) || (not
                                                                                                                                                               (true : Bool))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (SFENCE_VMA
                                                                                                                                                                (rs1, rs2))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none))))))) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__17 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping83_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__17
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping82_ : (BitVec 2) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__17
                                                                                                                                         13
                                                                                                                                         12)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__17
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_csrop_backwards_matches
                                                                                                                                           mapping82_) && (encdec_reg_backwards_matches
                                                                                                                                           mapping83_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__17
                                                                                                                                           14
                                                                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__17
                                                                                                                                           6
                                                                                                                                           0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__17
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    let mapping83_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__17
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping82_ : (BitVec 2) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__17
                                                                                                                                        13
                                                                                                                                        12)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__17
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__17
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_csrop_backwards
                                                                                                                                        mapping82_)), (← (encdec_reg_backwards
                                                                                                                                        mapping83_))) with
                                                                                                                                    | (rs1, op, rd) =>
                                                                                                                                      (do
                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                               Ext_Zicsr)) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (CSRReg
                                                                                                                                                (csr, rs1, rd, op))))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__14 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__14
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping84_ : (BitVec 2) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__14
                                                                                                                                             13
                                                                                                                                             12)
                                                                                                                                         ((encdec_csrop_backwards_matches
                                                                                                                                             mapping84_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping85_))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__14
                                                                                                                                               14
                                                                                                                                               14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                               v__14
                                                                                                                                               6
                                                                                                                                               0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let csr : (BitVec 12) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__14
                                                                                                                                            31
                                                                                                                                            20)
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__14
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping84_ : (BitVec 2) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__14
                                                                                                                                            13
                                                                                                                                            12)
                                                                                                                                        let imm : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__14
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let csr : (BitVec 12) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__14
                                                                                                                                            31
                                                                                                                                            20)
                                                                                                                                        match ((← (encdec_csrop_backwards
                                                                                                                                            mapping84_)), (← (encdec_reg_backwards
                                                                                                                                            mapping85_))) with
                                                                                                                                        | (op, rd) =>
                                                                                                                                          (do
                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                   Ext_Zicsr)) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (CSRImm
                                                                                                                                                    (csr, imm, rd, op))))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (match head_exp_ with
                                                                                                                                    | s =>
                                                                                                                                      (pure (ILLEGAL
                                                                                                                                          s)))))))))))))))))))))))))))))))))))

noncomputable def encdec_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure true)
      else (pure false))
  | .UTYPE (imm, rd, op) => (pure true)
  | .JAL (v__173, rd) =>
    (if (((Sail.BitVec.extractLsb v__173 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .JALR (imm, rs1, rd) => (pure true)
  | .BTYPE (v__175, rs2, rs1, op) =>
    (if (((Sail.BitVec.extractLsb v__175 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .ITYPE (imm, rs1, rd, op) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SLLI) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SRLI) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SRAI) => (pure true)
  | .RTYPE (rs2, rs1, rd, .ADD) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLT) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLTU) => (pure true)
  | .RTYPE (rs2, rs1, rd, .AND) => (pure true)
  | .RTYPE (rs2, rs1, rd, .OR) => (pure true)
  | .RTYPE (rs2, rs1, rd, .XOR) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLL) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SRL) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SUB) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SRA) => (pure true)
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (if ((valid_load_encdec width is_unsigned) : Bool)
    then (pure true)
    else (pure false))
  | .STORE (imm, rs2, rs1, width) => (pure true)
  | .ADDIW (imm, rs1, rd) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .ADDW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SUBW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SLLW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SRLW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SRAW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SLLIW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SRLIW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SRAIW) => (pure true)
  | .FENCE_TSO () => (pure true)
  | .FENCE (fm, pred, succ, rs, rd) => (pure true)
  | .ECALL () => (pure true)
  | .MRET () => (pure true)
  | .SRET () => (pure true)
  | .EBREAK () => (pure true)
  | .WFI () => (pure true)
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then (pure true)
      else (pure false))
  | .CSRReg (csr, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .CSRImm (csr, imm, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .ILLEGAL s => (pure true)
  | _ => (pure false)

noncomputable def encdec_backwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__332 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__332 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then (pure (some true))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__332 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__332 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__332 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__332 11 7)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__330 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__330 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__330 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__330 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__330 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__330 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__330 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__330 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__330 20 20)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (let imm := (((imm_19_19_ +++ imm_18_11_) +++ imm_10_10_) +++ imm_9_0_)
                  true))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__327 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__327 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__327 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__327 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__327 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__327 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__327 19 15)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some true)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__325 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__325 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__325 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__325 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__325 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__325 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__325 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__325 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__325 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__325 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__325 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__325 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__325 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (let imm := (((imm_11_11_ +++ imm_10_10_) +++ imm_9_4_) +++ imm_3_0_)
                          true))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__323 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__323 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__323 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__323 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__323 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__323 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__323 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__323 11 7)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some true)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__319 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__319 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__319 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__319 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__319 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__319 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__319 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__319 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__319 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some true))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__315 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__315 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__315 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__315 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__315 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__315 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__315 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__315 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__315 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some true))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__311 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__311 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__311 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__311 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__311 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__311 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__311 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__311 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__311 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some true))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__307 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__307 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__307 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__307 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__307 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__307 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__307 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__307 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__307 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__307 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) => (pure (some true)))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__303 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__303 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__303 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__303 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__303 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__303 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__303 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__303 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__303 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__303 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) => (pure (some true)))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__299 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__299 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__299 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__299 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__299 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__299 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__299 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__299 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__299 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__299 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) => (pure (some true)))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__295 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__295 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__295 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__295 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__295 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__295 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__295 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__295 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__295 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__295 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) => (pure (some true)))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__291 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__291 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__291 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__291 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__291 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__291 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__291 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__291 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__291 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__291 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) => (pure (some true)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__287 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__287 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__287 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__287 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__287 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__287 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__287 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__287 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__287 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__287 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) => (pure (some true)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__283 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__283 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__283 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__283 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__283 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__283 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__283 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__283 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__283 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__283 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some true)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__279 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__279 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__279 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__279 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__279 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__279 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__279 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__279
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__279
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__279
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some true)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__275 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__275 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__275 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__275 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__275 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__275 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__275 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__275 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__275 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__275 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some true)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__271 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__271 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__271 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__271 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__271 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__271 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__271 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__271 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__271 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__271 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some true)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__269 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__269 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__269 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__269 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__269 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__269 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__269 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__269 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__269 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__269 19 15)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bit_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some true))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__266 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__266 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__266 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__266 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__266 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__266 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__266 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__266 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__266 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__266 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__266 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__266 31 25)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((let imm :=
                                                                                           (imm_11_5_ +++ imm_4_0_)
                                                                                         (width ≤b xlen_bytes)) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (let imm :=
                                                                                              (imm_11_5_ +++ imm_4_0_)
                                                                                            true)))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__263 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__263
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__263
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__263
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__263
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__263
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__263
                                                                                            19 15)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                true))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__259 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__259
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__259
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__259
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__259
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__259
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__259
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__259
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__259
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__259
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    true))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__255 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__255
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__255
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__255
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__255
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__255
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__255
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__255
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__255
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__255
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        true))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__251 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__251
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__251
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__251
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__251
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__251
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__251
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__251
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__251
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__251
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            true))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__247 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__247
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__247
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__247
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__247
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__247
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__247
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__247
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__247
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__247
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                true))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__243 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__243
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__243
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__243
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__243
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__243
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__243
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__243
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__243
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__243
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    true))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__239 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__239
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__239
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__239
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__239
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__239
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__239
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__239
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        true))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__235 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__235
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__235
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__235
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__235
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__235
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__235
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__235
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            true))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__231 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__231
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__231
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__231
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__231
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__231
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__231
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__231
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                true))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__220 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__220 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__220
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__220
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__220
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__220
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__220
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__220
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping77_)), (← (encdec_reg_backwards
                                                                                                                                    mapping78_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (pure (some
                                                                                                                                      true)))
                                                                                                                            else
                                                                                                                              (pure none))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__183 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__183 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  true))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__183 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      true))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__183 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          true))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__183 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__183 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__183
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__183
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__183
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__183
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__183
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__183
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping79_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping80_))) with
                                                                                                                                                    | (rs2, rs1) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((← (virtual_memory_supported
                                                                                                                                                                 ())) || (not
                                                                                                                                                               (true : Bool))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              true))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none))))))) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__180 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping83_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__180
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping82_ : (BitVec 2) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__180
                                                                                                                                         13
                                                                                                                                         12)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__180
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_csrop_backwards_matches
                                                                                                                                           mapping82_) && (encdec_reg_backwards_matches
                                                                                                                                           mapping83_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__180
                                                                                                                                           14
                                                                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__180
                                                                                                                                           6
                                                                                                                                           0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping83_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__180
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping82_ : (BitVec 2) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__180
                                                                                                                                        13
                                                                                                                                        12)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__180
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_csrop_backwards
                                                                                                                                        mapping82_)), (← (encdec_reg_backwards
                                                                                                                                        mapping83_))) with
                                                                                                                                    | (rs1, op, rd) =>
                                                                                                                                      (do
                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                               Ext_Zicsr)) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__177 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__177
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping84_ : (BitVec 2) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__177
                                                                                                                                             13
                                                                                                                                             12)
                                                                                                                                         ((encdec_csrop_backwards_matches
                                                                                                                                             mapping84_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping85_))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__177
                                                                                                                                               14
                                                                                                                                               14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                               v__177
                                                                                                                                               6
                                                                                                                                               0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__177
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping84_ : (BitVec 2) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__177
                                                                                                                                            13
                                                                                                                                            12)
                                                                                                                                        match ((← (encdec_csrop_backwards
                                                                                                                                            mapping84_)), (← (encdec_reg_backwards
                                                                                                                                            mapping85_))) with
                                                                                                                                        | (op, rd) =>
                                                                                                                                          (do
                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                   Ext_Zicsr)) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (match head_exp_ with
                                                                                                                                    | s =>
                                                                                                                                      (pure true))))))))))))))))))))))))))))))))))

noncomputable def encdec_compressed_forwards (arg_ : instruction) : SailM (BitVec 16) := do
  match arg_ with
  | .C_ILLEGAL s => (pure s)
  | _ =>
    (do
      RiscvSail.assert false "Pattern match failure at unknown location"
      throw Error.Exit)

noncomputable def encdec_compressed_backwards (arg_ : (BitVec 16)) : instruction :=
  match arg_ with
  | s => (C_ILLEGAL s)

noncomputable def encdec_compressed_forwards_matches (arg_ : instruction) : Bool :=
  match arg_ with
  | .C_ILLEGAL s => true
  | _ => false

noncomputable def encdec_compressed_backwards_matches (arg_ : (BitVec 16)) : Bool :=
  match arg_ with
  | s => true

def execute_WFI (_ : Unit) : SailM ExecutionResult := do
  match (← readReg cur_privilege) with
  | .Machine => (pure (Enter_Wait WAIT_WFI))
  | .Supervisor => (pure (Enter_Wait WAIT_WFI))
  | .User =>
    (if (plat_wfi_available_to_usermode : Bool)
    then (pure (Enter_Wait WAIT_WFI))
    else (pure (Illegal_Instruction ())))
  | .VirtualUser =>
    (internal_error "extensions/I/base_insts.sail" 665 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "extensions/I/base_insts.sail" 666 "Hypervisor extension not supported")

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 64) (imm +++ 0x000#12))
  (wX_bits rd
    (← do
      match op with
      | .LUI => (pure off)
      | .AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, List.elem width [1, 2, 4, 8] -/
def execute_STORE (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  RiscvSail.assert (width ≤b xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29"
  let data ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) ((width *i 8) -i 1) 0))
  match (← (vmem_write rs1 offset width data (Store Data) false false false)) with
  | .Ok _ => (pure RETIRE_SUCCESS)
  | .Err e => (pure e)

def execute_SRET (_ : Unit) : SailM ExecutionResult := do
  let sret_illegal ← (( do
    match (← readReg cur_privilege) with
    | .User => (pure true)
    | .Supervisor =>
      (pure ((not (← (currentlyEnabled Ext_S))) || ((_get_Mstatus_TSR (← readReg mstatus)) == 1#1)))
    | .Machine => (pure (not (← (currentlyEnabled Ext_S))))
    | .VirtualUser =>
      (internal_error "extensions/I/base_insts.sail" 607 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 608 "Hypervisor extension not supported") ) :
    SailM Bool )
  if (sret_illegal : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Supervisor)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          let prev_priv ← do readReg cur_privilege
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
            (_get_Mstatus_SPIE (← readReg mstatus)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 1#1)
          writeReg cur_privilege (← do
            if (((_get_Mstatus_SPP (← readReg mstatus)) == 1#1) : Bool)
            then (pure Supervisor)
            else (pure User))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 0#1)
          if ((bne (← readReg cur_privilege) Machine) : Bool)
          then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
          else (pure ())
          if ((hartSupports Ext_Zicfilp) : Bool)
          then (zicfilp_restore_elp_on_xret sRET (← readReg cur_privilege))
          else (pure ())
          (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
          if ((get_config_print_exception ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "ret-ing from "
                  (HAppend.hAppend (← (privLevel_to_str prev_priv))
                    (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
          else (pure ())
          (set_next_pc (← (prepare_xret_target Supervisor)))
          let _ : Unit := (xret_callback false)
          (pure RETIRE_SUCCESS)))

def execute_SHIFTIWOP (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .SLLIW => (shift_bits_left rs1_val shamt)
    | .SRLIW => (shift_bits_right rs1_val shamt)
    | .SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd
    (← do
      match op with
      | .SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | .SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | .SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)

def execute_SFENCE_VMA (rs1 : regidx) (rs2 : regidx) : SailM ExecutionResult := do
  let addr ← do
    if ((bne rs1 zreg) : Bool)
    then (pure (some (← (rX_bits rs1))))
    else (pure none)
  let asid ← do
    if ((bne rs2 zreg) : Bool)
    then (pure (some (Sail.BitVec.extractLsb (← (rX_bits rs2)) (asidlen -i 1) 0)))
    else (pure none)
  match (← readReg cur_privilege) with
  | .User => (pure (Illegal_Instruction ()))
  | .Supervisor =>
    (do
      match (_get_Mstatus_TVM (← readReg mstatus)) with
      | 1 => (pure (Illegal_Instruction ()))
      | _ =>
        (do
          (flush_TLB asid addr)
          (pure RETIRE_SUCCESS)))
  | .Machine =>
    (do
      (flush_TLB asid addr)
      (pure RETIRE_SUCCESS))
  | .VirtualUser => (pure (Virtual_Instruction ()))
  | .VirtualSupervisor =>
    (internal_error "extensions/I/base_insts.sail" 692 "Hypervisor extension not supported")

def execute_RTYPEW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .ADDW => (rs1_val + rs2_val)
    | .SUBW => (rs1_val - rs2_val)
    | .SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | .SLT =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .SLTU =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | .OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | .XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | .SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | .SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)

def execute_MRET (_ : Unit) : SailM ExecutionResult := do
  if ((bne (← readReg cur_privilege) Machine) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Machine)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          let prev_priv ← do readReg cur_privilege
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3
            (_get_Mstatus_MPIE (← readReg mstatus)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7 1#1)
          writeReg cur_privilege (← (privLevel_bits_forwards
              ((_get_Mstatus_MPP (← readReg mstatus)), 0#1)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
            (privLevel_to_bits
              (← do
                if ((← (currentlyEnabled Ext_U)) : Bool)
                then (pure User)
                else (pure Machine))))
          if ((bne (← readReg cur_privilege) Machine) : Bool)
          then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
          else (pure ())
          if ((hartSupports Ext_Zicfilp) : Bool)
          then (zicfilp_restore_elp_on_xret mRET (← readReg cur_privilege))
          else (pure ())
          (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
          if ((get_config_print_exception ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "ret-ing from "
                  (HAppend.hAppend (← (privLevel_to_str prev_priv))
                    (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
          else (pure ())
          (set_next_pc (← (prepare_xret_target Machine)))
          let _ : Unit := (xret_callback true)
          (pure RETIRE_SUCCESS)))

def execute_LPAD (lpl : (BitVec 20)) : SailM ExecutionResult := do
  if ((← (is_landing_pad_expected ())) : Bool)
  then
    (do
      let unaligned_pc ← do (pure ((Sail.BitVec.extractLsb (← (get_arch_pc ())) 1 0) != 0b00#2))
      let label_mismatch ← do
        (pure (((Sail.BitVec.extractLsb (← (rX (Regno 7))) 31 12) != lpl) && (lpl != (zeros
                (n := 20)))))
      if ((unaligned_pc || label_mismatch) : Bool)
      then (trap (make_landing_pad_exception ()))
      else
        (do
          (reset_elp ())
          (pure RETIRE_SUCCESS)))
  else (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, k_ex471843_ : Bool, List.elem width [1, 2, 4, 8] -/
def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  RiscvSail.assert (width ≤b xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29"
  match (← (vmem_read rs1 offset width (Load Data) false false false)) with
  | .Ok data =>
    (do
      (wX_bits rd (extend_value is_unsigned data))
      (pure RETIRE_SUCCESS))
  | .Err e => (pure e)

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (update_elp_state rs1)
  let link_address ← do (get_next_pc ())
  let target ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  match (← (jump_to (BitVec.update target 0 0#1))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : xlenbits := (sign_extend (m := 64) imm)
  (wX_bits rd
    (← do
      match op with
      | .ADDI => (pure ((← (rX_bits rs1)) + immext))
      | .SLTI => (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) immext))))
      | .SLTIU =>
        (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) immext))))
      | .ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | .ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | .XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)

def execute_ILLEGAL (_s : (BitVec 32)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_FENCE_TSO (_ : Unit) : SailM ExecutionResult := do
  (sail_barrier Barrier_RISCV_tso)
  (pure RETIRE_SUCCESS)

def execute_FENCE (_fm : (BitVec 4)) (pred : (BitVec 4)) (succ : (BitVec 4)) (_rs : regidx) (_rd : regidx) : SailM ExecutionResult := do
  let fiom ← do (is_fiom_active ())
  let pred := (effective_fence_set pred fiom)
  let succ := (effective_fence_set succ fiom)
  match ((Sail.BitVec.extractLsb pred 1 0), (Sail.BitVec.extractLsb succ 1 0)) with
  | (0b11, 0b11) => (sail_barrier Barrier_RISCV_rw_rw)
  | (0b10, 0b11) => (sail_barrier Barrier_RISCV_r_rw)
  | (0b10, 0b10) => (sail_barrier Barrier_RISCV_r_r)
  | (0b11, 0b01) => (sail_barrier Barrier_RISCV_rw_w)
  | (0b01, 0b01) => (sail_barrier Barrier_RISCV_w_w)
  | (0b01, 0b11) => (sail_barrier Barrier_RISCV_w_rw)
  | (0b11, 0b10) => (sail_barrier Barrier_RISCV_rw_r)
  | (0b10, 0b01) => (sail_barrier Barrier_RISCV_r_w)
  | (0b01, 0b10) => (sail_barrier Barrier_RISCV_w_r)
  | (_, 0b00) => (pure ())
  | (_, _) => (pure ())
  (pure RETIRE_SUCCESS)

def execute_ECALL (_ : Unit) : SailM ExecutionResult := do
  let exc_type ← (( do
    match (← readReg cur_privilege) with
    | .User => (pure (E_U_EnvCall ()))
    | .Supervisor => (pure (E_S_EnvCall ()))
    | .Machine => (pure (E_M_EnvCall ()))
    | .VirtualUser =>
      (internal_error "extensions/I/base_insts.sail" 546 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 547 "Hypervisor extension not supported") ) :
    SailM ExceptionType )
  let t : sync_exception :=
    { trap := exc_type
      excinfo := none
      ext := none }
  (trap t)

def execute_EBREAK (_ : Unit) : SailM ExecutionResult := do
  (trap (make_sync_exception (E_Breakpoint Brk_Software) (← readReg PC)))

def execute_C_ILLEGAL (_s : (BitVec 16)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_CSRReg (csr : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := (csr_access_type op (rd == zreg) (rs1 == zreg))
  (doCSR csr (← (rX_bits rs1)) rd op access_type)

def execute_CSRImm (csr : (BitVec 12)) (imm : (BitVec 5)) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := (csr_access_type op (rd == zreg) (imm == (zeros (n := 5))))
  (doCSR csr (zero_extend (m := 64) imm) rd op access_type)

def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | .BEQ => (pure ((← (rX_bits rs1)) == (← (rX_bits rs2))))
    | .BNE => (pure ((← (rX_bits rs1)) != (← (rX_bits rs2))))
    | .BLT => (pure (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGE => (pure (zopz0zKzJ_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BLTU => (pure (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGEU => (pure (zopz0zKzJ_u (← (rX_bits rs1)) (← (rX_bits rs2)))) ) : SailM Bool )
  if (taken : Bool)
  then (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))
  else (pure RETIRE_SUCCESS)

def execute_ADDIW (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let result ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)))
  (pure RETIRE_SUCCESS)

def execute (merge_var : instruction) : SailM ExecutionResult := do
  match merge_var with
  | .LPAD lpl => (execute_LPAD lpl)
  | .UTYPE (imm, rd, op) => (execute_UTYPE imm rd op)
  | .JAL (imm, rd) => (execute_JAL imm rd)
  | .BTYPE (imm, rs2, rs1, op) => (execute_BTYPE imm rs2 rs1 op)
  | .ITYPE (imm, rs1, rd, op) => (execute_ITYPE imm rs1 rd op)
  | .SHIFTIOP (shamt, rs1, rd, op) => (execute_SHIFTIOP shamt rs1 rd op)
  | .RTYPE (rs2, rs1, rd, op) => (execute_RTYPE rs2 rs1 rd op)
  | .LOAD (imm, rs1, rd, is_unsigned, width) => (execute_LOAD imm rs1 rd is_unsigned width)
  | .STORE (imm, rs2, rs1, width) => (execute_STORE imm rs2 rs1 width)
  | .ADDIW (imm, rs1, rd) => (execute_ADDIW imm rs1 rd)
  | .RTYPEW (rs2, rs1, rd, op) => (execute_RTYPEW rs2 rs1 rd op)
  | .SHIFTIWOP (shamt, rs1, rd, op) => (execute_SHIFTIWOP shamt rs1 rd op)
  | .FENCE_TSO arg0 => (execute_FENCE_TSO arg0)
  | .FENCE (_fm, pred, succ, _rs, _rd) => (execute_FENCE _fm pred succ _rs _rd)
  | .ECALL arg0 => (execute_ECALL arg0)
  | .MRET arg0 => (execute_MRET arg0)
  | .SRET arg0 => (execute_SRET arg0)
  | .EBREAK arg0 => (execute_EBREAK arg0)
  | .WFI arg0 => (execute_WFI arg0)
  | .SFENCE_VMA (rs1, rs2) => (execute_SFENCE_VMA rs1 rs2)
  | .JALR (imm, rs1, rd) => (execute_JALR imm rs1 rd)
  | .CSRReg (csr, rs1, rd, op) => (execute_CSRReg csr rs1 rd op)
  | .CSRImm (csr, imm, rd, op) => (execute_CSRImm csr imm rd op)
  | .ILLEGAL _s => (pure (execute_ILLEGAL _s))
  | .C_ILLEGAL _s => (pure (execute_C_ILLEGAL _s))

def assembly_backwards (arg_ : String) : SailM instruction := do
  match arg_ with
  | _ => throw Error.Exit

def assembly_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

