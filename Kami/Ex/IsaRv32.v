Require Import Bool String List Vector ZArith.BinInt.
Require Import Lib.CommonTactics Lib.Word Lib.Struct.
Require Import Kami.Syntax Kami.Semantics Kami.Notations.
Require Import Ex.MemTypes Ex.SC.

Definition rv32InstBytes := 4.
Definition rv32DataBytes := 4.
(* 2^5 = 32 general purpose registers, x0 is hardcoded though *)
Definition rv32RfIdx := 5. 

Section Common.

  Definition getOpcodeE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (Trunc 7 _) inst)%kami_expr.

  Definition getRs1E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 15 5 _) inst)%kami_expr.
  
  Definition getRs1ValueE {ty}
             (s : StateT rv32DataBytes rv32RfIdx ty)
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (#s @[getRs1E inst])%kami_expr.

  Definition getRs2E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 20 5 _) inst)%kami_expr.

  Definition getRs2ValueE {ty}
             (s : StateT rv32DataBytes rv32RfIdx ty)
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (#s @[getRs2E inst])%kami_expr.

  Definition getRdE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    UniBit (ConstExtract 7 5 _) inst.

  Definition getFunct7E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 25 7) inst)%kami_expr.

  Definition getFunct6E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 26 6) inst)%kami_expr.

  Definition getFunct3E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 12 3 _) inst)%kami_expr.

  Definition getOffsetIE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 20 12) inst)%kami_expr.

  Definition getOffsetShamtE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 20 5 _) inst)%kami_expr.

  Definition getHiShamtE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 25 1 _) inst)%kami_expr.

  Definition getOffsetSE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (BinBit (Concat _ _)
            (UniBit (TruncLsb 25 7) inst)
            (UniBit (ConstExtract 7 5 _) inst))%kami_expr.

  Definition getOffsetSBE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (BinBit (Concat _ _)
            (BinBit (Concat _ _)
                    (UniBit (TruncLsb 31 1) inst)
                    (UniBit (ConstExtract 7 1 _) inst))
            (BinBit (Concat _ _)
                    (UniBit (ConstExtract 25 6 _) inst)
                    (UniBit (ConstExtract 8 4 _) inst)))%kami_expr.

  Definition getOffsetUE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 12 20) inst)%kami_expr.

  Definition getOffsetUJE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (BinBit (Concat _ _)
            (BinBit (Concat _ _)
                    (UniBit (TruncLsb 31 1) inst)
                    (UniBit (ConstExtract 12 8 _) inst))
            (BinBit (Concat _ _)
                    (UniBit (ConstExtract 20 1 _) inst)
                    (UniBit (ConstExtract 21 10 _) inst))).
End Common.

(** RV32I instructions (#instructions=40, categorized by opcode_)):
 * - Supported(37)
 *   + opcode_LUI(1): lui
 *   + opcode_AUIPC(1): auipc
 *   + opcode_JAL(1): jal
 *   + opcode_JALR(1): jalr
 *   + opcode_BRANCH(6): beq, bne, blt, bge, bltu, bgeu
 *   + opcode_LOAD(5): lb, lh, lw, lbu, lhu
 *   + opcode_STORE(3): sb, sh, sw
 *   + opcode_OP_IMM(9): addi, slti, sltiu, xori, ori, andi, slli, srli, srai
 *   + opcode_OP(10): add, sub, sll, slt, sltu, xor, srl, sra, or, and
 * - Treat as nop(3)
 *   + opcode_MISC_MEM(1): fence
 *   + opcode_SYSTEM(2): ecall, ebreak
 *   + NOTE: these instructions do not appear in [rv32DoExec] but since they
 *     require [rd = 0] thus [rv32DoExec] is not even called; they are handled
 *     by a rule when [rd = 0] (e.g., [execNmZ] in SC.v).
 *)

Section RV32IM.
  Variables rv32AddrSize (* 2^(rv32AddrSize) memory cells *)
            rv32IAddrSize: nat. (* 2^(rv32IAddrSize) instructions *)

  Hypotheses (Haddr1: rv32AddrSize = 2 + (rv32AddrSize - 2))
             (Haddr2: rv32AddrSize = 1 + 1 + (rv32AddrSize - 2))
             (Haddr3: rv32AddrSize = 2 + rv32IAddrSize
                                     + (rv32AddrSize - (2 + rv32IAddrSize))).

  Section Constants.

    Definition opcode_AUIPC: nat := 23.
    Definition opcode_BRANCH: nat := 99.
    Definition opcode_LOAD: nat := 3.
    Definition opcode_LUI: nat := 55.
    Definition opcode_JAL: nat := 111.
    Definition opcode_JALR: nat := 103.
    Definition opcode_OP: nat := 51.
    Definition opcode_OP_IMM: nat := 19.
    Definition opcode_STORE: nat := 35.

    Definition funct7_XOR: nat := 0.
    Definition funct7_SUBW: nat := 32.
    Definition funct7_SUB: nat := 32.
    Definition funct7_SRLW: nat := 0.
    Definition funct7_SRLIW: nat := 0.
    Definition funct7_SRL: nat := 0.
    Definition funct7_SRAW: nat := 32.
    Definition funct7_SRAIW: nat := 32.
    Definition funct7_SRA: nat := 32.
    Definition funct7_SLTU: nat := 0.
    Definition funct7_SLT: nat := 0.
    Definition funct7_SLLW: nat := 0.
    Definition funct7_SLLIW: nat := 0.
    Definition funct7_SLL: nat := 0.
    Definition funct7_SFENCE_VMA: nat := 9.
    Definition funct7_REMW: nat := 1.
    Definition funct7_REMUW: nat := 1.
    Definition funct7_REMU: nat := 1.
    Definition funct7_REM: nat := 1.
    Definition funct7_OR: nat := 0.
    Definition funct7_MULW: nat := 1.
    Definition funct7_MULHU: nat := 1.
    Definition funct7_MULHSU: nat := 1.
    Definition funct7_MULH: nat := 1.
    Definition funct7_MUL: nat := 1.
    Definition funct7_FSUB_S := 4: nat.
    Definition funct7_FSQRT_S := 44: nat.
    Definition funct7_FSGNJ_S := 16: nat.
    Definition funct7_FMV_X_W := 112: nat.
    Definition funct7_FMV_W_X := 120: nat.
    Definition funct7_FMUL_S := 8: nat.
    Definition funct7_FMIN_S := 20: nat.
    Definition funct7_FEQ_S := 80: nat.
    Definition funct7_FDIV_S := 12: nat.
    Definition funct7_FCVT_W_S := 96: nat.
    Definition funct7_FCVT_S_W := 104: nat.
    Definition funct7_FCLASS_S := 112: nat.
    Definition funct7_FADD_S := 0: nat.
    Definition funct7_DIVW: nat := 1.
    Definition funct7_DIVUW: nat := 1.
    Definition funct7_DIVU: nat := 1.
    Definition funct7_DIV: nat := 1.
    Definition funct7_AND: nat := 0.
    Definition funct7_ADDW: nat := 0.
    Definition funct7_ADD: nat := 0.

    Definition funct3_XORI: nat := 4.
    Definition funct3_XOR: nat := 4.
    Definition funct3_SW: nat := 2.
    Definition funct3_SUBW: nat := 0.
    Definition funct3_SUB: nat := 0.
    Definition funct3_SRLW: nat := 5.
    Definition funct3_SRLIW: nat := 5.
    Definition funct3_SRLI: nat := 5.
    Definition funct3_SRL: nat := 5.
    Definition funct3_SRAW: nat := 5.
    Definition funct3_SRAIW: nat := 5.
    Definition funct3_SRAI: nat := 5.
    Definition funct3_SRA: nat := 5.
    Definition funct3_SLTU: nat := 3.
    Definition funct3_SLTIU: nat := 3.
    Definition funct3_SLTI: nat := 2.
    Definition funct3_SLT: nat := 2.
    Definition funct3_SLLW: nat := 1.
    Definition funct3_SLLIW: nat := 1.
    Definition funct3_SLLI: nat := 1.
    Definition funct3_SLL: nat := 1.
    Definition funct3_SH: nat := 1.
    Definition funct3_SD: nat := 3.
    Definition funct3_SB: nat := 0.
    Definition funct3_REMW: nat := 6.
    Definition funct3_REMUW: nat := 7.
    Definition funct3_REMU: nat := 7.
    Definition funct3_REM: nat := 6.
    Definition funct3_PRIV: nat := 0.
    Definition funct3_ORI: nat := 6.
    Definition funct3_OR: nat := 6.
    Definition funct3_MULW: nat := 0.
    Definition funct3_MULHU: nat := 3.
    Definition funct3_MULHSU: nat := 2.
    Definition funct3_MULH: nat := 1.
    Definition funct3_MUL: nat := 0.
    Definition funct3_LWU: nat := 6.
    Definition funct3_LW: nat := 2.
    Definition funct3_LHU: nat := 5.
    Definition funct3_LH: nat := 1.
    Definition funct3_LD: nat := 3.
    Definition funct3_LBU: nat := 4.
    Definition funct3_LB: nat := 0.
    Definition funct3_FSW: nat := 2.
    Definition funct3_FSGNJ_S: nat := 0.
    Definition funct3_FSGNJX_S: nat := 2.
    Definition funct3_FSGNJN_S: nat := 1.
    Definition funct3_FMV_X_W: nat := 0.
    Definition funct3_FMIN_S: nat := 0.
    Definition funct3_FMAX_S: nat := 1.
    Definition funct3_FLW: nat := 2.
    Definition funct3_FLT_S: nat := 1.
    Definition funct3_FLE_S: nat := 0.
    Definition funct3_FEQ_S: nat := 2.
    Definition funct3_FENCE_I: nat := 1.
    Definition funct3_FENCE: nat := 0.
    Definition funct3_FCLASS_S: nat := 1.
    Definition funct3_DIVW: nat := 4.
    Definition funct3_DIVUW: nat := 5.
    Definition funct3_DIVU: nat := 5.
    Definition funct3_DIV: nat := 4.
    Definition funct3_CSRRWI: nat := 5.
    Definition funct3_CSRRW: nat := 1.
    Definition funct3_CSRRSI: nat := 6.
    Definition funct3_CSRRS: nat := 2.
    Definition funct3_CSRRCI: nat := 7.
    Definition funct3_CSRRC: nat := 3.
    Definition funct3_BNE: nat := 1.
    Definition funct3_BLTU: nat := 6.
    Definition funct3_BLT: nat := 4.
    Definition funct3_BGEU: nat := 7.
    Definition funct3_BGE: nat := 5.
    Definition funct3_BEQ: nat := 0.
    Definition funct3_ANDI: nat := 7.
    Definition funct3_AND: nat := 7.
    Definition funct3_AMOW: nat := 2.
    Definition funct3_AMOD: nat := 3.
    Definition funct3_ADDW: nat := 0.
    Definition funct3_ADDIW: nat := 0.
    Definition funct3_ADDI: nat := 0.
    Definition funct3_ADD: nat := 0.

    Definition funct6_SRLI: nat := 0.
    Definition funct6_SRAI: nat := 16.
    Definition funct6_SLLI: nat := 0.

  End Constants.

  Ltac register_op_funct7 inst op expr :=
    refine (IF (getFunct7E #inst == $op) then expr else _)%kami_expr.
  Ltac register_op_funct3 inst op expr :=
    refine (IF (getFunct3E #inst == $op) then expr else _)%kami_expr.
  Ltac register_op_funct6_funct3 inst op6 op3 expr :=
    refine (IF (getFunct6E #inst == $op6 && getFunct3E #inst == $op3 && getHiShamtE #inst == $0)
            then expr else _)%kami_expr.

  Section Decode.

    Definition rv32GetOptype: OptypeT rv32InstBytes.
      unfold OptypeT; intros ty inst.
      refine (IF (getOpcodeE #inst == $opcode_LOAD) then $$opLd else _)%kami_expr.
      refine (IF (getOpcodeE #inst == $opcode_STORE) then $$opSt else $$opNm)%kami_expr.
    Defined.

    Definition rv32GetLdDst: LdDstT rv32InstBytes rv32RfIdx.
      unfold LdDstT; intros ty inst.
      exact (getRdE #inst)%kami_expr.
    Defined.

    Definition rv32GetLdAddr: LdAddrT rv32AddrSize rv32InstBytes.
      unfold LdAddrT; intros ty inst.
      exact (_signExtend_ (getOffsetIE #inst))%kami_expr.
    Defined.

    Definition rv32GetLdSrc: LdSrcT rv32InstBytes rv32RfIdx.
      unfold LdSrcT; intros ty inst.
      exact (getRs1E #inst)%kami_expr.
    Defined.

    Definition rv32CalcLdAddr: LdAddrCalcT rv32AddrSize rv32DataBytes.
      unfold LdAddrCalcT; intros ty ofs base.
      exact ((_zeroExtend_ #base) + #ofs)%kami_expr.
    Defined.

    Definition rv32GetLdType: LdTypeT rv32InstBytes.
      unfold LdTypeT; intros ty inst.
      exact (getFunct3E #inst)%kami_expr.
    Defined.

    Definition rv32GetStAddr: StAddrT rv32AddrSize rv32InstBytes.
      unfold StAddrT; intros ty inst.
      exact (_signExtend_ (getOffsetSE #inst))%kami_expr.
    Defined.
      
    Definition rv32GetStSrc: StSrcT rv32InstBytes rv32RfIdx.
      unfold StSrcT; intros ty inst.
      exact (getRs1E #inst)%kami_expr.
    Defined.
    
    Definition rv32CalcStAddr: StAddrCalcT rv32AddrSize rv32DataBytes.
      unfold StAddrCalcT; intros ty ofs base.
      exact ((_zeroExtend_ #base) + (_signExtend_ #ofs))%kami_expr.
    Defined.

    Definition rv32CalcStByteEn: StByteEnCalcT rv32InstBytes rv32DataBytes.
      unfold StByteEnCalcT; intros ty inst.
      register_op_funct3
        inst funct3_SB
        (Const ty (ConstArray (cons _ (ConstBool true) _
                                    (cons _ (ConstBool false) _
                                          (cons _ (ConstBool false) _
                                                (cons _ (ConstBool false) _ (nil _))))))).
      register_op_funct3
        inst funct3_SH
        (Const ty (ConstArray (cons _ (ConstBool true) _
                                    (cons _ (ConstBool true) _
                                          (cons _ (ConstBool false) _
                                                (cons _ (ConstBool false) _ (nil _))))))).
      exact (Const ty (ConstArray (cons _ (ConstBool true) _
                                        (cons _ (ConstBool true) _
                                              (cons _ (ConstBool true) _
                                                    (cons _ (ConstBool true) _ (nil _))))))).
    Defined.

    Definition rv32GetStVSrc: StVSrcT rv32InstBytes rv32RfIdx.
      unfold StVSrcT; intros ty inst.
      exact (getRs2E #inst)%kami_expr.
    Defined.

    Definition rv32GetSrc1: Src1T rv32InstBytes rv32RfIdx.
      unfold Src1T; intros ty inst.
      exact (getRs1E #inst)%kami_expr.
    Defined.
    
    Definition rv32GetSrc2: Src2T rv32InstBytes rv32RfIdx.
      unfold Src2T; intros ty inst.
      exact (getRs2E #inst)%kami_expr.
    Defined.

    Definition rv32GetDst: DstT rv32InstBytes rv32RfIdx.
      unfold DstT; intros ty inst.
      refine (IF (getOpcodeE #inst == $opcode_BRANCH) then _ else _)%kami_expr.
      - exact ($0)%kami_expr. (* Branch instructions should not write registers *)
      - exact (getRdE #inst)%kami_expr.
    Defined.

  End Decode.
    
  Ltac rv32_undefined :=
    exact ($$Default)%kami_expr.

  Definition rv32DoExec: ExecT rv32AddrSize rv32InstBytes rv32DataBytes.
    unfold ExecT; intros ty val1 val2 pc inst.

    refine (IF (getOpcodeE #inst == $opcode_LUI)
            then {getOffsetUE #inst, $0::(12)}
            else _)%kami_expr.
    refine (IF (getOpcodeE #inst == $opcode_AUIPC)
            then ((_zeroExtend_ #pc) + {getOffsetUE #inst, $0::(12)})
            else _)%kami_expr.
    refine (IF (getOpcodeE #inst == $opcode_JAL)
            then (_zeroExtend_ (#pc + $4))
            else _)%kami_expr.
    refine (IF (getOpcodeE #inst == $opcode_JALR)
            then (_zeroExtend_ (#pc + $4))
            else _)%kami_expr.

    refine (IF (getOpcodeE #inst == $opcode_OP_IMM) then _ else _)%kami_expr.
    1: {
      register_op_funct3 inst funct3_ADDI
                         (#val1 + (_signExtend_ (getOffsetIE #inst)))%kami_expr.
      register_op_funct3 inst funct3_SLTI
                         (IF (#val1 <s (_signExtend_ (getOffsetIE #inst)))
                          then $1 else $$(natToWord (rv32DataBytes * 8) 0))%kami_expr.
      register_op_funct3 inst funct3_SLTIU
                         (IF (#val1 < (_signExtend_ (getOffsetIE #inst)))
                          then $1 else $$(natToWord (rv32DataBytes * 8) 0))%kami_expr.
      register_op_funct3 inst funct3_XORI
                         (#val1 ~+ (_signExtend_ (getOffsetIE #inst)))%kami_expr.
      register_op_funct3 inst funct3_ORI
                         (#val1 ~| (_signExtend_ (getOffsetIE #inst)))%kami_expr.
      register_op_funct3 inst funct3_ANDI
                         (#val1 ~& (_signExtend_ (getOffsetIE #inst)))%kami_expr.

      register_op_funct6_funct3 inst funct6_SLLI funct3_SLLI
                                (#val1 << (getOffsetShamtE #inst))%kami_expr.
      register_op_funct6_funct3 inst funct6_SRLI funct3_SRLI
                                (#val1 >> (getOffsetShamtE #inst))%kami_expr.
      register_op_funct6_funct3 inst funct6_SRAI funct3_SRAI
                                (#val1 ~>> (getOffsetShamtE #inst))%kami_expr.
      rv32_undefined.
    }

    refine (IF (getOpcodeE #inst == $opcode_OP) then _ else _)%kami_expr.
    1: {
      refine (IF (getFunct7E #inst == $$(WO~0~0~0~0~0~0~0)) then _ else _)%kami_expr.
      1: {
        register_op_funct3 inst funct3_ADD (#val1 + #val2)%kami_expr.
        register_op_funct3 inst funct3_SLL (#val1 << (UniBit (Trunc 5 _) #val2))%kami_expr.
        register_op_funct3 inst funct3_SLT
                           (IF (#val1 <s #val2)
                            then $1 else $$(natToWord (rv32DataBytes * 8) 0))%kami_expr.
        register_op_funct3 inst funct3_SLTU
                           (IF (#val1 < #val2)
                            then $1 else $$(natToWord (rv32DataBytes * 8) 0))%kami_expr.
        register_op_funct3 inst funct3_XOR (#val1 ~+ #val2)%kami_expr.
        register_op_funct3 inst funct3_SRL (#val1 >> (UniBit (Trunc 5 _) #val2))%kami_expr.
        register_op_funct3 inst funct3_OR (#val1 ~| #val2)%kami_expr.
        register_op_funct3 inst funct3_AND (#val1 ~& #val2)%kami_expr.
        rv32_undefined.
      }

      refine (IF (getFunct7E #inst == $$(WO~0~1~0~0~0~0~0)) then _ else _)%kami_expr.
      1: {
        register_op_funct3 inst funct3_SUB (#val1 - #val2)%kami_expr.
        register_op_funct3 inst funct3_SRA (#val1 ~>> (UniBit (Trunc 5 _) #val2))%kami_expr.
        rv32_undefined.
      }
      
      rv32_undefined.
    }

    rv32_undefined.
  Defined.

  Definition rv32CalcLdVal: LdValCalcT rv32AddrSize rv32DataBytes.
    unfold LdValCalcT; intros ty addr val ldty.
    refine (IF (#ldty == $funct3_LB)
            then _signExtend_ (UniBit (Trunc BitsPerByte _) #val)
            else _)%kami_expr.
    refine (IF (#ldty == $funct3_LH)
            then _signExtend_ (UniBit (Trunc (2 * BitsPerByte) _) #val)
            else _)%kami_expr.
    refine (IF (#ldty == $funct3_LBU)
            then _zeroExtend_ (UniBit (Trunc BitsPerByte _) #val)
            else _)%kami_expr.
    refine (IF (#ldty == $funct3_LHU)
            then _zeroExtend_ (UniBit (Trunc (2 * BitsPerByte) _) #val)
            else #val)%kami_expr.
  Defined.

  Definition rv32ToIAddr: ToIAddrT rv32AddrSize rv32IAddrSize.
    unfold ToIAddrT; intros ty addr.
    rewrite Haddr3 in addr.
    exact (_truncLsb_ (_truncate_ #addr))%kami_expr.
  Defined.

  Definition rv32ToAddr: ToAddrT rv32AddrSize rv32IAddrSize.
    unfold ToAddrT; intros ty iaddr.
    rewrite Haddr3.
    exact {$0, {#iaddr, $0}}%kami_expr.
  Defined.

  Definition rv32AlignInst: AlignInstT rv32InstBytes rv32DataBytes.
    unfold AlignInstT; intros ty data.
    exact (#data)%kami_expr.
  Defined.

  Definition rv32NextPc: NextPcT rv32AddrSize rv32InstBytes rv32DataBytes rv32RfIdx.
    unfold NextPcT; intros ty st pc inst.

    refine (IF (getOpcodeE #inst == $opcode_JAL)
            then #pc + (_signExtend_ {getOffsetUJE #inst, $$(WO~0)})
            else _)%kami_expr.
    refine (IF (getOpcodeE #inst == $opcode_JALR)
            then ((_signExtend_ (getRs1ValueE st #inst) + _signExtend_ (getOffsetIE #inst))
                    ~& (UniBit (Inv _) $1))
            else _)%kami_expr.

    refine (IF (getOpcodeE #inst == $opcode_BRANCH) then _ else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BEQ
                       (IF (getRs1ValueE st #inst == getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BNE
                       (IF (getRs1ValueE st #inst != getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BLT
                       (IF (getRs1ValueE st #inst <s getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BGE
                       (IF (getRs1ValueE st #inst >s= getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BLTU
                       (IF (getRs1ValueE st #inst < getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BGEU
                       (IF (getRs1ValueE st #inst >= getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    exact (#pc + $4)%kami_expr.
  Defined.

  Instance rv32Fetch: AbsFetch rv32AddrSize rv32IAddrSize rv32InstBytes rv32DataBytes :=
    {| toIAddr := rv32ToIAddr;
       toAddr := rv32ToAddr;
       alignInst := rv32AlignInst |}.

  Instance rv32Dec: AbsDec rv32AddrSize rv32InstBytes rv32DataBytes rv32RfIdx :=
    {| getOptype := rv32GetOptype;
       getLdDst := rv32GetLdDst;
       getLdAddr := rv32GetLdAddr;
       getLdSrc := rv32GetLdSrc;
       calcLdAddr := rv32CalcLdAddr;
       getLdType := rv32GetLdType;
       getStAddr := rv32GetStAddr;
       getStSrc := rv32GetStSrc;
       calcStAddr := rv32CalcStAddr;
       calcStByteEn := rv32CalcStByteEn;
       getStVSrc := rv32GetStVSrc;
       getSrc1 := rv32GetSrc1;
       getSrc2 := rv32GetSrc2;
       getDst := rv32GetDst |}.

  Instance rv32Exec:
    AbsExec rv32AddrSize rv32InstBytes rv32DataBytes rv32RfIdx :=
    {| calcLdVal := rv32CalcLdVal;
       doExec := rv32DoExec;
       getNextPc := rv32NextPc |}.

End RV32IM.

