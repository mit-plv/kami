Require Import Bool String List.
Require Import Lib.CommonTactics Lib.Word Lib.Struct.
Require Import Lts.Syntax Lts.Notations.
Require Import Ex.MemTypes Ex.SC.

(* Subset of RV32I instructions = {ld, st, add, sub, beq, blt} (+ halt) *)
Section RV32ISubset.
  Definition rv32iAddrSize := 32.
  Definition rv32iIAddrSize := 6. (* # of instructions = 64 *)
  Definition rv32iLgDataBytes := 4. (* TODO: invalid name; DataBytes is right *)
  Definition rv32iOpIdx := 7. (* always inst[6-0] *)
  Definition rv32iRfIdx := 5. (* 2^5 = 32 general purpose registers, x0 is hardcoded though *)

  Variable (insts: ConstT (Vector (Data rv32iLgDataBytes) rv32iIAddrSize)).

  Section Common.

    Definition getRs1ValueE {ty}
               (s : StateT rv32iLgDataBytes rv32iRfIdx ty)
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (#s @[UniBit (ConstExtract 12 5 _) inst])%kami_expr.
    Definition getRs2ValueE {ty}
               (s : StateT rv32iLgDataBytes rv32iRfIdx ty)
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (#s @[UniBit (ConstExtract 7 5 _) inst])%kami_expr.
    Definition getRdE {ty}
               (inst: Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      UniBit (ConstExtract 20 5 _) inst.
    Definition getLdBaseE {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (ZeroExtendTrunc _ rv32iAddrSize) (UniBit (TruncLsb 12 _) inst))%kami_expr.
    Definition getStBaseE {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (ZeroExtendTrunc _ rv32iAddrSize) (UniBit (TruncLsb 7 _) inst))%kami_expr.
    Definition getFunct7E {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (TruncLsb 7 _) inst)%kami_expr.
    Definition getFunct3E {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (ConstExtract 17 3 _) inst)%kami_expr.
    Definition getBrOffsetE {ty}
               (inst: Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (SignExtendTrunc _ rv32iIAddrSize)
              (BinBit (Concat _ 1)
                      (BinBit (Concat _ _)
                              (BinBit (Concat _ _) (UniBit (TruncLsb 1 _) inst)
                                      (UniBit (ConstExtract 24 1 _) inst))
                              (BinBit (Concat _ _) (UniBit (ConstExtract 1 6 _) inst)
                                      (UniBit (ConstExtract 20 4 _) inst)))
                      ($0)))%kami_expr.

  End Common.

  Section Opcodes.

    Definition rv32iOpLUI     := WO~0~1~1~0~1~1~1. (* U-type, load upper immediate *)
    Definition rv32iOpAUIPC   := WO~0~0~1~0~1~1~1. (* U-type, add upper immediate to PC *)
    Definition rv32iOpJAL     := WO~1~1~0~1~1~1~1. (* UJ-type, jump and link *)
    Definition rv32iOpJALR    := WO~1~1~0~0~1~1~1. (* I-type, jump and link register *)
    Definition rv32iOpBRANCH  := WO~1~1~0~0~0~1~1. (* SB-type, branch *)
    Definition rv32iOpLOAD    := WO~0~0~0~0~0~1~1. (* I-type, load *)
    Definition rv32iOpSTORE   := WO~0~1~0~0~0~1~1. (* S-type, store *)
    Definition rv32iOpOPIMM   := WO~0~0~1~0~0~1~1. (* I-type, register-immediate *)
    Definition rv32iOpOP      := WO~0~1~1~0~0~1~1. (* R-type, register-register *)
    Definition rv32iOpMISCMEM := WO~0~0~0~1~1~1~1.
    Definition rv32iOpSYSTEM  := WO~1~1~1~0~0~1~1.

  End Opcodes.

  (* NOTE: decode function simply separates memory operations and non-memory operations *)
  (* CAUTION: currently there are no distinctions among LW/LH/LB or SW/SH/SB.
   *          All loads (stores) are regarded as LW (SW).
   *)
  Definition rv32iDecode: DecT rv32iOpIdx rv32iAddrSize rv32iIAddrSize
                               rv32iLgDataBytes rv32iRfIdx.
    unfold DecT; intros ty st pc.
    set ($$insts @[ #pc ])%kami_expr as inst.
    refine (IF ((UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst)
                == ($$ rv32iOpLOAD)) then _ else _)%kami_expr.
    - (* load case *)
      exact (STRUCT { "opcode" ::= UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst;
                      "reg" ::= UniBit (ConstExtract 20 5 _) inst;
                      "addr" ::= (UniBit (ZeroExtendTrunc _ _) (getRs1ValueE st inst)
                                  + getLdBaseE inst);
                      "value" ::= $$Default;
                      "inst" ::= inst})%kami_expr.
    - refine (IF ((UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst)
                  == ($$ rv32iOpSTORE)) then _ else _)%kami_expr.
      + (* store case *)
        exact (STRUCT { "opcode" ::= (UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst);
                        "reg" ::= $$Default;
                        "addr" ::= (UniBit (ZeroExtendTrunc _ _) (getRs1ValueE st inst)
                                    + getStBaseE inst);
                        "value" ::= getRs2ValueE st inst;
                        "inst" ::= inst})%kami_expr.
      + (* others *)
        exact (STRUCT { "opcode" ::= (UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst);
                        "reg" ::= $$Default;
                        "addr" ::= $$Default;
                        "value" ::= $$Default;
                        "inst" ::= inst})%kami_expr.
  Defined.

  Section Funct7.

    Definition rv32iF7SLLI := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SRLI := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SRAI := WO~0~1~0~0~0~0~0.
    Definition rv32iF7ADD := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SUB := WO~0~1~0~0~0~0~0.
    Definition rv32iF7SLL := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SLT := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SLTU := WO~0~0~0~0~0~0~0.
    Definition rv32iF7XOR := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SRL := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SRA := WO~0~1~0~0~0~0~0.
    Definition rv32iF7OR := WO~0~0~0~0~0~0~0.
    Definition rv32iF7AND := WO~0~0~0~0~0~0~0.

  End Funct7.

  Section Funct3.

    Definition rv32iF3JALR := WO~0~0~0.
    Definition rv32iF3BEQ := WO~0~0~0.
    Definition rv32iF3BNE := WO~0~0~1.
    Definition rv32iF3BLT := WO~1~0~0.
    Definition rv32iF3BGE := WO~1~0~1.
    Definition rv32iF3BLTU := WO~1~1~0.
    Definition rv32iF3BGEU := WO~1~1~1.
    Definition rv32iF3LB := WO~0~0~0.
    Definition rv32iF3LH := WO~0~0~1.
    Definition rv32iF3LW := WO~0~1~0.
    Definition rv32iF3LBU := WO~1~0~0.
    Definition rv32iF3LHU := WO~1~0~1.
    Definition rv32iF3SB := WO~0~0~0.
    Definition rv32iF3SH := WO~0~0~1.
    Definition rv32iF3SW := WO~0~1~0.
    Definition rv32iF3ADDI := WO~0~0~0.
    Definition rv32iF3SLTI := WO~0~1~0.
    Definition rv32iF3SLTIU := WO~0~1~1.
    Definition rv32iF3XORI := WO~1~0~0.
    Definition rv32iF3ORI := WO~1~1~0.
    Definition rv32iF3ANDI := WO~1~1~1.
    Definition rv32iF3SLLI := WO~0~0~1.
    Definition rv32iF3SRLI := WO~1~0~1.
    Definition rv32iF3SRAI := WO~1~0~1.
    Definition rv32iF3ADD := WO~0~0~0.
    Definition rv32iF3SUB := WO~0~0~0.
    Definition rv32iF3SLL := WO~0~0~1.
    Definition rv32iF3SLTU := WO~0~1~1.
    Definition rv32iF3XOR := WO~1~0~0.
    Definition rv32iF3SRL := WO~1~0~1.
    Definition rv32iF3SRA := WO~1~0~1.
    Definition rv32iF3OR := WO~1~1~0.
    Definition rv32iF3AND := WO~1~1~1.
  
  End Funct3.

  Ltac register_op_funct7 inst op expr :=
    refine (IF (getFunct7E inst == $$op) then expr else _)%kami_expr.

  Definition rv32iExecState: ExecStateT rv32iOpIdx rv32iAddrSize rv32iIAddrSize
                                        rv32iLgDataBytes rv32iRfIdx.
    unfold ExecStateT; intros ty st pc dec.
    set (ReadField ``"inst" #dec)%kami_expr as inst.

    refine (IF (ReadField ``"opcode" #dec == $$rv32iOpOP) then _ else #st)%kami_expr.

    (* TODO: SLL, SLT, SLTU, XOR, *)
    register_op_funct7
      inst rv32iF7ADD
      (#st @[ getRdE inst <- getRs1ValueE st inst + getRs2ValueE st inst ])%kami_expr.
    register_op_funct7
      inst rv32iF7SUB
      (#st @[ getRdE inst <- getRs1ValueE st inst - getRs2ValueE st inst ])%kami_expr.

    exact (#st)%kami_expr.
  Defined.

  Definition rv32iExecNextPc: ExecNextPcT rv32iOpIdx rv32iAddrSize rv32iIAddrSize
                                          rv32iLgDataBytes rv32iRfIdx.
    unfold ExecNextPcT; intros ty st pc dec.
    set (ReadField {| StringBound.bindex := "inst"%string; StringBound.indexb := _ |}
                   #dec)%kami_expr as inst.

    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  #dec == $$rv32iOpBRANCH) then _ else #pc + $4)%kami_expr.

    (* branch instructions *)
    refine (IF (getFunct3E inst == $$rv32iF3BEQ) then _ else _)%kami_expr.
    - (* Beq *)
      refine (IF (getRs1ValueE st inst == getRs2ValueE st inst)
              then #pc + getBrOffsetE inst
              else #pc + $1)%kami_expr.
    - (* Blt *)
      refine (IF (getRs1ValueE st inst < getRs2ValueE st inst)
              then #pc + getBrOffsetE inst
              else #pc + $1)%kami_expr.
  Defined.
    
End RV32ISubset.

