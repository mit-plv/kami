Require Import Bool String List.
Require Import Lib.CommonTactics Lib.Word Lib.Struct Lib.StructNotation.
Require Import Lts.Syntax Lts.Notations.
Require Import Ex.MemTypes Ex.SC.

(* Subset of RV32I instructions (17/47):
 * - Branch : JAL, JALR, BEQ, BNE, BLT, BGE
 * - Memory : LW, SW
 * - Arithmetic : ADD, ADDI, SUB, SLL, SRL, SRA, OR, AND, XOR
 * Some pseudo instructions (9):
 * - LI, MV, BEQZ, BNEZ, BLEZ, BGEZ, BLTZ, BGTZ, J
 * Custom instructions (1):
 * - TOHOST
 *)
Section RV32I.
  Definition rv32iAddrSize := 4.
  Definition rv32iIAddrSize := 4. (* # of maximal instructions = 2^4 = 16 *)
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
    Definition getFunct7E {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (TruncLsb 7 _) inst)%kami_expr.
    Definition getFunct3E {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (ConstExtract 17 3 _) inst)%kami_expr.
    Definition getOffsetIE {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (UniBit (TruncLsb 12 _) inst)%kami_expr.
    Definition getOffsetSE {ty}
               (inst : Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (BinBit (Concat _ _)
              (UniBit (TruncLsb 7 _) inst)
              (UniBit (ConstExtract 20 5 _) inst))%kami_expr.
    Definition getOffsetSBE {ty}
               (inst: Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (BinBit (Concat _ 1)
              (BinBit (Concat _ _)
                      (BinBit (Concat _ _) (UniBit (TruncLsb 1 _) inst)
                              (UniBit (ConstExtract 24 1 _) inst))
                      (BinBit (Concat _ _) (UniBit (ConstExtract 1 6 _) inst)
                              (UniBit (ConstExtract 20 4 _) inst)))
              ($0))%kami_expr.
    Definition getOffsetUJE {ty}
               (inst: Expr ty (SyntaxKind (Data rv32iLgDataBytes))) :=
      (BinBit (Concat _ _)
              (BinBit (Concat _ _)
                      (UniBit (TruncLsb 1 _) inst)
                      (UniBit (ConstExtract 12 8 _) inst))
              (BinBit (Concat _ _)
                      (UniBit (ConstExtract 11 1 _) inst)
                      (UniBit (ConstExtract 1 10 _) inst))).
  End Common.

  Section Opcodes.

    Definition rv32iOpLUI     := WO~0~1~1~0~1~1~1. (* U-type, load upper immediate *)
    Definition rv32iOpAUIPC   := WO~0~0~1~0~1~1~1. (* U-type, add upper immediate to PC *)
    Definition rv32iOpJAL     := WO~1~1~0~1~1~1~1. (*v UJ-type, jump and link *)
    Definition rv32iOpJALR    := WO~1~1~0~0~1~1~1. (*v I-type, jump and link register *)
    Definition rv32iOpBRANCH  := WO~1~1~0~0~0~1~1. (*v SB-type, branch *)
    Definition rv32iOpLOAD    := WO~0~0~0~0~0~1~1. (*v I-type, load *)
    Definition rv32iOpSTORE   := WO~0~1~0~0~0~1~1. (*v S-type, store *)
    Definition rv32iOpOPIMM   := WO~0~0~1~0~0~1~1. (* I-type, register-immediate *)
    Definition rv32iOpOP      := WO~0~1~1~0~0~1~1. (*v R-type, register-register *)
    Definition rv32iOpMISCMEM := WO~0~0~0~1~1~1~1.
    Definition rv32iOpSYSTEM  := WO~1~1~1~0~0~1~1.

    Definition rv32iOpTOHOST    := WO~0~0~0~1~0~0~0. (* custom-0 opcode *)

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
                                  + (UniBit (ZeroExtendTrunc _ _) (getOffsetIE inst)));
                      "value" ::= $$Default;
                      "inst" ::= inst})%kami_expr.
    - refine (IF ((UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst)
                  == ($$ rv32iOpSTORE)) then _ else _)%kami_expr.
      + (* store case *)
        exact (STRUCT { "opcode" ::= (UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst);
                        "reg" ::= $$Default;
                        "addr" ::= (UniBit (ZeroExtendTrunc _ _) (getRs1ValueE st inst)
                                    + (UniBit (ZeroExtendTrunc _ _) (getOffsetSE inst)));
                        "value" ::= getRs2ValueE st inst;
                        "inst" ::= inst})%kami_expr.
      + refine (IF ((UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst)
                    == ($$ rv32iOpTOHOST)) then _ else _)%kami_expr.
        * (* tohost case *)
          exact (STRUCT { "opcode" ::= (UniBit (Trunc (rv32iLgDataBytes * 8 - rv32iOpIdx) _) inst);
                          "reg" ::= $$Default;
                          "addr" ::= $$Default;
                          "value" ::= getRs1ValueE st inst;
                          "inst" ::= inst})%kami_expr.
        * (* others *)
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
    Definition rv32iF7ADD := WO~0~0~0~0~0~0~0. (**)
    Definition rv32iF7SUB := WO~0~1~0~0~0~0~0. (**)
    Definition rv32iF7SLL := WO~0~0~0~0~0~0~0. (**)
    Definition rv32iF7SLT := WO~0~0~0~0~0~0~0.
    Definition rv32iF7SLTU := WO~0~0~0~0~0~0~0.
    Definition rv32iF7XOR := WO~0~0~0~0~0~0~0. (**)
    Definition rv32iF7SRL := WO~0~0~0~0~0~0~0. (**)
    Definition rv32iF7SRA := WO~0~1~0~0~0~0~0. (**)
    Definition rv32iF7OR := WO~0~0~0~0~0~0~0. (**)
    Definition rv32iF7AND := WO~0~0~0~0~0~0~0. (**)

  End Funct7.

  Section Funct3.

    Definition rv32iF3JALR := WO~0~0~0.
    Definition rv32iF3BEQ := WO~0~0~0. (**)
    Definition rv32iF3BNE := WO~0~0~1. (**)
    Definition rv32iF3BLT := WO~1~0~0. (**)
    Definition rv32iF3BGE := WO~1~0~1. (**)
    Definition rv32iF3BLTU := WO~1~1~0.
    Definition rv32iF3BGEU := WO~1~1~1.
    Definition rv32iF3LB := WO~0~0~0.
    Definition rv32iF3LH := WO~0~0~1.
    Definition rv32iF3LW := WO~0~1~0. (**)
    Definition rv32iF3LBU := WO~1~0~0.
    Definition rv32iF3LHU := WO~1~0~1.
    Definition rv32iF3SB := WO~0~0~0.
    Definition rv32iF3SH := WO~0~0~1.
    Definition rv32iF3SW := WO~0~1~0. (**)
    Definition rv32iF3ADDI := WO~0~0~0.
    Definition rv32iF3SLTI := WO~0~1~0.
    Definition rv32iF3SLTIU := WO~0~1~1.
    Definition rv32iF3XORI := WO~1~0~0.
    Definition rv32iF3ORI := WO~1~1~0.
    Definition rv32iF3ANDI := WO~1~1~1.
    Definition rv32iF3SLLI := WO~0~0~1.
    Definition rv32iF3SRLI := WO~1~0~1.
    Definition rv32iF3SRAI := WO~1~0~1.
    Definition rv32iF3ADD := WO~0~0~0. (**)
    Definition rv32iF3SUB := WO~0~0~0. (**)
    Definition rv32iF3SLL := WO~0~0~1. (**)
    Definition rv32iF3SLTU := WO~0~1~1.
    Definition rv32iF3XOR := WO~1~0~0. (**)
    Definition rv32iF3SRL := WO~1~0~1. (**)
    Definition rv32iF3SRA := WO~1~0~1. (**)
    Definition rv32iF3OR := WO~1~1~0. (**)
    Definition rv32iF3AND := WO~1~1~1. (**)
  
  End Funct3.

  Ltac register_op_funct7 inst op expr :=
    refine (IF (getFunct7E inst == $$op) then expr else _)%kami_expr.
  Ltac register_op_funct3 inst op expr :=
    refine (IF (getFunct3E inst == $$op) then expr else _)%kami_expr.

  Definition rv32iExecState: ExecStateT rv32iOpIdx rv32iAddrSize rv32iIAddrSize
                                        rv32iLgDataBytes rv32iRfIdx.
    unfold ExecStateT; intros ty st pc dec.
    set (ReadField ``"inst" #dec)%kami_expr as inst.

    refine (IF (ReadField ``"opcode" #dec == $$rv32iOpJAL)
            then #st @[getRdE inst <- (UniBit (ZeroExtendTrunc _ _) #pc) +
                       (UniBit (ZeroExtendTrunc _ _) (getOffsetUJE inst))]
            else _)%kami_expr.
    refine (IF (ReadField ``"opcode" #dec == $$rv32iOpJALR)
            then #st @[getRdE inst <- (UniBit (ZeroExtendTrunc _ _)
                                              (#pc + (UniBit (SignExtendTrunc _ _)
                                                             (getRs1ValueE st inst))
                                               + (UniBit (SignExtendTrunc _ _)
                                                         (getOffsetIE inst))))] else _)%kami_expr.
    refine (IF (ReadField ``"opcode" #dec == $$rv32iOpOP) then _ else _)%kami_expr.

    - register_op_funct7
        inst rv32iF7ADD
        (#st @[ getRdE inst <- getRs1ValueE st inst + getRs2ValueE st inst ])%kami_expr.
      register_op_funct7
        inst rv32iF7SUB
        (#st @[ getRdE inst <- getRs1ValueE st inst - getRs2ValueE st inst ])%kami_expr.
      register_op_funct7
        inst rv32iF7SLL
        (#st @[ getRdE inst <- (getRs1ValueE st inst)
                       << (UniBit (Trunc 27 5) (getRs2ValueE st inst)) ])%kami_expr.
      register_op_funct7
        inst rv32iF7SRL
        (#st @[ getRdE inst <- (getRs1ValueE st inst)
                       >> (UniBit (Trunc 27 5) (getRs2ValueE st inst)) ])%kami_expr.
      register_op_funct7
        inst rv32iF7SRA
        (#st @[ getRdE inst <- (getRs1ValueE st inst)
                       ~>> (UniBit (Trunc 27 5) (getRs2ValueE st inst)) ])%kami_expr.
      register_op_funct7
        inst rv32iF7OR
        (#st @[ getRdE inst <- (getRs1ValueE st inst) ~| (getRs2ValueE st inst) ])%kami_expr.
      register_op_funct7
        inst rv32iF7AND
        (#st @[ getRdE inst <- (getRs1ValueE st inst) ~& (getRs2ValueE st inst) ])%kami_expr.
      register_op_funct7
        inst rv32iF7XOR
        (#st @[ getRdE inst <- (getRs1ValueE st inst) ~+ (getRs2ValueE st inst) ])%kami_expr.
      exact (#st)%kami_expr.

    - refine (IF (ReadField ``"opcode" #dec == $$rv32iOpOPIMM) then _ else #st)%kami_expr.

      register_op_funct3
        inst rv32iF3ADDI
        (#st @[ getRdE inst <- getRs1ValueE st inst
                + (UniBit (ZeroExtendTrunc _ _) (getOffsetIE inst)) ])%kami_expr.
      exact (#st)%kami_expr.
  Defined.

  (* NOTE: Because instructions are not on the memory, we give (pc + 1) for the next pc.
   * Branch offsets are not aligned, so the complete offset bits are used.
   *)
  Definition rv32iExecNextPc: ExecNextPcT rv32iOpIdx rv32iAddrSize rv32iIAddrSize
                                          rv32iLgDataBytes rv32iRfIdx.
    unfold ExecNextPcT; intros ty st pc dec.
    set (ReadField {| StringBound.bindex := "inst"%string; StringBound.indexb := _ |}
                   #dec)%kami_expr as inst.

    (* NOTE: "rd" is updated by rv32iExecState *)
    refine (IF (ReadField ``"opcode" #dec == $$rv32iOpJAL)
            then #pc + (UniBit (SignExtendTrunc _ _) (getOffsetUJE inst)) else _)%kami_expr.
    refine (IF (ReadField ``"opcode" #dec == $$rv32iOpJALR)
            then #pc + (UniBit (SignExtendTrunc _ _) (getRs1ValueE st inst))
                 + (UniBit (SignExtendTrunc _ _) (getOffsetIE inst)) else _)%kami_expr.

    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  #dec == $$rv32iOpBRANCH) then _ else #pc + $1)%kami_expr.
    (* branch instructions *)
    register_op_funct3 inst rv32iF3BEQ
                       (IF (getRs1ValueE st inst == getRs2ValueE st inst)
                        then #pc + (UniBit (SignExtendTrunc _ _) (getOffsetSBE inst))
                        else #pc + $1)%kami_expr.
    register_op_funct3 inst rv32iF3BNE
                       (IF (getRs1ValueE st inst != getRs2ValueE st inst)
                        then #pc + (UniBit (SignExtendTrunc _ _) (getOffsetSBE inst))
                        else #pc + $1)%kami_expr.
    register_op_funct3 inst rv32iF3BLT
                       (IF (getRs1ValueE st inst < getRs2ValueE st inst)
                        then #pc + (UniBit (SignExtendTrunc _ _) (getOffsetSBE inst))
                        else #pc + $1)%kami_expr.
    register_op_funct3 inst rv32iF3BGE
                       (IF (getRs1ValueE st inst >= getRs2ValueE st inst)
                        then #pc + (UniBit (SignExtendTrunc _ _) (getOffsetSBE inst))
                        else #pc + $1)%kami_expr.
    exact (#pc + $1)%kami_expr.
  Defined.
    
End RV32I.

(* For easy RV32I programming *)
Section RV32IStruct.

  Inductive Gpr :=
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30 | x31.

  Definition gprToRaw (r: Gpr): word 5 :=
    match r with
    | x0 => natToWord _ 0 | x1 => natToWord _ 1 | x2 => natToWord _ 2 | x3 => natToWord _ 3
    | x4 => natToWord _ 4 | x5 => natToWord _ 5 | x6 => natToWord _ 6 | x7 => natToWord _ 7
    | x8 => natToWord _ 8 | x9 => natToWord _ 9 | x10 => natToWord _ 10 | x11 => natToWord _ 11
    | x12 => natToWord _ 12 | x13 => natToWord _ 13 | x14 => natToWord _ 14 | x15 => natToWord _ 15
    | x16 => natToWord _ 16 | x17 => natToWord _ 17 | x18 => natToWord _ 18 | x19 => natToWord _ 19
    | x20 => natToWord _ 20 | x21 => natToWord _ 21 | x22 => natToWord _ 22 | x23 => natToWord _ 23
    | x24 => natToWord _ 24 | x25 => natToWord _ 25 | x26 => natToWord _ 26 | x27 => natToWord _ 27
    | x28 => natToWord _ 28 | x29 => natToWord _ 29 | x30 => natToWord _ 30 | x31 => natToWord _ 31
    end.

  Inductive Rv32i :=
  | JAL (rd: Gpr) (ofs: word 20): Rv32i
  | JALR (rs1 rd: Gpr) (ofs: word 12): Rv32i
  | BEQ (rs1 rs2: Gpr) (ofs: word 12): Rv32i
  | BNE (rs1 rs2: Gpr) (ofs: word 12): Rv32i
  | BLT (rs1 rs2: Gpr) (ofs: word 12): Rv32i
  | BGE (rs1 rs2: Gpr) (ofs: word 12): Rv32i
  | LW (rs1 rd: Gpr) (ofs: word 12): Rv32i
  | SW (rs1 rs2: Gpr) (ofs: word 12): Rv32i
  | ADDI (rs1 rd: Gpr) (ofs: word 12): Rv32i
  | ADD (rs1 rs2 rd: Gpr): Rv32i
  | SUB (rs1 rs2 rd: Gpr): Rv32i
  | SLL (rs1 rs2 rd: Gpr): Rv32i
  | SRL (rs1 rs2 rd: Gpr): Rv32i
  | SRA (rs1 rs2 rd: Gpr): Rv32i
  | OR (rs1 rs2 rd: Gpr): Rv32i
  | AND (rs1 rs2 rd: Gpr): Rv32i
  | XOR (rs1 rs2 rd: Gpr): Rv32i
  (* pseudo-instructions *)
  | LI (rd: Gpr) (ofs: word 20): Rv32i
  | MV (rs1 rd: Gpr): Rv32i
  | BEQZ (rs1: Gpr) (ofs: word 12): Rv32i
  | BNEZ (rs1: Gpr) (ofs: word 12): Rv32i
  | BLEZ (rs1: Gpr) (ofs: word 12): Rv32i
  | BGEZ (rs1: Gpr) (ofs: word 12): Rv32i
  | BLTZ (rs1: Gpr) (ofs: word 12): Rv32i
  | BGTZ (rs1: Gpr) (ofs: word 12): Rv32i
  | J (ofs: word 20): Rv32i
  | TOHOST (rs1: Gpr): Rv32i.

  Local Infix "~~" := combine (at level 0).

  Definition offsetUJToRaw (ofs: word 20) :=
    let ofs20_12 := split2 11 9 ofs in
    let ofs11_1 := split1 11 9 ofs in
    combine (combine (split1 8 1 ofs20_12) (split2 10 1 ofs11_1))
            (combine (split1 10 1 ofs11_1) (split2 8 1 ofs20_12)).
  Definition offsetUJToRawTest:
    (offsetUJToRaw (WO~1~1~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0) =
     WO~1~1~0~0~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0) := eq_refl.

  Definition offsetSBToRaw12 (ofs: word 12) := split2 11 1 ofs.
  Definition offsetSBToRaw11 (ofs: word 12) := split2 10 1 (split1 11 1 ofs).
  Definition offsetSBToRaw10_5 (ofs: word 12) := split2 4 6 (split1 10 2 ofs).
  Definition offsetSBToRaw4_1 (ofs: word 12) := split1 4 8 ofs.
  Definition offsetSBToRawTest:
    let ofs := WO~1~1~1~0~0~0~0~0~1~0~0~0 in
    combine (combine (offsetSBToRaw4_1 ofs) (offsetSBToRaw10_5 ofs))
            (combine (offsetSBToRaw11 ofs) (offsetSBToRaw12 ofs)) =
    ofs := eq_refl.

  Definition offsetSToRaw11_5 (ofs: word 12) := split2 5 7 ofs.
  Definition offsetSToRaw4_0 (ofs: word 12) := split1 5 7 ofs.

  Definition RtypeToRaw (op: word 7) (rs1 rs2 rd: Gpr) (f7: word 7) (f3: word 3) :=
    op~~(gprToRaw rd)~~f3~~(gprToRaw rs1)~~(gprToRaw rs2)~~f7.
  Definition ItypeToRaw (op: word 7) (rs1 rd: Gpr) (f3: word 3) (ofs: word 12) :=
    op~~(gprToRaw rd)~~f3~~(gprToRaw rs1)~~ofs.
  Definition StypeToRaw (op: word 7) (rs1 rs2: Gpr) (f3: word 3) (ofs: word 12) :=
    op~~(offsetSToRaw4_0 ofs)~~f3~~(gprToRaw rs1)~~(gprToRaw rs2)~~(offsetSToRaw11_5 ofs).
  Definition SBtypeToRaw (op: word 7) (rs1 rs2: Gpr) (f3: word 3) (ofs: word 12) :=
    op~~(offsetSBToRaw11 ofs)~~(offsetSBToRaw4_1 ofs)
      ~~f3~~(gprToRaw rs1)~~(gprToRaw rs2)
      ~~(offsetSBToRaw10_5 ofs)~~(offsetSBToRaw12 ofs).
  Definition UJtypeToRaw (op: word 7) (rd: Gpr) (ofs: word 20) :=
    op~~(gprToRaw rd)~~(offsetUJToRaw ofs).
               
  Fixpoint rv32iToRaw (inst: Rv32i): word 32 :=
    match inst with
    | JAL rd ofs => UJtypeToRaw rv32iOpJAL rd ofs
    | JALR rs1 rd ofs => ItypeToRaw rv32iOpJALR rs1 rd WO~0~0~0 ofs
    | BEQ rs1 rs2 ofs => SBtypeToRaw rv32iOpBRANCH rs1 rs2 rv32iF3BEQ ofs
    | BNE rs1 rs2 ofs => SBtypeToRaw rv32iOpBRANCH rs1 rs2 rv32iF3BNE ofs
    | BLT rs1 rs2 ofs => SBtypeToRaw rv32iOpBRANCH rs1 rs2 rv32iF3BLT ofs
    | BGE rs1 rs2 ofs => SBtypeToRaw rv32iOpBRANCH rs1 rs2 rv32iF3BGE ofs
    | LW rs1 rd ofs => ItypeToRaw rv32iOpLOAD rs1 rd rv32iF3LW ofs
    | SW rs1 rs2 ofs => StypeToRaw rv32iOpSTORE rs1 rs2 rv32iF3SW ofs
    | ADDI rs1 rd ofs => ItypeToRaw rv32iOpOPIMM rs1 rd rv32iF3ADDI ofs
    | ADD rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7ADD rv32iF3ADD
    | SUB rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7SUB rv32iF3SUB
    | SLL rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7SLL rv32iF3SLL
    | SRL rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7SRL rv32iF3SRL
    | SRA rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7SRA rv32iF3SRA
    | OR rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7OR rv32iF3OR
    | AND rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7AND rv32iF3AND
    | XOR rs1 rs2 rd => RtypeToRaw rv32iOpOP rs1 rs2 rd rv32iF7XOR rv32iF3XOR
    (* pseudo-instructions *)
    | LI rd ofs => ItypeToRaw rv32iOpOPIMM x0 rd rv32iF3ADDI (split1 12 8 ofs)
    | MV rs1 rd => ItypeToRaw rv32iOpOPIMM rs1 rd rv32iF3ADDI (natToWord _ 0)
    | BEQZ rs1 ofs => SBtypeToRaw rv32iOpBRANCH rs1 x0 rv32iF3BEQ ofs
    | BNEZ rs1 ofs => SBtypeToRaw rv32iOpBRANCH rs1 x0 rv32iF3BNE ofs 
    | BLEZ rs1 ofs => SBtypeToRaw rv32iOpBRANCH x0 rs1 rv32iF3BGE ofs
    | BGEZ rs1 ofs => SBtypeToRaw rv32iOpBRANCH rs1 x0 rv32iF3BGE ofs
    | BLTZ rs1 ofs => SBtypeToRaw rv32iOpBRANCH rs1 x0 rv32iF3BLT ofs
    | BGTZ rs1 ofs => SBtypeToRaw rv32iOpBRANCH x0 rs1 rv32iF3BLT ofs
    | J ofs => UJtypeToRaw rv32iOpJAL x0 ofs
    | TOHOST rs1 => RtypeToRaw rv32iOpTOHOST rs1 x0 x0 rv32iF7ADD rv32iF3ADD
    end.

End RV32IStruct.

Section Examples.

  Section Fibonacci.

    Definition pgmFibonacci (n: nat) : ConstT (Vector (Data rv32iLgDataBytes) rv32iIAddrSize).
      refine (ConstVector _).
      refine (VecNext
                (VecNext
                   (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                   (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))
                (VecNext
                   (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                   (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))).
      - exact (ConstBit (rv32iToRaw (LI x21 (natToWord _ n)))).
      - exact (ConstBit (rv32iToRaw (BLEZ x21 (natToWord _ 12)))).
      - exact (ConstBit (rv32iToRaw (LI x9 (natToWord _ 1)))).
      - exact (ConstBit (rv32iToRaw (MV x21 x6))).
      - exact (ConstBit (rv32iToRaw (MV x9 x8))).
      - exact (ConstBit (rv32iToRaw (MV x9 x7))).
      - exact (ConstBit (rv32iToRaw (ADD x7 x8 x5))).
      - exact (ConstBit (rv32iToRaw (ADDI x9 x9 (natToWord _ 1)))).
      - exact (ConstBit (rv32iToRaw (MV x8 x7))).
      - exact (ConstBit (rv32iToRaw (MV x5 x8))).
      - exact (ConstBit (rv32iToRaw (BNE x6 x9 (natToWord _ 6)))).
      - exact (ConstBit (rv32iToRaw (TOHOST x5))).
      - exact (ConstBit (rv32iToRaw (LI x5 (natToWord _ 1)))).
      - exact (ConstBit (rv32iToRaw (J (natToWord _ 11)))).
      - exact (ConstBit (wzero _)).
      - exact (ConstBit (wzero _)).
    Defined.
    
  End Fibonacci.

End Examples.

