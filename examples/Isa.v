Require Import Bool String List.
Require Import Lib.CommonTactics Lib.Word.
Require Import Lts.Syntax Lts.Notations.
Require Import Ex.MemTypes Ex.SC.

(* Subset of RV32I instructions = {ld, st, halt, add, sub, beq, blt} *)
Section RV32ISubset.
  Definition rv32iAddrSize := 32.
  Definition rv32iLgDataBytes := 4.
  Definition rv32iOpIdx := 7. (* always inst[6-0] *)
  Definition rv32iRfIdx := 5. (* 2^5 = 32 general purpose registers, x0 is hardcoded though *)

  Variable (insts: ConstT (Vector (Data rv32iLgDataBytes) rv32iAddrSize)).

  Definition rv32iLd := WO~0~0~0~0~0~1~1.
  Definition rv32iSt := WO~0~1~0~0~0~1~1.
  Definition rv32iHt := WO~0~0~0~0~0~0~0. 
  Definition rv32iOp := WO~0~1~1~0~0~1~1. (* Register-Register operations *)
  Definition rv32iBr := WO~1~1~0~0~0~1~1. (* Branch operations *)

  Definition rv32iAdd := WO~0~0~0~0~0~0~0. (* funct7 Add *)
  Definition rv32iSub := WO~0~1~0~0~0~0~0. (* funct7 Sub *)

  Definition rv32iBeq := WO~0~0~0. (* funct3 Beq *)
  Definition rv32iBlt := WO~1~0~0. (* funct3 Blt *)

  Definition getRs1ValueE {ty}
             (s : StateT rv32iLgDataBytes rv32iRfIdx ty)
             (inst : Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (#s @[UniBit (ConstExtract 12 5 _) inst])%kami_expr.
  Definition getRs2ValueE {ty}
             (s : StateT rv32iLgDataBytes rv32iRfIdx ty)
             (inst : Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (#s @[UniBit (ConstExtract 7 5 _) inst])%kami_expr.
  Definition getRdE {ty}
             (inst: Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    UniBit (ConstExtract 20 5 _) inst.
  Definition getLdBaseE {ty}
             (inst : Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (UniBit (ZeroExtendTrunc _ rv32iAddrSize) (UniBit (TruncLsb 12 _) inst))%kami_expr.
  Definition getStBaseE {ty}
             (inst : Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (UniBit (ZeroExtendTrunc _ rv32iAddrSize) (UniBit (TruncLsb 7 _) inst))%kami_expr.
  Definition getFunct7E {ty}
             (inst : Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (UniBit (TruncLsb 7 _) inst)%kami_expr.
  Definition getFunct3E {ty}
             (inst : Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (UniBit (ConstExtract 17 3 _) inst)%kami_expr.
  Definition getBrOffsetE {ty}
             (inst: Expr ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (UniBit (SignExtendTrunc _ rv32iAddrSize)
            (BinBit (Concat _ 1)
                    (BinBit (Concat _ _)
                            (BinBit (Concat _ _) (UniBit (TruncLsb 1 _) inst)
                                    (UniBit (ConstExtract 24 1 _) inst))
                            (BinBit (Concat _ _) (UniBit (ConstExtract 1 6 _) inst)
                                    (UniBit (ConstExtract 20 4 _) inst)))
                    ($0)))%kami_expr.

  Definition rv32iDecode: DecT rv32iOpIdx rv32iAddrSize rv32iLgDataBytes rv32iRfIdx.
    unfold DecT; intros ty st pc.
    set ($$insts @[ #pc ])%kami_expr as inst.
    refine (IF ((UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) inst)
                == ($$ rv32iLd)) then _ else _)%kami_expr.
    - (* load case *)
      exact (STRUCT { "opcode" ::= UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) inst;
                      "reg" ::= UniBit (ConstExtract 20 5 _) inst;
                      "addr" ::= (getRs1ValueE st inst + getLdBaseE inst);
                      "value" ::= $$Default;
                      "inst" ::= inst})%kami_expr.
    - refine (IF ((UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) inst)
                  == ($$ rv32iSt)) then _ else _)%kami_expr.
      + (* store case *)
        exact (STRUCT { "opcode" ::= (UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) inst);
                        "reg" ::= $$Default;
                        "addr" ::= (getRs1ValueE st inst + getStBaseE inst);
                        "value" ::= getRs2ValueE st inst;
                        "inst" ::= inst})%kami_expr.
      + (* halt, non-memory, or branch operations *)
        exact (STRUCT { "opcode" ::= (UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) inst);
                        "reg" ::= $$Default;
                        "addr" ::= $$Default;
                        "value" ::= $$Default;
                        "inst" ::= inst})%kami_expr.
  Defined.

  Definition rv32iExecState: ExecStateT rv32iOpIdx rv32iAddrSize rv32iLgDataBytes rv32iRfIdx.
    unfold ExecStateT; intros ty st pc dec.
    set (ReadField {| StringBound.bindex := "inst"%string; StringBound.indexb := _ |}
                   #dec)%kami_expr as inst.

    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  #dec == $$rv32iOp) then _ else #st)%kami_expr.

    (* op instructions *)
    refine (IF (getFunct7E inst == $$rv32iAdd) then _ else _)%kami_expr.
    - (* Add *)
      refine (#st @[ getRdE inst <- getRs1ValueE st inst + getRs2ValueE st inst ])%kami_expr.
    - refine (IF (getFunct7E inst == $$rv32iSub) then _ else #st)%kami_expr.
      (* Sub *)
      refine (#st @[ getRdE inst <- getRs1ValueE st inst - getRs2ValueE st inst ])%kami_expr.
  Defined.

  Definition rv32iExecNextPc: ExecNextPcT rv32iOpIdx rv32iAddrSize rv32iLgDataBytes rv32iRfIdx.
    unfold ExecNextPcT; intros ty st pc dec.
    set (ReadField {| StringBound.bindex := "inst"%string; StringBound.indexb := _ |}
                   #dec)%kami_expr as inst.

    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  #dec == $$rv32iBr) then _ else #pc + $4)%kami_expr.

    (* branch instructions *)
    refine (IF (getFunct3E inst == $$rv32iBeq) then _ else _)%kami_expr.
    - (* Beq *)
      refine (IF (getRs1ValueE st inst == getRs2ValueE st inst)
              then #pc + getBrOffsetE inst
              else #pc + $4)%kami_expr.
    - (* Blt *)
      refine (IF (getRs1ValueE st inst < getRs2ValueE st inst)
              then #pc + getBrOffsetE inst
              else #pc + $4)%kami_expr.
  Defined.
    
End RV32ISubset.

