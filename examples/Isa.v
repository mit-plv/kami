Require Import Bool String List.
Require Import Lib.CommonTactics Lib.Word.
Require Import Lts.Syntax Lts.Notations.
Require Import Ex.SC.

(* Subset of RV32I instructions *)
Section RV32ISubset.

  Definition rv32iAddrSize := 32.
  Definition rv32iLgDataBytes := 4.
  Definition rv32iOpIdx := 7. (* always inst[6-0] *)
  Definition rv32iRfIdx := 5. (* 2^5 = 32 general purpose registers, x0 is hardcoded though *)

  Definition rv32iLd := WO~0~0~0~0~0~1~1.
  Definition rv32iSt := WO~0~1~0~0~0~1~1.
  Definition rv32iHt := WO~0~0~0~0~0~0~0. 
  Definition rv32iOp := WO~0~1~1~0~0~1~1. (* Register-Register operations *)

  Definition getRs1ValueE {ty}
             (s : StateT rv32iLgDataBytes rv32iRfIdx ty)
             (inst : fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (#s @[UniBit (ConstExtract 12 5 _) #inst])%kami_expr.
  Definition getRs2ValueE {ty}
             (s : StateT rv32iLgDataBytes rv32iRfIdx ty)
             (inst : fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (#s @[UniBit (ConstExtract 7 5 _) #inst])%kami_expr.
  Definition getLdBaseE {ty}
             (inst : fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (UniBit (ZeroExtendTrunc _ rv32iAddrSize) (UniBit (TruncLsb 12 _) #inst))%kami_expr.
  Definition getStBaseE {ty}
             (inst : fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
    (UniBit (ZeroExtendTrunc _ rv32iAddrSize) (UniBit (TruncLsb 7 _) #inst))%kami_expr.

  Definition rv32iDecode: DecT rv32iOpIdx rv32iAddrSize rv32iLgDataBytes rv32iRfIdx.
    unfold DecT; intros ty s inst.
    refine (IF ((UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) #inst)
                == ($$ rv32iLd)) then _ else _)%kami_expr.
    - (* load case *)
      exact (STRUCT { "inst" ::= #inst;
                      "opcode" ::= UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) #inst;
                      "reg" ::= UniBit (ConstExtract 20 5 _) #inst;
                      "addr" ::= (getRs1ValueE s inst + getLdBaseE inst);
                      "value" ::= $$Default })%kami_expr.
    - refine (IF ((UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) #inst)
                  == ($$ rv32iSt)) then _ else _)%kami_expr.
      + (* store case *)
        exact (STRUCT { "inst" ::= #inst;
                        "opcode" ::= (UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) #inst);
                        "reg" ::= $$Default;
                        "addr" ::= (getRs1ValueE s inst + getStBaseE inst);
                        "value" ::= getRs2ValueE s inst })%kami_expr.
      + (* halt OR non-memory operations *)
        exact (STRUCT { "inst" ::= #inst;
                        "opcode" ::= (UniBit (Trunc (rv32iAddrSize - rv32iOpIdx) _) #inst);
                        "reg" ::= $$Default;
                        "addr" ::= $$Default;
                        "value" ::= $$Default })%kami_expr.
  Defined.

  Definition rv32iExecState: ExecStateT rv32iOpIdx rv32iAddrSize rv32iLgDataBytes rv32iRfIdx.
    unfold ExecStateT; intros ty s pc inst.
    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  (#inst) == $$ rv32iLd) then #s else _)%kami_expr. (* load *)
    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  (#inst) == $$ rv32iSt) then #s else _)%kami_expr. (* store *)
    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  (#inst) == $$ rv32iHt) then #s else _)%kami_expr. (* halt *)

    refine (IF (ReadField
                  {| StringBound.bindex := "opcode"%string; StringBound.indexb := _ |}
                  (#inst) == $$ rv32iHt) then _ else #s)%kami_expr. (* op *)

    exact (#s)%kami_expr. (* TODO: more *)
  Defined.

  Definition rv32iExecNextPc: ExecNextPcT rv32iOpIdx rv32iAddrSize rv32iLgDataBytes rv32iRfIdx.
    unfold ExecStateT; intros ty s pc inst.
    exact (#pc + $4)%kami_expr.
  Defined.

End RV32ISubset.

