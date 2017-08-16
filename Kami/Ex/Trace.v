Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word.
Require Import Kami.Syntax Kami.Semantics.
Require Import Ex.SC Ex.IsaRv32.

Open Scope string_scope.

Definition spReg := gprToRaw x2.

Section AbstractTrace.
  Definition address := type (Bit rv32iAddrSize).
  Definition iaddress := type (Bit rv32iIAddrSize).

  Definition data := type (MemTypes.Data rv32iDataBytes).

  Definition register := type (Bit rv32iRfIdx).

  Definition regfile := StateT rv32iDataBytes rv32iRfIdx type.

  Definition rget (rf : regfile) (r : register) : data :=
    if weq r (wzero _)
    then wzero _
    else evalExpr (ReadIndex #r #rf)%kami_expr.

  Definition rset (rf : regfile) (r : register) (v : data) : regfile :=
    if weq r (wzero _)
    then rf
    else evalExpr (UpdateVector #rf #r #v)%kami_expr.

  Definition memory := address -> option data.

  Definition mget (m : memory) (addr : address) : option data :=
    m addr.

  Definition mset (m : memory) (addr : address) (val : data) : memory :=
    fun a => if weq a addr then Some val else m a.

  Definition progMem := iaddress -> data.
  Definition pmget (pm : progMem) (iaddr : iaddress) : data :=
    pm iaddr.

  Inductive TraceEvent : Type :=
  | Instr (pc : address)
  | Rd (addr : address) (val : data)
  | Wr (addr : address) (val : data)
  | Branch (taken : bool)
  | ToHost (val : data)
  | FromHost (val : data).

  Inductive hasTrace : regfile -> memory -> progMem -> address -> data -> list TraceEvent -> Prop :=
  | htNil : forall rf mem pm pc maxsp,
      hasTrace rf mem pm pc maxsp nil
  | htLd : forall inst val rf mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opLd ->
      let addr := evalExpr (rv32iGetLdAddr type inst) in
      let dstIdx := evalExpr (rv32iGetLdDst type inst) in
      let srcIdx := evalExpr (rv32iGetLdSrc type inst) in
      let srcVal := rget rf srcIdx in
      let laddr := evalExpr (rv32iCalcLdAddr type addr srcVal) in
      let laddr_aligned := evalExpr (rv32iAlignAddr type laddr) in
      mget mem laddr_aligned = Some val ->
      hasTrace (rset rf dstIdx val) mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (Instr pc :: Rd laddr_aligned val :: trace')
  | htSt : forall inst rf mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opSt ->
      let addr := evalExpr (rv32iGetStAddr type inst) in
      let srcIdx := evalExpr (rv32iGetStSrc type inst) in
      let srcVal := rget rf srcIdx in
      let vsrcIdx := evalExpr (rv32iGetStVSrc type inst) in
      let stVal := rget rf vsrcIdx in
      let saddr := evalExpr (rv32iCalcStAddr type addr srcVal) in
      let saddr_aligned := evalExpr (rv32iAlignAddr type saddr) in
      hasTrace rf (mset mem saddr_aligned stVal) pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (Instr pc :: Wr saddr_aligned stVal :: trace')
  | htTh : forall inst rf mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opTh ->
      let srcIdx := evalExpr (rv32iGetSrc1 type inst) in
      let srcVal := rget rf srcIdx in
      hasTrace rf mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (Instr pc :: ToHost srcVal :: trace')
  | htFh : forall inst rf val mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opFh ->
      let dst := evalExpr (rv32iGetDst type inst) in
      hasTrace (rset rf dst val) mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (Instr pc :: FromHost val :: trace')
  | htNmBranch : forall inst rf mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opNm ->
      evalExpr (getOpcodeE #inst)%kami_expr = rv32iOpBRANCH ->
      hasTrace rf mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (Instr pc :: Branch (evalExpr (rv32iBranchTaken type rf inst)) :: trace')
  | htNm : forall inst rf mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opNm ->
      evalExpr (getOpcodeE #inst)%kami_expr <> rv32iOpBRANCH ->
      let src1 := evalExpr (rv32iGetSrc1 type inst) in
      let val1 := rget rf src1 in
      let src2 := evalExpr (rv32iGetSrc2 type inst) in
      let val2 := rget rf src2 in
      let dst := evalExpr (rv32iGetDst type inst) in
      let execVal := evalExpr (rv32iExec type val1 val2 pc inst) in
      hasTrace (rset rf dst execVal) mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (Instr pc :: trace').


  Definition censorTrace : list TraceEvent -> list TraceEvent :=
    map (fun te => match te with
                | Instr _ => te
                | Branch _ => te
                | Rd addr val => Rd addr $0
                | Wr addr val => Wr addr $0
                | ToHost val => ToHost $0
                | FromHost val => FromHost $0
                end).

  Definition extractFhTrace : list TraceEvent -> list data :=
    flat_map (fun te => match te with
                | FromHost val => cons val nil
                | _ => nil
                end).

  Definition abstractHiding rf mem pm pc maxsp : Prop :=
    forall trace fhTrace,
      hasTrace rf mem pm pc maxsp trace ->
      extractFhTrace trace = fhTrace ->
      forall fhTrace',
        length fhTrace = length fhTrace' ->
        exists trace',
          hasTrace rf mem pm pc maxsp trace' /\
          censorTrace trace = censorTrace trace' /\
          extractFhTrace trace' = fhTrace'.

End AbstractTrace.

Section KamiTrace.
  Definition censorLabel censorMeth (l : LabelT) : LabelT :=
    match l with
    | {| annot := a;
         defs := d;
         calls := c; |} =>
      {| annot := a;
         defs := FMap.M.mapi censorMeth d;
         calls := FMap.M.mapi censorMeth c; |}
    end.

  Definition censorLabelSeq censorMeth : LabelSeqT -> LabelSeqT :=
    map (censorLabel censorMeth).

  Definition extractFhLabel extractFh (l : LabelT) : list (word 32) :=
    match l with
    | {| annot := _;
         defs := _;
         calls := c; |} => extractFh c
    end.

  Definition extractFhLabelSeq extractFh : LabelSeqT -> list (word 32) :=
    flat_map (extractFhLabel extractFh).


  Definition inBounds (maxsp : word 32) (regs : RegsT) : Prop :=
    match FMap.M.find "rf" regs with
    | Some (existT _
                   (SyntaxKind (Vector (Bit 32) 5))
                   rf) => rf spReg <= maxsp
    | _ => True
    end.

  Inductive BoundedMultistep (m : Modules) (maxsp : word 32) : RegsT -> RegsT -> list LabelT -> Prop :=
    NilBMultistep : forall o1 o2 : RegsT,
      o1 = o2 -> BoundedMultistep m maxsp o1 o2 nil
  | BMulti : forall (o : RegsT) (a : list LabelT) (n : RegsT),
      BoundedMultistep m maxsp o n a ->
      inBounds maxsp n ->
      forall (u : UpdatesT) (l : LabelT),
        Step m n u l -> BoundedMultistep m maxsp o (FMap.M.union u n) (l :: a).

  Definition kamiHiding censorMeth extractFh m maxsp regs : Prop :=
    forall labels newRegs fhs,
      BoundedMultistep m maxsp regs newRegs labels ->
      extractFhLabelSeq extractFh labels = fhs ->
      forall fhs',
        length fhs = length fhs' ->
        exists labels' newRegs',
          BoundedMultistep m maxsp regs newRegs' labels' /\
          censorLabelSeq censorMeth labels = censorLabelSeq censorMeth  labels' /\
          extractFhLabelSeq extractFh labels' = fhs'.
End KamiTrace.

Section SCTiming.

  Definition rv32iProcInst :=
    procInst rv32iGetOptype
             rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
             rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
             rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst
             rv32iExec rv32iNextPc rv32iAlignPc rv32iAlignAddr
             (procInitDefault  _ _ _ _).

  Definition SCRegs rf pm pc : RegsT :=
    FMap.M.add "rf" (existT _ (SyntaxKind (Vector (Bit 32) 5)) rf)
               (FMap.M.add "pgm" (existT _ (SyntaxKind (Vector (Bit 32) 8)) pm)
                           (FMap.M.add "pc" (existT _ (SyntaxKind (Bit 16)) pc)
                                       (FMap.M.empty _))).

  Definition censorSCMeth (n : String.string) (t : {x : SignatureT & SignT x}) : {x : SignatureT & SignT x} :=
    if String.string_dec n "exec"
    then match t with
         | existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (argV, retV) =>
           existT _
                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                            "op" :: Bool;
                                            "data" :: Bit 32});
                     ret := Struct (STRUCT {"data" :: Bit 32}) |}
                  (evalExpr (STRUCT { "addr" ::= #argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."addr";
                                      "op" ::= #argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."op";
                                      "data" ::= $0 })%kami_expr,
                   evalExpr (STRUCT { "data" ::= $0 })%kami_expr)
         | _ => t
         end
    else if String.string_dec n "toHost"
    then match t with
         | existT _
                  {| arg := Bit 32;
                     ret := Bit 0 |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 32;
                     ret := Bit 0 |}
                  ($0, retV)
         | _ => t
         end
    else if String.string_dec n "fromHost"
    then match t with
         | existT _
                  {| arg := Bit 0;
                     ret := Bit 32 |}
                  (argV, retV) =>
           existT _
                  {| arg := Bit 0;
                     ret := Bit 32 |}
                  (argV, $0)
         | _ => t
         end
    else t.

  Definition callsToTraceEvent (c : MethsT) : option TraceEvent :=
    match FMap.M.find "exec" c with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Struct (STRUCT {"data" :: Bit 32}) |}
                   (argV, retV)) =>
      let addr := evalExpr (#argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."addr")%kami_expr in
      let val := evalExpr (#argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."data")%kami_expr in
      if evalExpr (#argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."op")%kami_expr
      then Some (Wr addr val)
      else Some (Rd addr val)
    | None =>
      match FMap.M.find "toHost" c with
      | Some (existT _
                     {| arg := Bit 32;
                        ret := Bit 0 |}
                     (argV, retV)) =>
        Some (ToHost argV)
      | None =>
        match FMap.M.find "fromHost" c with
        | Some (existT _
                       {| arg := Bit 0;
                          ret := Bit 32 |}
                       (argV, retV)) =>
          Some (FromHost retV)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

  Definition labelToTraceEvent (l : LabelT) : option TraceEvent :=
    match l with
    | {| annot := _;
         defs := _;
         calls := c; |} => callsToTraceEvent c
    end.

  Definition extractFhSC (cs : MethsT) : list (word 32) :=
    match callsToTraceEvent cs with
    | Some (FromHost val) => cons val nil
    | _ => nil
    end.

  Inductive relatedTrace : list TraceEvent -> LabelSeqT -> Prop :=
  | RtNil : relatedTrace nil nil
  | RtRd : forall pc addr val lbl trace' ls',
      labelToTraceEvent lbl = Some (Rd addr val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Instr pc :: Rd addr val :: trace') (lbl :: ls')
  | RtWr : forall pc addr val lbl trace' ls',
      labelToTraceEvent lbl = Some (Wr addr val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Instr pc :: Wr addr val :: trace') (lbl :: ls')
  | RtTh : forall pc val lbl trace' ls',
      labelToTraceEvent lbl = Some (ToHost val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Instr pc :: ToHost val :: trace') (lbl :: ls')
  | RtFh : forall pc val lbl trace' ls',
      labelToTraceEvent lbl = Some (FromHost val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Instr pc :: FromHost val :: trace') (lbl :: ls')
  | RtBranch : forall pc taken lbl trace' ls',
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (Instr pc :: Branch taken :: trace') (lbl :: ls')
  | RtNm : forall pc lbl trace' ls',
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (Instr pc :: trace') (lbl :: ls').

  Lemma relatedFhTrace :
    forall trace ls,
      relatedTrace trace ls -> extractFhTrace trace = extractFhLabelSeq extractFhSC ls.
  Proof.
    induction 1;
      try solve
          [ eauto |
            simpl;
            match goal with
            | [ H : ?a = ?b |- ?a = ?c ++ ?b ] => assert (Hnil : c = nil); [ idtac | rewrite Hnil; simpl; assumption ]
            | [ H : ?a = ?b |- ?v :: ?a = ?c ++ ?b ] => assert (Hval : c = cons val nil); [ idtac | rewrite Hval; simpl; rewrite H; reflexivity ]
            end;
            match goal with
            | [ |- extractFhLabel extractFhSC ?l = _ ] => destruct l
            end;
            unfold labelToTraceEvent in *;
            unfold extractFhLabel, extractFhSC;
            match goal with
            | [ H : ?t = _ |- context[?t] ] => rewrite H
            end;
            reflexivity ].
  Qed.

  Lemma relatedCensor :
    forall rf mem pm pc maxsp trace1 trace2 newRegs1 newRegs2 ls1 ls2,
      hasTrace rf mem pm pc maxsp trace1 ->
      hasTrace rf mem pm pc maxsp trace2 ->
      BoundedMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs1 ls1 ->
      BoundedMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs2 ls2 ->
      relatedTrace trace1 ls1 ->
      relatedTrace trace2 ls2 ->
      censorTrace trace1 = censorTrace trace2 ->
      censorLabelSeq censorSCMeth ls1 = censorLabelSeq censorSCMeth ls2.
  Proof.
  Admitted.

  Lemma abstractToSCRelated :
    forall rf mem pm pc maxsp trace,
      hasTrace rf mem pm pc maxsp trace ->
      exists newRegs ls,
        BoundedMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs ls /\
        relatedTrace trace ls.
  Proof.
  Admitted.

  Lemma SCToAbstractRelated :
    forall rf mem pm pc maxsp newRegs ls,
      BoundedMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs ls ->
      exists trace,
        hasTrace rf mem pm pc maxsp trace /\
        relatedTrace trace ls.
  Proof.
  Admitted.

  Ltac shatter :=
    repeat match goal with
           | [ H : exists _, _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           end.

  Theorem abstractToSCHiding :
    forall rf mem pm pc maxsp,
      abstractHiding rf mem pm pc maxsp ->
      kamiHiding censorSCMeth extractFhSC
                 rv32iProcInst
                 maxsp
                 (SCRegs rf pm pc).
  Proof.
    unfold abstractHiding, kamiHiding.
    intros.
    match goal with
    | [ H : BoundedMultistep _ _ _ _ _ |- _ ] => let H' := fresh in assert (H' := H); eapply SCToAbstractRelated in H'
    end.
    shatter.
    match goal with
    | [ Hrel : relatedTrace ?t ?ls,
               Hextract : extractFhLabelSeq extractFhSC ?ls = _,
                          Htrace : hasTrace _ _ _ _ _ _,
                                   Habs : forall _ _, hasTrace _ _ _ _ _ _ -> extractFhTrace _ = _ -> forall _, length _ = length _ -> _,
          Hlen : length _ = length _
          |- context[extractFhLabelSeq _ _ = ?fhTrace] ] =>
      rewrite <- (relatedFhTrace _ _ Hrel) in Hextract; specialize (Habs _ _ Htrace Hextract fhTrace Hlen)
    end.
    shatter.
    match goal with
    | [ Htrace : hasTrace _ _ _ _ _ ?t,
                 Hextract : extractFhTrace ?t = ?fhTrace
        |- context[?fhTrace] ] => pose (abstractToSCRelated _ _ _ _ _ _ Htrace)
    end.
    shatter.
    match goal with
    | [ H : BoundedMultistep _ _ _ ?regs ?ls |- _ ] => exists ls, regs
    end.
    repeat split;
      match goal with
      | [ |- BoundedMultistep _ _ _ _ _ ] => assumption
      | [ Htrace1 : hasTrace _ _ _ _ _ _, Htrace2 : hasTrace _ _ _ _ _ _ |- censorLabelSeq _ _ = censorLabelSeq _ _ ] => eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ Htrace1 Htrace2); eassumption
      | [ |- extractFhLabelSeq _ _ = _ ] => erewrite <- relatedFhTrace; eassumption
      end.
  Qed.

End SCTiming.
