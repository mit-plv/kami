Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics.
Require Import Ex.SC Ex.IsaRv32.
Require Import Lib.CommonTactics.
Require Import Compile.Rtl Compile.CompileToRtlTryOpt.
Require Import Logic.FunctionalExtensionality.

Open Scope string_scope.

Definition spReg := gprToRaw x2.

Section AbstractTrace.
  Definition address := type (Bit rv32iAddrSize).
  Definition iaddress := type (Bit rv32iIAddrSize).

  Definition data := type (MemTypes.Data rv32iDataBytes).

  Definition register := type (Bit rv32iRfIdx).

  Definition regfile := StateT rv32iDataBytes rv32iRfIdx type.

  Definition rset (rf : regfile) (r : register) (v : data) : regfile :=
    if weq r (wzero _)
    then rf
    else evalExpr (UpdateVector #rf #r #v)%kami_expr.

  Definition progMem := iaddress -> data.
  Inductive TraceEvent : Type :=
  | Nm (pc : address)
  | Rd (pc : address) (addr : address) (val : data)
  | RdZ (pc : address) (addr : address)
  | Wr (pc : address) (addr : address) (val : data)
  | Branch (pc : address) (taken : bool)
  | ToHost (pc : address) (val : data)
  | FromHost (pc : address) (val : data).

  Inductive hasTrace : regfile -> progMem -> address -> data -> list TraceEvent -> Prop :=
  | htNil : forall rf pm pc maxsp,
      hasTrace rf pm pc maxsp nil
  | htLd : forall inst val rf pm pc maxsp trace',
      rf spReg <= maxsp ->
      pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opLd ->
      let addr := evalExpr (rv32iGetLdAddr type inst) in
      let dstIdx := evalExpr (rv32iGetLdDst type inst) in
      dstIdx <> wzero _ ->
      let srcIdx := evalExpr (rv32iGetLdSrc type inst) in
      let srcVal := rf srcIdx in
      let laddr := evalExpr (rv32iCalcLdAddr type addr srcVal) in
      let laddr_aligned := evalExpr (rv32iAlignAddr type laddr) in
      hasTrace (rset rf dstIdx val) pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf pm pc maxsp (Rd pc laddr_aligned val :: trace')
  | htLdZ : forall inst rf pm pc maxsp trace',
      rf spReg <= maxsp ->
      pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opLd ->
      evalExpr (rv32iGetLdDst type inst) = wzero _ ->
      let addr := evalExpr (rv32iGetLdAddr type inst) in
      let srcIdx := evalExpr (rv32iGetLdSrc type inst) in
      let srcVal := rf srcIdx in
      let laddr := evalExpr (rv32iCalcLdAddr type addr srcVal) in
      let laddr_aligned := evalExpr (rv32iAlignAddr type laddr) in
      hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf pm pc maxsp (RdZ pc laddr_aligned :: trace')
  | htSt : forall inst rf pm pc maxsp trace',
      rf spReg <= maxsp ->
      pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opSt ->
      let addr := evalExpr (rv32iGetStAddr type inst) in
      let srcIdx := evalExpr (rv32iGetStSrc type inst) in
      let srcVal := rf srcIdx in
      let vsrcIdx := evalExpr (rv32iGetStVSrc type inst) in
      let stVal := rf vsrcIdx in
      let saddr := evalExpr (rv32iCalcStAddr type addr srcVal) in
      let saddr_aligned := evalExpr (rv32iAlignAddr type saddr) in
      hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf pm pc maxsp (Wr pc saddr_aligned stVal :: trace')
  | htTh : forall inst rf pm pc maxsp trace',
      rf spReg <= maxsp ->
      pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opTh ->
      let srcIdx := evalExpr (rv32iGetSrc1 type inst) in
      let srcVal := rf srcIdx in
      hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf pm pc maxsp (ToHost pc srcVal :: trace')
  | htFh : forall inst rf val pm pc maxsp trace',
      rf spReg <= maxsp ->
      pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opFh ->
      let dst := evalExpr (rv32iGetDst type inst) in
      hasTrace (rset rf dst val) pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf pm pc maxsp (FromHost pc val :: trace')
  | htNmBranch : forall inst rf pm pc maxsp trace',
      rf spReg <= maxsp ->
      pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opNm ->
      evalExpr (getOpcodeE #inst)%kami_expr = rv32iOpBRANCH ->
      hasTrace rf pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf pm pc maxsp (Branch pc (evalExpr (rv32iBranchTaken type rf inst)) :: trace')
  | htNm : forall inst rf pm pc maxsp trace',
      rf spReg <= maxsp ->
      pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opNm ->
      evalExpr (getOpcodeE #inst)%kami_expr <> rv32iOpBRANCH ->
      let src1 := evalExpr (rv32iGetSrc1 type inst) in
      let val1 := rf src1 in
      let src2 := evalExpr (rv32iGetSrc2 type inst) in
      let val2 := rf src2 in
      let dst := evalExpr (rv32iGetDst type inst) in
      let execVal := evalExpr (rv32iExec type val1 val2 pc inst) in
      hasTrace (rset rf dst execVal) pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf pm pc maxsp (Nm pc :: trace').


  Definition censorTrace : list TraceEvent -> list TraceEvent :=
    map (fun te => match te with
                | Nm _ => te
                | Branch _ _ => te
                | RdZ _ _ => te
                | Rd pc addr val => Rd pc addr $0
                | Wr pc addr val => Wr pc addr $0
                | ToHost pc val => ToHost pc $0
                | FromHost pc val => FromHost pc $0
                end).

  Definition extractFhTrace : list TraceEvent -> list data :=
    flat_map (fun te => match te with
                | FromHost _ val => cons val nil
                | _ => nil
                end).

  Definition abstractHiding rf pm pc maxsp : Prop :=
    forall trace fhTrace,
      hasTrace rf pm pc maxsp trace ->
      extractFhTrace trace = fhTrace ->
      forall fhTrace',
        length fhTrace = length fhTrace' ->
        exists trace',
          hasTrace rf pm pc maxsp trace' /\
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

  Inductive BoundedForwardActiveMultistep (m : Modules) (maxsp : word 32) : RegsT -> RegsT -> list LabelT -> Prop :=
    NilBFMultistep : forall o1 o2 : RegsT,
      o1 = o2 -> BoundedForwardActiveMultistep m maxsp o1 o2 nil
  | BFMulti : forall (o : RegsT) (a : list LabelT) (n : RegsT) (u : UpdatesT) (l : LabelT),
      inBounds maxsp o ->
      Step m o u l ->
      annot l <> None ->
      annot l <> Some None ->
      BoundedForwardActiveMultistep m maxsp (FMap.M.union u o) n a ->
      BoundedForwardActiveMultistep m maxsp o n (l :: a).

  Lemma BFMulti_Multi : forall m maxsp o n a,
      BoundedForwardActiveMultistep m maxsp o n a ->
      Multistep m o n (List.rev a).
  Proof.
    intros m maxsp o n a.
    move a at top.
    generalize m maxsp o n.
    clear - a.
    induction a; intros;
    match goal with
    | [ H : BoundedForwardActiveMultistep _ _ _ _ _ |- _ ] => inversion H; clear H
    end.
    - constructor.
      assumption.
    - simpl.
      subst.
      match goal with
      | [ H : BoundedForwardActiveMultistep _ _ _ _ _, IH : forall _ _ _ _, BoundedForwardActiveMultistep _ _ _ _ _ -> _ |- _ ] => specialize (IH _ _ _ _ H)
      end.
      match goal with
      | [ HM : Multistep ?m (FMap.M.union ?u ?o) ?n (List.rev ?a), HS : Step ?m ?o ?u ?l |- _ ] =>
        let a' := fresh in
        remember (List.rev a) as a'; clear - HM HS; move a' at top; generalize m u o n l HM HS; clear - a'; induction a'
      end;
        simpl;
        intros;
        match goal with
        | [ HM : Multistep _ _ _ _ |- _ ] => inversion HM
        end;
        subst;
        repeat constructor; 
        try assumption.
      eapply IHlist; eassumption.
  Qed.
      
  Definition kamiHiding censorMeth extractFh m maxsp regs : Prop :=
    forall labels newRegs fhs,
      BoundedForwardActiveMultistep m maxsp regs newRegs labels ->
      extractFhLabelSeq extractFh labels = fhs ->
      forall fhs',
        length fhs = length fhs' ->
        exists labels' newRegs',
          BoundedForwardActiveMultistep m maxsp regs newRegs' labels' /\
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

  Lemma SCRegs_find_rf : forall rf pm pc rf',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "rf"
                                   (SCRegs rf pm pc) =
                       Some
                         (existT (fullType type) (SyntaxKind (Vector (Bit 32) 5)) rf') -> rf = rf'.
  Proof.
    intros.
    unfold SCRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma SCRegs_find_pm : forall rf pm pc pm',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pgm"
                  (SCRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Vector (Bit 32) 8)) pm') -> pm = pm'.
  Proof.
    intros.
    unfold SCRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Lemma SCRegs_find_pc : forall rf pm pc pc',
      FMap.M.find (elt:={x : FullKind & fullType type x}) "pc"
                  (SCRegs rf pm pc) =
      Some
        (existT (fullType type) (SyntaxKind (Bit 16)) pc') -> pc = pc'.
  Proof.
    intros.
    unfold SCRegs in *.
    FMap.findeq.
    exact (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H1).
  Qed.

  Ltac SCRegs_find :=
    repeat match goal with
           | [ H : FMap.M.find "rf" (SCRegs ?rf _ _) = Some (existT _ _ ?rf') |- _ ] => assert (rf = rf') by (eapply SCRegs_find_rf; eassumption); subst; clear H
           | [ H : FMap.M.find "pgm" (SCRegs _ ?pm _) = Some (existT _ _ ?pm') |- _ ] => assert (pm = pm') by (eapply SCRegs_find_pm; eassumption); subst; clear H
           | [ H : FMap.M.find "pc" (SCRegs _ _ ?pc) = Some (existT _ _ ?pc') |- _ ] => assert (pc = pc') by (eapply SCRegs_find_pc; eassumption); subst; clear H
           end.
  
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
      let argval := evalExpr (#argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."data")%kami_expr in
      let retval := evalExpr (#retV!(RsToProc rv32iDataBytes)@."data")%kami_expr in
      if evalExpr (#argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."op")%kami_expr
      then Some (Wr $0 addr argval)
      else Some (Rd $0 addr retval)
    | None =>
      match FMap.M.find "toHost" c with
      | Some (existT _
                     {| arg := Bit 32;
                        ret := Bit 0 |}
                     (argV, retV)) =>
        Some (ToHost $0 argV)
      | None =>
        match FMap.M.find "fromHost" c with
        | Some (existT _
                       {| arg := Bit 0;
                          ret := Bit 32 |}
                       (argV, retV)) =>
          Some (FromHost $0 retV)
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
    | Some (FromHost _ val) => cons val nil
    | _ => nil
    end.

  Inductive relatedTrace : list TraceEvent -> LabelSeqT -> Prop :=
  | RtNil : relatedTrace nil nil
  | RtRd : forall pc addr val lbl trace' ls',
      labelToTraceEvent lbl = Some (Rd $0 addr val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Rd pc addr val :: trace') (lbl :: ls')
  | RtWr : forall pc addr val lbl trace' ls',
      labelToTraceEvent lbl = Some (Wr $0 addr val) ->
      relatedTrace trace' ls' ->
      relatedTrace (Wr pc addr val :: trace') (lbl :: ls')
  | RtTh : forall pc val lbl trace' ls',
      labelToTraceEvent lbl = Some (ToHost $0 val) ->
      relatedTrace trace' ls' ->
      relatedTrace (ToHost pc val :: trace') (lbl :: ls')
  | RtFh : forall pc val lbl trace' ls',
      labelToTraceEvent lbl = Some (FromHost $0 val) ->
      relatedTrace trace' ls' ->
      relatedTrace (FromHost pc val :: trace') (lbl :: ls')
  | RtBranch : forall pc taken lbl trace' ls',
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (Branch pc taken :: trace') (lbl :: ls')
  | RtNm : forall pc lbl trace' ls',
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (Nm pc :: trace') (lbl :: ls')
  | RtRdZ : forall pc addr lbl trace' ls',
      labelToTraceEvent lbl = None ->
      relatedTrace trace' ls' ->
      relatedTrace (RdZ pc addr :: trace') (lbl :: ls'). 

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

  (* A [subst] tactic that doesn't unfold definitions *)
  Ltac opaque_subst :=
    repeat match goal with
           | [ Heq : ?x = ?y |- _ ] => ((tryif unfold x then fail else subst x) || (tryif unfold y then fail else subst y))
           end.

  Ltac shatter := repeat match goal with
                         | [ H : exists _, _ |- _ ] => destruct H
                         | [ H : _ /\ _ |- _ ] => destruct H
                         end.

  Lemma SCSubsteps :
    forall o (ss : Substeps rv32iProcInst o),
      SubstepsInd rv32iProcInst o (foldSSUpds ss) (foldSSLabel ss) ->
      (((foldSSLabel ss) = {| annot := None; defs := FMap.M.empty _; calls := FMap.M.empty _ |}
        \/ (foldSSLabel ss) = {| annot := Some None; defs := FMap.M.empty _; calls := FMap.M.empty _ |})
       /\ (foldSSUpds ss) = FMap.M.empty _)
      \/ (exists k a u cs,
            In (k :: a)%struct (getRules rv32iProcInst)
            /\ SemAction o (a type) u cs WO
            /\ (foldSSLabel ss) = {| annot := Some (Some k); defs := FMap.M.empty _; calls := cs |}
            /\ (foldSSUpds ss) = u).
  Proof.
    intros.
    match goal with
    | [ H : SubstepsInd _ _ _ _ |- _ ] => induction H
    end.
    - tauto.
    - intuition idtac;
        simpl;
        shatter;
        intuition idtac;
        subst;
        match goal with
        | [ H : Substep _ _ _ _ _ |- _ ] => destruct H
        end;
        try tauto;
        match goal with
        | [ HCCU : CanCombineUUL _ {| annot := Some _; defs := FMap.M.empty _; calls := _ |} _ _ (Rle _) |- _ ] =>
          unfold CanCombineUUL in HCCU;
            simpl in HCCU;
            tauto
        | [ HIn : In _ (getDefsBodies rv32iProcInst) |- _ ] =>
          simpl in HIn;
            tauto
        | [ HIR : In (?k :: ?a)%struct _, HA : SemAction _ _ ?u ?cs _ |- _ ] =>
          right;
            exists k, a, u, cs;
            simpl in HIR;
            intuition idtac;
            simpl;
            FMap.findeq
        end.
  Qed.

  Ltac evex H := unfold evalExpr in H; fold evalExpr in H.
  Ltac evexg := unfold evalExpr; fold evalExpr.

  Ltac boolex :=
    try match goal with
        | [ H : evalUniBool Neg _ = _ |- _ ] =>
          unfold evalUniBool in H;
          rewrite Bool.negb_true_iff in H
        end;
    match goal with
    | [ H : (if ?x then true else false) = _ |- _ ] =>
      destruct x; try discriminate
    end.

  Ltac evbool_auto :=
    match goal with
    | [ H : _ = true |- _ ] => evex H; boolex
    end.

  Ltac simplify_match :=
    repeat match goal with
           | [ |- context[match ?x with _ => _ end] ] =>
             let x' := eval hnf in x in change x with x'; cbv beta iota
           end.

  Ltac simplify_match_hyp :=
    repeat multimatch goal with
           | [ H : context[match ?x with _ => _ end] |- _ ] =>
             let x' := eval hnf in x in change x with x' in H; cbv beta iota
           end.

  Lemma relatedCensor :
    forall rf1 rf2 pm pc maxsp trace1 trace2 newRegs1 newRegs2 ls1 ls2,
      hasTrace rf1 pm pc maxsp trace1 ->
      hasTrace rf2 pm pc maxsp trace2 ->
      BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf1 pm pc) newRegs1 ls1 ->
      BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf2 pm pc) newRegs2 ls2 ->
      relatedTrace trace1 ls1 ->
      relatedTrace trace2 ls2 ->
      censorTrace trace1 = censorTrace trace2 ->
      censorLabelSeq censorSCMeth ls1 = censorLabelSeq censorSCMeth ls2.
  Proof.
    intros rf1 rf2 pm pc maxsp trace1 trace2 newRegs1 newRegs2 ls1 ls2 Hht1.
    move Hht1 at top.
    generalize rf2 trace2 newRegs1 newRegs2 ls1 ls2.
    clear trace2 newRegs1 newRegs2 ls1 ls2.
    induction Hht1; intros.
    - match goal with
      | [ H : censorTrace nil = censorTrace ?l |- _ ] => destruct l; simpl in H; try congruence
      end.
      match goal with
      | [ H1 : relatedTrace nil _, H2 : relatedTrace nil _ |- _ ] => inversion H1; inversion H2
      end.
      reflexivity.
    - match goal with
      | [ Hct : censorTrace (Rd _ _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : BoundedForwardActiveMultistep _ _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest.
      Transparent evalExpr.
      + apply substepsComb_substepsInd in HSubsteps0.
        apply SCSubsteps in HSubsteps0.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest.
        Transparent evalExpr.
        * SCRegs_find.
          f_equal.
          -- do 2 match goal with
                  | [ |- context[@evalExpr ?t (STRUCT {"addr" ::= rv32iAlignAddr ?ty ?adr; "op" ::= ?o; "data" ::= ?d})%kami_expr] ] => replace (@evalExpr t (STRUCT {"addr" ::= rv32iAlignAddr ty adr; "op" ::= _; "data" ::= _})%kami_expr) with (@evalExpr t (STRUCT {"addr" ::= #(evalExpr (rv32iAlignAddr ty adr)); "op" ::= o; "data" ::= d})%kami_expr) by eauto
                  end.
             unfold censorLabel, censorSCMeth, hide, annot, calls, defs.
             f_equal.
             match goal with
             | [ H1 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr1; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _,
                 H2 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr2; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _
                 |- _ ] => replace (evalExpr addr1) with (evalExpr addr2)
             end.
             ++ clear; eauto.
             ++ match goal with
                | [ H : labelToTraceEvent ?l = _,
                    x : forall _ : Fin.t 1, _
                    |- evalExpr ?adr = _ ] =>
                  replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!(RsToProc rv32iDataBytes)@."data")%kami_expr))) in H by eauto
                end.
                Opaque evalExpr.
                match goal with
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                end.
                Transparent evalExpr.
                match goal with
                | [ H : ?x = _ |- ?x = _ ] => rewrite H
                end.
                reflexivity.
          -- match goal with
             | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
             end;
               try match goal with
                   | [ HBFM : BoundedForwardActiveMultistep _ _ ?r1 _ ?l |- BoundedForwardActiveMultistep _ _ ?r2 _ ?l ] =>
                     replace r2 with r1; try eassumption
                   | [ |- censorTrace _ = censorTrace _ ] => eassumption
                   | [ |- relatedTrace _ _ ] => eassumption
                   end.
             ++ match goal with
                | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
                end.
                subst.
                match goal with
                | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1; try eassumption
                end.
                unfold rv32iNextPc.
                unfold rv32iGetOptype in H1.
                evexg.
                evex H1.
                repeat match goal with
                       | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                       | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                       end;
                  unfold evalConstT in *;
                  try reflexivity;
                  try match goal with
                      | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                      end;
                  discriminate H1.
             ++ match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                match goal with
                | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2
                end.
                ** clear; eauto.
                ** unfold rset.
                   destruct (weq dstIdx (wzero _)); try tauto.
                   evexg.
                   apply functional_extensionality.
                   intros.
                   unfold dstIdx.
                   match goal with
                   | [ |- (if _ then ?x else _) = (if _ then ?y else _) ] => replace x with y; [ reflexivity | idtac ]
                   end.
                   simpl.
                   match goal with
                   | [ H : labelToTraceEvent ?l = Some (Rd $ (0) laddr_aligned val),
                           x : forall _ : Fin.t 1, _
                                              |- _ ] =>
                     match goal with
                     | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= _}%kami_expr, x)) _|}) = Some (Rd $ (0) _ val) |- _ ] =>
                       replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!(RsToProc rv32iDataBytes)@."data")%kami_expr))) in H by eauto; inversion H
                     end
                   end.
                   reflexivity.
             ++ match goal with
                | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
                end.
                match goal with
                | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2; [ replace p1 with p2 | idtac ]
                end.
                ** clear; eauto.
                ** evexg.
                   unfold rv32iNextPc.
                   unfold rv32iGetOptype in H1.
                   evexg.
                   evex H1.
                   repeat match goal with
                          | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                          | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                          end;
                     unfold evalConstT in *;
                     try reflexivity;
                     try match goal with
                         | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                         end;
                     discriminate H1.
                ** unfold rset.
                   fold dstIdx.
                   destruct (weq dstIdx (wzero _)); try tauto.
                   evexg.
                   apply functional_extensionality.
                   intros.
                   unfold dstIdx.
                   match goal with
                   | [ |- (if _ then ?x else _) = (if _ then ?y else _) ] => replace x with y; [ reflexivity | idtac ]
                   end.
                   simpl.
                   match goal with
                   | [ H : labelToTraceEvent ?l = Some (Rd $ (0) laddr_aligned val0),
                           x : forall _ : Fin.t 1, _
                                              |- _ ] =>
                     match goal with
                     | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= _}%kami_expr, x)) _|}) = Some (Rd $ (0) _ val0) |- _ ] =>
                       replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!(RsToProc rv32iDataBytes)@."data")%kami_expr))) in H
                     end
                   end.
                   --- Opaque evalExpr.
                       inversion H18.
                       Transparent evalExpr.
                       reflexivity.
                   --- eauto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
    - match goal with
      | [ Hct : censorTrace (Rd _ _ _ :: _) = censorTrace ?tr |- _ ] =>
        let t := fresh in
        destruct tr as [|t tr];
          simpl in Hct;
          try destruct t;
          try congruence;
          inversion Hct;
          clear Hct;
          opaque_subst
      end.
      match goal with
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2; clear Hrt1; clear Hrt2
      end.
      opaque_subst.
      simpl.
      repeat match goal with
             | [ Hbm : BoundedForwardActiveMultistep _ _ _ _ (?lbl :: _) |- _ ] =>
               inversion Hbm;
                 clear Hbm;
                 match goal with
                 | [ Hst : Step _ _ _ lbl |- _ ] =>
                   inversion Hst;
                     clear Hst
                 end
             end.
      opaque_subst.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ H : foldSSLabel ss = _, H1 : annot (hide (foldSSLabel ss)) = None -> False, H2 : annot (hide (foldSSLabel ss)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
        end.
      match goal with
      | [ H : In _ _ |- _ ] => simpl in H
      end.
      Opaque evalExpr.
      intuition idtac; kinv_action_dest.
      Transparent evalExpr.
      + apply substepsComb_substepsInd in HSubsteps0.
        apply SCSubsteps in HSubsteps0.
        intuition idtac; shatter;
          match goal with
          | [ H : foldSSLabel ss0 = _, H1 : annot (hide (foldSSLabel ss0)) = None -> False, H2 : annot (hide (foldSSLabel ss0)) = Some None -> False |- _ ] => rewrite H in *; simpl in H1; simpl in H2; try tauto
          end.
        match goal with
        | [ H : In _ _ |- _ ] => simpl in H
        end.
        Opaque evalExpr.
        intuition idtac; kinv_action_dest.
        Transparent evalExpr.
        * SCRegs_find.
          f_equal.
          -- do 2 match goal with
                  | [ |- context[@evalExpr ?t (STRUCT {"addr" ::= rv32iAlignAddr ?ty ?adr; "op" ::= ?o; "data" ::= ?d})%kami_expr] ] => replace (@evalExpr t (STRUCT {"addr" ::= rv32iAlignAddr ty adr; "op" ::= _; "data" ::= _})%kami_expr) with (@evalExpr t (STRUCT {"addr" ::= #(evalExpr (rv32iAlignAddr ty adr)); "op" ::= o; "data" ::= d})%kami_expr) by eauto
                  end.
             unfold censorLabel, censorSCMeth, hide, annot, calls, defs.
             f_equal.
             match goal with
             | [ H1 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr1; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _,
                 H2 : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add "exec" (existT _ _ (evalExpr STRUCT {"addr" ::= ?addr2; "op" ::= _; "data" ::= _}%kami_expr, _)) _ |}) = _
                 |- _ ] => replace (evalExpr addr1) with (evalExpr addr2)
             end.
             ++ clear; eauto.
             ++ match goal with
                | [ H : labelToTraceEvent ?l = _,
                    x : forall _ : Fin.t 1, _
                    |- evalExpr ?adr = _ ] =>
                  replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!(RsToProc rv32iDataBytes)@."data")%kami_expr))) in H by eauto
                end.
                Opaque evalExpr.
                match goal with
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                end.
                Transparent evalExpr.
                match goal with
                | [ H : ?x = _ |- ?x = _ ] => rewrite H
                end.
                reflexivity.
          -- match goal with
             | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
             end;
               try match goal with
                   | [ HBFM : BoundedForwardActiveMultistep _ _ ?r1 _ ?l |- BoundedForwardActiveMultistep _ _ ?r2 _ ?l ] =>
                     replace r2 with r1; try eassumption
                   | [ |- censorTrace _ = censorTrace _ ] => eassumption
                   | [ |- relatedTrace _ _ ] => eassumption
                   end.
             ++ match goal with
                | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
                end.
                subst.
                match goal with
                | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1; try eassumption
                end.
                unfold rv32iNextPc.
                unfold rv32iGetOptype in H1.
                evexg.
                evex H1.
                repeat match goal with
                       | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                       | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                       end;
                  unfold evalConstT in *;
                  try reflexivity;
                  try match goal with
                      | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                      end;
                  discriminate H1.
             ++ match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                match goal with
                | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2
                end.
                ** clear; eauto.
                ** unfold rset.
                   destruct (weq dstIdx (wzero _)); try tauto.
                   evexg.
                   apply functional_extensionality.
                   intros.
                   unfold dstIdx.
                   match goal with
                   | [ |- (if _ then ?x else _) = (if _ then ?y else _) ] => replace x with y; [ reflexivity | idtac ]
                   end.
                   simpl.
                   match goal with
                   | [ H : labelToTraceEvent ?l = Some (Rd $ (0) laddr_aligned val),
                           x : forall _ : Fin.t 1, _
                                              |- _ ] =>
                     match goal with
                     | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= _}%kami_expr, x)) _|}) = Some (Rd $ (0) _ val) |- _ ] =>
                       replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!(RsToProc rv32iDataBytes)@."data")%kami_expr))) in H by eauto; inversion H
                     end
                   end.
                   reflexivity.
             ++ match goal with
                | [ H : foldSSUpds ss0 = _ |- _ ] => rewrite H
                end.
                match goal with
                | [ |- FMap.M.union (FMap.M.add "rf" (existT _ _ ?r1) (FMap.M.add "pc" (existT _ _ ?p1) (FMap.M.empty _))) _ = SCRegs ?r2 _ ?p2 ] => unfold SCRegs; replace r1 with r2; [ replace p1 with p2 | idtac ]
                end.
                ** clear; eauto.
                ** evexg.
                   unfold rv32iNextPc.
                   unfold rv32iGetOptype in H1.
                   evexg.
                   evex H1.
                   repeat match goal with
                          | [ H : context[isEq _ _ (evalConstT ?o)] |- _ ] => destruct (isEq _ _ (evalConstT o))
                          | [ |- context[isEq _ _ (evalConstT ?o) ] ] => destruct (isEq _ _ (evalConstT o))
                          end;
                     unfold evalConstT in *;
                     try reflexivity;
                     try match goal with
                         | [ H1 : evalExpr (getOpcodeE _) = ?o1, H2 : evalExpr (getOpcodeE _) = ?o2 |- _ ] => rewrite H1 in H2; discriminate H2
                         end;
                     discriminate H1.
                ** unfold rset.
                   fold dstIdx.
                   destruct (weq dstIdx (wzero _)); try tauto.
                   evexg.
                   apply functional_extensionality.
                   intros.
                   unfold dstIdx.
                   match goal with
                   | [ |- (if _ then ?x else _) = (if _ then ?y else _) ] => replace x with y; [ reflexivity | idtac ]
                   end.
                   simpl.
                   match goal with
                   | [ H : labelToTraceEvent ?l = Some (Rd $ (0) laddr_aligned val0),
                           x : forall _ : Fin.t 1, _
                                              |- _ ] =>
                     match goal with
                     | [ H : labelToTraceEvent (hide {| annot := _; defs := _; calls := FMap.M.add _ (existT _ _ (evalExpr STRUCT {"addr" ::= ?adr; "op" ::= _; "data" ::= _}%kami_expr, x)) _|}) = Some (Rd $ (0) _ val0) |- _ ] =>
                       replace (labelToTraceEvent l) with (Some (Rd $ (0) (evalExpr adr) (evalExpr (#x!(RsToProc rv32iDataBytes)@."data")%kami_expr))) in H
                     end
                   end.
                   --- Opaque evalExpr.
                       inversion H18.
                       Transparent evalExpr.
                       reflexivity.
                   --- eauto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
        * evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
      + evbool_auto.
  Admitted.

  Lemma eval_const : forall n (t : Expr type (SyntaxKind (Bit n))) c, evalExpr t = c -> evalExpr (t == (Const _ (ConstBit c)))%kami_expr = true.
    simpl.
    intros.
    rewrite H.
    destruct (weq c c); tauto.
  Qed.

  Lemma abstractToSCRelated :
    forall rf pm pc maxsp trace,
      hasTrace rf pm pc maxsp trace ->
      exists newRegs ls,
        BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs ls /\
        relatedTrace trace ls.
  Proof.
    induction 1.
    - repeat eexists; repeat econstructor.
    - shatter.
      repeat eexists.
      + eapply BFMulti.
        * tauto.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execLd").
                simpl.
                tauto.
             ++ repeat match goal with
                       | [ |- SemAction _ (MCall _ _ _ _) _ _ _ ] => fail 1
                       | _ => econstructor
                       end; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     let Heq := fresh in
                     assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       rewrite Heq;
                       rewrite H0;
                       rewrite eval_const;
                       tauto
                   end.
                ** unfold evalExpr; fold evalExpr.
                   unfold evalUniBool.
                   rewrite Bool.negb_true_iff.
                   unfold isEq.
                   match goal with
                   | |- (if ?b then _ else _) = _ => destruct b
                   end.
                   --- rewrite H0 in e.
                       tauto.
                   --- reflexivity.
                ** eapply SemMCall.
                   --- instantiate (1 := FMap.M.empty _).
                       FMap.findeq.
                   --- instantiate (1 := evalExpr (STRUCT { "data" ::= #val })%kami_expr).
                       reflexivity.
                   --- repeat econstructor; try FMap.findeq.
        * simpl. congruence.
        * simpl. congruence.
        * match goal with
          | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs, rset.
          eauto.
      + constructor; try assumption.
        unfold labelToTraceEvent, getLabel.
        unfold callsToTraceEvent.
        repeat (match goal with
                | [ |- context[match ?x with _ => _ end] ] =>
                  let x' := eval hnf in x in change x with x'
                end; cbv beta iota).
        unfold evalExpr.
        match goal with
        | [ |- Some (Rd $ (0) ?x1 ?y1) = Some (Rd $ (0) ?x2 ?y2) ] => replace x1 with x2; [ reflexivity | idtac ]
        end.
        match goal with
        | [ |- context[icons' ("addr" ::= ?x)%init _] ] => replace laddr_aligned with (evalExpr x)%kami_expr; [ reflexivity | idtac ] 
        end.
        subst.
        repeat match goal with
               | [ x : fullType type _ |- _ ] =>
                 progress unfold x
               | [ x : word _ |- _ ] =>
                 progress unfold x
               end.
        unfold evalExpr.
        reflexivity.
    - shatter.
      repeat eexists.
      + eapply BFMulti.
        * tauto.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execLdZ").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     let Heq := fresh in
                     assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       rewrite Heq;
                       rewrite H0;
                       rewrite eval_const;
                       tauto
                   end.
                ** unfold evalExpr; fold evalExpr.
                   unfold evalUniBool.
                   unfold isEq.
                   match goal with
                   | |- (if ?b then _ else _) = _ => destruct b
                   end.
                   --- reflexivity.
                   --- rewrite H0 in n.
                       tauto.
        * simpl. congruence.
        * simpl. congruence.
        * match goal with
          | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs, rset.
          eauto.
      + constructor; try assumption.
        unfold labelToTraceEvent, getLabel.
        unfold callsToTraceEvent.
        repeat (match goal with
                | [ |- context[match ?x with _ => _ end] ] =>
                  let x' := eval hnf in x in change x with x'
                end; cbv beta iota).
        reflexivity.
    - shatter.
      repeat eexists.
      + eapply BFMulti.
        * tauto.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execSt").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     let Heq := fresh in
                     assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       rewrite Heq;
                       rewrite H0;
                       rewrite eval_const;
                       tauto
                   end.
        * simpl. congruence.
        * simpl. congruence.
        * match goal with
          | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs.
          eauto.
      + constructor; try assumption.
        unfold labelToTraceEvent, getLabel.
        unfold callsToTraceEvent.
        repeat (match goal with
                | [ |- context[match ?x with _ => _ end] ] =>
                  let x' := eval hnf in x in change x with x'
                end; cbv beta iota).
        unfold evalExpr.
        match goal with
        | [ |- Some (Wr $ (0) ?x1 ?y1) = Some (Wr $ (0) ?x2 ?y2) ] => replace x1 with x2; [ replace y1 with y2; [ reflexivity | idtac ] | idtac ]
        end.
        * match goal with
          | [ |- context[icons' ("data" ::= ?x)%init _] ] => replace stVal with (evalExpr x)%kami_expr; [ reflexivity | idtac ] 
          end.
          subst.
          unfold evalExpr.
          repeat match goal with
                 | [ x : fullType type _ |- _ ] =>
                   progress unfold x
                 | [ x : word _ |- _ ] =>
                   progress unfold x
                 end.
          reflexivity.
        * match goal with
          | [ |- context[icons' ("addr" ::= ?x)%init _] ] => replace saddr_aligned with (evalExpr x)%kami_expr; [ reflexivity | idtac ] 
          end.
          subst.
          repeat match goal with
                 | [ x : fullType type _ |- _ ] =>
                   progress unfold x
                 | [ x : word _ |- _ ] =>
                   progress unfold x
                 end.
          unfold evalExpr.
          reflexivity.
    - shatter.
      repeat eexists.
      + eapply BFMulti.
        * tauto.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execToHost").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     let Heq := fresh in
                     assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       rewrite Heq;
                       rewrite H0;
                       rewrite eval_const;
                       tauto
                   end.
        * simpl. congruence.
        * simpl. congruence.
        * match goal with
          | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs.
          eauto.
      + constructor; try assumption.
        unfold labelToTraceEvent, getLabel.
        unfold callsToTraceEvent.
        repeat (match goal with
                | [ |- context[match ?x with _ => _ end] ] =>
                  let x' := eval hnf in x in change x with x'
                end; cbv beta iota).
        unfold evalExpr; fold evalExpr.
        match goal with
        | [ |- Some (ToHost $ (0) ?x1) = Some (ToHost $ (0) ?x2) ] => replace x1 with x2; [ reflexivity | idtac ]
        end.
        subst.
        repeat match goal with
               | [ x : fullType type _ |- _ ] =>
                 progress unfold x
               | [ x : word _ |- _ ] =>
                 progress unfold x
               end.
          reflexivity.
    - shatter.
      destruct (isEq (Bit rv32iRfIdx)
                     dst
                     (wzero _)).
      + repeat eexists.
        * eapply BFMulti.
          -- tauto.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execFromHostZ").
                   simpl.
                   tauto.
                ** repeat econstructor; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         let Heq := fresh in
                         assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           rewrite Heq;
                           rewrite H0;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold isEq.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ reflexivity.
                       +++ unfold dst in e.
                           rewrite <- H0 in e.
                           tauto.
          -- simpl. congruence.
          -- simpl. congruence.
          -- match goal with
             | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
             eauto.
        * constructor; try assumption.
          reflexivity.
      + repeat eexists.
        * eapply BFMulti.
          -- tauto.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execFromHost").
                   simpl.
                   tauto.
                ** repeat match goal with
                          | [ |- SemAction _ (MCall _ _ _ _) _ _ _ ] => fail 1
                          | _ => econstructor
                          end; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         let Heq := fresh in
                         assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           rewrite Heq;
                           rewrite H0;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold evalUniBool.
                       unfold isEq.
                       rewrite Bool.negb_true_iff.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ unfold dst in n.
                           rewrite <- H0 in n.
                           tauto.
                       +++ reflexivity.
                   --- eapply SemMCall.
                       +++ instantiate (1 := FMap.M.empty _).
                           FMap.findeq.
                       +++ instantiate (1 := val).
                           reflexivity.
                       +++ repeat econstructor; FMap.findeq.
          -- simpl. congruence.
          -- simpl. congruence.
          -- match goal with
             | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
             eauto.
        * constructor; try assumption.
          reflexivity.
    - shatter.
      repeat eexists.
      + eapply BFMulti.
        * tauto.
        * apply SemFacts.substepZero_imp_step.
          -- reflexivity.
          -- eapply SingleRule.
             ++ instantiate (2 := "execNmZ").
                simpl.
                tauto.
             ++ repeat econstructor; try FMap.findeq.
                ** match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                     let Heq := fresh in
                     assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                       rewrite Heq;
                       rewrite H0;
                       rewrite eval_const;
                       tauto
                   end.
                ** unfold rv32iGetDst.
                   unfold evalExpr; fold evalExpr.
                   rewrite H0.
                   rewrite H2.
                   simpl.
                   reflexivity.
        * simpl. congruence.
        * simpl. congruence.
        * match goal with
          | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
          end.
          unfold SCRegs, rset.
          eauto.
      + constructor; try assumption.
        reflexivity.
    - shatter.
      destruct (isEq (Bit rv32iRfIdx)
                     dst
                     (wzero _)).
      + repeat eexists.
        * eapply BFMulti.
          -- tauto.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execNmZ").
                   simpl.
                   tauto.
                ** repeat econstructor; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         let Heq := fresh in
                         assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           rewrite Heq;
                           rewrite H0;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold isEq.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ reflexivity.
                       +++ unfold dst in e.
                           rewrite <- H0 in e.
                           tauto.
          -- simpl. congruence.
          -- simpl. congruence.
          -- match goal with
             | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
             eauto.
        * constructor; try assumption.
          reflexivity.
      + repeat eexists.
        * eapply BFMulti.
          -- tauto.
          -- apply SemFacts.substepZero_imp_step.
             ++ reflexivity.
             ++ eapply SingleRule.
                ** instantiate (2 := "execNm").
                   simpl.
                   tauto.
                ** repeat econstructor; try FMap.findeq.
                   --- match goal with
                       | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true =>
                         let Heq := fresh in
                         assert (Heq : x = pm (evalExpr (rv32iAlignPc type pc))) by reflexivity;
                           rewrite Heq;
                           rewrite H0;
                           rewrite eval_const;
                           tauto
                       end.
                   --- unfold evalExpr; fold evalExpr.
                       unfold evalUniBool.
                       unfold isEq.
                       rewrite Bool.negb_true_iff.
                       match goal with
                       | |- (if ?b then _ else _) = _ => destruct b
                       end.
                       +++ unfold dst in n.
                           rewrite <- H0 in n.
                           tauto.
                       +++ reflexivity.
          -- simpl. congruence.
          -- simpl. congruence.
          -- match goal with
             | [ IH : BoundedForwardActiveMultistep _ _ ?r _ _ |- BoundedForwardActiveMultistep _ _ ?r' _ _ ] => replace r' with r; try eassumption
             end.
             unfold SCRegs, rset.
             eauto.
        * constructor; try assumption.
          reflexivity.
          Unshelve.
          -- exact (evalExpr (STRUCT { "data" ::= $0 }))%kami_expr.
          -- exact (wzero _).
  Qed.

  Definition getrf (regs : RegsT) : regfile :=
    match FMap.M.find "rf" regs with
    | Some (existT _
                   (SyntaxKind (Vector (Bit 32) 5))
                   rf) => rf
    | _ => (fun _ => wzero _)
    end.

  Definition getpm (regs : RegsT) : progMem :=
    match FMap.M.find "pgm" regs with
    | Some (existT _
                   (SyntaxKind (Vector (Bit 32) 8))
                   pm) => pm
    | _ => (fun _ => wzero _)
    end.

  Definition getpc (regs : RegsT) : word 16 :=
    match FMap.M.find "pc" regs with
    | Some (existT _
                   (SyntaxKind (Bit 16))
                   pc) => pc
    | _ => (wzero _)
    end.

  Lemma SCToAbstractRelated :
    forall rf pm pc maxsp newRegs ls,
      BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs ls ->
      exists trace,
        hasTrace rf pm pc maxsp trace /\
        relatedTrace trace ls.
  Proof.
    intros.
    let Heq := fresh in
    remember (SCRegs rf pm pc) as regs eqn:Heq; unfold SCRegs in Heq;
      replace rf with (getrf regs) by (subst; FMap.findeq);
      replace pm with (getpm regs) by (subst; FMap.findeq);
      replace pc with (getpc regs) by (subst; FMap.findeq);
      clear rf pm pc Heq.
    match goal with
    | [ H : BoundedForwardActiveMultistep _ _ _ _ _ |- _ ] =>
      induction H
    end.
    - eexists; repeat econstructor.
    - shatter.
      destruct H0.
      apply substepsComb_substepsInd in HSubsteps.
      apply SCSubsteps in HSubsteps.
      intuition idtac; shatter;
        match goal with
        | [ Hle : foldSSLabel ss = _, Hue : foldSSUpds ss = _ |- _ ] => rewrite Hle in *; rewrite Hue in *
        end; try tauto.
      Opaque evalExpr.
      match goal with
      | [ HIn : In (_ :: _)%struct (getRules _) |- _ ] => simpl in HIn; intuition idtac
      end;
        match goal with
        | [ Heq : _ = (_ :: _)%struct |- _ ] =>
          inversion Heq; clear Heq
        end; subst;
          kinv_action_dest;
          match goal with
          | [ Hpc : FMap.M.find "pc" o = Some (existT _ _ ?pc),
                    Hrf : FMap.M.find "rf" o = Some (existT _ _ ?rf),
                          Hpm : FMap.M.find "pgm" o = Some (existT _ _ ?pm)
              |- _ ] =>
            replace (getpc o) with pc by (unfold getpc; FMap.findeq);
              replace (getrf o) with rf by (unfold getrf; FMap.findeq);
              replace (getpm o) with pm by (unfold getpm; FMap.findeq)
          end.
      Transparent evalExpr.
      + eexists.
        split.
        * apply htLd.
          -- match goal with
             | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
             end.
             match goal with
             | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
             end.
             assumption.
          -- reflexivity.
          -- match goal with
             | [ H : context[rv32iGetOptype] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ H : context[rv32iGetLdDst] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ Hht : hasTrace ?x1 ?x2 ?x3 _ _ |- hasTrace ?y1 ?y2 ?y3 _ _ ] =>
               let Heq := fresh in
               assert (x1 = y1) as Heq;
                 [ idtac |
                   rewrite Heq in Hht;
                   clear Heq;
                   assert (x2 = y2) as Heq;
                   [ idtac |
                     rewrite Heq in Hht;
                     clear Heq;
                     assert (x3 = y3) as Heq;
                     [ idtac |
                       rewrite Heq in Hht;
                       clear Heq;
                       eassumption
                     ]
                   ]
                 ]
             end.
             ++ match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                unfold getrf.
                FMap.findeq.
                simplify_match.
                evexg.
                apply functional_extensionality.
                intros.
                unfold rset.
                evex H11.
                boolex.
                match goal with
                | [ |- _ = (if ?eq then _ else _) _ ] => destruct eq; tauto
                end.
             ++ rewrite H14.
                unfold getpm.
                FMap.findeq.
             ++ rewrite H14.
                unfold getpc.
                FMap.findeq.
        * constructor; try assumption.
          FMap.findeq.
      + eexists.
        split.
        * eapply htLdZ.
          -- match goal with
             | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
             end.
             match goal with
             | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
             end.
             assumption.
          -- reflexivity.
          -- match goal with
             | [ H : context[rv32iGetOptype] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ H : context[rv32iGetLdDst] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ Hfu : foldSSUpds ss = _,
                       Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
               replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                 replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                 replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                 eassumption
             end.
        * constructor; try assumption.
          FMap.findeq.
      + eexists.
        split.
        * eapply htSt.
          -- match goal with
             | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
             end.
             match goal with
             | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
             end.
             assumption.
          -- reflexivity.
          -- match goal with
             | [ H : context[rv32iGetOptype] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ Hfu : foldSSUpds ss = _,
                       Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
               replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                 replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                 replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                 eassumption
             end.
        * constructor; try assumption.
          FMap.findeq.
      + eexists.
        split.
        * eapply htTh.
          -- match goal with
             | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
             end.
             match goal with
             | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
             end.
             assumption.
          -- reflexivity.
          -- match goal with
             | [ H : context[rv32iGetOptype] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ Hfu : foldSSUpds ss = _,
                       Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
               replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                 replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                 replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                 eassumption
             end.
        * constructor; try assumption.
          FMap.findeq.
      + eexists.
        split.
        * eapply htFh.
          -- match goal with
             | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
             end.
             match goal with
             | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
             end.
             assumption.
          -- reflexivity.
          -- match goal with
             | [ H : context[rv32iGetOptype] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ Hfu : foldSSUpds ss = _,
                       Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
               replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                 replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                 replace (getrf o') with x1 in Hht;
                 try eassumption
             end.
             match goal with
             | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
             end.
             unfold getrf.
             FMap.findeq.
             simplify_match.
             evexg.
             apply functional_extensionality.
             intros.
             unfold rset.
             evex H11.
             boolex.
             match goal with
             | [ |- (if ?eq then _ else _) _ = _ ] => destruct eq; tauto
             end.
        * constructor; try assumption.
          FMap.findeq.
      + eexists.
        split.
        * eapply htFh.
          -- match goal with
             | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
             end.
             match goal with
             | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
             end.
             assumption.
          -- reflexivity.
          -- match goal with
             | [ H : context[rv32iGetOptype] |- _ ] =>
               evex H
             end.
             boolex.
             assumption.
          -- match goal with
             | [ Hfu : foldSSUpds ss = _,
                       Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
               replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                 replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                 replace (getrf o') with x1 in Hht;
                 try eassumption
             end.
             match goal with
             | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
             end.
             unfold getrf.
             FMap.findeq.
             simplify_match.
             unfold rset.
             evexg.
             apply functional_extensionality.
             intros.
             evex H11.
             boolex.
             match goal with
             | [ |- (if ?eq then _ else _) _ = _ ] => destruct eq; tauto
             end.
        * constructor; try assumption.
          FMap.findeq.
      + destruct (weq
                    (evalExpr (getOpcodeE # (x2 (evalExpr (rv32iAlignPc type x0)))%kami_expr))
                    rv32iOpBRANCH).
        * eexists.
          split.
          -- eapply htNmBranch.
             ++ match goal with
                | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
                end.
                match goal with
                | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
                end.
                assumption.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    replace (getrf o') with x1 in Hht;
                    try eassumption
                end.
                match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                unfold getrf.
                FMap.findeq.
                simplify_match.
                evexg.
                apply functional_extensionality.
                intros.
                evex H11.
                boolex.
                unfold rv32iGetDst in n0.
                evex n0.
                rewrite e in n0.
                tauto.
          -- constructor; try assumption.
             FMap.findeq.
        * eexists.
          split.
          -- eapply htNm.
             ++ match goal with
                | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
                end.
                match goal with
                | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
                end.
                assumption.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    replace (getrf o') with x1 in Hht;
                    try eassumption
                end.
                match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                unfold getrf.
                FMap.findeq.
                simplify_match.
                unfold rset.
                evexg.
                apply functional_extensionality.
                intros.
                evex H11.
                boolex.
                match goal with
                | [ |- (if ?eq then _ else _) _ = _ ] => destruct eq; tauto
                end.
          -- constructor; try assumption.
             FMap.findeq.
      + destruct (weq
                    (evalExpr (getOpcodeE # (x2 (evalExpr (rv32iAlignPc type x0)))%kami_expr))
                    rv32iOpBRANCH).
        * eexists.
          split.
          -- eapply htNmBranch.
             ++ match goal with
                | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
                end.
                match goal with
                | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
                end.
                assumption.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    replace (getrf o') with x1 in Hht by (rewrite Hfu; unfold getrf; FMap.findeq);
                    eassumption
                end.
          -- constructor; try assumption.
             FMap.findeq.
        * eexists.
          split.
          -- eapply htNm.
             ++ match goal with
                | [ H : inBounds _ _ |- _ ] => unfold inBounds in H
                end.
                match goal with
                | [ H : FMap.M.find "rf" _ = _ |- _ ] => rewrite H in *
                end.
                assumption.
             ++ reflexivity.
             ++ match goal with
                | [ H : context[rv32iGetOptype] |- _ ] =>
                  evex H
                end.
                boolex.
                assumption.
             ++ assumption.
             ++ match goal with
                | [ Hfu : foldSSUpds ss = _,
                          Hht : hasTrace (getrf ?o') (getpm ?o') (getpc ?o') _ _ |- hasTrace ?x1 ?x2 ?x3 _ _ ] =>
                  replace (getpm o') with x2 in Hht by (rewrite Hfu; unfold getpm; FMap.findeq);
                    replace (getpc o') with x3 in Hht by (rewrite Hfu; unfold getpc; FMap.findeq);
                    replace (getrf o') with x1 in Hht;
                    try eassumption
                end.
                match goal with
                | [ H : foldSSUpds ss = _ |- _ ] => rewrite H
                end.
                unfold getrf.
                FMap.findeq.
                simplify_match.
                unfold rset.
                evexg.
                evex H11.
                boolex.
                match goal with
                | [ |- (if ?eq then _ else _) = _ ] => destruct eq; tauto
                end.
          -- constructor; try assumption.
             FMap.findeq.
  Qed.

  Theorem abstractToSCHiding :
    forall rf pm pc maxsp,
      abstractHiding rf pm pc maxsp ->
      kamiHiding censorSCMeth extractFhSC
                 rv32iProcInst
                 maxsp
                 (SCRegs rf pm pc).
  Proof.
    unfold abstractHiding, kamiHiding.
    intros.
    match goal with
    | [ H : BoundedForwardActiveMultistep _ _ _ _ _ |- _ ] => let H' := fresh in assert (H' := H); eapply SCToAbstractRelated in H'
    end.
    shatter.
    match goal with
    | [ Hrel : relatedTrace ?t ?ls,
               Hextract : extractFhLabelSeq extractFhSC ?ls = _,
                          Htrace : hasTrace _ _ _ _ _,
                                   Habs : forall _ _, hasTrace _ _ _ _ _ -> extractFhTrace _ = _ -> forall _, length _ = length _ -> _,
          Hlen : length _ = length _
          |- context[extractFhLabelSeq _ _ = ?fhTrace] ] =>
      rewrite <- (relatedFhTrace _ _ Hrel) in Hextract; specialize (Habs _ _ Htrace Hextract fhTrace Hlen)
    end.
    shatter.
    match goal with
    | [ Htrace : hasTrace _ _ _ _ ?t,
                 Hextract : extractFhTrace ?t = ?fhTrace
        |- context[?fhTrace] ] => pose (abstractToSCRelated _ _ _ _ _ Htrace)
    end.
    shatter.
    match goal with
    | [ H : BoundedForwardActiveMultistep _ _ _ ?regs ?ls |- _ ] => exists ls, regs
    end.
    repeat split;
      match goal with
      | [ |- BoundedForwardActiveMultistep _ _ _ _ _ ] => assumption
      | [ Htrace1 : hasTrace _ _ _ _ _, Htrace2 : hasTrace _ _ _ _ _ |- censorLabelSeq _ _ = censorLabelSeq _ _ ] => eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ Htrace1 Htrace2); eassumption
      | [ |- extractFhLabelSeq _ _ = _ ] => erewrite <- relatedFhTrace; eassumption
      end.
  Qed.

End SCTiming.

Section Compilation.

  Definition RtlHiding : Prop := True.

End Compilation.