Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics.
Require Import Ex.SC Ex.IsaRv32.
Require Import Lib.CommonTactics.
Require Import Compile.Rtl Compile.CompileToRtlTryOpt.

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
      relatedTrace (Nm pc :: trace') (lbl :: ls').

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
      simpl;
      f_equal;
        repeat match goal with
               | [ Hbm : BoundedForwardActiveMultistep _ _ _ _ (?lbl :: _) |- _ ] =>
                 inversion Hbm;
                   clear Hbm;
                   match goal with
                   | [ Hst : Step _ _ _ lbl |- _ ] =>
                     inversion Hst;
                       clear Hst
                   end
               end;
        opaque_subst.
      + apply substepsComb_substepsInd in HSubsteps.
        destruct HSubsteps.
        * simpl in H10.
          congruence.
        * destruct sul.
          -- simpl in H6.
             destruct l.
             replace ll with {| annot := Some o;
                                defs := FMap.M.union (FMap.M.empty {x : SignatureT & SignT x}) defs;
                                calls := FMap.M.union scs calls |} in * by (destruct annot; subst; reflexivity).
             inversion H0; subst.
             ++ simpl in H14.
                congruence.
             ++ simpl in HInRules.
                intuition idtac.
(*        Check (existT _
                                      {| arg := Struct
                                                  (STRUCT
                                                     {"addr" :: Bit 16;
                                                      "op" :: Bool;
                                                      "data" :: Bit 32});
                                         ret := Struct
                                                  (STRUCT
                                                     {"data" :: Bit 32})
                                      |}
                                      (evalExpr (STRUCT { "addr" ::= #laddr_aligned;
                                                                   "op" ::= _;
                                                                   "data" ::= $0 })%kami_expr,
                                                evalExpr (STRUCT { "data" ::= #val0 })%kami_expr)).
        assert (foldSSLabel ss =
                {| annot := Some (Some "execLd");
                   defs := FMap.M.empty _;
                   calls := FMap.M.add
                              "exec"
                              (existT _
                                      {| arg := Struct
                                                  (STRUCT
                                                     {"addr" :: Bit 16;
                                                      "op" :: Bool;
                                                      "data" :: Bit 32});
                                         ret := Struct
                                                  (STRUCT
                                                     {"data" :: Bit 32})
                                      |}
                                      (evalExpr (STRUCT { "addr" ::= #laddr_aligned;
                                                                   "op" ::= #(false);
                                                                   "data" ::= $0 })%kami_expr,
                                                evalExpr (STRUCT { "data" ::= #val0 })%kami_expr)) |}).
        induction HSubsteps.
        * simpl in H10.
          congruence.
        * 
      + match goal with
        | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
        end;
        try match goal with
            | [ HBFM : BoundedForwardActiveMultistep _ _ ?r1 _ ?l |- BoundedForwardActiveMultistep _ _ ?r2 _ ?l ] =>
              replace r2 with r1; try eassumption
            | [ |- censorTrace _ = censorTrace _ ] => eassumption
            | [ |- relatedTrace _ _ ] => eassumption
            end.
        * match goal with
          | [ Hht : hasTrace _ _ _ _ (_ :: ?t) |- hasTrace _ _ _ _ ?t ] => inversion Hht
          end.
          subst.
          match goal with
          | [ Hht : hasTrace _ _ ?pc1 _ ?t |- hasTrace _ _ ?pc2 _ ?t ] => replace pc2 with pc1; try eassumption
          end.
          unfold rv32iNextPc.
          unfold rv32iGetOptype in H1.
          try destruct (getOpcodeE # (pm (evalExpr (rv32iAlignPc type pc0)))%kami_expr).*)
  Admitted.

  Ltac shatter := repeat match goal with
                         | [ H : exists _, _ |- _ ] => destruct H
                         | [ H : _ /\ _ |- _ ] => destruct H
                         end.

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
      destruct HSubsteps.
      + simpl in H1.
        congruence.
      + destruct s.
        destruct unitAnnot.
        * simpl in *.
          unfold addLabelLeft, getSLabel in *.
          simpl in *.
          destruct (foldSSLabel ss).
          destruct annot.
          -- simpl in *.
             unfold hide in *.
             FMap.findeq.
             simpl in *.
             inversion substep.
             ++ subst.
                tauto.
             ++ subst.
                simpl in *.
                intuition idtac;
                match goal with
                | [ Heq : _ = (_ :: _)%struct |- _ ] =>
                  inversion Heq; clear Heq
                end; subst.
                ** SymEval.
  Admitted.

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