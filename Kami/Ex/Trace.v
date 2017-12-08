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
  | Nm (pc : address)
  | Rd (pc : address) (addr : address) (val : data)
  | Wr (pc : address) (addr : address) (val : data)
  | Branch (pc : address) (taken : bool)
  | ToHost (pc : address) (val : data)
  | FromHost (pc : address) (val : data).

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
      hasTrace rf mem pm pc maxsp (Rd pc laddr_aligned val :: trace')
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
      hasTrace rf mem pm pc maxsp (Wr pc saddr_aligned stVal :: trace')
  | htTh : forall inst rf mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opTh ->
      let srcIdx := evalExpr (rv32iGetSrc1 type inst) in
      let srcVal := rget rf srcIdx in
      hasTrace rf mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (ToHost pc srcVal :: trace')
  | htFh : forall inst rf val mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opFh ->
      let dst := evalExpr (rv32iGetDst type inst) in
      hasTrace (rset rf dst val) mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (FromHost pc val :: trace')
  | htNmBranch : forall inst rf mem pm pc maxsp trace',
      rget rf spReg <= maxsp ->
      pmget pm (evalExpr (rv32iAlignPc _ pc)) = inst ->
      evalExpr (rv32iGetOptype type inst) = opNm ->
      evalExpr (getOpcodeE #inst)%kami_expr = rv32iOpBRANCH ->
      hasTrace rf mem pm (evalExpr (rv32iNextPc type rf pc inst)) maxsp trace' ->
      hasTrace rf mem pm pc maxsp (Branch pc (evalExpr (rv32iBranchTaken type rf inst)) :: trace')
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
      hasTrace rf mem pm pc maxsp (Nm pc :: trace').


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

  Inductive BoundedForwardActiveMultistep (m : Modules) (maxsp : word 32) : RegsT -> RegsT -> list LabelT -> Prop :=
    NilBFMultistep : forall o1 o2 : RegsT,
      o1 = o2 -> BoundedForwardActiveMultistep m maxsp o1 o2 nil
  | BFMulti : forall (o : RegsT) (a : list LabelT) (n : RegsT) (u : UpdatesT) (l : LabelT),
      inBounds maxsp o ->
      Step m o u l ->
      annot l <> None ->
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
      let val := evalExpr (#argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."data")%kami_expr in
      if evalExpr (#argV!(RqFromProc rv32iAddrSize rv32iDataBytes)@."op")%kami_expr
      then Some (Wr $0 addr val)
      else Some (Rd $0 addr val)
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
    forall rf mem pm pc maxsp trace1 trace2 newRegs1 newRegs2 ls1 ls2,
      hasTrace rf mem pm pc maxsp trace1 ->
      hasTrace rf mem pm pc maxsp trace2 ->
      BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs1 ls1 ->
      BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs2 ls2 ->
      relatedTrace trace1 ls1 ->
      relatedTrace trace2 ls2 ->
      censorTrace trace1 = censorTrace trace2 ->
      censorLabelSeq censorSCMeth ls1 = censorLabelSeq censorSCMeth ls2.
  Proof.
    intros rf mem pm pc maxsp trace1 trace2 newRegs1 newRegs2 ls1 ls2 Hht1.
    move Hht1 at top.
    generalize trace2 newRegs1 newRegs2 ls1 ls2.
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
      | [ Hrt1 : relatedTrace (_ :: _) ?l1, Hrt2 : relatedTrace (_ :: _) ?l2 |- _ ] => destruct l1; destruct l2; inversion Hrt1; inversion Hrt2
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
        inversion HSubsteps.
        * simpl.
          destruct ss.
          -- simpl in H9.
             rewrite FMap.M.subtractKV_empty_1 in H9.
             unfold callsToTraceEvent in H9.
             simpl in H9.
             congruence.
          -- simpl in H5.
             unfold addLabelLeft in H5.
             unfold mergeLabel in H5.
             simpl in H5.
             admit.
        * admit.
      + match goal with
        | [ IH : context[censorLabelSeq _ _ = censorLabelSeq _ _] |- _ ] => eapply IH
        end;
        try match goal with
            | [ HBFM : BoundedForwardActiveMultistep _ _ ?r1 _ ?l |- BoundedForwardActiveMultistep _ _ ?r2 _ ?l ] =>
              let H := fresh in
              assert (r2 = r1) as H by admit;
                rewrite H;
                eassumption
            | [ |- censorTrace _ = censorTrace _ ] => eassumption
            end.
        apply substepsComb_substepsInd in HSubsteps0.
        induction HSubsteps0.
        * simpl in H18.
          rewrite FMap.M.subtractKV_empty_1 in H18.
          unfold callsToTraceEvent in H18.
          repeat rewrite FMap.M.find_empty in H18.
          congruence.
          (*
        * inversion H3.
        replace dstIdx0 with dstIdx in * by (subst; reflexivity).
        replace val0 with val in *.
        * subst; assumption.
        * admit.
    *)
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

  (* Lemma no_meths_wellHidden : forall regs rules label,  (Step (Mod regs rules nil) wellHidden*)

  Lemma abstractToSCRelated :
    forall rf mem pm pc maxsp trace,
      hasTrace rf mem pm pc maxsp trace ->
      exists newRegs ls,
        BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs ls /\
        relatedTrace trace ls.
  Proof.
    induction 1.
    - repeat eexists; repeat econstructor.
    - shatter.
      assert (substep : SubstepRec rv32iProcInst (SCRegs rf pm pc)).
      + destruct (weq dstIdx (wzero _)); econstructor.
        * eapply SingleRule.
          -- instantiate (2 := "execLdZ").
             simpl.
             tauto.
             -- repeat (econstructor; try FMap.findeq).
                ++ match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true => assert (x = pmget pm (evalExpr (rv32iAlignPc type pc)))
                   end.
                   ** reflexivity.
                      ** rewrite H6.
                         rewrite H0.
                         rewrite eval_const; tauto.
                ++ rewrite eval_const.
                   ** reflexivity.
                   ** unfold evalExpr; fold evalExpr.
                      unfold pmget in *.
                      rewrite H0.
                      assumption.
                ++ FMap.findeq.
        * eapply SingleRule.
          -- instantiate (2 := "execLd").
             simpl.
             tauto.
             -- repeat (econstructor; try FMap.findeq).
                ++ match goal with
                   | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true => assert (x = pmget pm (evalExpr (rv32iAlignPc type pc)))
                   end.
                   ** reflexivity.
                   ** rewrite H6.
                      rewrite H0.
                      rewrite eval_const; tauto.
                ++ unfold evalExpr; fold evalExpr.
                   unfold evalUniBool.
                   rewrite Bool.negb_true_iff.
                   unfold isEq.
                   match goal with
                   | |- (if ?b then _ else _) = _ => destruct b
                   end.
                   ** unfold pmget in *.
                      rewrite H0 in e.
                      tauto.
                   ** reflexivity.
                ++ FMap.findeq.
                ++ FMap.findeq.
                ++ FMap.findeq.
      + repeat eexists.
        * eapply BFMulti.
          -- tauto.
          -- constructor.
             ++ apply AddSubstep.
                apply NilSubsteps.
                simpl.
                tauto.
             ++ instantiate (1 := substep).
                unfold wellHidden.
                simpl.
                split; FMap.findeq.
(*                
                unfold substep.
                unfold unitAnnot
                
                match goal with
                | |- wellHidden _ (hide (_ [?P])) =>
               match type of P with
               | ?TP => assert (sth: TP); pose P
               end
             end.
             ++ admit.
             ++ Set Printing All.
                simpl.
                clear - sth y.
                
                  instantiate (1 := sth).
             ++ destruct (weq dstIdx (wzero _)); econstructor.
                ** eapply SingleRule.
                   --- instantiate (2 := "execLdZ").
                       simpl.
                       tauto.
                   --- repeat (econstructor; try FMap.findeq).
                       +++ match goal with
                           | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true => assert (x = pmget pm (evalExpr (rv32iAlignPc type pc)))
                           end.
                           *** reflexivity.
                           *** rewrite H6.
                               rewrite H0.
                               rewrite eval_const; tauto.
                       +++ rewrite eval_const.
                           *** reflexivity.
                           *** unfold evalExpr; fold evalExpr.
                               unfold pmget in *.
                               rewrite H0.
                               assumption.
                       +++ FMap.findeq.
                ** eapply SingleRule.
                   --- instantiate (2 := "execLd").
                       simpl.
                       tauto.
                   --- repeat (econstructor; try FMap.findeq).
                       +++ match goal with
                           | |- evalExpr (( _ _ ?x ) == _)%kami_expr = true => assert (x = pmget pm (evalExpr (rv32iAlignPc type pc)))
                           end.
                           *** reflexivity.
                           *** rewrite H6.
                               rewrite H0.
                               rewrite eval_const; tauto.
                       +++ unfold evalExpr; fold evalExpr.
                           unfold evalUniBool.
                           rewrite Bool.negb_true_iff.
                           unfold isEq.
                           match goal with
                           | |- (if ?b then _ else _) = _ => destruct b
                           end.
                           *** unfold pmget in *.
                               rewrite H0 in e.
                               tauto.
                           *** reflexivity.
                       +++ FMap.findeq.
                       +++ FMap.findeq.
                       +++ FMap.findeq.
             ++ instantiate (1 := sth).
                ** 
                     Lemma evalExprVarRewrite: forall k e, evalExpr (Var type k e) = e.
                       Proof.
                         intros; reflexivity.
                       Qed.
                       unfold pmget in *.
                       
                       rewrite evalExprVarRewrite.

                   --- *)
  Admitted.

  Lemma SCToAbstractRelated :
    forall rf mem pm pc maxsp newRegs ls,
      BoundedForwardActiveMultistep rv32iProcInst maxsp (SCRegs rf pm pc) newRegs ls ->
      exists trace,
        hasTrace rf mem pm pc maxsp trace /\
        relatedTrace trace ls.
  Proof.
    induction 1.
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
        simpl in *.
        unfold addLabelLeft in *.
        unfold getSLabel in *.
        simpl in *.
  Admitted.

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
    | [ H : BoundedForwardActiveMultistep _ _ _ _ _ |- _ ] => let H' := fresh in assert (H' := H); eapply SCToAbstractRelated in H'
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
    | [ H : BoundedForwardActiveMultistep _ _ _ ?regs ?ls |- _ ] => exists ls, regs
    end.
    repeat split;
      match goal with
      | [ |- BoundedForwardActiveMultistep _ _ _ _ _ ] => assumption
      | [ Htrace1 : hasTrace _ _ _ _ _ _, Htrace2 : hasTrace _ _ _ _ _ _ |- censorLabelSeq _ _ = censorLabelSeq _ _ ] => eapply (relatedCensor _ _ _ _ _ _ _ _ _ _ _ Htrace1 Htrace2); eassumption
      | [ |- extractFhLabelSeq _ _ = _ ] => erewrite <- relatedFhTrace; eassumption
      end.
  Qed.

End SCTiming.
