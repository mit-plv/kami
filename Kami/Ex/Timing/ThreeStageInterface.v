Require Import List.
Require Import Notations.
Require Import Coq.Numbers.BinNums.
Require Import Lib.Word Lib.Indexer Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification Ex.Timing.Inversion.
Require Import Lib.CommonTactics.
Require Import Compile.Rtl Compile.CompileToRtlTryOpt.
Require Import Logic.FunctionalExtensionality.
Require Import Renaming.

Open Scope string_scope.

Ltac shatter := repeat match goal with
                       | [ H : exists _, _ |- _ ] => destruct H
                       | [ H : _ /\ _ |- _ ] => destruct H
                       end.

Module ThreeStageDefs (ThreeStage : ThreeStageInterface).
  Import ThreeStage.
  Module Invs := Inversions ThreeStage.
  Import Invs.
  
  Definition getRqCall (lastRq : option bool) (l : LabelT) : option bool:=
    match FMap.M.find rqMeth (calls l) with
    | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) =>
      Some (evalExpr (#argV!rv32iRq@."op")%kami_expr)
    | _ => match FMap.M.find rsMeth (calls l) with
          | Some _ => None
          | None => lastRq  (* nothing memory-relevant happened this cycle *)
          end
    end.

  Definition getRqDef (lastRq : option bool) (l : LabelT) : option bool :=
    match FMap.M.find rqMeth (defs l) with
    | Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) =>
      Some (evalExpr (#argV!rv32iRq@."op")%kami_expr)
    | _ => match FMap.M.find rsMeth (defs l) with
          | Some _ => None
          | None => lastRq
          end
    end.


  Fixpoint censorThreeStageLabelSeq (lastRq: option bool) getRqMeth censorMeth (ls : LabelSeqT) {struct ls} : LabelSeqT :=
    match ls with
    | nil => nil
    | l :: ls' => 
      (censorLabel (censorMeth lastRq) l) :: censorThreeStageLabelSeq (getRqMeth lastRq l) getRqMeth censorMeth ls'
    end.
      
  Inductive ThreeStageProcMemConsistent : LabelSeqT -> option (bool * address) -> memory -> Prop := (* unclear what this becomes if calls aren't well-balanced, or whether that matters *)
  | S3PMCnil : forall lastRq mem, ThreeStageProcMemConsistent nil lastRq mem
  | S3PMCrq : forall (lastRq :option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rqMeth (calls l) = Some (existT _
                                                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                                                             "op" :: Bool;
                                                                             "data" :: Bit 32});
                                                      ret := Bit 0 |}
                                                   (argV, retV)) /\
       let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
       let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
       let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
       last' = Some (op, addr) /\
       if op
       then mem' = (fun a => if weq a addr then argval else mem a) (* ST *)
       else mem' = mem (* LD *)) ->
      ThreeStageProcMemConsistent ls last' mem' ->
      ThreeStageProcMemConsistent (l :: ls) lastRq mem
  | S3PMCrs : forall (lastRq :option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rsMeth (calls l) = Some (existT _
                                                   {| arg := Bit 0;
                                                      ret := Struct (STRUCT {"data" :: Bit 32})|}
                                                   (argV, retV)) /\
       last' = None /\ 
       match lastRq with
       | Some (op, addr) =>
         if op
         then (* previous request was a ST *)
           mem' = mem (* we already did the update immediately upon getting the request *)
         else (* previous request was "LD addr" *)
           let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
           mem' = mem /\ mem addr = retval
       | _ => (* this is the non-well-balanced case, not sure what goes here *)
         mem' = mem 
       end) ->
      ThreeStageProcMemConsistent ls last' mem' ->
      ThreeStageProcMemConsistent (l :: ls) lastRq mem
  | S3PMCcons : forall (lastRq :option(bool*address)) mem l last' mem' ls, 
      (FMap.M.find rqMeth (calls l) = None
       /\ FMap.M.find rsMeth (calls l) = None
       /\ mem' = mem /\ last' = lastRq) -> 
      ThreeStageProcMemConsistent ls last' mem' ->
      ThreeStageProcMemConsistent (l :: ls) lastRq mem.
  
  Definition ThreeStageProcHiding m (lastRq : option (bool * address)) regs mem : Prop := 
    forall labels newRegs fhs,
      ForwardMultistep m regs newRegs labels ->
      ThreeStageProcMemConsistent labels lastRq mem ->
      extractFhLabelSeq fhMeth labels = fhs ->
      forall fhs',
        length fhs = length fhs' ->
        exists labels' newRegs',
          ForwardMultistep m regs newRegs' labels' /\
          ThreeStageProcMemConsistent labels' lastRq mem /\
          censorThreeStageLabelSeq (option_map fst lastRq) getRqCall censorThreeStageMeth labels = censorThreeStageLabelSeq (option_map fst lastRq) getRqCall censorThreeStageMeth labels' /\
          extractFhLabelSeq fhMeth labels' = fhs'.

  Definition ThreeStageProcLabelAirtight (l : LabelT) : Prop :=
    match FMap.M.find rqMeth (calls l) with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool; 
                                             "data" :: Bit 32});
                      ret := Bit 0 |}
                   (argV, _)) =>
      if evalExpr (#argV!rv32iRq@."op")%kami_expr
      then True (* ST *)
      else evalExpr (#argV!rv32iRq@."data")%kami_expr = $0 (* LD *)
    | _ => True
    end. (* Guarantees the _processor_ doesn't leak over the unused fields. *)
  
  Definition ThreeStageProcLabelSeqAirtight : LabelSeqT -> Prop := Forall ThreeStageProcLabelAirtight.


  Definition extractMethsWrVals (ms : MethsT) : list (word 32) :=
    match FMap.M.find rqMeth ms with
    | Some (existT _
                   {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                             "op" :: Bool;
                                             "data" :: Bit 32});
                      ret := Bit 0 |}
                   (argV, retV)) =>
      if evalExpr (#argV!rv32iRq@."op")%kami_expr
      then [evalExpr (#argV!rv32iRq@."data")%kami_expr]
      else nil
    | _ => nil
    end.

  Definition extractMethsRdVals (lastRq : option bool) (ms : MethsT) : list (word 32) :=
    match FMap.M.find rsMeth ms with
    | Some (existT _
                   {| arg := Bit 0;
                      ret := Struct (STRUCT {"data" :: Bit 32}) |}
                   (argV, retV)) =>
      match lastRq with
      | Some op => 
        if op
        then nil
        else [evalExpr (#retV!rv32iRs@."data")%kami_expr]
      | _ => nil
      end
    | _ => nil
    end.
  
  Definition extractProcWrValSeq : LabelSeqT -> list (word 32) :=
    flat_map (fun l => extractMethsWrVals (calls l)).
  
  Definition extractMemWrValSeq : LabelSeqT -> list (word 32) :=
    flat_map (fun l => extractMethsWrVals (defs l)).

  Fixpoint extractProcRdValSeq (lastRq : option bool) (ls :  LabelSeqT) : list (word 32) :=
    match ls with
    | nil => nil
    | l :: ls' => (extractMethsRdVals lastRq (calls l)) ++ extractProcRdValSeq (getRqCall lastRq l) ls' 
    end.


  Fixpoint extractMemRdValSeq (lastRq : option bool) (ls :  LabelSeqT) : list (word 32) :=
    match ls with
    | nil => nil
    | l :: ls' => (extractMethsRdVals lastRq (defs l)) ++ extractMemRdValSeq (getRqDef lastRq l) ls' 
    end.
  
  Inductive ThreeStageMemMemConsistent : LabelSeqT -> option (bool * address) -> memory -> Prop := 
  | S3MMCnil : forall lastRq mem, ThreeStageMemMemConsistent nil lastRq mem
  | S3MMCrq : forall (lastRq:option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rqMeth (defs l) = Some (existT _
                     {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                               "op" :: Bool;
                                               "data" :: Bit 32});
                        ret := Bit 0 |}
                     (argV, retV)) /\
                    let addr := evalExpr (#argV!rv32iRq@."addr")%kami_expr in
                    let argval := evalExpr (#argV!rv32iRq@."data")%kami_expr in
                    let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
                    last' = Some (op, addr) /\
                    if op
                    then mem' = (fun a => if weq a addr then argval else mem a) (* ST *)
                    else mem' = mem (* LD *)
      ) ->
      ThreeStageMemMemConsistent ls last' mem' ->
      ThreeStageMemMemConsistent (l :: ls) lastRq mem
  | S3MMCrs : forall (lastRq:option(bool*address)) mem l last' mem' ls argV retV,
      (FMap.M.find rsMeth (defs l) = Some (existT _
                                                  {| arg := Bit 0;
                                                     ret := Struct (STRUCT {"data" :: Bit 32})|}
                                                  (argV, retV)) /\
       last' = None /\ match lastRq with
                      | Some (op, addr) =>
                        if op
                        then (* previous request was a ST *)
                          mem' = mem (* we already did the update immediately upon getting the request *)
                        else (* previous request was "LD addr" *)
                          let retval := evalExpr (#retV!rv32iRs@."data")%kami_expr in
                          mem' = mem /\ mem addr = retval
                      | _ => (* this is the non-well-balanced case, not sure what goes here *)
                        mem' = mem 
                      end)      ->
      ThreeStageMemMemConsistent ls last' mem' ->
      ThreeStageMemMemConsistent (l :: ls) lastRq mem
  | S3MMCcons : forall (lastRq :option(bool*address)) mem l last' mem' ls,
      (FMap.M.find rqMeth (defs l) = None /\ FMap.M.find rsMeth (defs l) = None /\
       mem' = mem /\ last' = lastRq)
      ->
      ThreeStageMemMemConsistent ls last' mem' ->
      ThreeStageMemMemConsistent (l :: ls) lastRq mem.

  Definition ThreeStageMemHiding m lastRq : Prop :=
    forall mem labels newRegs,
      ThreeStageMemMemConsistent labels lastRq mem ->
      ForwardMultistep m (ThreeStageMemRegs mem) newRegs labels ->
      forall wrs,
        extractMemWrValSeq labels = wrs ->
        forall mem' wrs',
          length wrs = length wrs' ->
          exists labels' newRegs',
            ForwardMultistep m (ThreeStageMemRegs mem') newRegs' labels' /\
            ThreeStageMemMemConsistent labels' lastRq mem' /\
            censorThreeStageLabelSeq (option_map fst lastRq) getRqDef censorThreeStageMemDefs labels = censorThreeStageLabelSeq  (option_map fst lastRq) getRqDef censorThreeStageMemDefs labels' /\
            extractMemWrValSeq labels' = wrs'.

  Definition ThreeStageMemSpec m : Prop :=
    forall oldRegs newRegs labels,
      ForwardMultistep m oldRegs newRegs labels ->
      forall mem,
        oldRegs = ThreeStageMemRegs mem ->
        exists lastRq, 
        ThreeStageMemMemConsistent labels lastRq mem.

  Inductive ThreeStageMemLabelSeqAirtight : LabelSeqT -> option bool -> Prop :=
  | S3MLSAnil : forall lastRq, ThreeStageMemLabelSeqAirtight nil lastRq
  | S3MLSAcons : forall l ls (lastRq :option bool) last', (
      (exists argV retV, FMap.M.find rqMeth (defs l) = Some (existT _
                                                  {| arg := Struct (STRUCT {"addr" :: Bit 16;
                                                                            "op" :: Bool;
                                                                            "data" :: Bit 32});
                                                     ret := Bit 0 |}
                                                  (argV, retV))
                    /\ let op := evalExpr (#argV!rv32iRq@."op")%kami_expr in
                      last' = Some op
      ) \/ (
        exists argV retV, FMap.M.find rsMeth (defs l) = Some (existT _
                                                                {| arg := Bit 0;
                                                                   ret := Struct (STRUCT {"data" :: Bit 32})|}
                                                                (argV, retV))
                     /\ last' = None /\
                     match lastRq with
                     | Some op =>
                       if op then evalExpr (#retV!rv32iRs@."data")%kami_expr = $0 else True
                     | _ => evalExpr (#retV!rv32iRs@."data")%kami_expr = $0  (* being cautious *)
                     end
      ) \/ (
        FMap.M.find rqMeth (defs l) = None /\ FMap.M.find rsMeth (defs l) = None /\ last' = lastRq
      )) -> 
      ThreeStageMemLabelSeqAirtight ls last' ->
      ThreeStageMemLabelSeqAirtight (l :: ls) lastRq.
  
End ThreeStageDefs.

Module Type ThreeStageModularHiding (ThreeStage : ThreeStageInterface).
  Module Defs := ThreeStageDefs ThreeStage.
  Module Invs := Inversions ThreeStage.
  Import ThreeStage Defs Invs.

  Axiom abstractToProcHiding :
    forall rf pm pc mem,
      abstractHiding rf pm pc mem ->
      ThreeStageProcHiding p None (ThreeStageProcRegs rf pm pc) mem.
  (* Not sure if it's sufficient to have None here, but we'll see. *)
  
  Axiom ProcAirtight : forall oldregs newregs labels,
      ForwardMultistep p oldregs newregs labels ->
      ThreeStageProcLabelSeqAirtight labels.
  
  Axiom MemHiding : ThreeStageMemHiding m None.

  Axiom MemSpec : ThreeStageMemSpec m.

  Axiom MemAirtight : forall oldregs newregs labels,
      ForwardMultistep m oldregs newregs labels ->
      ThreeStageMemLabelSeqAirtight labels None.

End ThreeStageModularHiding.

Module ThreeStageHiding (ThreeStage : ThreeStageInterface) (Hiding : ThreeStageModularHiding ThreeStage).
  Module Defs := ThreeStageDefs ThreeStage.
  Module Invs := Inversions ThreeStage.
  Import ThreeStage Defs Invs Hiding.

  Lemma mncfh : ~ In fhMeth (getCalls m).
    pose (callsDisj fhMeth).
    pose pcfh.
    tauto.
  Qed.

  Lemma mncth : ~ In thMeth (getCalls m).
    pose (callsDisj thMeth).
    pose pcth.
    tauto.
  Qed.

  
  Lemma mncrq : ~ In rqMeth (getCalls m).
    pose (callsDisj rqMeth).
    pose pcrq.
    tauto.
  Qed.

  Lemma mncrs : ~ In rsMeth (getCalls m).
    pose (callsDisj rsMeth).
    pose pcrs.
    tauto.
  Qed.


  Lemma pndrq : ~ In rqMeth (getDefs p).
    pose (defsDisj rqMeth).
    pose mdrq.
    tauto.
  Qed.

  
  Lemma pndrs : ~ In rsMeth (getDefs p).
    pose (defsDisj rsMeth).
    pose mdrs.
    tauto.
  Qed.


  Lemma whc_rq : forall lp lm rp up rm um,
      WellHiddenConcat p m lp lm ->
      Step p rp up lp ->
      Step m rm um lm ->
      FMap.M.find rqMeth (Semantics.calls lp) = FMap.M.find rqMeth (Semantics.defs lm).
  Proof.
    intros.
    unfold WellHiddenConcat, wellHidden in *.
    shatter.
    destruct lp as [ap dp cp]. destruct lm as [am dm cm].
    unfold mergeLabel, hide, Semantics.defs, Semantics.calls in *.
    repeat match goal with
           | [ H : FMap.M.KeysDisj _ ?x |- _ ] =>
             let Hin := fresh in
             unfold FMap.M.KeysDisj in H;
               assert (In rqMeth x) as Hin by ((apply getCalls_in_1; apply pcrq) || (apply getDefs_in_2; apply mdrq));
               specialize (H rqMeth Hin);
               clear Hin;
               pose proof (fun v => FMap.M.subtractKV_not_In_find (v := v) H)
           end.
    replace (FMap.M.find rqMeth (FMap.M.union dp dm)) with (FMap.M.find rqMeth dm) in *;
      [replace (FMap.M.find rqMeth (FMap.M.union cp cm)) with (FMap.M.find rqMeth cp) in *|].
    - match goal with
      | [ |- ?x = ?y ] => case_eq x; case_eq y; intros
      end;
        repeat match goal with
               | [ H : forall _, ?x = _ -> _, H' : ?x = _ |- _ ] => specialize (H _ H')
               end;
        congruence.
    - rewrite FMap.M.find_union.
      replace (FMap.M.find rqMeth cm) with (None (A:={x : SignatureT & SignT x})).
      + destruct (FMap.M.find rqMeth cp); reflexivity.
      + apply eq_sym.
        rewrite <- FMap.M.F.P.F.not_find_in_iff.
        assert (FMap.M.KeysDisj cm (getCalls p)); [|pose proof pcrq; auto].
        eapply RefinementFacts.DisjList_KeysSubset_KeysDisj.
        * apply FMap.DisjList_comm.
          apply callsDisj.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hsci := fresh in
            pose (step_calls_in mequiv H) as Hsci;
              simpl in Hsci
          end.
          assumption.
    - rewrite FMap.M.find_union.
      replace (FMap.M.find rqMeth dp) with (None (A:={x : SignatureT & SignT x})); auto.
      apply eq_sym.
      rewrite <- FMap.M.F.P.F.not_find_in_iff.
      assert (FMap.M.KeysDisj dp (getDefs m)); [|pose proof mdrq; auto].
      eapply RefinementFacts.DisjList_KeysSubset_KeysDisj; try apply defsDisj.
      match goal with
      | [ H : Step p _ _ _ |- _ ] =>
        let Hsdi := fresh in
        pose (step_defs_in H) as Hsdi;
          simpl in Hsdi
      end.
      assumption.
  Qed.

  Lemma whc_rs : forall lp lm rp up rm um,
      WellHiddenConcat p m lp lm ->
      Step p rp up lp ->
      Step m rm um lm ->
      FMap.M.find rsMeth (Semantics.calls lp) = FMap.M.find rsMeth (Semantics.defs lm).
  Proof.
    intros.
    unfold WellHiddenConcat, wellHidden in *.
    shatter.
    destruct lp as [ap dp cp]. destruct lm as [am dm cm].
    unfold mergeLabel, hide, Semantics.defs, Semantics.calls in *.
    repeat match goal with
           | [ H : FMap.M.KeysDisj _ ?x |- _ ] =>
             let Hin := fresh in
             unfold FMap.M.KeysDisj in H;
               assert (In rsMeth x) as Hin by ((apply getCalls_in_1; apply pcrs) || (apply getDefs_in_2; apply mdrs));
               specialize (H rsMeth Hin);
               clear Hin;
               pose proof (fun v => FMap.M.subtractKV_not_In_find (v := v) H)
           end.
    replace (FMap.M.find rsMeth (FMap.M.union dp dm)) with (FMap.M.find rsMeth dm) in *;
      [replace (FMap.M.find rsMeth (FMap.M.union cp cm)) with (FMap.M.find rsMeth cp) in *|].
    - match goal with
      | [ |- ?x = ?y ] => case_eq x; case_eq y; intros
      end;
        repeat match goal with
               | [ H : forall _, ?x = _ -> _, H' : ?x = _ |- _ ] => specialize (H _ H')
               end;
        congruence.
    - rewrite FMap.M.find_union.
      replace (FMap.M.find rsMeth cm) with (None (A:={x : SignatureT & SignT x})).
      + destruct (FMap.M.find rsMeth cp); reflexivity.
      + apply eq_sym.
        rewrite <- FMap.M.F.P.F.not_find_in_iff.
        assert (FMap.M.KeysDisj cm (getCalls p)); [|pose proof pcrs; auto].
        eapply RefinementFacts.DisjList_KeysSubset_KeysDisj.
        * apply FMap.DisjList_comm.
          apply callsDisj.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hsci := fresh in
            pose (step_calls_in mequiv H) as Hsci;
              simpl in Hsci
          end.
          assumption.
    - rewrite FMap.M.find_union.
      replace (FMap.M.find rsMeth dp) with (None (A:={x : SignatureT & SignT x})); auto.
      apply eq_sym.
      rewrite <- FMap.M.F.P.F.not_find_in_iff.
      assert (FMap.M.KeysDisj dp (getDefs m)); [|pose proof mdrs; auto].
      eapply RefinementFacts.DisjList_KeysSubset_KeysDisj; try apply defsDisj.
      match goal with
      | [ H : Step p _ _ _ |- _ ] =>
        let Hsdi := fresh in
        pose (step_defs_in H) as Hsdi;
          simpl in Hsdi
      end.
      assumption.
  Qed.

  
  
  Lemma ConcatMemoryConsistent :
    forall lastRq lsm mem,
      Defs.ThreeStageMemMemConsistent lsm lastRq mem ->
      forall om nm,
        ForwardMultistep m om nm lsm ->
        forall lsp op np,
          ForwardMultistep p op np lsp ->
          WellHiddenConcatSeq p m lsp lsm ->
          Defs.ThreeStageProcMemConsistent lsp lastRq mem.
  Proof.
    induction 1; intros;
      match goal with
      | [ H : WellHiddenConcatSeq _ _ _ _ |- _ ] => inv H
      end; try constructor; repeat match goal with
                                   | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
                                   end;
      [eapply Defs.S3PMCrq | eapply Defs.S3PMCrs | eapply Defs.S3PMCcons]; shatter;
      repeat match goal with
             |  [ |- _ /\ _ ] => split
             end;
      replace ((calls la) @[ rqMeth])%fmap with ((defs l) @[ rqMeth])%fmap
        by (symmetry; eapply whc_rq; eauto);
      replace ((calls la) @[ rsMeth])%fmap with ((defs l) @[ rsMeth])%fmap
        by (symmetry; eapply whc_rs; eauto);
      try eassumption;
      try apply a;
      eapply IHThreeStageMemMemConsistent; eauto.
  Qed.
        
      
  Lemma fhCombine : forall rm um lsm,
      ForwardMultistep m rm um lsm ->
      forall rp up lsp lspm,
        ForwardMultistep p rp up lsp ->
        CanCombineLabelSeq lsp lsm ->
        lspm = composeLabels lsp lsm ->
        extractFhLabelSeq fhMeth lspm = extractFhLabelSeq fhMeth lsp.
  Proof.
    induction 1; intros; destruct lsp; subst; intuition.
    simpl.
    match goal with
    | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
    end.
    f_equal.
    - destruct l0.
      destruct l.
      unfold extractFhLabel, extractFhMeths.
      match goal with
      | [ |- match ?x with | _ => _ end = match ?y with | _ => _ end ] => replace x with y; auto
      end.
      unfold Semantics.calls, Semantics.defs, mergeLabel.
      rewrite FMap.M.subtractKV_find.
      repeat rewrite FMap.M.find_union.
      match goal with
      | [ H : Step p _ _ _ |- _ ] => pose (step_defs_in H); pose (step_calls_in pequiv H)
      end.
      match goal with
      | [ H : Step m _ _ _ |- _ ] => pose (step_defs_in H); pose (step_calls_in mequiv H)
      end.
      pose pndfh.
      pose mndfh.
      pose mncfh.
      unfold Semantics.calls, Semantics.defs in *.
      repeat multimatch goal with
             | [ |- context[FMap.M.find fhMeth ?mths] ] =>
               replace (FMap.M.find fhMeth mths) with (None (A := {x : SignatureT & SignT x})) by (apply eq_sym; eapply FMap.M.find_KeysSubset; eassumption)
             end.
      destruct (FMap.M.find fhMeth calls); reflexivity.
    - match goal with
      | [ H : CanCombineLabelSeq (_ :: _) (_ :: _) |- _ ] => destruct H
      end.
      eapply IHForwardMultistep; eauto.
  Qed.

  Lemma concatWrLen : forall lsp lsm,
      WellHiddenConcatSeq p m lsp lsm ->
      forall rp rp' rm rm',
        ForwardMultistep p rp rp' lsp ->
        ForwardMultistep m rm rm' lsm ->
        length (Defs.extractProcWrValSeq lsp) = length (Defs.extractMemWrValSeq lsm).
  Proof.
    induction 1; auto; intros.
    simpl.
    repeat match goal with
           | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
           end.
    match goal with
    | [ IH : forall _ _ _ _, ForwardMultistep p _ _ _ -> ForwardMultistep m _ _ _ -> _, Hp : ForwardMultistep p _ _ _, Hm : ForwardMultistep m _ _ _ |- _ ] => specialize (IHWellHiddenConcatSeq _ _ _ _ Hp Hm)
    end.
    repeat rewrite app_length.
    match goal with
    | [ |- ?x + _ = ?y + _ ] => replace x with y; auto
    end.
    unfold Defs.extractMethsWrVals.
    match goal with
    | [ |- length match ?x with | _ => _ end = length match ?y with | _ => _ end ] => replace x with y; auto
    end.
    eapply whc_rq; eauto.
  Qed.

  Lemma concatRdLen : forall lsp lsm,
      WellHiddenConcatSeq p m lsp lsm ->
      forall lastRq rp rp' rm rm',
        ForwardMultistep p rp rp' lsp ->
        ForwardMultistep m rm rm' lsm ->
        length (Defs.extractProcRdValSeq lastRq lsp) = length (Defs.extractMemRdValSeq lastRq lsm).
  Proof.
    induction 1; auto; intros.
    simpl.
    repeat match goal with
           | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
           end.
    match goal with
    | [   IH : forall _ _ _ _ _, ForwardMultistep p _ _ _ -> ForwardMultistep m _ _ _ -> _,
          Hp : ForwardMultistep p _ _ _,
          Hm : ForwardMultistep m _ _ _ |- _ ] =>
      specialize (IH (Defs.getRqCall lastRq la) _ _ _ _ Hp Hm)
    end.    
    repeat rewrite app_length.
    match goal with
    | [ |- ?x + _ = ?y + _ ] => replace x with y; [apply f_equal|]
    end.
    match goal with
    | [ H : length (_ ?x lsa) = length (_ ?x lsb) |- length (_ ?x lsa) = length (_ ?y lsb) ] =>
      replace y with x; [apply H|]
    end.
    eassert _ as rq_agree by (eapply whc_rq; eassumption).
    eassert _ as rs_agree by (eapply whc_rs; eassumption).
    unfold Defs.getRqCall, Defs.getRqDef. repeat rewrite rq_agree, rs_agree.
    reflexivity.
    unfold Defs.extractMethsRdVals.
    match goal with
    | [ |- length match ?x with | _ => _ end = length match ?y with | _ => _ end ] => replace x with y; auto
    end. 
    eapply whc_rs; eauto.
  Qed.

  Ltac normalize := repeat match goal with
                           | [ H : context[@FMap.M.find (@sigT SignatureT (fun x : SignatureT => SignT x)) ?k ?mp] |- _ ] => replace (@FMap.M.find (@sigT SignatureT (fun x : SignatureT => SignT x)) k mp) with (@FMap.M.find (@sigT SignatureT SignT) k mp) in H by reflexivity
                           end.
  
  Ltac normalize_goal := repeat match goal with
                           | [ |- context[@FMap.M.find (@sigT SignatureT (fun x : SignatureT => SignT x)) ?k ?mp] ] => replace (@FMap.M.find (@sigT SignatureT (fun x : SignatureT => SignT x)) k mp) with (@FMap.M.find (@sigT SignatureT SignT) k mp) by reflexivity
                           end.
    

  Ltac inv_meth_eq :=
    match goal with
    | [ H : Some (existT _ _ (?q1, ?s1)) = Some (existT _ _ (?q2, ?s2)) |- _ ] =>
      apply inv_some in H;
      apply Semantics.sigT_eq in H;
      let Heqa := fresh in
      let Heqo := fresh in
      let Heqd := fresh in
      let Heqv := fresh in
      let Hdiscard := fresh in
      assert (evalExpr (#(q1)!rv32iRq@."addr")%kami_expr = evalExpr (#(q2)!rv32iRq@."addr")%kami_expr) as Heqa by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(q1)!rv32iRq@."op")%kami_expr = evalExpr (#(q2)!rv32iRq@."op")%kami_expr) as Heqo by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(q1)!rv32iRq@."data")%kami_expr = evalExpr (#(q2)!rv32iRq@."data")%kami_expr) as Heqd by (apply inv_pair in H; destruct H as [Hdiscard _]; rewrite Hdiscard; reflexivity);
      assert (evalExpr (#(s1)!rv32iRs@."data")%kami_expr = evalExpr (#(s2)!rv32iRs@."data")%kami_expr) as Heqv by (apply inv_pair in H; destruct H as [_ Hdiscard]; rewrite Hdiscard; reflexivity);
      simpl in Heqa;
      simpl in Heqo;
      simpl in Heqd;
      simpl in Heqv;
      subst;
      clear H
    end.

  Lemma censor_length_extract_wr : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMeth la = censorThreeStageLabel lastRq censorThreeStageMeth lb ->
      length (Defs.extractMethsWrVals (calls la)) = length (Defs.extractMethsWrVals (calls lb)).
  Proof.
    intros lastRq la lb H.
    unfold Defs.extractMethsWrVals.
    destruct (inv_censoreq_rq_calls lastRq _ _ H) as [Heq | [? [? [? [? [Ha [Hb Hopeq]]]]]]].
    - rewrite Heq; reflexivity.
    - rewrite Ha; rewrite Hb; simpl.
      destruct x0; reflexivity.
  Qed.
  
  Lemma censor_length_extract_rd : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMeth la = censorThreeStageLabel lastRq censorThreeStageMeth lb ->
      length (Defs.extractMethsRdVals lastRq (calls la)) = length (Defs.extractMethsRdVals lastRq (calls lb)).
  Proof.
    intros lastRq la lb H.
    unfold Defs.extractMethsRdVals.
    destruct (inv_censoreq_rs_calls lastRq _ _ H) as [Heq | [? [? [Ha [Hb Hopeq]]]]].
    - rewrite Heq; reflexivity.
    - rewrite Ha; rewrite Hb; simpl.
      destruct lastRq; [destruct b|]; reflexivity.
  Qed.
  
  
  Lemma censor_mem_length_extract_wr : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMemDefs la = censorThreeStageLabel lastRq censorThreeStageMemDefs lb ->
      length (Defs.extractMethsWrVals (defs la)) = length (Defs.extractMethsWrVals (defs lb)).
  Proof.
    intros lastRq la lb H.
    unfold Defs.extractMethsWrVals.
    destruct (inv_censoreq_rq_memdefs lastRq _ _ H) as [Heq | [? [? [? [? [Ha [Hb _]]]]]]].
    - rewrite Heq; reflexivity.
    - rewrite Ha; rewrite Hb; simpl.
      destruct x0; reflexivity.
  Qed.


  Lemma censor_mem_length_extract_rd : forall lastRq la lb,
      censorThreeStageLabel lastRq censorThreeStageMemDefs la = censorThreeStageLabel lastRq censorThreeStageMemDefs lb ->
      length (Defs.extractMethsRdVals lastRq (defs la)) = length (Defs.extractMethsRdVals lastRq (defs lb)).
  Proof.
    intros lastRq la lb H.
    unfold Defs.extractMethsRdVals.
    destruct (inv_censoreq_rs_memdefs lastRq _ _ H) as [Heq | [? [? [Ha [Hb _]]]]].
    - rewrite Heq; reflexivity.
    - rewrite Ha; rewrite Hb; simpl.
      destruct lastRq; [destruct b|]; reflexivity.
  Qed.

  
  Lemma rqCall_from_censor : forall lastRq a b,
      censorThreeStageLabel lastRq censorThreeStageMeth a =
      censorThreeStageLabel lastRq censorThreeStageMeth b ->
      (getRqCall lastRq a) = (getRqCall lastRq b).
  Proof.
    intros.
    destruct (inv_censoreq_rq_calls lastRq a b H) as [Rqeq | [adra [opa [arga [argb ?]]]]];
    destruct (inv_censoreq_rs_calls lastRq a b H) as [Rseq | [arga' [argb' ?]]].
    - unfold getRqCall; repeat rewrite Rqeq, Rseq; reflexivity.
    - shatter. unfold getRqCall; repeat rewrite Rqeq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqCall; repeat rewrite Rseq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqCall;
      repeat match goal with
             | [H : (_ === calls _ .[ _ ])%fmap |- _ ] => rewrite H
             end.
      reflexivity.
  Qed.

  Lemma rqDef_from_censor : forall lastRq a b,
      censorThreeStageLabel lastRq censorThreeStageMemDefs a =
      censorThreeStageLabel lastRq censorThreeStageMemDefs b ->
      (getRqDef lastRq a) = (getRqDef lastRq b).
  Proof.
    intros.
    destruct (inv_censoreq_rq_memdefs lastRq a b H) as [Rqeq | [adra [opa [arga [argb ?]]]]];
    destruct (inv_censoreq_rs_memdefs lastRq a b H) as [Rseq | [arga' [argb' ?]]].
    - unfold getRqDef; repeat rewrite Rqeq, Rseq; reflexivity.
    - shatter. unfold getRqDef; repeat rewrite Rqeq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqDef; repeat rewrite Rseq, H0, H1;
                 reflexivity.
    - shatter. unfold getRqDef;
      repeat match goal with
             | [H : (_ === defs _ .[ _ ])%fmap |- _ ] => rewrite H
             end.
      reflexivity.
  Qed.

       
  Lemma censorWrLen : forall lastRq lsp lsp',
      censorThreeStageLabelSeq lastRq getRqCall censorThreeStageMeth lsp =
      censorThreeStageLabelSeq lastRq getRqCall censorThreeStageMeth lsp' ->
      length (Defs.extractProcWrValSeq lsp) = length (Defs.extractProcWrValSeq lsp').
  Proof.
    intros lastRq lsp; generalize lastRq; clear lastRq.
    induction lsp; intros; destruct lsp'; simpl in *; try congruence.
    match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inv H
    end.
    repeat rewrite app_length.
    match goal with
    | [ |- ?x + _ = ?y + _ ] => replace x with y
    end; [
          match goal with
          | [ |- _ + ?x = _ + ?y ] => replace y with x
          end|]; try reflexivity.
    - eapply IHlsp; replace (getRqCall lastRq a) with (getRqCall lastRq l) in H2. eapply H2.
      eapply rqCall_from_censor; symmetry; eapply H1.
    -  destruct (inv_censoreq_rq_calls lastRq a l H1) as [Haeq | [adra [opa [arga [argl Hac]]]]].
       + unfold Defs.extractMethsWrVals;
           replace ((calls a) @[ rqMeth]%fmap) with ((calls l) @[ rqMeth]%fmap);
           reflexivity.
       + shatter.
         unfold Defs.extractMethsWrVals; rewrite H, H0; clear H; clear H0; simpl in *.
         destruct opa; reflexivity.
  Qed.

  Lemma combineCensor : forall lastRqp lastRqm lsp lsm lsp' lsm',
      CanCombineLabelSeq lsp lsm ->
      censorThreeStageLabelSeq lastRqp getRqCall censorThreeStageMeth lsp =
      censorThreeStageLabelSeq lastRqp getRqCall censorThreeStageMeth lsp' ->
      censorThreeStageLabelSeq lastRqm getRqDef censorThreeStageMemDefs lsm =
      censorThreeStageLabelSeq lastRqm getRqDef censorThreeStageMemDefs lsm' ->
      CanCombineLabelSeq lsp' lsm'.
  Proof.
    intros lastRqp lastRqm lsp; generalize lastRqp lastRqm; clear lastRqp lastRqm.
    induction lsp; intros;
      destruct lsm; destruct lsp'; destruct lsm';
        simpl in *; try tauto; try congruence.
    repeat match goal with
           | [ H : _ :: _ = _ :: _ |- _ ] => inv H
           end.
    intuition idtac.
    - repeat match goal with
             | [ H : context[censorThreeStageLabelSeq] |- _ ] => clear H
             | [ H : context[CanCombineLabelSeq] |- _ ] => clear H
             | [ x : list _ |- _ ] => clear x
             | [ x : LabelT |- _ ] => destruct x
             end.
      unfold CanCombineLabel, censorLabel, Semantics.annot, Semantics.calls, Semantics.defs in *.
      repeat inv_label.
      subst.
      intuition idtac;
        match goal with
        | [ Hx : _ = FMap.M.mapi _ ?x, Hy : _ = FMap.M.mapi _ ?y |- FMap.M.Disj ?x ?y ] =>
          unfold FMap.M.Disj in *;
            intros;
            erewrite <- (FMap.M.F.P.F.mapi_in_iff x);
            erewrite <- (FMap.M.F.P.F.mapi_in_iff y);
            rewrite <- Hx;
            rewrite <- Hy;
            repeat rewrite FMap.M.F.P.F.mapi_in_iff;
            auto
        end.
    - eapply IHlsp; eauto.
      + replace (getRqCall _ l0) with (getRqCall lastRqp a) in H5.
        eapply H5.
        eapply rqCall_from_censor.
        apply H2.
      + replace (getRqDef _ l1) with (getRqDef lastRqm l) in H4.
        eapply H4.
        eapply rqDef_from_censor.
        eapply H3.
  Qed.

  Lemma app_inv : forall A (lh1 lt1 lh2 lt2 : list A),
      lh1 ++ lt1 = lh2 ++ lt2 ->
      length lh1 = length lh2 ->
      lh1 = lh2 /\ lt1 = lt2.
  Proof.
    induction lh1; intros; destruct lh2; simpl in *; try congruence; auto.
    inv H.
    inv H0.
    split.
    - f_equal.
      eapply proj1; apply IHlh1; eauto.
    - eapply proj2; apply IHlh1; eauto.
  Qed.

  Lemma In_subtractKV : forall A k (m1 m2 : FMap.M.t A) dec,
      FMap.M.In k (FMap.M.subtractKV dec m1 m2) <-> (FMap.M.In k m1 /\ (~ FMap.M.In k m2 \/ FMap.M.find k m1 <> FMap.M.find k m2)).
  Proof.
    intros.
    intuition idtac;
      rewrite FMap.M.F.P.F.in_find_iff in *;
      match goal with
      | [ H : context[FMap.M.subtractKV] |- _ ] => rewrite FMap.M.subtractKV_find in H
      | [ |- context[FMap.M.subtractKV] ] => rewrite FMap.M.subtractKV_find
      end;
      destruct (FMap.M.Map.find k m1);
      destruct (FMap.M.Map.find k m2);
      try congruence;
      try tauto.
    - destruct (dec a a0); try congruence.
      right.
      congruence.
    - exfalso; apply H; congruence.
    - destruct (dec a a0); congruence.
  Qed.

  Lemma In_union : forall A k (m1 m2 : FMap.M.t A),
      FMap.M.In k (FMap.M.union m1 m2) <-> (FMap.M.In k m1 \/ FMap.M.In k m2).
  Proof.
    intros; 
      intuition idtac;
      repeat rewrite FMap.M.F.P.F.in_find_iff in *;
      match goal with
      | [ H : context[FMap.M.union] |- _ ] => rewrite FMap.M.find_union in H
      | [ |- context[FMap.M.union] ] => rewrite FMap.M.find_union
      end;
      destruct (FMap.M.find k m1);
      destruct (FMap.M.find k m2);
      try congruence;
      tauto.
  Qed.

 
  Ltac conceal x :=
    let x' := fresh in
    let H := fresh in
    remember x as x' eqn:H;
    clear H.

  Ltac subst_finds :=
    repeat match goal with
           | [ H : context[FMap.M.find rqMeth ?x] |- _ ] => conceal (FMap.M.find rqMeth x)
           end;
    subst.

  Ltac exhibit_finds :=
    repeat match goal with
           | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
             assert (FMap.M.find rqMeth (calls (censorLabel c l)) = FMap.M.find rqMeth (calls (censorLabel c l'))) by (rewrite H; reflexivity);
             assert (FMap.M.find rqMeth (defs (censorLabel c l)) = FMap.M.find rqMeth (defs (censorLabel c l'))) by (rewrite H; reflexivity);
             clear H
           end.

  Ltac meth_equal :=
    match goal with
    | [ |- Some (existT _ _ (evalExpr STRUCT {"addr" ::= #(?a); "op" ::= #(?o); "data" ::= #(?d)}%kami_expr, evalExpr STRUCT {"data" ::= #(?v)}%kami_expr)) = Some (existT _ _ (evalExpr STRUCT {"addr" ::= #(?a'); "op" ::= #(?o'); "data" ::= #(?d')}%kami_expr, evalExpr STRUCT {"data" ::= #(?v')}%kami_expr)) ] => replace a with a'; [replace o with o'; [replace d with d'; [replace v with v'; [reflexivity|]|]|]|]
    end; try reflexivity.

  Lemma rq_consistent_censor:
    forall (lp lm lp' lm' : LabelT) (lRqp lRqm : option bool),
      Defs.extractMethsWrVals (calls lp') =
      Defs.extractMethsWrVals (defs lm') ->
      censorLabel
        (censorThreeStageMemDefs lRqm) lm =
      censorLabel
        (censorThreeStageMemDefs lRqm) lm' ->
      censorLabel
        (censorThreeStageMeth lRqp) lp =
      censorLabel
        (censorThreeStageMeth lRqp) lp' ->
      (calls lp) @[ rqMeth]%fmap =
      (defs lm) @[ rqMeth]%fmap ->
      (calls lp') @[ rqMeth]%fmap =
      (defs lm') @[ rqMeth]%fmap.
  Proof.
    intros lp lm lp' lm' lRqp lRqm H' Hm Hp H.
      destruct (inv_censoreq_rq_calls _ _ _ (eq_sym Hp)) as
          [Heqp | [adrp [opp [argp [arg'p [Hpeq' [Hpeq Hargsp]]]]]]];
      destruct (inv_censoreq_rq_memdefs _ _ _ (eq_sym Hm)) as
          [Heqm | [adrm [opm [argm [arg'm [Hmeq' [Hmeq Hargsm]]]]]]].
      -  congruence.
      - rewrite Heqp, H. rewrite Hmeq', Hmeq.
        replace arg'm with argm.  reflexivity.
        destruct opm.
        + unfold Defs.extractMethsWrVals in H'.
          rewrite Heqp, H in H'. rewrite Hmeq', Hmeq in H'. simpl in H'.
          inv H'. congruence.
        + assumption.
      - rewrite Heqm, <- H. rewrite Hpeq', Hpeq.
        replace arg'p with argp. reflexivity.
        destruct opp.
        + unfold Defs.extractMethsWrVals in H'.
          rewrite Heqm, <- H in H'. rewrite Hpeq', Hpeq in H'. simpl in H'.
          inv H'. congruence.
        + assumption.
      - eassert (_ = _). etransitivity. apply (eq_sym Hmeq).
        etransitivity. apply (eq_sym H). apply Hpeq.
        inv_rq_eq.
        rewrite Hpeq', Hmeq'.
        unfold Defs.extractMethsWrVals in H'.
        rewrite Hpeq', Hmeq' in H'. simpl in H'.
        shatter; subst. destruct opp.
        + inv H'. reflexivity.
        + subst; reflexivity.
  Qed.

  
  Lemma rs_consistent_censor:
    forall (lp lm lp' lm' : LabelT) (lRqp lRqm : option bool),
      Defs.extractMethsRdVals lRqp (calls lp') =
      Defs.extractMethsRdVals lRqm (defs lm') ->
      censorLabel
        (censorThreeStageMemDefs lRqm) lm =
      censorLabel
        (censorThreeStageMemDefs lRqm) lm' ->
      censorLabel
        (censorThreeStageMeth lRqp) lp =
      censorLabel
        (censorThreeStageMeth lRqp) lp' ->
      (calls lp) @[ rsMeth]%fmap =
      (defs lm) @[ rsMeth]%fmap ->
      (calls lp') @[ rsMeth]%fmap =
      (defs lm') @[ rsMeth]%fmap.
  Proof.
    intros lp lm lp' lm' lRqp lRqm H' Hm Hp H.
      destruct (inv_censoreq_rs_calls _ _ _ (eq_sym Hp)) as
          [Heqp | [argp [arg'p [Hpeq' [Hpeq Hargsp]]]]];
      destruct (inv_censoreq_rs_memdefs _ _ _ (eq_sym Hm)) as
          [Heqm | [argm [arg'm [Hmeq' [Hmeq Hargsm]]]]].
      - congruence.
      - rewrite Heqp, H. rewrite Hmeq', Hmeq.
        replace arg'm with argm.  reflexivity.
        repeat match goal with
               | [ H : option bool |- _ ] => destruct H
               | [ H : bool |- _ ] => destruct H
               | [ H : True |- _ ] => clear H
               end; try congruence;
          unfold Defs.extractMethsRdVals in H';
          rewrite Heqp, H in H'; rewrite Hmeq', Hmeq in H';
            inv H'; try congruence.
      - rewrite Heqm, <- H. rewrite Hpeq', Hpeq.
        replace arg'p with argp. reflexivity.
        repeat match goal with
               | [ H : option bool |- _ ] => destruct H
               | [ H : bool |- _ ] => destruct H
               | [ H : True |- _ ] => clear H
               end; try congruence;
          unfold Defs.extractMethsRdVals in H';
          rewrite Heqm, <- H in H'; rewrite Hpeq', Hpeq in H';
            inv H'; try congruence.
      - eassert (_ = _). etransitivity. apply (eq_sym Hmeq).
        etransitivity. apply (eq_sym H). apply Hpeq.
        inv_rs_eq.
        rewrite Hpeq', Hmeq'.
        unfold Defs.extractMethsRdVals in H'.
        rewrite Hpeq', Hmeq' in H'. simpl in H'.
        shatter; subst.
        repeat match goal with
               | [ H : option bool |- _ ] => destruct H
               | [ H : bool |- _ ] => destruct H
               | [ H : True |- _ ] => clear H
               end; subst; try inv H'; congruence.
  Qed.

  Lemma proc_no_def_rq : forall r u l,
      Step p r u l ->
      (_=== (defs l) .[ rqMeth ])%fmap.
  Proof.
    intros.
    pose proof (step_defs_in H) as step_defs; simpl in step_defs;
      unfold M.KeysSubset in step_defs; specialize (step_defs rqMeth);
        pose proof pndrq as not_def;
        match goal with
        | [ Hn : ~ ?x, Hi : ?y -> ?x |- _ ] => 
          assert (~ y) as not_in by auto; clear Hn; clear Hi
        end;
        rewrite FMap.M.F.P.F.not_find_in_iff in not_in;
        assumption.
  Qed.

    Lemma proc_no_def_rs : forall r u l,
      Step p r u l ->
      (_=== (defs l) .[ rsMeth ])%fmap.
  Proof.
    intros.
    pose proof (step_defs_in H) as step_defs; simpl in step_defs;
      unfold M.KeysSubset in step_defs; specialize (step_defs rsMeth);
        pose proof pndrs as not_def;
        match goal with
        | [ Hn : ~ ?x, Hi : ?y -> ?x |- _ ] => 
          assert (~ y) as not_in by auto; clear Hn; clear Hi
        end;
        rewrite FMap.M.F.P.F.not_find_in_iff in not_in;
        assumption.
  Qed.

  Lemma mem_no_call_rq : forall r u l,
      Step m r u l ->
      (_=== (calls l) .[ rqMeth ])%fmap.
  Proof.
    intros.
    pose proof (step_calls_in mequiv H) as step_calls; simpl in step_calls;
      unfold M.KeysSubset in step_calls; specialize (step_calls rqMeth);
        pose proof mncrq as not_def.
        match goal with
        | [ Hn : ~ ?x, Hi : ?y -> ?x |- _ ] => 
          assert (~ y) as not_in by auto; clear Hn; clear Hi
        end;
        rewrite FMap.M.F.P.F.not_find_in_iff in not_in;
        assumption.
  Qed.

  Lemma mem_no_call_rs : forall r u l,
      Step m r u l ->
      (_=== (calls l) .[ rsMeth ])%fmap.
  Proof.
    intros.
    pose proof (step_calls_in mequiv H) as step_calls; simpl in step_calls;
      unfold M.KeysSubset in step_calls; specialize (step_calls rsMeth);
        pose proof mncrs as not_def.
        match goal with
        | [ Hn : ~ ?x, Hi : ?y -> ?x |- _ ] => 
          assert (~ y) as not_in by auto; clear Hn; clear Hi
        end;
        rewrite FMap.M.F.P.F.not_find_in_iff in not_in;
        assumption.
  Qed.
      
  Lemma concatCensor : forall lsp lsm,
      WellHiddenConcatSeq p m lsp lsm ->
      forall lastRq rp up rm um lsp' lsm' mem,
        ForwardMultistep p rp up lsp ->
        ForwardMultistep m rm um lsm ->
        let lRq := (option_map fst lastRq) in
        censorThreeStageLabelSeq lRq getRqCall censorThreeStageMeth lsp =
        censorThreeStageLabelSeq lRq getRqCall censorThreeStageMeth lsp' ->
        censorThreeStageLabelSeq lRq getRqDef censorThreeStageMemDefs lsm =
        censorThreeStageLabelSeq lRq getRqDef censorThreeStageMemDefs lsm' ->
        Defs.extractProcWrValSeq lsp' = Defs.extractMemWrValSeq lsm' ->
        Defs.extractProcRdValSeq lRq lsp' = Defs.extractMemRdValSeq lRq lsm' ->
        Defs.ThreeStageProcMemConsistent lsp' lastRq mem ->
        Defs.ThreeStageMemMemConsistent lsm' lastRq mem ->
        WellHiddenConcatSeq p m lsp' lsm'.
  Proof.
    induction 1;
      intros;
      destruct lsp';
      destruct lsm';
      simpl in *;
      try congruence;
      try solve [ constructor ].
    match goal with
    | [ H : ForwardMultistep p _ _ _ |- _ ] =>
      let t := fresh in 
      pose (ProcAirtight _ _ _ H) as t;
        conceal t; clear t
    end.
    match goal with
    | [ H : ForwardMultistep m _ _ _ |- _ ] =>
      let t := fresh in 
      pose (MemAirtight _ _ _ H) as t;
        conceal t; clear t
    end.
    repeat match goal with
           | [ H : ForwardMultistep _ _ _ (_ :: _) |- _ ] => inv H
           | [ H : _ :: _ = _ :: _ |- _ ] => inv H
           end.
    match goal with
    | [ H : WellHiddenConcat _ _ _ _ |- _ ] =>
      let H' := fresh in
      let H'' := fresh in
      remember H as H' eqn:H'';
        clear H'';
        eapply whc_rq in H';
        eauto
    end.
    match goal with
    | [ H : WellHiddenConcat _ _ _ _ |- _ ] =>
      let H' := fresh in
      let H'' := fresh in
      remember H as H' eqn:H'';
        clear H'';
        eapply whc_rs in H';
        eauto
    end. 
    repeat match goal with
           | [ H : ?x ++ ?xs = ?y ++ ?ys |- WellHiddenConcatSeq _ _ _ _ ] => apply app_inv in H
           end; shatter; [|erewrite <- censor_length_extract_wr by eassumption;
                           erewrite <- censor_mem_length_extract_wr by eassumption;
                           pose (concatWrLen [la] [lb]) as e;
                           unfold Defs.extractProcWrValSeq, Defs.extractMemWrValSeq, flat_map  in e;
                           repeat rewrite app_nil_r in e;
                           eapply e; repeat (econstructor; eauto)
                          |erewrite <- censor_length_extract_rd by eassumption;
                           erewrite <- censor_mem_length_extract_rd by eassumption;
                           eassert _ as e by (eapply (concatRdLen [la] [lb]); repeat (econstructor; eauto));
                           unfold Defs.extractProcRdValSeq, Defs.extractMemRdValSeq, flat_map in e;
                           repeat rewrite app_nil_r in e;
                           eapply e].
    
    eassert _ as rq_consistent by (eapply rq_consistent_censor; eassumption).
    eassert _ as rs_consistent by (eapply rs_consistent_censor; eassumption).
    eassert _ as proc_no_rq by (eapply proc_no_def_rq; eassumption).
    eassert _ as proc_no_rs by (eapply proc_no_def_rs; eassumption).
    eassert _ as mem_no_rq by (eapply mem_no_call_rq; eassumption).
    eassert _ as mem_no_rs by (eapply mem_no_call_rs; eassumption).
    assert ((_=== defs l .[ rqMeth])%fmap /\ (_=== defs l .[ rsMeth])%fmap /\ (_=== calls l0 .[ rqMeth])%fmap /\ (_=== calls l0 .[ rsMeth])%fmap) by
        (eassert _ as e by (eapply mRqRs; eassumption); destruct e;
         eassert _ as inv_rq_eq by (eapply inv_censoreq_rq_memdefs_as_calls; try eassumption);
         destruct inv_rq_eq;
         eassert _ as inv_rs_eq by (apply inv_censoreq_rs_memdefs_as_calls; eassumption);
         destruct inv_rs_eq;
         eassert _ as inv_rq_eq by (eapply inv_censoreq_rq_calls_as_defs; try eassumption);
         destruct inv_rq_eq;
         eassert _ as inv_rs_eq by (apply inv_censoreq_rs_calls_as_defs; eassumption);
         destruct inv_rs_eq;
         shatter;
         repeat split; congruence). 
    
    repeat match goal with
           | [ H : context[_ :: lsp'] |- _ ] => inv H
           | [ H : context[_ :: lsm'] |- _ ] => inv H
           end; shatter; constructor;
      try (eassert (_ = _) as args_same by 
                (shatter; etransitivity; [
                   match goal with
                   | [ H : (_ === calls l .[ rqMeth ])%fmap |- _ ] =>
                     apply (eq_sym H)
                   end | etransitivity; [
                           apply rq_consistent | eassumption]]);
           inv_rq_eq);
      try match goal with
          | [ |- WellHiddenConcatSeq _ _ _ _ ] =>
            eapply IHWellHiddenConcatSeq; try eassumption
          end; clear IHWellHiddenConcatSeq;
        intuition idtac;
        cbv zeta in *;
        match goal with
        | [ H : Defs.ThreeStageMemMemConsistent ?ls ?lst ?mem |-
            Defs.ThreeStageMemMemConsistent ?ls ?lst' ?mem' ] =>
          replace lst' with lst; [replace mem' with mem; [apply H|]|]
        | _ => idtac
        end;
        match goal with
        | [ H : censorThreeStageLabelSeq ?lRq ?get ?meth ?x =
                censorThreeStageLabelSeq ?lRq' ?get ?meth ?y |-
            censorThreeStageLabelSeq ?lRq0 ?get ?meth ?x =
            censorThreeStageLabelSeq ?lRq0' ?get ?meth ?y ] =>
          replace lRq0 with lRq at 1; [replace lRq0' with lRq'; [apply H|]|]
        | _ => idtac
        end;
        match goal with
        | [ H : Defs.extractProcRdValSeq ?x lsp' = Defs.extractMemRdValSeq ?y lsm' |-
            Defs.extractProcRdValSeq ?x' lsp' = Defs.extractMemRdValSeq ?y' lsm' ] =>
          replace x' with x at 1; [replace y' with y; [apply H|]|]
        | _ => idtac
        end;
        change Defs.getRqDef with getRqDef in *;
        change Defs.getRqCall with getRqCall in *;
        intuition idtac;
        match goal with
        | [ |- getRqCall _ _ = option_map fst ?lst ] =>
          try erewrite rqCall_from_censor by eassumption;
            repeat match goal with
                     [ H : (M.find _ (defs l0)) = _ |- _ ] => try rewrite <- rq_consistent in H; try rewrite <- rs_consistent in H
                   end;
            try match goal with
                | [ _ : (_ === calls l .[rsMeth])%fmap, _ : ((M.find rqMeth (calls l)) = Some _) |- _ ] => fail 1
                | [ _ : (_ === calls l .[rsMeth])%fmap, _ : ((M.find rqMeth (calls l)) = None) |- _ ] => fail 1
                | [ H : (_ === calls l .[rsMeth])%fmap |- _] =>
                  assert (_=== calls l .[ rqMeth ])%fmap 
                    by (eassert _ as e by (eapply mRqRs; eassumption); destruct e;
                        eassert _ as inv_rq_eq by (eapply inv_censoreq_rq_memdefs; try eassumption);
                        destruct inv_rq_eq;
                        eassert _ as inv_rs_eq by (apply inv_censoreq_rs_memdefs; eassumption);
                        destruct inv_rs_eq;
                        shatter;
                        try congruence;
                        try match goal with
                            |  [ Hs : ?x = Some _ , Hn : ?x = None |- _ ] => exfalso; rewrite Hn in Hs; discriminate
                            end)
                end;
            match goal with
            | [ H : (_ === calls l .[rqMeth])%fmap |- _ ] => unfold getRqCall; rewrite H; subst lst; auto
            | [ H : (_=== calls l .[rqMeth])%fmap, H' : ((M.find rsMeth (calls l)) = _)  |- _ ] => unfold getRqCall; rewrite H, H'; subst lst; auto
            end
        | _ => idtac
        end;
        match goal with
        | [ |- getRqDef _ _ = option_map fst ?lst ] =>
          try erewrite rqDef_from_censor by eassumption;
            repeat match goal with
                   | [ H : (M.find _ (calls l)) = Some _ |- _ ] => try rewrite rq_consistent in H; try rewrite rs_consistent in H
                   | [ H : (M.find _ (calls l)) = None |- _ ] => try rewrite rq_consistent in H; try  rewrite rs_consistent in H
                   end;
            try match goal with
                | [ _ : (_ === defs l0 .[rsMeth])%fmap, _ : ((M.find rqMeth (defs l0)) = Some _) |- _ ] => fail 1
                | [ _ : (_ === defs l0 .[rsMeth])%fmap, _ : ((M.find rqMeth (defs l0)) = None) |- _ ] => fail 1
                | [ H : (_ === defs l0 .[rsMeth])%fmap |- _] =>
                  assert (_=== defs l0 .[ rqMeth ])%fmap 
                    by (eassert _ as e by (eapply pRqRs; eassumption); destruct e;
                        eassert _ as inv_rq_eq by (eapply inv_censoreq_rq_memdefs; try eassumption);
                        destruct inv_rq_eq;
                        eassert _ as inv_rs_eq by (apply inv_censoreq_rs_memdefs; eassumption);
                        destruct inv_rs_eq;
                        shatter;
                        try congruence;
                        try match goal with
                            |  [ Hs : ?x = Some _ , Hn : ?x = None |- _ ] => exfalso; rewrite Hn in Hs; discriminate
                            end)
                end;
            match goal with
            | [ H : (_ === defs l0 .[rqMeth])%fmap |- _ ] => unfold getRqDef; rewrite H; subst lst; auto; simpl
            | [ H : (_=== defs l0 .[rqMeth])%fmap, H' : ((M.find rsMeth (defs l0)) = _)  |- _ ] => unfold getRqDef; rewrite H, H'; subst lst; auto; simpl
            end
        | _ => idtac 
        end;
        try (simpl; congruence);
        match goal with
        | [ |- @eq ?T _ _ ] => try change T with memory
        | _ => idtac
        end;
        match goal with
        | [ _ : (_ === _ .[ rsMeth ])%fmap, _ : (_ === _ .[ rqMeth ])%fmap |- _ ] =>
          exfalso; repeat rewrite rq_consistent in *; repeat rewrite rs_consistent in *;
            eassert _ as e by (eapply mRqRs; eassumption); destruct e;
              eassert _ as inv_rq_eq by (eapply inv_censoreq_rq_memdefs; try eassumption);
              destruct inv_rq_eq;
              eassert _ as inv_rs_eq by (apply inv_censoreq_rs_memdefs; eassumption);
              destruct inv_rs_eq;
              shatter;
              congruence
        | _ => idtac
        end;
        match goal with 
        | [ |- @eq memory _ _ ] =>
          repeat match goal with
                 | [ H : if (evalExpr _) then _ else _ |- _ ] => simpl in H
                 end;
            repeat match goal with
                   | [ H : if ?x then _ else _, K : ?x = _ |- _ ] => rewrite K in H
                   end;
            match goal with
            | [ H : if ?x then _ else _ |- _ ] => destruct x
            end;
            subst;
            repeat match goal with
                     [ K : _ = _ |- _ ] => rewrite K
                   end
        | _ => idtac
        end;
        try (reflexivity +
             (destruct lastRq as [[b adr]|]; [destruct b|]; intuition congruence) +
             (subst; simpl; congruence)).

    
    (* 3 goals for if l/l0 contain (a) a request, (b) a response, (c) neither. *)
    
    - (* Rq *)
      assert ((_=== defs lb .[ rsMeth])%fmap /\ (_=== defs l0 .[ rsMeth])%fmap)
        by (
            eassert _ as e by (eapply mRqRs; eassumption); destruct e;
            eassert _ as inv_rs_eq by (eapply inv_censoreq_rs_memdefs; try eassumption);
            destruct inv_rs_eq;
            eassert _ as inv_rq_eq by (eapply inv_censoreq_rq_memdefs; try eassumption);
            destruct inv_rq_eq; shatter; split; try (exfalso; congruence); congruence).      
      unfold WellHiddenConcat, wellHidden in *.
      simpl in *. intuition subst; eapply RefinementFacts.DomainSubset_KeysDisj; eauto.
      (* 2 goals, for defs/calls and calls/defs *) 
      + unfold FMap.M.DomainSubset.
        intros.
        destruct la as [annota defsa callsa]. destruct lb as [annotb defsb callsb]. destruct l as [annot defs calls]. destruct l0 as [annot0 defs0 calls0].
        unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
        repeat match goal with
        | [ H : censorLabel _ {| annot := ?a; defs := _; calls := _ |} = censorLabel _ _ |- _ ] =>
          match goal with
          | [ H' : {| annot := a; defs := _; calls := _ |} = _ |- _ ] => fail 1
          | _ => idtac
          end;
            let H' := fresh in (pose proof H as H'; simpl in H')
        end.
        repeat inv_label.
        rewrite In_subtractKV in *; shatter; split.
        * match goal with
           | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
           end;
             match goal with
             | [ Hin : FMap.M.In k ?d |- _ ] => 
               erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                 match goal with
               | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite <- Heq in Hin
                 end;
                 rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                 tauto
             end. 
        * intuition idtac.
           -- left; intros;
                match goal with
                | [ H : _ -> False |- _ ] => apply H
                end.
              match goal with
              | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
              end;
                match goal with
                | [ Hin : FMap.M.In k ?c  |- _ ] =>
                  erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                    match goal with
                    | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite -> Heq in Hin
                    end;
                    rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                    tauto
                end.
           -- right; intros;
                match goal with
                | [ H : _ -> False |- _ ] => apply H; clear H
                end.
              destruct (String.string_dec k rqMeth); [subst | destruct (String.string_dec k rsMeth); [subst |]].
              ++ repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                        end;
                   match goal with
                   | [ H : ?x = _ |- ?x = _ ] => rewrite H
                   end; repeat apply f_equal;
                     apply pair_eq; [fin_func_eq | pose proof (inv_none retV); pose proof (inv_none retV0)]; congruence.
              ++ repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                        end.
                 match goal with
                 | [ H : ?x = _ |- _ = ?x ] => rewrite H
                 end. reflexivity.
              ++ assert (k <> fhMeth /\ k <> thMeth). {
                   match goal with [ H : FMap.M.In _ (FMap.M.union _ _) |- _ ] => apply M.union_In in H end;
                     intuition subst.
                   1: apply pndfh. 2: apply pndth. 3: apply mndfh. 4: apply mndth.
                   all: eapply step_defs_in; [eassumption|]; unfold Semantics.defs;
                     erewrite <- (FMap.M.F.P.F.mapi_in_iff _);
                     match goal with
                     | [ H : M.mapi _ ?x = M.mapi _ _ |- M.Map.In _ (M.Map.mapi _ ?x) ] => rewrite H
                     end; rewrite (FMap.M.F.P.F.mapi_in_iff _); assumption.
                 }
                 shatter.
                 repeat match goal with
                        | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                          assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            clear H
                        end.
                 repeat match goal with
                        | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                          change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
                        end.
                 repeat match goal with
                        | [ H : context[censorThreeStageLabel] |- _ ] => 
                          repeat rewrite <- (inv_censor_other_calls lRq _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H by assumption
                        end.
                 unfold Semantics.calls, Semantics.defs in *.
                 repeat match goal with [ H : context[FMap.M.find _ (FMap.M.union _ _)] |- _ ] => rewrite M.find_union in H end.
                 repeat rewrite M.find_union.
                repeat match goal with
                       | [ H : _ = ?x |- context[?x] ] => rewrite <- H
                       end; reflexivity.
      + unfold FMap.M.DomainSubset.
        intros.
        destruct la as [annota defsa callsa]. destruct lb as [annotb defsb callsb]. destruct l as [annot defs calls]. destruct l0 as [annot0 defs0 calls0].
        unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
        repeat match goal with
               | [ H : censorLabel _ {| annot := ?a; defs := _; calls := _ |} = censorLabel _ _ |- _ ] =>
                 match goal with
                 | [ H' : {| annot := a; defs := _; calls := _ |} = _ |- _ ] => fail 1
                 | _ => idtac
                 end;
                   let H' := fresh in (pose proof H as H'; simpl in H')
               end.
        repeat inv_label.
        rewrite In_subtractKV in *; shatter; split.
        * match goal with
          | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
          end;
            match goal with
            | [ Hin : FMap.M.In k ?d |- _ ] => 
              erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                match goal with
                | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite <- Heq in Hin
                end;
                rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                tauto
            end. 
        * intuition idtac.
          -- left; intros;
               match goal with
               | [ H : _ -> False |- _ ] => apply H
               end.
             match goal with
             | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
             end;
               match goal with
               | [ Hin : FMap.M.In k ?c  |- _ ] =>
                 erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                   match goal with
                   | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite -> Heq in Hin
                   end;
                   rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                   tauto
               end.
          --  destruct (String.string_dec k rqMeth);
                [subst | destruct (String.string_dec k rsMeth);
                         [subst | destruct (String.string_dec k fhMeth);
                                  [subst | destruct (String.string_dec k thMeth); [subst|]]]].
              ++ right; intro; match goal with | [ H : _ -> False |- _ ] => apply H end.
                 repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                        end.
                 match goal with
                 | [ H : ?x = _ |- _ = ?x ] => rewrite H
                 end. repeat apply f_equal; apply pair_eq;
                        [fin_func_eq | pose proof (inv_none retV); pose proof (inv_none retV0)]; congruence.
              ++ right; intro; match goal with | [ H : _ -> False |- _ ] => apply H end.
                 repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                        end.
                 match goal with
                 | [ H : ?x = _ |- ?x = _ ] => rewrite H
                 end. reflexivity.
              ++ left; intro.
                 match goal with [ H : FMap.M.In _ (FMap.M.union defsa defsb) |- _ ] => rewrite In_union in H; destruct H end.
                 1: apply pndfh. 2: apply mndfh.
                 all: eapply step_defs_in; [eassumption|]; unfold Semantics.calls, Semantics.defs; assumption.
              ++ left; intro.
                 match goal with [ H : FMap.M.In _ (FMap.M.union defsa defsb) |- _ ] => rewrite In_union in H; destruct H end.
                 1: apply pndth. 2: apply mndth.
                 all: eapply step_defs_in; [eassumption|]; unfold Semantics.calls, Semantics.defs; assumption.
              ++ right; intro. match goal with [ H : _ -> False |- False ] => apply H end.
                 repeat match goal with
                        | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                          assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            clear H
                        end.
                 repeat match goal with
                        | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                          change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
                        end.
                 repeat match goal with
                        | [ H : context[censorThreeStageLabel] |- _ ] => 
                          repeat rewrite <- (inv_censor_other_calls lRq _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H by assumption
                        end.
                 unfold Semantics.calls, Semantics.defs in *.
                 repeat match goal with [ H : context[FMap.M.find _ (FMap.M.union _ _)] |- _ ] => rewrite M.find_union in H end.
                 repeat rewrite M.find_union.
                 repeat match goal with
                        | [ H : _ = ?x |- context[?x] ] => rewrite <- H
                        end; reflexivity.

    - (* Rs *)
      eassert (_ = _)
        by (etransitivity; [
              match goal with
              | [ H : (_ === calls l .[ rsMeth ])%fmap |- _ ] =>
                apply (eq_sym H)
              end | etransitivity; [
                      apply rs_consistent | eassumption]]).
      inv_rs_eq.      
      assert ((_=== defs lb .[ rqMeth])%fmap /\ (_=== defs l0 .[ rqMeth])%fmap) by (
      eassert _ as e by (eapply mRqRs; eassumption); destruct e;
        eassert _ as inv_rs_eq by (eapply inv_censoreq_rs_memdefs; try eassumption);
        destruct inv_rs_eq;
        eassert _ as inv_rq_eq by (eapply inv_censoreq_rq_memdefs; try eassumption);
        destruct inv_rq_eq; shatter; split; try (exfalso; congruence); congruence).
      unfold WellHiddenConcat, wellHidden in *.
      simpl in *. intuition subst; eapply RefinementFacts.DomainSubset_KeysDisj; eauto.
      (* 2 goals, for defs/calls and calls/defs *) 
      + unfold FMap.M.DomainSubset.
        intros.
        destruct la as [annota defsa callsa]. destruct lb as [annotb defsb callsb]. destruct l as [annot defs calls]. destruct l0 as [annot0 defs0 calls0].
        unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
        repeat match goal with
               | [ H : censorLabel _ {| annot := ?a; defs := _; calls := _ |} = censorLabel _ _ |- _ ] =>
                 match goal with
                 | [ H' : {| annot := a; defs := _; calls := _ |} = _ |- _ ] => fail 1
                 | _ => idtac
                 end;
                   let H' := fresh in (pose proof H as H'; simpl in H')
               end.
        repeat inv_label.
        rewrite In_subtractKV in *; shatter; split.
        * match goal with
          | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
          end;
            match goal with
            | [ Hin : FMap.M.In k ?d |- _ ] => 
              erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                match goal with
                | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite <- Heq in Hin
                end;
                rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                tauto
            end. 
        * intuition idtac.
          -- left; intros;
               match goal with
               | [ H : _ -> False |- _ ] => apply H
               end.
             match goal with
             | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
             end;
               match goal with
               | [ Hin : FMap.M.In k ?c  |- _ ] =>
                 erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                   match goal with
                   | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite -> Heq in Hin
                   end;
                   rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                   tauto
               end.
          -- right; intros;
               match goal with
               | [ H : _ -> False |- _ ] => apply H; clear H
               end. 
             destruct (String.string_dec k rsMeth); [subst | destruct (String.string_dec k rqMeth); [subst |]].
             ++ repeat rewrite FMap.M.find_union.
                repeat match goal with
                       | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                       end;
                  match goal with
                  | [ H : ?x = _ |- ?x = _ ] => rewrite H
                  end. repeat apply f_equal; apply pair_eq; [
                         pose proof (inv_none argV); pose proof (inv_none argV0); congruence |
                         fin_func_eq; congruence]. 
             ++ repeat rewrite FMap.M.find_union.
                repeat match goal with
                       | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                       end.
                match goal with
                | [ H : ?x = _ |- _ = ?x ] => rewrite H
                end. reflexivity.
             ++ assert (k <> fhMeth /\ k <> thMeth). {
                  match goal with [ H : FMap.M.In _ (FMap.M.union _ _) |- _ ] => apply M.union_In in H end;
                    intuition subst.
                  1: apply pndfh. 2: apply pndth. 3: apply mndfh. 4: apply mndth.
                  all: eapply step_defs_in; [eassumption|]; unfold Semantics.defs;
                    erewrite <- (FMap.M.F.P.F.mapi_in_iff _);
                    match goal with
                    | [ H : M.mapi _ ?x = M.mapi _ _ |- M.Map.In _ (M.Map.mapi _ ?x) ] => rewrite H
                    end; rewrite (FMap.M.F.P.F.mapi_in_iff _); assumption.
                }
                shatter.
                repeat match goal with
                       | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                         assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l')))
                           by (rewrite H; reflexivity);
                           assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l')))
                           by (rewrite H; reflexivity);
                           clear H
                       end.
                repeat match goal with
                       | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                         change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
                       end.
                repeat match goal with
                       | [ H : context[censorThreeStageLabel] |- _ ] => 
                         repeat rewrite <- (inv_censor_other_calls lRq _ _ _ eq_refl) in H by assumption;
                           repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H by assumption;
                           repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H by assumption;
                           repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H by assumption
                       end.
                unfold Semantics.calls, Semantics.defs in *.
                repeat match goal with [ H : context[FMap.M.find _ (FMap.M.union _ _)] |- _ ] => rewrite M.find_union in H end.
                repeat rewrite M.find_union.
                repeat match goal with
                       | [ H : _ = ?x |- context[?x] ] => rewrite <- H
                       end; reflexivity.
      + unfold FMap.M.DomainSubset.
        intros.
        destruct la as [annota defsa callsa]. destruct lb as [annotb defsb callsb]. destruct l as [annot defs calls]. destruct l0 as [annot0 defs0 calls0].
        unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
        repeat match goal with
               | [ H : censorLabel _ {| annot := ?a; defs := _; calls := _ |} = censorLabel _ _ |- _ ] =>
                 match goal with
                 | [ H' : {| annot := a; defs := _; calls := _ |} = _ |- _ ] => fail 1
                 | _ => idtac
                 end;
                   let H' := fresh in (pose proof H as H'; simpl in H')
               end.
        repeat inv_label.
        rewrite In_subtractKV in *; shatter; split.
        * match goal with
          | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
          end;
            match goal with
            | [ Hin : FMap.M.In k ?d |- _ ] => 
              erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                match goal with
                | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite <- Heq in Hin
                end;
                rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                tauto
            end. 
        * intuition idtac.
          -- left; intros;
               match goal with
               | [ H : _ -> False |- _ ] => apply H
               end.
             match goal with
             | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
             end;
               match goal with
               | [ Hin : FMap.M.In k ?c  |- _ ] =>
                 erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                   match goal with
                   | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite -> Heq in Hin
                   end;
                   rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                   tauto
               end.
          --  destruct (String.string_dec k rqMeth);
                [subst | destruct (String.string_dec k rsMeth);
                         [subst | destruct (String.string_dec k fhMeth);
                                  [subst | destruct (String.string_dec k thMeth); [subst|]]]].
              ++ right; intro; match goal with | [ H : _ -> False |- _ ] => apply H end.
                 repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                        end. assumption.
              ++ right; intro; match goal with | [ H : _ -> False |- _ ] => apply H end.
                 repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[match ?x with | _ => _ end] ] => rewrite H
                        end.
                 match goal with
                 | [ H : ?x = _ |- _ = ?x ] => rewrite H
                 end.
                 repeat apply f_equal; apply pair_eq; [pose proof (inv_none argV); pose proof (inv_none argV0) | fin_func_eq]; congruence.
              ++ left; intro. rewrite In_union in H32. destruct H32.
                 1: apply pndfh. 2: apply mndfh.
                 all: eapply step_defs_in; [eassumption|]; unfold Semantics.calls, Semantics.defs; assumption.
              ++ left; intro. rewrite In_union in H32. destruct H32.
                 1: apply pndth. 2: apply mndth.
                 all: eapply step_defs_in; [eassumption|]; unfold Semantics.calls, Semantics.defs; assumption.
              ++ right; intro. match goal with [ H : _ -> False |- False ] => apply H end.
                 repeat match goal with
                        | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                          assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            clear H
                        end.
                 repeat match goal with
                        | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                          change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
                        end.
                 repeat match goal with
                        | [ H : context[censorThreeStageLabel] |- _ ] => 
                          repeat rewrite <- (inv_censor_other_calls lRq _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H by assumption
                        end.
                 unfold Semantics.calls, Semantics.defs in *.
                 repeat match goal with [ H : context[FMap.M.find _ (FMap.M.union _ _)] |- _ ] => rewrite M.find_union in H end.
                 repeat rewrite M.find_union.
                 repeat match goal with
                       | [ H : _ = ?x |- context[?x] ] => rewrite <- H
                        end; reflexivity.

    - (* Neither *)    
      unfold WellHiddenConcat, wellHidden in *.
      simpl in *. intuition subst; eapply RefinementFacts.DomainSubset_KeysDisj; eauto.
      (* 2 goals, for defs/calls and calls/defs *) 
      + unfold FMap.M.DomainSubset.
        intros.
        destruct la as [annota defsa callsa]. destruct lb as [annotb defsb callsb]. destruct l as [annot defs calls]. destruct l0 as [annot0 defs0 calls0].
        unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
        repeat match goal with
               | [ H : censorLabel _ {| annot := ?a; defs := _; calls := _ |} = censorLabel _ _ |- _ ] =>
                 match goal with
                 | [ H' : {| annot := a; defs := _; calls := _ |} = _ |- _ ] => fail 1
                 | _ => idtac
                 end;
                   let H' := fresh in (pose proof H as H'; simpl in H')
               end.
        repeat inv_label.
        rewrite In_subtractKV in *; shatter; split.
        * match goal with
          | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
          end;
            match goal with
            | [ Hin : FMap.M.In k ?d |- _ ] => 
              erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                match goal with
                | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite <- Heq in Hin
                end;
                rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                tauto
            end. 
        * intuition idtac.
          -- left; intros;
               match goal with
               | [ H : _ -> False |- _ ] => apply H
               end.
             match goal with
             | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
             end;
               match goal with
               | [ Hin : FMap.M.In k ?c  |- _ ] =>
                 erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                   match goal with
                   | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite -> Heq in Hin
                   end;
                   rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                   tauto
               end.
          -- right; intros;
               match goal with
               | [ H : _ -> False |- _ ] => apply H; clear H
               end.
             destruct (String.string_dec k rqMeth); [subst | destruct (String.string_dec k rsMeth); [subst |]].
             ++ repeat rewrite FMap.M.find_union.
                repeat match goal with
                       | [ H : ?x = _ |- context[?x] ] => rewrite H
                       end; reflexivity.
             ++ repeat rewrite FMap.M.find_union.
                repeat match goal with
                       | [ H : ?x = _ |- context[?x] ] => rewrite H
                       end; reflexivity.
             ++ assert (k <> fhMeth /\ k <> thMeth). {
                  match goal with [ H : FMap.M.In _ (FMap.M.union _ _) |- _ ] => apply M.union_In in H end;
                    intuition subst.
                  1: apply pndfh. 2: apply pndth. 3: apply mndfh. 4: apply mndth.
                  all: eapply step_defs_in; [eassumption|]; unfold Semantics.defs;
                    erewrite <- (FMap.M.F.P.F.mapi_in_iff _);
                    match goal with
                    | [ H : M.mapi _ ?x = M.mapi _ _ |- M.Map.In _ (M.Map.mapi _ ?x) ] => rewrite H
                    end; rewrite (FMap.M.F.P.F.mapi_in_iff _); assumption.
                }
                shatter.
                repeat match goal with
                       | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                         assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l')))
                           by (rewrite H; reflexivity);
                           assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l')))
                           by (rewrite H; reflexivity);
                           clear H
                       end.
                repeat match goal with
                       | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                         change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
                       end.
                repeat match goal with
                       | [ H : context[censorThreeStageLabel] |- _ ] => 
                         repeat rewrite <- (inv_censor_other_calls lRq _ _ _ eq_refl) in H by assumption;
                           repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H by assumption;
                           repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H by assumption;
                           repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H by assumption
                       end.
                unfold Semantics.calls, Semantics.defs in *.
                repeat match goal with [ H : context[FMap.M.find _ (FMap.M.union _ _)] |- _ ] => rewrite M.find_union in H end.
                repeat rewrite M.find_union.
                repeat match goal with
                       | [ H : _ = ?x |- context[?x] ] => rewrite <- H
                       end; reflexivity.
      + unfold FMap.M.DomainSubset.
        intros.
        destruct la as [annota defsa callsa]. destruct lb as [annotb defsb callsb]. destruct l as [annot defs calls]. destruct l0 as [annot0 defs0 calls0].
        unfold hide, mergeLabel, Semantics.calls, Semantics.defs in *.
        repeat match goal with
               | [ H : censorLabel _ {| annot := ?a; defs := _; calls := _ |} = censorLabel _ _ |- _ ] =>
                 match goal with
                 | [ H' : {| annot := a; defs := _; calls := _ |} = _ |- _ ] => fail 1
                 | _ => idtac
                 end;
                   let H' := fresh in (pose proof H as H'; simpl in H')
               end.
        repeat inv_label.
        rewrite In_subtractKV in *; shatter; split.
        * match goal with
          | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
          end;
            match goal with
            | [ Hin : FMap.M.In k ?d |- _ ] => 
              erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                match goal with
                | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite <- Heq in Hin
                end;
                rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                tauto
            end. 
        * intuition idtac.
           -- left; intros;
                match goal with
                | [ H : _ -> False |- _ ] => apply H
                end.
              match goal with
              | [ H : FMap.M.In k (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H
              end;
                match goal with
                | [ Hin : FMap.M.In k ?c  |- _ ] =>
                  erewrite <- FMap.M.F.P.F.mapi_in_iff in Hin;
                    match goal with
                    | [ Heq : M.mapi _ _ = M.mapi _ _ |- _ ] => rewrite -> Heq in Hin
                    end;
                    rewrite FMap.M.F.P.F.mapi_in_iff in Hin;
                    tauto
                end.
           -- destruct (String.string_dec k rqMeth);
                [subst | destruct (String.string_dec k rsMeth);
                         [subst | destruct (String.string_dec k fhMeth);
                                  [subst | destruct (String.string_dec k thMeth); [subst|]]]].
              ++ right; intro; match goal with | [ H : _ -> False |- _ ] => apply H end.
                 repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[?x] ] => rewrite H
                        end; reflexivity.
              ++ right; intro; match goal with | [ H : _ -> False |- _ ] => apply H end.
                 repeat rewrite FMap.M.find_union.
                 repeat match goal with
                        | [ H : ?x = _ |- context[?x] ] => rewrite H
                        end; reflexivity.
              ++ left; intro.
                 match goal with [ H : FMap.M.In _ (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H end.
                 1: apply pndfh. 2: apply mndfh.
                 all: eapply step_defs_in; [eassumption|]; unfold Semantics.calls, Semantics.defs; assumption.
              ++ left; intro.
                 match goal with [ H : FMap.M.In _ (FMap.M.union _ _) |- _ ] => rewrite In_union in *; destruct H end.
                 1: apply pndth. 2: apply mndth.
                 all: eapply step_defs_in; [eassumption|]; unfold Semantics.calls, Semantics.defs; assumption.
              ++ right; intro. match goal with [ H : _ -> False |- False ] => apply H end.
                 repeat match goal with
                        | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                          assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l')))
                            by (rewrite H; reflexivity);
                            clear H
                        end.
                 repeat match goal with
                        | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                          change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
                        end.
                 repeat match goal with
                        | [ H : context[censorThreeStageLabel] |- _ ] => 
                          repeat rewrite <- (inv_censor_other_calls lRq _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H by assumption;
                            repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H by assumption
                        end.
                 unfold Semantics.calls, Semantics.defs in *.
                 repeat match goal with [ H : context[FMap.M.find _ (FMap.M.union _ _)] |- _ ] => rewrite M.find_union in H end.
                 repeat rewrite M.find_union.
                 repeat match goal with
                       | [ H : _ = ?x |- context[?x] ] => rewrite <- H
                       end; reflexivity.
  Qed.


  Lemma getRq_consistent :
    forall (lp lm : LabelT) (lastRq : option bool) (rp rm : RegsT) (up um : UpdatesT),
      Step m rm um lm -> Step p rp up lp -> WellHiddenConcat p m lp lm -> getRqCall lastRq lp = getRqDef lastRq lm.
  Proof.
    intros.
    eassert _ by (eapply whc_rq; eassumption).
    eassert _ by (eapply whc_rs; eassumption).
    unfold getRqCall, getRqDef.
    repeat match goal with
           | [ H : ?x = _ |- context[?x] ] => rewrite H
           end; reflexivity.
  Qed.

  Lemma composeCensor : forall lsp lsm,
      CanCombineLabelSeq lsp lsm ->
      forall lastRq rp up rm um lsp' lsm',
      WellHiddenConcatSeq p m lsp lsm ->
      ForwardMultistep p rp up lsp ->
      ForwardMultistep m rm um lsm ->
        censorThreeStageLabelSeq lastRq getRqCall censorThreeStageMeth lsp = censorThreeStageLabelSeq lastRq getRqCall censorThreeStageMeth lsp' ->
        censorThreeStageLabelSeq lastRq getRqDef censorThreeStageMemDefs lsm = censorThreeStageLabelSeq lastRq getRqDef censorThreeStageMemDefs lsm' ->
        WellHiddenConcatSeq p m lsp' lsm' ->
        censorLabelSeq (censorHostMeth fhMeth thMeth) (composeLabels lsp lsm) =
        censorLabelSeq (censorHostMeth fhMeth thMeth) (composeLabels lsp' lsm').
  Proof.
    intro lsp;
      induction lsp as [ | lp lsp IH];
      intros;
      destruct lsm as [ | lm lsm];
      destruct lsp' as [ | lp' lsp'];
      destruct lsm' as [ | lm' lsm'];
      try solve [ simpl in *; congruence ].
    repeat match goal with
           | [ H : context[_ :: _] |- _ ] => inv H
           end.
    unfold censorLabelSeq.
    unfold composeLabels; fold composeLabels.
    repeat match goal with
           | [ |- context[map ?f (?h :: ?t)] ] => replace (map f (h :: t)) with (f h :: map f t) by reflexivity
           end.
    repeat match goal with
           | [ |- context[map (censorLabel ?f) ?ls] ] => replace (map (censorLabel f) ls) with (censorLabelSeq f ls) by reflexivity
           end.
    f_equal; [| eapply IH; try eassumption]; clear IH.
    2: match goal with
       | [ H : censorThreeStageLabelSeq ?x ?meth _ _ = censorThreeStageLabelSeq ?y ?meth _ _
           |- censorThreeStageLabelSeq _ ?meth _ _ = censorThreeStageLabelSeq _ ?meth _ _ ] => 
         replace x with y in H; try eassumption
       end.
    3: match goal with
       | [ H : censorThreeStageLabelSeq ?x ?meth _ _ = censorThreeStageLabelSeq ?y ?meth _ _
           |- censorThreeStageLabelSeq ?z ?meth _ _ = censorThreeStageLabelSeq ?z ?meth _ _ ] =>
         replace x with z in H at 1; replace y with z in H; try eassumption
       end. 
    2, 3, 4, 5: repeat erewrite <- rqCall_from_censor by eassumption; repeat erewrite <- rqDef_from_censor by eassumption;
      let H := fresh in
      eassert _ as H by (eapply (getRq_consistent _ _ lastRq); eassumption); try reflexivity; try eassumption.      

    destruct lp as [ap dp cp].
    destruct lm as [am dm cm].
    destruct lp' as [ap' dp' cp'].
    destruct lm' as [am' dm' cm'].
    unfold mergeLabel, annot, defs, calls in *.
    unfold censorLabel, hide, annot, calls, defs.
    f_equal.
    - unfold censorLabel in *.
      repeat inv_label.
      subst.
      reflexivity.
    - FMap.M.ext k.
      repeat rewrite FMap.M.F.P.F.mapi_o by (intros ? ? ? Heq; rewrite Heq; reflexivity).
      destruct (String.string_dec k rqMeth);
        [|destruct (String.string_dec k rsMeth); 
          [|destruct (String.string_dec k fhMeth);
            [|destruct (String.string_dec k thMeth)]]];
        subst.
      + unfold WellHiddenConcat, wellHidden, mergeLabel, hide, calls, defs in H16, H11.
        shatter.
        specialize (H rqMeth).
        specialize (H3 rqMeth).
        rewrite FMap.M.F.P.F.not_find_in_iff in H.
        rewrite FMap.M.F.P.F.not_find_in_iff in H3.
        assert (In rqMeth (getCalls (p ++ m)%kami));
          [|rewrite H by assumption; rewrite H3 by assumption; reflexivity].
        apply getCalls_in_1.
        apply pcrq.
      + unfold WellHiddenConcat, wellHidden, mergeLabel, hide, calls, defs in H16, H11.
        shatter.
        specialize (H rsMeth).
        specialize (H3 rsMeth).
        rewrite FMap.M.F.P.F.not_find_in_iff in H.
        rewrite FMap.M.F.P.F.not_find_in_iff in H3.
        assert (In rsMeth (getCalls (p ++ m)%kami));
          [|rewrite H by assumption; rewrite H3 by assumption; reflexivity].
        apply getCalls_in_1.
        apply pcrs.
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find fhMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find fhMeth dm = (None (A := {x : SignatureT & SignT x})))].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dp); try reflexivity.
          assert (In fhMeth (getDefs p)) by (apply H; congruence).
          apply pndfh in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dm); try reflexivity.
          assert (In fhMeth (getDefs m)) by (apply H2; congruence).
          apply mndfh in H3.
          tauto.
        * rewrite H.
          rewrite H2.
          unfold censorLabel in *; repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find fhMeth (FMap.M.mapi f mp) = FMap.M.find fhMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H19.
          destruct (FMap.M.find fhMeth dp'); try solve [simpl in H19; congruence].
          rewrite H2 in H5.
          destruct (FMap.M.find fhMeth dm'); try solve [simpl in H5; congruence].
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find thMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find thMeth dm = (None (A := {x : SignatureT & SignT x})))].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dp); try reflexivity.
          assert (In thMeth (getDefs p)) by (apply H; congruence).
          apply pndth in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dm); try reflexivity.
          assert (In thMeth (getDefs m)) by (apply H2; congruence).
          apply mndth in H3.
          tauto.
        * rewrite H.
          rewrite H2.
          unfold censorLabel in *.
          repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find thMeth (FMap.M.mapi f mp) = FMap.M.find thMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H19.
          destruct (FMap.M.find thMeth dp'); try solve [simpl in H19; congruence].
          rewrite H2 in H5.
          destruct (FMap.M.find thMeth dm'); try solve [simpl in H5; congruence].
      + repeat match goal with
               | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                 assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l'))) by (rewrite H; reflexivity);
                   assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l'))) by (rewrite H; reflexivity);
                   clear H
               end.
        repeat match goal with
               | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                 change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
               end.
        repeat rewrite <- (inv_censor_other_calls _ _ _ _ eq_refl) in H by assumption.
        repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H2 by assumption.
        repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H3 by assumption.
        repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H5 by assumption.
        unfold calls, defs in *.
        repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        rewrite H; rewrite H2; rewrite H3; rewrite H5; reflexivity.
    - FMap.M.ext k.
      repeat rewrite FMap.M.F.P.F.mapi_o by (intros ? ? ? Heq; rewrite Heq; reflexivity).
      destruct (String.string_dec k rqMeth);
        [|destruct (String.string_dec k rsMeth);
          [|destruct (String.string_dec k fhMeth);
            [|destruct (String.string_dec k thMeth)]]];
        subst.
      + unfold WellHiddenConcat, wellHidden, mergeLabel, hide, calls, defs in H16, H11.
        shatter.
        specialize (H2 rqMeth).
        specialize (H10 rqMeth).
        rewrite FMap.M.F.P.F.not_find_in_iff in H2.
        rewrite FMap.M.F.P.F.not_find_in_iff in H10.
        assert (In rqMeth (getDefs (p ++ m)%kami));
          [|rewrite H2 by assumption; rewrite H10 by assumption; reflexivity].
        apply getDefs_in_2.
        apply mdrq.
      + unfold WellHiddenConcat, wellHidden, mergeLabel, hide, calls, defs in H16, H11.
        shatter.
        specialize (H2 rsMeth).
        specialize (H10 rsMeth).
        rewrite FMap.M.F.P.F.not_find_in_iff in H2.
        rewrite FMap.M.F.P.F.not_find_in_iff in H10.
        assert (In rsMeth (getDefs (p ++ m)%kami));
          [|rewrite H2 by assumption; rewrite H10 by assumption; reflexivity].
        apply getDefs_in_2.
        apply mdrs.
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find fhMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find fhMeth dm = (None (A := {x : SignatureT & SignT x})));
            [|assert (FMap.M.find fhMeth cm = (None (A := {x : SignatureT & SignT x})))]].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dp); try reflexivity.
          assert (In fhMeth (getDefs p)) by (apply H; congruence).
          apply pndfh in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth dm); try reflexivity.
          assert (In fhMeth (getDefs m)) by (apply H2; congruence).
          apply mndfh in H3.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_calls_in mequiv H) as Hin;
              simpl in Hin;
              specialize (Hin fhMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find fhMeth cm); try reflexivity.
          assert (In fhMeth (getCalls m)) by (apply H3; congruence).
          apply mncfh in H10.
          tauto.
        * rewrite H.
          rewrite H2.
          rewrite H3.
          unfold censorLabel in *; repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find fhMeth (FMap.M.mapi f mp) = FMap.M.find fhMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H20.
          destruct (FMap.M.find fhMeth dp'); try solve [simpl in H20; congruence].
          rewrite H2 in H10.
          destruct (FMap.M.find fhMeth dm'); try solve [simpl in H10; congruence].
          rewrite H3 in H19.
          destruct (FMap.M.find fhMeth cm'); try solve [simpl in H19; congruence].
          destruct (FMap.M.Map.find fhMeth cp); destruct (FMap.M.Map.find fhMeth cp'); simpl in *; try congruence.
          f_equal.
          pose methsDistinct.
          destruct (inv_censor_host_fh lastRq s _ eq_refl);
            destruct (inv_censor_host_fh lastRq s0 _ eq_refl);
            shatter; subst; try congruence.
          -- rewrite H23 in H17.
             inv H17.
             unfold censorThreeStageMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
          -- rewrite H22 in H17.
             inv H17.
             unfold censorThreeStageMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
      + repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        assert (FMap.M.find thMeth dp = (None (A := {x : SignatureT & SignT x})));
          [|assert (FMap.M.find thMeth dm = (None (A := {x : SignatureT & SignT x})));
            [|assert (FMap.M.find thMeth cm = (None (A := {x : SignatureT & SignT x})))]].
        * match goal with
          | [ H : Step p _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dp); try reflexivity.
          assert (In thMeth (getDefs p)) by (apply H; congruence).
          apply pndth in H2.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_defs_in H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth dm); try reflexivity.
          assert (In thMeth (getDefs m)) by (apply H2; congruence).
          apply mndth in H3.
          tauto.
        * match goal with
          | [ H : Step m _ _ _ |- _ ] =>
            let Hin := fresh in
            pose (step_calls_in mequiv H) as Hin;
              simpl in Hin;
              specialize (Hin thMeth);
              rewrite FMap.M.F.P.F.in_find_iff in Hin
          end.
          destruct (FMap.M.find thMeth cm); try reflexivity.
          assert (In thMeth (getCalls m)) by (apply H3; congruence).
          apply mncth in H10.
          tauto.
        * rewrite H.
          rewrite H2.
          rewrite H3.
          unfold censorLabel in *.
          repeat inv_label.
          repeat match goal with
                 | [ H : FMap.M.mapi ?f ?mp = FMap.M.mapi ?f ?mp' |- _ ] => assert (FMap.M.find thMeth (FMap.M.mapi f mp) = FMap.M.find thMeth (FMap.M.mapi f mp')) by (f_equal; assumption); clear H
                 end.
          repeat rewrite FMap.M.F.P.F.mapi_o in * by (intros ? ? ? Heq; rewrite Heq; reflexivity).
          normalize.
          rewrite H in H20.
          destruct (FMap.M.find thMeth dp'); try solve [simpl in H20; congruence].
          rewrite H2 in H10.
          destruct (FMap.M.find thMeth dm'); try solve [simpl in H10; congruence].
          rewrite H3 in H19.
          destruct (FMap.M.find thMeth cm'); try solve [simpl in H19; congruence].
          destruct (FMap.M.Map.find thMeth cp); destruct (FMap.M.Map.find thMeth cp'); simpl in *; try congruence.
          f_equal.
          pose methsDistinct.
          destruct (inv_censor_host_th lastRq s _ eq_refl);
            destruct (inv_censor_host_th lastRq s0 _ eq_refl);
            shatter; subst; try congruence.
          -- rewrite H23 in H17.
             inv H17.
             unfold censorThreeStageMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
          -- rewrite H22 in H17.
             inv H17.
             unfold censorThreeStageMeth, censorHostMeth.
             repeat match goal with
                    | [ |- context[String.string_dec ?x ?y] ] => destruct (String.string_dec x y); try congruence
                    end.
             reflexivity.
      + repeat match goal with
               | [ H : censorLabel ?c ?l = censorLabel ?c ?l' |- _ ] =>
                 assert (FMap.M.find k (Semantics.calls (censorLabel c l)) = FMap.M.find k (Semantics.calls (censorLabel c l')))
                   by (rewrite H; reflexivity);
                   assert (FMap.M.find k (Semantics.defs (censorLabel c l)) = FMap.M.find k (Semantics.defs (censorLabel c l')))
                   by (rewrite H; reflexivity);
                   clear H
               end.
        repeat match goal with
               | [ H : context[censorLabel (?censorMeth ?lrq) ?l] |- _ ] =>
                 change (censorLabel (censorMeth lrq) l) with (censorThreeStageLabel lrq censorMeth l) in H
               end.
        repeat rewrite <- (inv_censor_other_calls _ _ _ _ eq_refl) in H by assumption.
        repeat rewrite <- (inv_censor_other_defs _ _ _ _ eq_refl) in H2 by assumption.
        repeat rewrite <- (inv_censor_other_mem_calls _ _ _ _ eq_refl) in H3 by assumption.
        repeat rewrite <- (inv_censor_other_mem_defs _ _ _ _ eq_refl) in H5 by assumption.
        unfold calls, defs in *.
        repeat rewrite FMap.M.subtractKV_find.
        repeat rewrite FMap.M.find_union.
        rewrite H; rewrite H2; rewrite H3; rewrite H5; reflexivity.
  Qed.

  Theorem abstractToSCHiding : forall rf pm pc mem,
      abstractHiding rf pm pc mem ->
      kamiHiding fhMeth thMeth (p ++ m)%kami (FMap.M.union (SCProcRegs rf pm pc) (SCMemRegs mem)).
  Proof.
    unfold kamiHiding.
    intros.
    assert (regsA p (FMap.M.union (SCProcRegs rf pm pc) (SCMemRegs mem)) = SCProcRegs rf pm pc) as Hrp by
        (unfold regsA;
         rewrite FMap.M.restrict_union;
         rewrite FMap.M.restrict_KeysSubset; [|apply pRegs];
         erewrite FMap.M.restrict_DisjList; [FMap.findeq|apply mRegs|];
         apply FMap.DisjList_comm;
         apply reginits).
    assert (regsB m (FMap.M.union (SCProcRegs rf pm pc) (SCMemRegs mem)) = SCMemRegs mem) as Hrm by
        (unfold regsB;
         rewrite FMap.M.restrict_union;
         erewrite FMap.M.restrict_DisjList; [|apply pRegs|apply reginits];
         rewrite FMap.M.restrict_KeysSubset; [FMap.findeq|apply mRegs]).
    match goal with
    | [ H : ForwardMultistep (p ++ m)%kami _ _ _ |- _ ] =>
      apply (forward_multistep_split p m pequiv mequiv reginits defsDisj callsDisj validRegs) in H;
        try congruence;
        destruct H as [sp [lsp [sm [lsm [Hfmp [Hfmm [Hdisj [Hnr [Hcomb [Hconc Hcomp]]]]]]]]]]
    end.
    rewrite Hrp, Hrm in *.
    assert (Defs.ThreeStageProcMemConsistent lsp mem) as Hpmc by (eapply ConcatMemoryConsistent; eauto; eapply MemSpec; eauto).
    assert (extractFhLabelSeq fhMeth lsp = fhs) as Hfh by (erewrite <- fhCombine; eauto).
    match goal with
    | [ Hah : abstractHiding _ _ _ _,
              Hlen : length _ = length _ |- _ ] =>
      let Hph := fresh in
      pose (abstractToProcHiding _ _ _ _ Hah) as Hph;
        unfold Defs.SCProcHiding in Hph;
        specialize (Hph _ _ fhs Hfmp Hpmc Hfh _ Hlen);
        destruct Hph as [lsp' [sp' [Hfmp' [Hpmc' [Hpcensor Hfh']]]]]
    end.
    assert (length (Defs.extractMemWrValSeq lsm) = length (Defs.extractProcWrValSeq lsp')) as Hlen by (erewrite <- censorWrLen by eassumption; apply eq_sym; eapply concatWrLen; eassumption).
    pose (MemHiding _ _ _ (MemSpec _ _ _ Hfmm _ eq_refl) Hfmm _ eq_refl mem (Defs.extractProcWrValSeq lsp') Hlen) as Hmh.
    destruct Hmh as [lsm' [sm' [Hfmm' [Hmmc' [Hmcensor Hwrval]]]]].
    exists (composeLabels lsp' lsm'), (FMap.M.union sp' sm').
    intuition idtac.
    - apply (forward_multistep_modular p m pequiv mequiv reginits defsDisj callsDisj validRegs); auto.
      + apply pRegs.
      + apply mRegs.
      + eapply combineCensor; eauto.
      + apply wellHidden_concat_modular_seq.
        eapply concatCensor; eauto.
    - subst.
      eapply composeCensor; eauto.
      eapply concatCensor; eauto.
    - erewrite fhCombine; eauto.
      eapply combineCensor; eauto.
  Qed.

End SCHiding.
