Require Import List String.
Require Import Lib.CommonTactics Lib.Struct Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.

Set Implicit Arguments.
Set Asymmetric Patterns.

Fixpoint composeLabels (ls1 ls2: LabelSeqT) :=
  match ls1, ls2 with
    | l1 :: ls1', l2 :: ls2' =>
      (hide (mergeLabel l1 l2)) :: (composeLabels ls1' ls2')
    | _, _ => nil
  end.

Section TwoModules.
  Variables (ma mb: Modules).

  Hypotheses (HmaEquiv: ModEquiv type typeUT ma)
             (HmbEquiv: ModEquiv type typeUT mb).

  Hypotheses (Hinit: DisjList (namesOf (getRegInits ma)) (namesOf (getRegInits mb)))
             (Hdefs: DisjList (getDefs ma) (getDefs mb))
             (Hcalls1: DisjList (getCalls ma) (getIntCalls mb))
             (Hcalls2: DisjList (getIntCalls ma) (getCalls mb))
             (Hvr: ValidRegsModules type (ConcatMod ma mb)).

  Definition regsA (r: RegsT) := M.restrict r (namesOf (getRegInits ma)).
  Definition regsB (r: RegsT) := M.restrict r (namesOf (getRegInits mb)).

  Definition mergeUnitLabel (ul1 ul2: UnitLabel): UnitLabel :=
    match ul1, ul2 with
      | Rle (Some _), _ => ul1
      | _, Rle (Some _) => ul2
      | Meth (Some _), _ => ul1
      | _, Meth (Some _) => ul2
      | Rle None, _ => ul1
      | _, Rle None => ul2
      | _, _ => Meth None (* unspecified *)
    end.

  Definition OneMustMethNone (ul1 ul2: UnitLabel) :=
    ul1 = Meth None \/ ul2 = Meth None.
  #[local] Hint Unfold OneMustMethNone.

  Lemma substep_split:
    forall o u ul cs,
      Substep (ConcatMod ma mb) o u ul cs ->
      exists ua ub ula ulb csa csb,
        Substep ma (regsA o) ua ula csa /\
        Substep mb (regsB o) ub ulb csb /\
        M.Disj ua ub /\ u = M.union ua ub /\
        OneMustMethNone ula ulb /\ ul = mergeUnitLabel ula ulb /\ 
        M.Disj csa csb /\ cs = M.union csa csb.
  Proof.
    induction 1; simpl; intros.

    - exists (M.empty _), (M.empty _).
      exists (Rle None), (Meth None), (M.empty _), (M.empty _).
      repeat split; auto; constructor.

    - exists (M.empty _), (M.empty _).
      exists (Meth None), (Meth None), (M.empty _), (M.empty _).
      repeat split; auto; constructor.

    - simpl in HInRules; apply in_app_or in HInRules.
      destruct HInRules.
      + exists u, (M.empty _).
        exists (Rle (Some k)), (Meth None), cs, (M.empty _).
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_old_regs_restrict; auto.
        eapply validRegsRules_rule; eauto.
        inv Hvr; apply validRegsModules_validRegsRules; auto.
      + exists (M.empty _), u.
        exists (Meth None), (Rle (Some k)), (M.empty _), cs.
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_old_regs_restrict; auto.
        eapply validRegsRules_rule; eauto.
        inv Hvr; apply validRegsModules_validRegsRules; auto.

    - simpl in HIn; apply in_app_or in HIn.
      destruct HIn.
      + exists u, (M.empty _).
        eexists (Meth (Some _)), (Meth None), cs, (M.empty _).
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_old_regs_restrict; auto.
        eapply validRegsDms_dm; eauto.
        inv Hvr; apply validRegsModules_validRegsDms; auto.
      + exists (M.empty _), u.
        eexists (Meth None), (Meth (Some _)), (M.empty _), cs.
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_old_regs_restrict; auto.
        eapply validRegsDms_dm; eauto.
        inv Hvr; apply validRegsModules_validRegsDms; auto.
        
  Qed.

  Lemma substepsInd_split:
    forall o u l,
      SubstepsInd (ConcatMod ma mb) o u l ->
      exists ua ub la lb,
        SubstepsInd ma (regsA o) ua la /\
        SubstepsInd mb (regsB o) ub lb /\
        M.Disj ua ub /\ u = M.union ua ub /\
        CanCombineLabel la lb /\ l = mergeLabel la lb.
  Proof.
    induction 1; simpl; intros.
    - exists (M.empty _), (M.empty _), emptyMethLabel, emptyMethLabel.
      repeat split; auto; try constructor;
        simpl; intro; eapply M.F.P.F.empty_in_iff; eauto.

    - subst.
      destruct IHSubstepsInd as [pua [pub [pla [plb ?]]]]; dest; subst.
      apply substep_split in H0.
      destruct H0 as [sua [sub [sula [sulb [scsa [scsb ?]]]]]];
        dest; subst.

      exists (M.union pua sua), (M.union pub sub).
      exists (mergeLabel (getLabel sula scsa) pla),
      (mergeLabel (getLabel sulb scsb) plb).
      inv H1; inv H6; dest.

      repeat split.

      + eapply SubstepsCons; eauto.
        repeat split; auto.
        { destruct pla, plb; simpl in *; mdisj. }
        { destruct pla as [[[|]|] ? ?], plb as [[[|]|] ? ?];
          destruct sula as [[|]|[|]], sulb as [[|]|[|]];
          simpl in *; auto; findeq; try (inv H9; discriminate).
        }
        
      + eapply SubstepsCons; eauto.
        repeat split; auto.
        { destruct pla, plb; simpl in *; mdisj. }
        { destruct pla as [[[|]|] ? ?], plb as [[[|]|] ? ?];
          destruct sula as [[|]|[|]], sulb as [[|]|[|]];
          simpl in *; auto; findeq; try (inv H9; discriminate);
          try (destruct (M.find a defs); discriminate).
        }
        
      + auto.
      + auto.
      + destruct pla as [[[|]|] pdsa pcsa], plb as [[[|]|] pdsb pcsb];
          destruct sula as [[|]|[[? ?]|]], sulb as [[|]|[[? ?]|]];
          simpl in *; try (inv H9; discriminate); auto.
      + destruct pla as [[[|]|] pdsa pcsa], plb as [[[|]|] pdsb pcsb];
          destruct sula as [[|]|[[? ?]|]], sulb as [[|]|[[? ?]|]];
          simpl in *; try (inv H9; discriminate); auto.
      + destruct pla as [[[|]|] ? ?], plb as [[[|]|] ? ?];
          destruct sula as [[|]|[|]], sulb as [[|]|[|]];
          simpl in *; try (inv H9; discriminate); auto.
      + destruct pla as [[[|]|] pdsa pcsa], plb as [[[|]|] pdsb pcsb];
          destruct sula as [[|]|[[? ?]|]], sulb as [[|]|[[? ?]|]];
          simpl in *; try (inv H9; discriminate);
            try (intuition auto; fail);
            try (f_equal; auto; fail).
  Qed.

  Definition WellHiddenConcat (ma mb: Modules) (la lb: LabelT) :=
    wellHidden (ConcatMod ma mb) (hide (mergeLabel la lb)).

  Lemma stepInd_split:
    forall o u l,
      StepInd (ConcatMod ma mb) o u l ->
      exists ua ub la lb,
        StepInd ma (regsA o) ua la /\ StepInd mb (regsB o) ub lb /\
        M.Disj ua ub /\ u = M.union ua ub /\
        CanCombineLabel la lb /\ wellHidden (ConcatMod ma mb) (hide (mergeLabel la lb)) /\
        WellHiddenConcat ma mb la lb /\ l = hide (mergeLabel la lb).
  Proof.
    induction 1; simpl; intros.
    pose proof (substepsInd_split HSubSteps)
      as [ua [ub [la [lb ?]]]]; dest; subst.
    exists ua, ub, (hide la), (hide lb).
    intuition auto.

    - constructor; auto.
      inv H3; dest.
      pose proof (substepsInd_calls_in HmaEquiv H).
      pose proof (substepsInd_defs_in H).
      pose proof (substepsInd_calls_in HmbEquiv H0).
      pose proof (substepsInd_defs_in H0).
      eapply wellHidden_split
      with (ma:= ma) (mb:= mb) (la:= la) (lb:= lb); eauto.
    - constructor; auto.
      inv H3; dest.
      pose proof (substepsInd_calls_in HmaEquiv H).
      pose proof (substepsInd_defs_in H).
      pose proof (substepsInd_calls_in HmbEquiv H0).
      pose proof (substepsInd_defs_in H0).
      eapply wellHidden_split
      with (ma:= ma) (mb:= mb) (la:= la) (lb:= lb); eauto.
    - apply CanCombineLabel_hide; auto.
    - inv H3; dest.
      rewrite <-hide_mergeLabel_idempotent; auto.
    - unfold WellHiddenConcat; intros.
      inv H3; rewrite <-hide_mergeLabel_idempotent; auto.
    - inv H3; rewrite <-hide_mergeLabel_idempotent; auto.
  Qed.

  Lemma step_split:
    forall o u l,
      Step (ConcatMod ma mb) o u l ->
      exists ua ub la lb,
        Step ma (regsA o) ua la /\ Step mb (regsB o) ub lb /\
        M.Disj ua ub /\ u = M.union ua ub /\
        CanCombineLabel la lb /\ wellHidden (ConcatMod ma mb) (hide (mergeLabel la lb)) /\
        WellHiddenConcat ma mb la lb /\ l = hide (mergeLabel la lb).
  Proof.
    intros; apply step_consistent in H.
    pose proof (stepInd_split H) as [ua [ub [la [lb ?]]]]; dest; subst.
    exists ua, ub, la, lb.
    inv H4; inv H5; dest.
    repeat split; auto; apply step_consistent; auto.
  Qed.

  Inductive WellHiddenConcatSeq (ma mb: Modules): LabelSeqT -> LabelSeqT -> Prop :=
  | WHCSNil: WellHiddenConcatSeq ma mb nil nil
  | WHCSCons:
      forall la lb lsa lsb,
        WellHiddenConcatSeq ma mb lsa lsb ->
        WellHiddenConcat ma mb la lb ->
        WellHiddenConcatSeq ma mb (la :: lsa) (lb :: lsb).

  Lemma wellHiddenConcatSeq_length:
    forall ma mb lsa lsb,
      WellHiddenConcatSeq ma mb lsa lsb ->
      List.length lsa = List.length lsb.
  Proof. induction lsa; intros; inv H; simpl; auto. Qed.

  Lemma multistep_split:
    forall s ls ir,
      Multistep (ConcatMod ma mb) ir s ls ->
      ir = initRegs (getRegInits ma ++ getRegInits mb) ->
      exists sa lsa sb lsb,
        Multistep ma (initRegs (getRegInits ma)) sa lsa /\
        Multistep mb (initRegs (getRegInits mb)) sb lsb /\
        M.Disj sa sb /\ s = M.union sa sb /\ 
        CanCombineLabelSeq lsa lsb /\ WellHiddenConcatSeq ma mb lsa lsb /\
        ls = composeLabels lsa lsb.
  Proof.
    induction 1; simpl; intros; subst.
    - do 2 (eexists; exists nil); repeat split; try (econstructor; eauto; fail).
      + eapply M.DisjList_KeysSubset_Disj with (d1:= namesOf (getRegInits ma)); eauto;
          unfold initRegs; rewrite rawInitRegs_namesOf;
            apply makeMap_KeysSubset; auto.
      + subst; unfold initRegs.
        rewrite <-makeMap_union.
        * unfold rawInitRegs; rewrite map_app; auto.
        * rewrite <- !rawInitRegs_namesOf; auto.

    - intros; subst.
      specialize (IHMultistep eq_refl).
      destruct IHMultistep as [sa [lsa [sb [lsb ?]]]]; dest; subst.

      apply step_split in HStep.
      destruct HStep as [sua [sub [sla [slb ?]]]]; dest; subst.

      inv Hvr.
      pose proof (validRegsModules_multistep_newregs_subset H8 H0 eq_refl).
      pose proof (validRegsModules_multistep_newregs_subset H12 H1 eq_refl).
      pose proof (validRegsModules_step_newregs_subset H8 H3).
      pose proof (validRegsModules_step_newregs_subset H12 H6).

      inv H9; dest.
      exists (M.union sua sa), (sla :: lsa).
      exists (M.union sub sb), (slb :: lsb).
      repeat split; auto.

      + constructor; auto.
        p_equal H3.
        unfold regsA; rewrite M.restrict_union.
        rewrite M.restrict_KeysSubset; auto.
        rewrite M.restrict_DisjList with (d1:= namesOf (getRegInits mb)); auto.
        apply DisjList_comm; auto.

      + constructor; auto.
        p_equal H6.
        unfold regsB; rewrite M.restrict_union.
        rewrite M.restrict_KeysSubset with (m:= sb); auto.
        rewrite M.restrict_DisjList with (d1:= namesOf (getRegInits ma)); auto.

      + mdisj.
        * eapply M.DisjList_KeysSubset_Disj with (d1:= namesOf (getRegInits mb)); eauto.
          apply DisjList_comm; auto.
        * eapply M.DisjList_KeysSubset_Disj with (d1:= namesOf (getRegInits mb)); eauto.
          apply DisjList_comm; auto.

      + pose proof (M.DisjList_KeysSubset_Disj Hinit H13 H16).
        meq.

      + constructor; auto.
  Qed.

  Lemma behavior_split:
    forall s ls,
      Behavior (ConcatMod ma mb) s ls ->
      exists sa lsa sb lsb,
        Behavior ma sa lsa /\ Behavior mb sb lsb /\
        M.Disj sa sb /\ s = M.union sa sb /\
        CanCombineLabelSeq lsa lsb /\ WellHiddenConcatSeq ma mb lsa lsb /\
        ls = composeLabels lsa lsb.
  Proof.
    induction 1.
    apply multistep_split in HMultistepBeh.
    destruct HMultistepBeh as [sa [lsa [sb [lsb ?]]]]; dest; subst.
    exists sa, lsa, sb, lsb.
    repeat split; auto.
    reflexivity.
  Qed.

  (** Now modular theorem begins *)

  Lemma substepsInd_modular:
    forall oa ua la,
      SubstepsInd ma oa ua la ->
      forall ob ub lb,
        M.Disj oa ob -> CanCombineUL ua ub la lb ->
        SubstepsInd mb ob ub lb ->
        SubstepsInd (ConcatMod ma mb) (M.union oa ob) (M.union ua ub) (mergeLabel la lb).
  Proof.
    induction 1; simpl; intros; subst.
    - destruct lb as [annb dsb csb]; simpl in *.
      do 3 rewrite M.union_empty_L.
      apply substepsInd_modules_weakening with (mc:= mb); [|eauto].
      eapply substepsInd_oldRegs_weakening; eauto.
      apply M.Sub_union_2; auto.
    - rewrite mergeLabel_assoc.
      inv H1; dest.
      rewrite M.union_comm with (m1:= u); [|auto].
      eapply SubstepsCons.
      + eapply IHSubstepsInd; eauto.
        clear -H5.

        (* Better to extract a lemma *)
        inv H5; inv H0; dest.
        destruct (getLabel sul scs), l, lb; simpl in *.
        repeat split; simpl; auto.
        destruct annot, annot0, annot1; auto.
        
      + apply substep_modules_weakening with (mc:= ma); [|eauto].
        eapply substep_oldRegs_weakening; eauto.
        apply M.Sub_union_1.
      + inv H5; inv H8; dest.
        destruct l, lb; repeat split; simpl in *; auto.
        destruct annot, annot0, sul as [|[[? ?]|]]; auto; findeq.
      + inv H5; inv H8; dest; auto.
      + reflexivity.
  Qed.

  Definition WellHiddenModular (ma mb: Modules) (la lb: LabelT) :=
    ValidLabel ma la ->
    ValidLabel mb lb ->
    wellHidden ma (hide la) ->
    wellHidden mb (hide lb) ->
    wellHidden (ConcatMod ma mb) (hide (mergeLabel la lb)).

  Inductive WellHiddenModularSeq (ma mb: Modules): LabelSeqT -> LabelSeqT -> Prop :=
  | WHMSNil: WellHiddenModularSeq ma mb nil nil
  | WHMSCons:
      forall la lb lsa lsb,
        WellHiddenModularSeq ma mb lsa lsb ->
        WellHiddenModular ma mb la lb ->
        WellHiddenModularSeq ma mb (la :: lsa) (lb :: lsb).

  Lemma wellHidden_concat_modular:
    forall ma mb la lb, WellHiddenConcat ma mb la lb ->
                        WellHiddenModular ma mb la lb.
  Proof. unfold WellHiddenModular, WellHiddenConcat; intros; auto. Qed.

  Lemma wellHidden_concat_modular_seq:
    forall ma mb la lb, WellHiddenConcatSeq ma mb la lb ->
                        WellHiddenModularSeq ma mb la lb.
  Proof.
    induction la; intros.
    - inv H; constructor.
    - inv H; constructor; auto.
      apply wellHidden_concat_modular; auto.
  Qed.

  Lemma validLabel_wellHidden_calls_disj:
    forall la lb,
      ValidLabel ma la -> wellHidden ma (hide la) ->
      ValidLabel mb lb -> wellHidden mb (hide lb) ->
      M.Disj (calls (hide la)) (calls (hide lb)) ->
      M.Disj (calls la) (calls lb).
  Proof.
    unfold ValidLabel, wellHidden; intros; dest.
    destruct la as [anna dsa csa], lb as [annb dsb csb].
    simpl in *.
    unfold M.Disj, M.KeysDisj, M.KeysSubset in *; intros.
    specializeAll k.
    repeat rewrite M.F.P.F.in_find_iff in *.
    rewrite M.subtractKV_find in H0, H2, H3, H4, H6.
    rewrite M.subtractKV_find in H3.
    destruct (M.find k csa); [right|auto].
    destruct (M.find k csb); [|auto].
    exfalso.
    specialize (H5 (opt_discr _)).
    specialize (H7 (opt_discr _)).
    destruct (M.find k dsa).
    1: {
      specialize (H (opt_discr _)).
      specialize (Hcalls2 k); destruct Hcalls2.
      { elim H8.
        apply filter_In; split; [auto|].
        apply existsb_exists; exists k.
        split; [auto|apply StringEq.string_eq_true].
      }
      { elim H8; assumption. }
    }

    destruct (M.find k dsb).
    1: {
      specialize (H1 (opt_discr _)).
      specialize (Hcalls1 k); destruct Hcalls1.
      { elim H8; assumption. }
      { elim H8.
        apply filter_In; split; [auto|].
        apply existsb_exists; exists k.
        split; [auto|apply StringEq.string_eq_true].
      }
    }

    destruct H3; elim H3; discriminate.
  Qed.

  Lemma stepInd_modular:
    forall oa ua la,
      StepInd ma oa ua la ->
      forall ob ub lb,
        M.Disj oa ob -> CanCombineUL ua ub la lb ->
        WellHiddenModular ma mb la lb ->
        StepInd mb ob ub lb ->
        StepInd (ConcatMod ma mb) (M.union oa ob) (M.union ua ub)
                (hide (mergeLabel la lb)).
  Proof.
    intros; inv H; inv H3.

    pose proof (substepsInd_defs_in HSubSteps).
    pose proof (substepsInd_calls_in HmaEquiv HSubSteps).
    pose proof (substepsInd_defs_in HSubSteps0).
    pose proof (substepsInd_calls_in HmbEquiv HSubSteps0).

    inv H1; inv H7; dest.
    assert (M.Disj (defs l) (defs l0))
      by (eapply M.DisjList_KeysSubset_Disj with (d1:= getDefs ma); eauto).
    assert (M.Disj (calls l) (calls l0))
      by (apply validLabel_wellHidden_calls_disj; auto; try (split; assumption)).

    replace (hide (mergeLabel (hide l) (hide l0))) with (hide (mergeLabel l l0))
      by (apply hide_mergeLabel_idempotent; auto).
    constructor.
    - apply substepsInd_modular; auto.
      constructor; auto.
      repeat split; auto.
    - unfold WellHiddenModular, ValidLabel in H2.
      rewrite <-hide_mergeLabel_idempotent in H2 by auto.
      apply H2.
      + split.
        * apply M.KeysSubset_Sub with (m2:= defs l); auto.
          apply M.subtractKV_sub.
        * apply M.KeysSubset_Sub with (m2:= calls l); auto.
          apply M.subtractKV_sub.
      + split.
        * apply M.KeysSubset_Sub with (m2:= defs l0); auto.
          apply M.subtractKV_sub.
        * apply M.KeysSubset_Sub with (m2:= calls l0); auto.
          apply M.subtractKV_sub.
      + rewrite <-hide_idempotent; auto.
      + rewrite <-hide_idempotent; auto.
  Qed.

  Lemma step_modular:
    forall oa ua la,
      Step ma oa ua la ->
      forall ob ub lb,
        M.Disj oa ob -> CanCombineUL ua ub la lb ->
        WellHiddenModular ma mb la lb ->
        Step mb ob ub lb ->
        Step (ConcatMod ma mb) (M.union oa ob) (M.union ua ub) (hide (mergeLabel la lb)).
  Proof.
    intros.
    apply step_consistent in H; apply step_consistent in H3.
    apply step_consistent.
    apply stepInd_modular; auto.
  Qed.

  Lemma multistep_modular:
    forall lsa oa sa,
      Multistep ma oa sa lsa ->
      oa = initRegs (getRegInits ma) ->
      forall ob sb lsb,
        Multistep mb ob sb lsb ->
        ob = initRegs (getRegInits mb) ->
        CanCombineLabelSeq lsa lsb ->
        WellHiddenModularSeq ma mb lsa lsb ->
        Multistep (ConcatMod ma mb) (initRegs (getRegInits (ConcatMod ma mb))) 
                  (M.union sa sb) (composeLabels lsa lsb).
  Proof.
    induction lsa; simpl; intros; subst.

    - destruct lsb; [|intuition idtac].
      inv H; inv H1; constructor.
      unfold initRegs.
      rewrite <-makeMap_union; auto.
      + unfold rawInitRegs; rewrite map_app; auto.
      + rewrite <- !rawInitRegs_namesOf; auto.

    - destruct lsb as [|]; [intuition idtac|].
      destruct H3; inv H4.
      inv H; inv H1.
      pose proof Hvr as Hvr'.
      inv Hvr'.
      
      pose proof (validRegsModules_multistep_newregs_subset H HMultistep eq_refl).
      pose proof (validRegsModules_multistep_newregs_subset H1 HMultistep0 eq_refl).
      pose proof (validRegsModules_step_newregs_subset H HStep).
      pose proof (validRegsModules_step_newregs_subset H1 HStep0).

      replace (M.union (M.union u n) (M.union u0 n0))
      with (M.union (M.union u u0) (M.union n n0))
        by (pose proof (M.DisjList_KeysSubset_Disj Hinit H3 H6); meq).

      inv H0; dest.
      constructor; eauto.
      apply step_modular; auto.
      + eapply M.DisjList_KeysSubset_Disj with (d1:= namesOf (getRegInits ma)); eauto.
      + repeat split; auto.
        eapply M.DisjList_KeysSubset_Disj with (d1:= namesOf (getRegInits ma)); eauto.
  Qed.

  Lemma behavior_modular:
    forall sa sb lsa lsb,
      Behavior ma sa lsa ->
      Behavior mb sb lsb ->
      CanCombineLabelSeq lsa lsb ->
      WellHiddenModularSeq ma mb lsa lsb ->
      Behavior (ConcatMod ma mb) (M.union sa sb) (composeLabels lsa lsb).
  Proof.
    intros; inv H; inv H0; constructor.
    eapply multistep_modular; eauto.
  Qed.

End TwoModules.
