Require Import List String.
Require Import Lib.CommonTactics Lib.Struct Lib.FMap.
Require Import Syntax Semantics SemFacts Wf.

Set Implicit Arguments.

Definition emptyLabel: LabelT :=
  {| annot := None; defs := M.empty _; calls := M.empty _ |}.

Fixpoint composeLabels (ls1 ls2: LabelSeqT) :=
  match ls1, ls2 with
    | l1 :: ls1', l2 :: ls2' =>
      (hide (mergeLabel l1 l2)) :: (composeLabels ls1' ls2')
    | _, _ => nil
  end.

Section TwoModules.
  Variables (ma mb: Modules).
  Hypothesis (Hinit: DisjList (namesOf (getRegInits ma)) (namesOf (getRegInits mb))).
  Hypothesis (Hvr: ValidRegsModules type (ConcatMod ma mb)).

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

  Definition BothNotRule (ul1 ul2: UnitLabel) :=
    (exists x, ul1 = Meth x \/ ul2 = Meth x).

  Lemma substep_split:
    forall o u ul cs,
      Substep (ConcatMod ma mb) o u ul cs ->
      exists ua ub ula ulb csa csb,
        Substep ma (regsA o) ua ula csa /\
        Substep mb (regsB o) ub ulb csb /\
        u = M.union ua ub /\
        ul = mergeUnitLabel ula ulb /\ BothNotRule ula ulb /\
        cs = M.union csa csb.
  Proof.
    induction 1; simpl; intros.

    - exists (M.empty _), (M.empty _).
      exists (Rle None), (Meth None), (M.empty _), (M.empty _).
      repeat split; auto; try constructor.
      eexists; intuition.

    - exists (M.empty _), (M.empty _).
      exists (Meth None), (Meth None), (M.empty _), (M.empty _).
      repeat split; auto; try constructor.
      eexists; intuition.

    - simpl in HInRules; apply in_app_or in HInRules.
      destruct HInRules.
      + exists u, (M.empty _).
        exists (Rle (Some k)), (Meth None), cs, (M.empty _).
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_weakening; auto.
        eapply validRegsRules_rule; eauto.
        inv Hvr.
        apply validRegsRules_rules_weakening
        with (rules1:= getRules (ConcatMod ma mb)).
        * eapply validRegsRules_regs_weakening; eauto.
          unfold namesOf; simpl; rewrite map_app.
          eapply SubList_app_1, SubList_refl.
        * simpl; eapply SubList_app_1, SubList_refl.
      + exists (M.empty _), u.
        exists (Meth None), (Rle (Some k)), (M.empty _), cs.
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_weakening; auto.
        eapply validRegsRules_rule; eauto.
        inv Hvr.
        apply validRegsRules_rules_weakening
        with (rules1:= getRules (ConcatMod ma mb)).
        * eapply validRegsRules_regs_weakening; eauto.
          unfold namesOf; simpl; rewrite map_app.
          eapply SubList_app_2, SubList_refl.
        * simpl; eapply SubList_app_2, SubList_refl.

    - simpl in HIn; apply in_app_or in HIn.
      destruct HIn.
      + exists u, (M.empty _).
        eexists (Meth (Some _)), (Meth None), cs, (M.empty _).
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_weakening; auto.
        eapply validRegsDms_dm; eauto.
        inv Hvr.
        apply validRegsDms_dms_weakening
        with (dms1:= getDefsBodies (ConcatMod ma mb)).
        * eapply validRegsDms_regs_weakening; eauto.
          unfold namesOf; simpl; rewrite map_app.
          eapply SubList_app_1, SubList_refl.
        * simpl; eapply SubList_app_1, SubList_refl.
      + exists (M.empty _), u.
        eexists (Meth None), (Meth (Some _)), (M.empty _), cs.
        repeat split; auto; econstructor; eauto.
        apply validRegsAction_weakening; auto.
        eapply validRegsDms_dm; eauto.
        inv Hvr.
        apply validRegsDms_dms_weakening
        with (dms1:= getDefsBodies (ConcatMod ma mb)).
        * eapply validRegsDms_regs_weakening; eauto.
          unfold namesOf; simpl; rewrite map_app.
          eapply SubList_app_2, SubList_refl.
        * simpl; eapply SubList_app_2, SubList_refl.
        
  Qed.

  Lemma substepsInd_split:
    forall o u l,
      SubstepsInd (ConcatMod ma mb) o u l ->
      exists ua ub la lb,
        SubstepsInd ma (regsA o) ua la /\
        SubstepsInd mb (regsB o) ub lb /\
        u = M.union ua ub /\ l = mergeLabel la lb.
  Proof.
    induction 1; simpl; intros.
    - exists (M.empty _), (M.empty _), emptyLabel, emptyLabel.
      repeat split; auto; try constructor.

    - subst.
      destruct IHSubstepsInd as [pua [pub [pla [plb ?]]]]; dest; subst.
      apply substep_split in H0.
      destruct H0 as [sua [sub [sula [sulb [scsa [scsb ?]]]]]];
        dest; subst.

      exists (M.union pua sua), (M.union pub sub).
      exists (mergeLabel (getLabel sula scsa) pla),
      (mergeLabel (getLabel sulb scsb) plb).

      repeat split.

      + eapply SubstepsCons; eauto.
        inv H1; dest.
        repeat split; auto.
        { destruct pla, plb; simpl in *; mdisj. }
        { (* destruct pla as [[[|]|] ? ?], plb as [[[|]|] ? ?]; *)
          (* destruct sula as [[|]|[|]], sulb as [[|]|[|]]; *)
          (* simpl in *; auto; findeq. *)
          admit. (* wierd because of "Rle None" *)
        }

      + eapply SubstepsCons; eauto.
        inv H1; dest.
        repeat split; auto.
        { destruct pla, plb; simpl in *; mdisj. }
        { admit. (* also wierd *) }
        
      + inv H1; auto.
      + admit.
  Qed.

  Lemma stepInd_split:
    forall o u l,
      StepInd (ConcatMod ma mb) o u l ->
      exists ua ub la lb,
        StepInd ma (regsA o) ua la /\ StepInd mb (regsB o) ub lb /\
        u = M.union ua ub /\ l = hide (mergeLabel la lb).
  Proof.
    induction 1; simpl; intros.
    pose proof (substepsInd_split HSubSteps)
      as [ua [ub [la [lb ?]]]]; dest; subst.
    exists ua, ub, (hide la), (hide lb).
    intuition auto.

    - constructor; auto.
      admit. (* maybe the most difficult part *)
    - constructor; auto.
      admit. (* maybe the most difficult part *)
    - clear.
      admit. (* also nontrivial *)
  Qed.

  Lemma step_split:
    forall o u l,
      Step (ConcatMod ma mb) o u l ->
      exists ua ub la lb,
        Step ma (regsA o) ua la /\ Step mb (regsB o) ub lb /\
        u = M.union ua ub /\ l = hide (mergeLabel la lb).
  Proof.
    intros; apply step_consistent in H.
    pose proof (stepInd_split H) as [ua [ub [la [lb ?]]]]; dest; subst.
    exists ua, ub, la, lb.
    repeat split; apply step_consistent; auto.
  Qed.

  Lemma multistep_split:
    forall s ls ir,
      Multistep (ConcatMod ma mb) ir s ls ->
      ir = initRegs (getRegInits ma ++ getRegInits mb) ->
      exists sa lsa sb lsb,
        Multistep ma (initRegs (getRegInits ma)) sa lsa /\
        Multistep mb (initRegs (getRegInits mb)) sb lsb /\
        s = M.union sa sb /\ ls = composeLabels lsa lsb.
  Proof.
    induction 1.
    - do 2 (eexists; exists nil); repeat split; try constructor.
      subst.
      unfold initRegs.
      apply makeMap_union; auto.

    - intros; subst.
      specialize (IHMultistep eq_refl).
      destruct IHMultistep as [sa [lsa [sb [lsb ?]]]]; dest; subst.

      apply step_split in HStep.
      destruct HStep as [sua [sub [sla [slb ?]]]]; dest; subst.

      exists (M.union sua sa), (sla :: lsa).
      exists (M.union sub sb), (slb :: lsb).
      repeat split.

      + constructor; auto.
        admit. (* map stuff; disj comes from ValidRegsModules *)
      + constructor; auto.
        admit. (* map stuff; disj comes from ValidRegsModules *)
      + admit. (* map stuff; disj comes from ValidRegsModules *)
  Qed.

  Lemma behavior_split:
    forall s ls,
      Behavior (ConcatMod ma mb) s ls ->
      exists sa lsa sb lsb,
        Behavior ma sa lsa /\ Behavior mb sb lsb /\
        s = M.union sa sb /\
        ls = composeLabels lsa lsb. 
  Proof.
    induction 1.
    apply multistep_split in HMultistepBeh.
    destruct HMultistepBeh as [sa [lsa [sb [lsb [? [? [? ?]]]]]]];
      subst.
    exists sa, lsa, sb, lsb.
    repeat split; auto.
    reflexivity.
  Qed.

  Lemma behavior_modular:
    forall sa sb lsa lsb,
      Behavior ma sa lsa ->
      Behavior mb sb lsb ->
      Behavior (ConcatMod ma mb) (M.union sa sb) (composeLabels lsa lsb).
  Proof.
    admit.
  Qed.

End TwoModules.

Section LabelMap.
  Variable (p: MethsT -> MethsT).
  Hypotheses (Hpunion: forall m1 m2, M.union (p m1) (p m2) =
                                     p (M.union m1 m2))
             (Hpsub: forall m1 m2, M.subtractKV signIsEq (p m1) (p m2) =
                                   p (M.subtractKV signIsEq m1 m2)).

  Lemma equivalentLabel_hide_mergeLabel:
    forall la lb,
      equivalentLabel p la lb ->
      forall lc ld,
        equivalentLabel p lc ld ->
        equivalentLabel p (hide (mergeLabel la lc)) (hide (mergeLabel lb ld)).
  Proof.
    intros.
    destruct la as [anna dsa csa], lb as [annb dsb csb].
    destruct lc as [annc dsc csc], ld as [annd dsd csd].
    unfold equivalentLabel in *; simpl in *; dest; subst.
    repeat split.
    - do 2 rewrite Hpunion.
      rewrite Hpsub.
      reflexivity.
    - do 2 rewrite Hpunion.
      rewrite Hpsub.
      reflexivity.
    - destruct anna, annb, annc, annd; auto.
  Qed.

  Lemma composeLabels_modular:
    forall lsa lsb,
      equivalentLabelSeq p lsa lsb ->
      forall lsc lsd,
        equivalentLabelSeq p lsc lsd ->
        equivalentLabelSeq p (composeLabels lsa lsc) (composeLabels lsb lsd).
  Proof.
    induction 1; simpl; intros; [constructor|].
    destruct lsc, lsd; [constructor|inv H1|inv H1|].
    inv H1; constructor; [|apply IHequivalentLabelSeq; auto].
    apply equivalentLabel_hide_mergeLabel; auto.
  Qed.

End LabelMap.

