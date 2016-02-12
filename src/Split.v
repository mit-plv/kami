Require Import List String.
Require Import Lib.CommonTactics Lib.Struct Lib.FMap.
Require Import Syntax Semantics SemFacts.

Set Implicit Arguments.

Definition emptyLabel: LabelT :=
  {| annot := None; defs := M.empty _; calls := M.empty _ |}.

Fixpoint composeLabels (ls1 ls2: LabelSeqT) :=
  match ls1, ls2 with
    | l1 :: ls1', l2 :: ls2' =>
      (hide (mergeLabel l1 l2)) :: (composeLabels ls1' ls2')
    | _, _ => nil
  end.

Lemma substep_regs_new:
  forall m o u ul cs,
    Substep m o u ul cs -> M.KeysSubset u (namesOf (getRegInits m)).
Proof.
  induction 1; auto.
  - apply M.KeysSubset_empty.
  - apply M.KeysSubset_empty.
  - admit. (* easy but tedious *)
  - admit. (* easy but tedious *)
Qed.

Lemma substepsInd_regs_new:
  forall m o u l,
    SubstepsInd m o u l -> M.KeysSubset u (namesOf (getRegInits m)).
Proof.
  admit.
Qed.

Lemma step_regs_new:
  forall m o u l,
    Step m o u l -> M.KeysSubset u (namesOf (getRegInits m)).
Proof.
  intros; apply step_consistent in H.
  induction H.
  eapply substepsInd_regs_new; eauto.
Qed.

Lemma multistep_regs:
  forall m s ls ir,
    Multistep m ir s ls ->
    ir = initRegs (getRegInits m) ->
    M.KeysSubset s (namesOf (getRegInits m)).
Proof.
  induction 1; simpl; intros; subst.
  - admit. (* easy *)
  - apply M.KeysSubset_union; auto.
    eapply step_regs_new; eauto.
Qed.

Section TwoModules.
  Variables (ma mb: Modules).
  Hypothesis (Hinit: DisjList (namesOf (getRegInits ma)) (namesOf (getRegInits mb))).

  Definition mergeUnitLabel (ul1 ul2: UnitLabel): UnitLabel :=
    match ul1, ul2 with
      | _, Rle _ => ul2
      | _, _ => ul1
    end.

  Lemma substep_split:
    forall o u ul cs,
      Substep (ConcatMod ma mb) o u ul cs ->
      exists oa ob ua ub ula ulb csa csb,
        Substep ma oa ua ula csa /\ Substep mb ob ub ulb csb /\
        o = M.union oa ob /\ u = M.union ua ub /\
        ul = mergeUnitLabel ula ulb /\ cs = M.union csa csb.
  Proof.
    induction 1; simpl; intros.

    - 
  Qed.

  Lemma substepsInd_split:
    forall o u l,
      SubstepsInd (ConcatMod ma mb) o u l ->
      exists oa ob ua ub la lb,
        SubstepsInd ma oa ua la /\ SubstepsInd mb ob ub lb /\
        o = M.union oa ob /\ u = M.union ua ub /\ l = mergeLabel la lb.
  Proof.
    induction 1; simpl; intros.
    - exists o, (M.empty _), (M.empty _), (M.empty _), emptyLabel, emptyLabel.
      repeat split; auto; constructor.

    - subst.
      destruct IHSubstepsInd as [poa [pob [pua [pub [pla [plb ?]]]]]]; dest; subst.
      apply substep_split in H0.
      destruct H0 as [soa [sob [sua [sub [sula [sulb [scsa [scsb ?]]]]]]]]; dest; subst.

      exists poa, pob, (M.union pua sua), (M.union pub sub).
      exists (mergeLabel (getLabel sula scsa) pla), (mergeLabel (getLabel sulb scsb) plb).

      repeat split.

      + eapply SubstepsCons; eauto.
        * assert (poa = soa) by admit; subst. (* map stuff *)
          auto.
        * inv H1; dest.
          repeat split; auto.
          { mdisj. admit. }
          { admit. }

      + eapply SubstepsCons; eauto.
        * assert (pob = sob) by admit; subst. (* map stuff *)
          auto.
        * inv H1; dest.
          repeat split; auto.
          { mdisj. admit. }
          { admit. }

      + inv H1; auto.
      + admit.
  Qed.

  Lemma stepInd_split:
    forall o u l,
      StepInd (ConcatMod ma mb) o u l ->
      exists oa ob ua ub la lb,
        StepInd ma oa ua la /\ StepInd mb ob ub lb /\
        o = M.union oa ob /\ u = M.union ua ub /\ l = hide (mergeLabel la lb).
  Proof.
    induction 1; simpl; intros.
    pose proof (substepsInd_split HSubSteps)
      as [oa [ob [ua [ub [la [lb ?]]]]]]; dest; subst.
    exists oa, ob, ua, ub, (hide la), (hide lb).
    intuition auto.

    - constructor; auto.
      admit. (* maybe the most difficult part *)
    - constructor; auto.
      admit. (* maybe the most difficult part *)
    - admit. (* easy, using hide_idempotent *)
  Qed.

  Lemma step_split:
    forall o u l,
      Step (ConcatMod ma mb) o u l ->
      exists oa ob ua ub la lb,
        Step ma oa ua la /\ Step mb ob ub lb /\
        o = M.union oa ob /\ u = M.union ua ub /\ l = hide (mergeLabel la lb).
  Proof.
    intros; apply step_consistent in H.
    pose proof (stepInd_split H) as [oa [ob [ua [ub [la [lb ?]]]]]]; dest; subst.
    exists oa, ob, ua, ub, la, lb.
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
      admit. (* map stuff *)

    - intros; subst.
      specialize (IHMultistep eq_refl).
      destruct IHMultistep as [sa [lsa [sb [lsb ?]]]]; dest; subst.

      apply step_split in HStep.
      destruct HStep as [soa [sob [sua [sub [sla [slb ?]]]]]]; dest; subst.

      exists (M.union sua sa), (sla :: lsa).
      exists (M.union sub sb), (slb :: lsb).
      repeat split.

      + constructor; auto.
        admit. (* map stuff *)
      + constructor; auto.
        admit. (* map stuff *)
      + admit. (* map stuff *)
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
    destruct HMultistepBeh as [sa [lsa [sb [lsb [? [? [? ?]]]]]]]; subst.
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

Lemma equivalentLabel_hide_mergeLabel:
  forall p la lb,
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
  - clear H2 H4. (* ?!?!? *)
    admit.
  - admit.
  - destruct anna, annb, annc, annd; auto.
Qed.

Lemma composeLabels_modular:
  forall p lsa lsb,
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
