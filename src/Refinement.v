Require Import List String.
Require Import Program.Equality Program.Basics Classes.Morphisms.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Syntax Semantics SemFacts Wf Equiv Split.

Set Implicit Arguments.

(* TODO: should move to proper file *)
Lemma liftToMap1_find:
  forall {A} vp (m: M.t A) k,
    M.find k (liftToMap1 vp m) = match M.find k m with
                                 | Some v => vp k v
                                 | None => None
                                 end.
Proof.
  intros.
  case_eq (M.find k (liftToMap1 vp m)); intros.
  - apply M.Facts.P.F.find_mapsto_iff in H.
    apply liftToMap1MapsTo in H; dest; subst.
    apply M.F.P.F.find_mapsto_iff in H0.
    rewrite H0; auto.
  - apply M.F.P.F.not_find_in_iff in H.
    case_eq (M.find k m); intros; auto.
    apply M.Facts.P.F.find_mapsto_iff in H0.
    case_eq (vp k a); intros; auto.
    assert (exists v', vp k v' = Some a0 /\ M.MapsTo k v' m).
    { eexists; eauto. }
    apply liftToMap1MapsTo in H2.
    elim H. 
    eapply M.MapsToIn1; eauto.
Qed.

Lemma liftToMap1_union:
  forall {A} vp (m1 m2: M.t A),
    M.Disj m1 m2 ->
    M.union (liftToMap1 vp m1) (liftToMap1 vp m2) = liftToMap1 vp (M.union m1 m2).
Proof.
  intros; M.ext y.
  findeq.
  repeat rewrite liftToMap1_find.
  findeq.
  - destruct (H y); findeq.
  - destruct (vp y a); auto.
Qed.

Lemma liftToMap1_subtractKV:
  forall {A} deceqA vp (m1 m2: M.t A),
    M.Disj m1 m2 ->
    M.subtractKV deceqA (liftToMap1 vp m1) (liftToMap1 vp m2) =
    liftToMap1 vp (M.subtractKV deceqA m1 m2).
Proof.
  intros; M.ext y.
  findeq.
  repeat rewrite liftToMap1_find.
  findeq.
  - destruct (H y); findeq.
  - destruct (vp y a); auto.
Qed.

Lemma liftToMap1_KeysDisj:
  forall {A} vp (m: M.t A) d,
    M.KeysDisj m d ->
    M.KeysDisj (liftToMap1 vp m) d.
Proof.
  M.mintros.
  specialize (H k H0).
  findeq.
  rewrite liftToMap1_find.
  rewrite H; auto.
Qed.

Section StepToRefinement.
  Variable imp spec: Modules.
  Variable p: MethsT -> MethsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable theta: RegsT -> RegsT.
  Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).

  Definition liftPLabel o l :=
    match l with
    | {| annot := a; defs := dfs; calls := clls |} =>
      {| annot := match a with
                  | Some (Some r) => Some (ruleMap o r)
                  | Some None => Some None
                  | None => None
                  end;
         defs := p dfs;
         calls := p clls |}
    end.

  Variable stepMap:
    forall o u l, Step imp o u l ->
             exists uspec, Step spec (theta o) uspec (liftPLabel o l) /\
                      theta (M.union u o) = M.union uspec (theta o).

  Theorem stepRefinement':
    forall s sig, Behavior imp s sig ->
                  exists sigSpec, Behavior spec (theta s) sigSpec /\
                                  equivalentLabelSeq p sig sigSpec.
  Proof.
    intros.
    dependent induction H.
    dependent induction HMultistepBeh; subst.
    - exists nil; rewrite thetaInit; repeat constructor.
    - specialize (IHHMultistepBeh thetaInit stepMap eq_refl).
      pose proof (stepMap HStep) as [uSpec [stepSpec upd]].
      destruct IHHMultistepBeh as [sigSpec [behSpec eqv]].
      inversion behSpec; subst.
      pose proof (BehaviorIntro (Multi HMultistepBeh0 stepSpec)) as sth.
      rewrite <- upd in sth.
      exists (liftPLabel n l :: sigSpec).
      constructor.
      + intuition.
      + constructor.
        * unfold equivalentLabel, liftPLabel; simpl.
          destruct l; destruct annot; simpl; intuition.
          destruct o; simpl; intuition.
        * intuition.
  Qed.

  Theorem stepRefinement: traceRefines p imp spec.
  Proof.
    unfold traceRefines; intros.
    pose proof (stepRefinement' H) as [sigSpec beh].
    exists (theta s1); exists sigSpec.
    intuition.
  Qed.
End StepToRefinement.

Lemma vp_equivalentLabel_CanCombineLabel_proper:
  forall vp,
    Proper (equivalentLabel (liftToMap1 vp) ==> equivalentLabel (liftToMap1 vp) ==> impl)
           CanCombineLabel.
Proof.
  unfold Proper, respectful, impl; intros.
  destruct x as [annx dsx csx], y as [anny dsy csy].
  destruct x0 as [annx0 dsx0 csx0], y0 as [anny0 dsy0 csy0]; simpl in *.
  inv H; inv H0; inv H1; dest; simpl in *; subst.
  repeat split; simpl; auto.
  - apply M.DomainSubset_Disj with (m2:= dsx); [|apply liftToMap1Subset].
    apply M.Disj_comm.
    apply M.DomainSubset_Disj with (m2:= dsx0); [|apply liftToMap1Subset].
    auto.
  - apply M.DomainSubset_Disj with (m2:= csx); [|apply liftToMap1Subset].
    apply M.Disj_comm.
    apply M.DomainSubset_Disj with (m2:= csx0); [|apply liftToMap1Subset].
    auto.
  - destruct annx, annx0, anny, anny0; auto.
Qed.

Section Facts.

  Lemma traceRefines_refl:
    forall m, traceRefines id m m.
  Proof.
    unfold traceRefines; intros.
    exists s1, sig1; split; auto.
    clear; induction sig1; constructor; auto.
    clear; repeat split.
    destruct (annot a); auto.
  Qed.

  Lemma traceRefines_trans:
    forall ma mb mc p q,
      traceRefines p ma mb ->
      traceRefines q mb mc ->
      traceRefines (fun f => q (p f)) ma mc.
  Proof.
    unfold traceRefines; intros.
    specialize (H _ _ H1); destruct H as [s2 [sig2 ?]]; dest.
    specialize (H0 _ _ H); destruct H0 as [s3 [sig3 ?]]; dest.
    exists s3, sig3; split; auto.
    clear -H2 H3.
    generalize dependent sig2; generalize dependent sig3.
    induction sig1; intros.
    - inv H2; inv H3; constructor.
    - inv H2; inv H3; constructor; eauto.
      clear -H1 H2.
      inv H1; inv H2; dest.
      repeat split; auto.
      + rewrite H; auto.
      + rewrite H0; auto.
      + destruct (annot y), (annot y0), (annot a); auto.
  Qed.

  Definition NonInteracting (m1 m2: Modules) :=
    DisjList (getDefs m1) (getCalls m2) /\
    DisjList (getCalls m1) (getDefs m2).

  Lemma nonInteracting_implies_wellHiddenModular:
    forall ma mb,
      NonInteracting ma mb ->
      forall la lb,
        WellHiddenModular ma mb la lb.
  Proof.
    unfold NonInteracting, WellHiddenModular, ValidLabel, wellHidden; intros; dest.
    destruct la as [anna dsa csa], lb as [annb dsb csb]; simpl in *.
    split.

    - unfold M.KeysDisj, M.KeysSubset in *; intros.
      apply M.F.P.F.not_find_in_iff.
      specializeAll k.
      apply getCalls_in in H9; destruct H9.
      + specialize (H2 H9).
        apply M.F.P.F.not_find_in_iff in H2.
        rewrite M.F.P.F.in_find_iff in *.
        (* findeq; *)
        (*   try (specialize (H8 k); destruct H8; *)
        (*        [elim H5; auto| *)
        (*         elim H5; apply H2; intro; inv H6]). *)
        admit.
      + specialize (H3 H9).
        apply M.F.P.F.not_find_in_iff in H3.
        rewrite M.F.P.F.in_find_iff in *.
        (* findeq; *)
        (*   try (specialize (H k); destruct H; *)
        (*        [elim H; apply H0; intro; inv H4| *)
        (*         elim H; auto]; fail). *)
        (* specialize (H8 k); destruct H8; *)
        (*   [elim H4; apply H1; intro; inv H6| *)
        (*    elim H4; apply H2; intro; inv H6]. *)
        admit.
    - unfold M.KeysDisj, M.KeysSubset in *; intros.
      apply M.F.P.F.not_find_in_iff.
      specializeAll k.
      apply getDefs_in in H9; destruct H9.
      + specialize (H5 H9).
        apply M.F.P.F.not_find_in_iff in H5.
        rewrite M.F.P.F.in_find_iff in *.
        (* findeq; *)
        (*   try (specialize (H k); destruct H; *)
        (*        [elim H; auto| *)
        (*         elim H; apply H3; intro; inv H4]). *)
        admit.
      + specialize (H4 H9).
        apply M.F.P.F.not_find_in_iff in H4.
        rewrite M.F.P.F.in_find_iff in *.
        (* findeq; *)
        (*   try (specialize (H8 k); destruct H8; *)
        (*        [elim H4; apply H1; intro; inv H5| *)
        (*         elim H4; auto]; fail). *)
        (* specialize (H k); destruct H; *)
        (*   [elim H; apply H0; intro; inv H4| *)
        (*    elim H; apply H3; intro; inv H4]. *)
        admit.
  Qed.

  Lemma nonInteracting_implies_wellHiddenModularSeq:
    forall ma mb,
      NonInteracting ma mb ->
      forall lsa lsb,
        List.length lsa = List.length lsb ->
        WellHiddenModularSeq ma mb lsa lsb.
  Proof.
    induction lsa; intros.
    - destruct lsb; [constructor|inv H0].
    - destruct lsb; [inv H0|].
      constructor; auto.
      apply nonInteracting_implies_wellHiddenModular; auto.
  Qed.

  Definition Interacting (m1 m2: Modules)
             (vp: M.key -> sigT SignT -> option (sigT SignT)) :=
    (forall k, In k (getCalls m1) -> ~ In k (getDefs m2) ->
               forall v, vp k v = Some v) /\
    (forall k, In k (getCalls m2) -> ~ In k (getDefs m1) ->
               forall v, vp k v = Some v).

  Lemma interacting_implies_wellHiddenModular:
    forall ma mb mc md vp,
      Interacting ma mc vp ->
      forall la lb lc ld,
        ValidLabel ma la -> ValidLabel mc lc ->
        WellHiddenModular ma mc la lc ->
        equivalentLabel (liftToMap1 vp) la lb ->
        equivalentLabel (liftToMap1 vp) lc ld ->
        WellHiddenModular mb md lb ld.
  Proof.
    intros.
    admit.
  Qed.

  Lemma interacting_implies_wellHiddenModularSeq:
    forall ma mb mc md vp,
      Interacting ma mc vp ->
      forall la lb lc ld,
        Forall (fun l => M.KeysSubset (defs l) (getDefs ma)) la ->
        Forall (fun l => M.KeysSubset (calls l) (getCalls ma)) la ->
        Forall (fun l => M.KeysSubset (defs l) (getDefs mc)) lc ->
        Forall (fun l => M.KeysSubset (calls l) (getCalls mc)) lc ->
        WellHiddenModularSeq ma mc la lc ->
        equivalentLabelSeq (liftToMap1 vp) la lb ->
        equivalentLabelSeq (liftToMap1 vp) lc ld ->
        WellHiddenModularSeq mb md lb ld.
  Proof.
    induction la; intros.
    - inv H4; inv H5; inv H6; constructor.
    - inv H0; inv H1; inv H2; inv H3; inv H4; inv H5; inv H6; constructor.
      + eapply IHla; eauto.
      + eapply interacting_implies_wellHiddenModular; eauto; split; auto.
  Qed.

  Section Modularity.
    Variables (ma mb mc md: Modules).

    Hypotheses (HmaEquiv: Equiv.ModEquiv type typeUT ma)
               (HmbEquiv: Equiv.ModEquiv type typeUT mb)
               (HmcEquiv: Equiv.ModEquiv type typeUT mc)
               (HmdEquiv: Equiv.ModEquiv type typeUT md).

    Hypotheses (Hacregs: DisjList (namesOf (getRegInits ma))
                                  (namesOf (getRegInits mc)))
               (Hbdregs: DisjList (namesOf (getRegInits mb))
                                  (namesOf (getRegInits md)))
               (Hacval: ValidRegsModules type (ConcatMod ma mc))
               (Hbdval: ValidRegsModules type (ConcatMod mb md)).

    Hypotheses (Hacdefs: DisjList (getDefs ma) (getDefs mc))
               (Haccalls: DisjList (getCalls ma) (getCalls mc))
               (Hbddefs: DisjList (getDefs mb) (getDefs md))
               (Hbdcalls: DisjList (getCalls mb) (getCalls md)).

    Section NonInteracting.
      Variable (p: MethsT -> MethsT).

      Hypotheses (Hpunion: forall m1 m2, M.union (p m1) (p m2) = p (M.union m1 m2))
                 (Hpsub: forall m1 m2, M.subtractKV signIsEq (p m1) (p m2) =
                                       p (M.subtractKV signIsEq m1 m2))
                 (Hpcomb: Proper (equivalentLabel p ==> equivalentLabel p ==> impl)
                                 CanCombineLabel).

      Lemma traceRefines_modular_noninteracting:
        NonInteracting mb md ->
        traceRefines p ma mb ->
        traceRefines p mc md ->
        traceRefines p (ConcatMod ma mc) (ConcatMod mb md).
      Proof.
        unfold traceRefines; intros.
        apply behavior_split in H2; auto.
        destruct H2 as [sa [lsa [sc [lsc ?]]]]; dest; subst.
        specialize (H0 _ _ H2).
        destruct H0 as [sb [lsb [? ?]]].
        specialize (H1 _ _ H3).
        destruct H1 as [sd [lsd [? ?]]].

        exists (M.union sb sd).
        exists (composeLabels lsb lsd).
        split; auto.
        - apply behavior_modular; auto.
          + eapply equivalentLabelSeq_CanCombineLabelSeq; eauto.
          + apply nonInteracting_implies_wellHiddenModularSeq; auto.
            admit. (* easy *)
        - apply composeLabels_modular; auto.
      Qed.

    End NonInteracting.

    Section Interacting.
      Variable (vp: M.key -> sigT SignT -> option (sigT SignT)).

      Lemma traceRefines_modular_interacting:
        Interacting ma mc vp ->
        traceRefines (liftToMap1 vp) ma mb ->
        traceRefines (liftToMap1 vp) mc md ->
        traceRefines id (ConcatMod ma mc) (ConcatMod mb md).
      Proof.
        unfold traceRefines; intros.
        apply behavior_split in H2; auto.
        destruct H2 as [sa [lsa [sc [lsc ?]]]]; dest; subst.
        specialize (H0 _ _ H2).
        destruct H0 as [sb [lsb [? ?]]].
        specialize (H1 _ _ H3).
        destruct H1 as [sd [lsd [? ?]]].

        exists (M.union sb sd).
        exists (composeLabels lsb lsd).
        split; auto.
        - apply behavior_modular; auto.
          + eapply equivalentLabelSeq_CanCombineLabelSeq; eauto.
            apply vp_equivalentLabel_CanCombineLabel_proper.
          + pose proof (behavior_defs_in HmaEquiv H2).
            pose proof (behavior_calls_in HmaEquiv H2).
            pose proof (behavior_defs_in HmcEquiv H3).
            pose proof (behavior_calls_in HmcEquiv H3).
            eapply interacting_implies_wellHiddenModularSeq; eauto.
        - apply composeLabels_modular; auto.
          + (* pose proof (behavior_defs_disj H2). *)
            (* pose proof (behavior_calls_disj H2). *)
            (* clear -H H5 H8 H9. *)
            (* generalize dependent lsb. *)
            (* induction lsa; intros; [inv H5; constructor|]. *)
            (* inv H5; inv H8; inv H9. *)
            (* constructor; auto. *)
            admit. (* true with "Behavior property w.r.t. label" and Interacting predicate *)
          + admit.
      Qed.

    End Interacting.

  End Modularity.
  
End Facts.

