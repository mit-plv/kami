Require Import Bool List String Omega.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.ListSupport Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.
Require Import Kami.ModularFacts Kami.RefinementFacts Kami.Label.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Notion of amortization *)

Inductive AmortizedSeq: LabelSeqT (* amortization *) -> LabelSeqT -> LabelSeqT -> Prop :=
| AmortizedNil: AmortizedSeq nil nil nil
| AmortizedPrd:
    forall amt ll1 ll2,
      AmortizedSeq amt ll1 ll2 ->
      forall l1, AmortizedSeq (amt ++ [l1]) (l1 :: ll1) (emptyMethLabel :: ll2)
| AmortizedBoth:
    forall amt l2 ll1 ll2,
      AmortizedSeq (l2 :: amt) ll1 ll2 ->
      forall l1, AmortizedSeq (amt ++ [l1]) (l1 :: ll1) (l2 :: ll2)
| AmortizedSame:
    forall ll1 ll2,
      AmortizedSeq nil ll1 ll2 ->
      forall l, AmortizedSeq nil (l :: ll1) (l :: ll2).

Lemma amortizedSeq_length:
  forall amt ll1 ll2, AmortizedSeq amt ll1 ll2 -> List.length ll1 = List.length ll2.
Proof. induction 1; simpl; intros; auto. Qed.

Lemma amortizedSeq_methLabelSeq:
  forall amt ll1 ll2,
    AmortizedSeq amt ll1 ll2 ->
    MethLabelSeq ll1 -> MethLabelSeq ll2 -> MethLabelSeq amt.
Proof.
  induction 1; simpl; intros; try constructor.
  - inv H0; inv H1.
    apply methLabelSeq_app; auto.
    repeat constructor; auto.
  - inv H0; inv H1.
    specialize (IHAmortizedSeq H4 H3); inv IHAmortizedSeq.
    apply methLabelSeq_app; auto.
    repeat constructor; auto.
Qed.

(** * Two kinds of amortized trace refinements *)
Section AmortizedRefinement.
  Variable p: MethsT -> MethsT.
  Variable fs: list string.

  Definition EquivalentLabelWithout l1 l2 :=
    p (M.complement (defs l1) fs) = M.complement (defs l2) fs /\
    p (M.complement (calls l1) fs) = M.complement (calls l2) fs /\
    match annot l1, annot l2 with
    | Some _, Some _ => True
    | None, None => True
    | _, _ => False
    end.

  Inductive EquivalentLabelSeqWithout: LabelSeqT -> LabelSeqT -> Prop :=
  | ELSWNil: EquivalentLabelSeqWithout nil nil
  | ELSWCons:
      forall ll1 ll2,
        EquivalentLabelSeqWithout ll1 ll2 ->
        forall l1 l2,
          EquivalentLabelWithout l1 l2 ->
          EquivalentLabelSeqWithout (l1 :: ll1) (l2 :: ll2).

  Definition traceRefinesAmort m1 m2 :=
    forall s1 ll1,
      Behavior m1 s1 ll1 ->
      exists s2 ll2,
        Behavior m2 s2 ll2 /\
        EquivalentLabelSeqWithout ll1 ll2 /\
        exists amt, AmortizedSeq amt (restrictLabelSeq ll1 fs) (restrictLabelSeq ll2 fs).

  Definition traceRefinesAmortA m1 m2 :=
    forall s1 ll1,
      Behavior m1 s1 ll1 ->
      forall amt all2,
        AmortizedSeq amt (restrictLabelSeq ll1 fs) all2 ->
        exists s2 ll2,
          Behavior m2 s2 ll2 /\
          EquivalentLabelSeqWithout ll1 ll2 /\
          all2 = restrictLabelSeq ll2 fs.

End AmortizedRefinement.

Notation "ma <<~[ p ]{ fs } mb" :=
  (traceRefinesAmort (liftToMap1 p) fs ma mb)
    (at level 100, format "ma  <<~[  p  ]{  fs  }  mb").

Notation "ma <|~[ p ]{ fs } mb" :=
  (traceRefinesAmortA (liftToMap1 p) fs ma mb)
    (at level 100, format "ma  <|~[  p  ]{  fs  }  mb").

(** Some facts between amortization and duality *)
Section Duality.
  
  Lemma amortizedSeq_dual:
    forall amt ll1 ll2,
      AmortizedSeq amt ll1 ll2 ->
      forall damt dll1 dll2,
        DualSeq amt damt -> DualSeq ll1 dll1 -> DualSeq ll2 dll2 ->
        MethLabelSeq damt -> MethLabelSeq dll1 -> MethLabelSeq dll2 ->
        AmortizedSeq damt dll1 dll2.
  Proof.
    induction 1; simpl; intros.
    - inv H; inv H0; inv H1; constructor.
    - inv H1; inv H2; inv H4; inv H5.
      apply dualSeqOf_cons_rev in H0; dest; subst.
      apply methLabelSeq_rev in H3.
      rewrite rev_app_distr in H3; simpl in H3; inv H3.
      apply methLabelSeq_rev in H13; rewrite rev_involutive in H13.
      assert (x0 = l2) by (eapply dual_methLabel_trans; eauto); subst.
      assert (l3 = emptyMethLabel) by (apply dual_emptyMethLabel; auto); subst.
      econstructor; eauto.
    - inv H1; inv H2; inv H4; inv H5.
      apply dualSeqOf_cons_rev in H0; dest; subst.
      apply methLabelSeq_rev in H3.
      rewrite rev_app_distr in H3; simpl in H3; inv H3.
      apply methLabelSeq_rev in H13; rewrite rev_involutive in H13.
      assert (x0 = l3) by (eapply dual_methLabel_trans; eauto); subst.
      constructor.
      apply IHAmortizedSeq; auto; constructor; auto.
    - inv H0; inv H1; inv H2; inv H4; inv H5.
      assert (l2 = l0) by (eapply dual_methLabel_trans; eauto); subst.
      constructor.
      apply IHAmortizedSeq; auto; constructor.
  Qed.

  Lemma wellHiddenConcat_restrictLabel_Dual:
    forall m1 m2 fs,
      DisjList (getDefs m1) (getDefs m2) ->
      DisjList (getCalls m1) (getCalls m2) ->
      DisjList fs (getExtMeths (m1 ++ m2)%kami) ->
      forall l1 l2,
        ValidLabel m1 l1 -> ValidLabel m2 l2 ->
        wellHidden m1 l1 -> wellHidden m2 l2 ->
        WellHiddenConcat m1 m2 l1 l2 ->
        Dual (restrictLabel l1 fs) (restrictLabel l2 fs).
  Proof.
    intros.
    pose proof (validLabel_wellHidden_getExtDefs H2 H4).
    pose proof (validLabel_wellHidden_getExtDefs H3 H5).
    pose proof (validLabel_wellHidden_getExtCalls H2 H4).
    pose proof (validLabel_wellHidden_getExtCalls H3 H5).
    clear H2 H3 H4 H5.
    destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2];
      unfold WellHiddenConcat, wellHidden, hide in *; simpl in *; dest.

    assert (DisjList (getExtDefs m1) (getExtDefs m2)).
    { eapply DisjList_SubList; [apply getExtDefs_getDefs|].
      apply DisjList_comm.
      eapply DisjList_SubList; [apply getExtDefs_getDefs|].
      apply DisjList_comm; auto.
    }
    assert (DisjList (getExtCalls m1) (getExtCalls m2)).
    { eapply DisjList_SubList; [apply getExtCalls_getCalls|].
      apply DisjList_comm.
      eapply DisjList_SubList; [apply getExtCalls_getCalls|].
      apply DisjList_comm; auto.
    }

    rewrite M.subtractKV_disj_union_1 in H2 by (eauto using M.DisjList_KeysSubset_Disj).
    rewrite M.subtractKV_disj_union_5 in H2
      by (eauto using M.DisjList_KeysSubset_Disj, extDefs_extCalls_disj).
    rewrite M.subtractKV_disj_union_6 in H2
      by (eauto using M.DisjList_KeysSubset_Disj, extDefs_extCalls_disj).
    rewrite M.subtractKV_disj_union_1 in H3 by (eauto using M.DisjList_KeysSubset_Disj).
    rewrite M.subtractKV_disj_union_5 in H3
      by (eauto using M.DisjList_KeysSubset_Disj, DisjList_comm, extDefs_extCalls_disj).
    rewrite M.subtractKV_disj_union_6 in H3
      by (eauto using M.DisjList_KeysSubset_Disj, DisjList_comm, extDefs_extCalls_disj).
    pose proof (M.KeysDisj_union_1 H2).
    pose proof (M.KeysDisj_union_2 H2).
    pose proof (M.KeysDisj_union_1 H3).
    pose proof (M.KeysDisj_union_2 H3).
    clear H2 H3.

    unfold Dual, restrictLabel; simpl; split.
    - M.ext k.
      rewrite 2! M.restrict_find.
      destruct (in_dec M.F.P.F.eq_dec k fs); auto.

      remember (M.find k d1) as ov1; destruct ov1 as [v1|]; intros.
      + destruct (in_dec string_dec k (getCalls (m1 ++ m2)%kami)).
        * apply M.subtractKV_KeysDisj_cases with (k0:= k) (v:= v1) in H6; auto.
        * apply DisjList_logic_inv with (e:= k) in H1; intuition.
          apply in_or_app; left.
          apply filter_In; split.
          -- apply getDefs_in_1, getExtDefs_getDefs, H7; findeq.
          -- apply negb_true_iff.
             remember (string_in _ _); destruct b; auto.
             apply string_in_dec_in in Heqb; elim n; auto.
      + remember (M.find k c2) as ov2; destruct ov2 as [v2|]; auto.
        apply DisjList_logic_inv with (e:= k) in H1; intuition.
        apply in_or_app; right.
        apply filter_In; split.
        * apply getCalls_in_2, getExtCalls_getCalls, H10; findeq.
        * apply negb_true_iff.
          remember (string_in _ _); destruct b; auto.
          apply string_in_dec_in in Heqb.
          apply M.subtractKV_KeysDisj_cases with (k0:= k) (v:= v2) in H13; auto.
          rewrite H13 in Heqov1; inv Heqov1.
    - M.ext k.
      rewrite 2! M.restrict_find.
      destruct (in_dec M.F.P.F.eq_dec k fs); auto.

      remember (M.find k c1) as ov1; destruct ov1 as [v1|]; intros.
      + destruct (in_dec string_dec k (getDefs (m1 ++ m2)%kami)).
        * apply M.subtractKV_KeysDisj_cases with (k0:= k) (v:= v1) in H12; auto.
        * apply DisjList_logic_inv with (e:= k) in H1; intuition.
          apply in_or_app; right.
          apply filter_In; split.
          -- apply getCalls_in_1, getExtCalls_getCalls, H9; findeq.
          -- apply negb_true_iff.
             remember (string_in _ _); destruct b; auto.
             apply string_in_dec_in in Heqb; elim n; auto.
      + remember (M.find k d2) as ov2; destruct ov2 as [v2|]; auto.
        apply DisjList_logic_inv with (e:= k) in H1; intuition.
        apply in_or_app; left.
        apply filter_In; split.
        * apply getDefs_in_2, getExtDefs_getDefs, H8; findeq.
        * apply negb_true_iff.
          remember (string_in _ _); destruct b; auto.
          apply string_in_dec_in in Heqb.
          apply M.subtractKV_KeysDisj_cases with (k0:= k) (v:= v2) in H11; auto.
          rewrite H11 in Heqov1; inv Heqov1.
  Qed.

  Lemma wellHiddenConcatSeq_restrictLabelSeq_DualSeq:
    forall m1 m2 fs,
      DisjList (getDefs m1) (getDefs m2) ->
      DisjList (getCalls m1) (getCalls m2) ->
      DisjList fs (getExtMeths (m1 ++ m2)%kami) ->
      forall ll1 ll2,
        WellHiddenConcatSeq m1 m2 ll1 ll2 ->
        Forall (fun l => ValidLabel m1 l) ll1 ->
        Forall (fun l => ValidLabel m2 l) ll2 ->
        Forall (fun l => wellHidden m1 l) ll1 ->
        Forall (fun l => wellHidden m2 l) ll2 ->
        DualSeq (restrictLabelSeq ll1 fs) (restrictLabelSeq ll2 fs).
  Proof.
    induction 4; [constructor|]; intros.
    inv H4; inv H5; inv H6; inv H7.
    simpl; constructor; auto.
    eapply wellHiddenConcat_restrictLabel_Dual; eauto.
  Qed.

End Duality.

Section TwoModuleFacts.
  Variables (m1 m2: Modules).
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hddisj: DisjList (getDefs m1) (getDefs m2))
             (Hcdisj: DisjList (getCalls m1) (getCalls m2)).

  Lemma equivalentLabelSeqWithout_CanCombineLabelSeq:
    forall p fs ll1 ll2 lsa lsb,
      CanCombineLabelSeq lsa lsb ->
      EquivalentLabelSeqWithout p fs lsa ll1 ->
      EquivalentLabelSeqWithout p fs lsb ll2 ->
      forall s1 s2,
        Multistep m1 (initRegs (getRegInits m1)) s1 ll1 ->
        Multistep m2 (initRegs (getRegInits m2)) s2 ll2 ->
        CanCombineLabelSeq ll1 ll2.
  Proof.
    induction ll1 as [|l1 ll1]; simpl; intros;
      [inv H2; inv H0; destruct lsb; inv H; inv H1; auto|].

    destruct lsa as [|la lsa]; inv H0.
    destruct lsb as [|lb lsb]; inv H.
    destruct ll2 as [|l2 ll2]; inv H1.
    inv H2; inv H3.
    specialize (IHll1 _ _ _ H4 H7 H8 _ _ HMultistep HMultistep0);
      clear H4 H7 H8 HMultistep HMultistep0.
    split; auto.

    repeat split.
    - eapply M.DisjList_KeysSubset_Disj.
      + exact Hddisj.
      + eapply step_defs_in; eauto.
      + eapply step_defs_in; eauto.
    - eapply M.DisjList_KeysSubset_Disj.
      + exact Hcdisj.
      + eapply step_calls_in; eauto.
      + eapply step_calls_in; eauto.
    - inv H0; inv H9; inv H11; dest.
      destruct (annot l1), (annot l2), (annot la), (annot lb); auto.
  Qed.

End TwoModuleFacts.

(** m <|~[id]{fs} m *)
Section AmortARefl.
  Variables (m: Modules)
            (fs: list string).
  Hypothesis (Hwf: ModEquiv type typeUT m)
             (Hmeths: SubList (getExtMeths m) fs)
             (Hrules: getRules m = nil).

  Lemma step_restrictLabel:
    forall o u l,
      Step m o u l ->
      Step m o u (restrictLabel l fs).
  Proof.
    intros.
    pose proof (step_defs_ext_in Hwf H).
    pose proof (step_calls_ext_in Hwf H).
    eapply M.KeysSubset_SubList in H0; eauto.
    eapply M.KeysSubset_SubList in H1; eauto.
    destruct l as [a d c]; unfold restrictLabel; simpl in *.
    rewrite 2! M.restrict_KeysSubset by assumption.
    pose proof (step_getRules_nil Hrules H); simpl in *.
    destruct H2; subst; auto.
    apply step_rule_annot_2; auto.
  Qed.

  Lemma step_restrictLabel_inv:
    forall o u l,
      Step m o u (restrictLabel l fs) ->
      M.KeysSubset (defs l) fs ->
      M.KeysSubset (calls l) fs ->
      (annot l = Some None \/ annot l = None) ->
      Step m o u l.
  Proof.
    destruct l as [a d c]; unfold restrictLabel; simpl; intros.
    rewrite 2! M.restrict_KeysSubset in H by assumption.
    destruct H2; subst; auto.
    apply step_rule_annot_1; auto.
  Qed.

  Lemma absorber_amortizeSeq_invariant:
    forall amt rll1 rll2,
      AmortizedSeq amt rll1 rll2 ->
      forall ll1 ll2,
        rll1 = restrictLabelSeq ll1 fs ->
        rll2 = restrictLabelSeq ll2 fs ->
        forall n1,
          Multistep m (initRegs (getRegInits m)) n1 ll1 ->
          forall n2,
            Multistep m (initRegs (getRegInits m)) n2 ll2 ->
            Multistep m (initRegs (getRegInits m)) n1 ((rev amt) ++ ll2).
  Proof.
    induction 1; simpl; intros; auto.
    - destruct ll1; [|inv H].
      destruct ll2; [|inv H0].
      assumption.
    - rewrite rev_app_distr; simpl.
      destruct ll0; inv H0.
      destruct ll3; inv H1.
      inv H2; inv H3.

      pose proof (step_defs_ext_in Hwf HStep0).
      pose proof (step_calls_ext_in Hwf HStep0).
      eapply M.KeysSubset_SubList in H0; eauto.
      eapply M.KeysSubset_SubList in H1; eauto.
      rewrite M.restrict_KeysSubset in H4; auto.
      rewrite M.restrict_KeysSubset in H5; auto.

      specialize (IHAmortizedSeq _ _ eq_refl eq_refl _ HMultistep _ HMultistep0).
      apply multistep_app in IHAmortizedSeq; dest.
      constructor.
      + apply multistep_app_inv with (n':= x); auto.
        replace x with (M.union (M.empty _) x) by meq.
        constructor; auto.
        destruct l0 as [a d c]; simpl in *; subst.
        apply step_empty; auto.
        apply step_getRules_nil in HStep0; simpl in *; intuition idtac.
      + apply step_restrictLabel; auto.

    - rewrite rev_app_distr; simpl.
      destruct ll0; inv H0.
      destruct ll3; inv H1.
      inv H2; inv H3.
      specialize (IHAmortizedSeq _ _ eq_refl eq_refl _ HMultistep _ HMultistep0).
      simpl in *; rewrite <-app_assoc in IHAmortizedSeq; simpl in *.
      apply multistep_app in IHAmortizedSeq; dest; inv H0.

      constructor; [|apply step_restrictLabel; auto].
      eapply multistep_app_inv; eauto.
      constructor; auto.

      apply step_restrictLabel_inv; auto.
      + apply M.KeysSubset_SubList with (d1:= getExtMeths m); auto.
        eapply step_defs_ext_in; eauto.
      + apply M.KeysSubset_SubList with (d1:= getExtMeths m); auto.
        eapply step_calls_ext_in; eauto.
      + eapply step_getRules_nil; eauto.
        
    - destruct ll0; inv H0.
      destruct ll3; inv H1.
      inv H2; inv H3.
      specialize (IHAmortizedSeq _ _ eq_refl eq_refl _ HMultistep _ HMultistep0).
      simpl in *.
      constructor; auto.

      pose proof (step_defs_ext_in Hwf HStep).
      pose proof (step_calls_ext_in Hwf HStep).
      pose proof (step_defs_ext_in Hwf HStep0).
      pose proof (step_calls_ext_in Hwf HStep0).
      eapply M.KeysSubset_SubList in H0; eauto.
      eapply M.KeysSubset_SubList in H1; eauto.
      eapply M.KeysSubset_SubList in H2; eauto.
      eapply M.KeysSubset_SubList in H3; eauto.
      rewrite 2! M.restrict_KeysSubset in H4; auto.
      rewrite 2! M.restrict_KeysSubset in H5; auto.

      pose proof (step_getRules_nil Hrules HStep).
      pose proof (step_getRules_nil Hrules HStep0).

      destruct l as [a d c], l0 as [a0 d0 c0]; simpl in *; subst.
      destruct H6; destruct H7; subst; auto.
      + apply step_rule_annot_2; auto.
      + apply step_rule_annot_1; auto.
  Qed.

  Lemma amortizedSeq_restrictLabelSeq:
    forall rll1 ll2 amt,
      AmortizedSeq amt rll1 ll2 ->
      forall ll1,
        rll1 = restrictLabelSeq ll1 fs ->
        Forall (fun l => annot l = None /\
                         M.restrict (defs l) fs = defs l /\
                         M.restrict (calls l) fs = calls l) amt /\
        Forall (fun l => annot l = None /\
                         M.restrict (defs l) fs = defs l /\
                         M.restrict (calls l) fs = calls l) ll2.
  Proof.
    induction 1; simpl; intros.
    - destruct ll1; inv H.
      split; constructor.
    - destruct ll0; inv H0.
      specialize (IHAmortizedSeq _ eq_refl); dest.
      split.
      + apply Forall_app; auto.
        constructor; auto.
        destruct l as [a d c]; simpl.
        repeat split; apply M.restrict_idempotent.
      + constructor; auto.
    - destruct ll0; inv H0.
      specialize (IHAmortizedSeq _ eq_refl); dest.
      inv H0.
      split.
      + apply Forall_app; auto.
        constructor; auto.
        destruct l as [a d c]; simpl.
        repeat split; apply M.restrict_idempotent.
      + constructor; auto.
    - destruct ll0; inv H0.
      specialize (IHAmortizedSeq _ eq_refl); dest.
      split; auto.
      constructor; auto.
      destruct l0 as [a d c]; simpl.
      repeat split; apply M.restrict_idempotent.
  Qed.

  Lemma traceRefinesAmortA_refl':
    forall s1 ll1 o,
      o = (initRegs (getRegInits m)) ->
      Multistep m o s1 ll1 ->
      forall amt rll2,
        AmortizedSeq amt (restrictLabelSeq ll1 fs) rll2 ->
        exists (s2 : RegsT) (ll2 : LabelSeqT),
          Behavior m s2 ll2 /\
          EquivalentLabelSeqWithout id fs ll1 ll2 /\
          rll2 = restrictLabelSeq ll2 fs.
  Proof.
    induction 2; simpl; intros;
      [inv H1; do 2 eexists; repeat split; repeat constructor|].

    subst.
    pose proof (amortizedSeq_restrictLabelSeq H1 (l :: a) eq_refl) as Hrest.
    destruct Hrest as [_ Hrest].
    destruct rll2 as [|rl2 rll2]; [inv H1|].
    inv H1.

    - specialize (IHMultistep eq_refl _ _ H3).
      destruct IHMultistep as [ps2 [pll2 ?]]; dest.
      exists (M.union (M.empty _) ps2).
      exists (match annot l with
              | Some _ => emptyRuleLabel
              | None => emptyMethLabel
              end :: pll2).
      repeat split.
      + inv H; constructor; auto.
        destruct (annot l); apply step_empty; auto.
      + constructor; auto.
        pose proof (step_defs_ext_in Hwf HStep).
        pose proof (step_calls_ext_in Hwf HStep).
        apply M.KeysSubset_SubList with (d2:= fs) in H4; auto.
        apply M.KeysSubset_SubList with (d2:= fs) in H5; auto.
        constructor; unfold id; simpl;
          try (destruct (annot l); simpl; rewrite M.complement_KeysSubset; auto).
      + destruct (annot l); simpl; f_equal; assumption.

    - specialize (IHMultistep eq_refl _ _ H3).
      destruct IHMultistep as [ps2 [pll2 ?]]; dest; subst.
      inv H.
      eapply absorber_amortizeSeq_invariant in H3; eauto.
      simpl in H3; rewrite <-app_assoc in H3; simpl in H3.
      apply multistep_app in H3; dest.

      exists x; exists ({| annot := annot l;
                           defs := defs rl2;
                           calls := calls rl2 |} :: pll2).
      inv H.

      pose proof (step_defs_ext_in Hwf HStep).
      pose proof (step_calls_ext_in Hwf HStep).
      pose proof (step_defs_ext_in Hwf HStep0).
      pose proof (step_calls_ext_in Hwf HStep0).
      eapply M.KeysSubset_SubList in H; eauto.
      eapply M.KeysSubset_SubList in H3; eauto.
      eapply M.KeysSubset_SubList in H4; eauto.
      eapply M.KeysSubset_SubList in H5; eauto.
      
      repeat split.
      + constructor; auto.
        pose proof (step_getRules_nil Hrules HStep).
        pose proof (step_getRules_nil Hrules HStep0).
        destruct rl2 as [ra2 rd2 rc2]; simpl in *.
        destruct l as [la ld lc]; simpl in *.
        destruct H6, H7; subst; auto.
        * apply step_rule_annot_1; auto.
        * apply step_rule_annot_2; auto.
      + constructor; auto.
        repeat split; unfold id; simpl.
        * rewrite 2! M.complement_KeysSubset; auto.
        * rewrite 2! M.complement_KeysSubset; auto.
        * destruct (annot l); auto.
      + simpl; f_equal.
        unfold restrictLabel; simpl.
        inv Hrest; destruct rl2 as [a2 d2 c2]; simpl in *; dest.
        f_equal; auto.

    - specialize (IHMultistep eq_refl _ _ H3).
      destruct IHMultistep as [ps2 [pll2 ?]]; dest; subst.
      inv H.
      eapply absorber_amortizeSeq_invariant in H3; eauto.
      simpl in H3.
      eexists; eexists (_ :: _); repeat split.
      + constructor; eauto.
      + constructor; auto.
        repeat split.
        destruct (annot l); auto.
  Qed.

  Lemma traceRefinesAmortA_refl:
    traceRefinesAmortA id fs m m.
  Proof.
    unfold traceRefinesAmortA; intros.
    eapply traceRefinesAmortA_refl'; eauto.
    inv H; eauto.
  Qed.

End AmortARefl.

Section Modularity.
  Variables (m1 m2 m3 m4: Modules).
  Variable fs: list string.
  
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hwf3: ModEquiv type typeUT m3)
             (Hwf4: ModEquiv type typeUT m4)
             (Hrdisj13: DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m3)))
             (Hrdisj24: DisjList (namesOf (getRegInits m2)) (namesOf (getRegInits m4)))
             (Hddisj13: DisjList (getDefs m1) (getDefs m3))
             (Hcdisj13: DisjList (getCalls m1) (getCalls m3))
             (Hddisj24: DisjList (getDefs m2) (getDefs m4))
             (Hcdisj24: DisjList (getCalls m2) (getCalls m4))
             (Hvr1: ValidRegsModules type m1)
             (Hvr2: ValidRegsModules type m2)
             (Hvr3: ValidRegsModules type m3)
             (Hvr4: ValidRegsModules type m4)
             (Hfs: DisjList fs (getExtMeths (m1 ++ m3)%kami)).

  (** m1 <<~[p]{fs} m2 -> m3 <|~[p]{fs} m4 -> (m1 + m3) <=[p] (m2 + m4) *)
  Section AmortizedInteracting.
    
    Definition AmortizedInteracting :=
      (forall f, In f (getExtCalls m1) /\ In f (getExtDefs m3) -> In f fs) /\
      (forall f, In f (getExtDefs m1) /\ In f (getExtCalls m3) -> In f fs) /\
      (forall f, In f (getExtCalls m2) /\ In f (getExtDefs m4) -> In f fs) /\
      (forall f, In f (getExtDefs m2) /\ In f (getExtCalls m4) -> In f fs).

    Hypothesis (Hai: AmortizedInteracting).
    
    Lemma amortizedInteracting_wellHiddenModular:
      forall l2 l4,
        Hidden l2 -> Hidden l4 ->
        Dual (restrictLabel l2 fs) (restrictLabel l4 fs) ->
        WellHiddenModular m2 m4 l2 l4.
    Proof.
      unfold WellHiddenModular; intros.

      rewrite H in H4; rewrite H0 in H5; clear H H0.

      assert (M.Disj (defs l2) (defs l4)) by
          (eapply M.DisjList_KeysSubset_Disj; [exact Hddisj24|apply H2|apply H3]).
      assert (M.Disj (calls l2) (calls l4)) by
          (eapply M.DisjList_KeysSubset_Disj; [exact Hcdisj24|apply H2|apply H3]).

      pose proof (validLabel_wellHidden_getExtDefs H2 H4).
      pose proof (validLabel_wellHidden_getExtCalls H2 H4).
      pose proof (validLabel_wellHidden_getExtDefs H3 H5).
      pose proof (validLabel_wellHidden_getExtCalls H3 H5).
      clear H2 H3 H4 H5.

      assert (M.Disj (defs l2) (calls l2)) by
          (eapply M.DisjList_KeysSubset_Disj;
           [eapply extDefs_extCalls_disj with (m:= m2)|assumption|assumption]).
      assert (M.Disj (defs l4) (calls l4)) by
          (eapply M.DisjList_KeysSubset_Disj;
           [eapply extDefs_extCalls_disj with (m:= m4)|assumption|assumption]).

      destruct l2 as [a1 d1 c1], l4 as [a3 d3 c3]; unfold wellHidden; simpl in *.
      split.

      - rewrite M.subtractKV_disj_union_1 by assumption.
        rewrite 2! M.subtractKV_disj_union_2 by assumption.
        rewrite M.subtractKV_disj_invalid with (m5:= d1) (m6:= c1) by assumption.
        rewrite M.subtractKV_disj_invalid with (m5:= (M.subtractKV signIsEq d3 c1))
          by (apply M.subtractKV_disj_1; auto).
        apply M.KeysDisj_union.
        + eapply M.KeysDisj_SubList; [|eapply getCalls_subList_2].
          apply M.KeysDisj_app.
          * apply M.subtractKV_KeysDisj_1.
            eapply DisjList_KeysSubset_KeysDisj.
            -- apply extDefs_calls_disj.
            -- assumption.
          * pose proof (restrictLabel_dual_implies H1) as Hdr; simpl in Hdr.
            apply M.subtractKV_KeysDisj_2; intros.
            apply Hdr, (proj2 Hai); split.
            -- apply H6; findeq.
            -- apply getCalls_not_getDefs_getExtCalls; auto.
               destruct (Hddisj24 k); auto.
               elim H10; apply getExtDefs_getDefs; apply H6; findeq.
        + eapply M.KeysDisj_SubList; [|eapply getCalls_subList_2].
          apply M.KeysDisj_app.
          * pose proof (restrictLabel_dual_implies H1) as Hdr; simpl in Hdr.
            apply M.subtractKV_KeysDisj_2; intros.
            apply eq_sym, Hdr, (proj1 (proj2 (proj2 Hai))); split.
            -- apply getCalls_not_getDefs_getExtCalls; auto.
               destruct (Hddisj24 k); auto.
               elim H10; apply getExtDefs_getDefs; apply H8; findeq.
            -- apply H8; findeq.
          * apply M.subtractKV_KeysDisj_1.
            eapply DisjList_KeysSubset_KeysDisj.
            -- apply extDefs_calls_disj.
            -- assumption.
      - rewrite M.subtractKV_disj_union_1 by assumption.
        rewrite 2! M.subtractKV_disj_union_2 by assumption.
        rewrite M.subtractKV_disj_invalid with (m5:= c1) (m6:= d1)
          by (apply M.Disj_comm; assumption).
        rewrite M.subtractKV_disj_invalid with (m5:= (M.subtractKV signIsEq c3 d1))
          by (apply M.subtractKV_disj_1; auto).
        apply M.KeysDisj_union.
        + rewrite getDefs_app; apply M.KeysDisj_app.
          * apply M.subtractKV_KeysDisj_1.
            eapply DisjList_KeysSubset_KeysDisj.
            -- apply extCalls_defs_disj.
            -- assumption.
          * pose proof (restrictLabel_dual_implies H1) as Hdr; simpl in Hdr.
            apply M.subtractKV_KeysDisj_2; intros.
            apply Hdr, (proj1 (proj2 (proj2 Hai))); split.
            -- apply H7; findeq.
            -- apply getDefs_not_getCalls_getExtDefs; auto.
               destruct (Hcdisj24 k); auto.
               elim H10; apply getExtCalls_getCalls; apply H7; findeq.
        + rewrite getDefs_app; apply M.KeysDisj_app.
          * pose proof (restrictLabel_dual_implies H1) as Hdr; simpl in Hdr.
            apply M.subtractKV_KeysDisj_2; intros.
            apply eq_sym, Hdr, (proj2 Hai); split.
            -- apply getDefs_not_getCalls_getExtDefs; auto.
               destruct (Hcdisj24 k); auto.
               elim H10; apply getExtCalls_getCalls; apply H9; findeq.
            -- apply H9; findeq.
          * apply M.subtractKV_KeysDisj_1.
            eapply DisjList_KeysSubset_KeysDisj.
            -- apply extCalls_defs_disj.
            -- assumption.
    Qed.

    Lemma amortizedInteracting_wellHiddenModularSeq:
      forall ll2 ll4,
        HiddenSeq ll2 -> HiddenSeq ll4 ->
        DualSeq (restrictLabelSeq ll2 fs) (restrictLabelSeq ll4 fs) ->
        WellHiddenModularSeq m2 m4 ll2 ll4.
    Proof.
      induction ll2 as [|l2 ll2]; simpl; intros;
        [inv H1; apply eq_sym, restrictLabelSeq_nil in H2; subst; constructor|].

      destruct ll4 as [|l4 ll4]; inv H1.
      inv H; inv H0.
      constructor; auto.
      eauto using amortizedInteracting_wellHiddenModular.
    Qed.

    Lemma equivalentLabelWithout_dual_equivalentLabel:
      forall vp l1 l2,
        ValidLabel m1 l1 -> ValidLabel m2 l2 ->
        wellHidden m1 l1 -> wellHidden m2 l2 ->
        Hidden l1 -> Hidden l2 ->
        EquivalentLabelWithout (liftToMap1 vp) fs l1 l2 ->
        forall l3 l4,
          ValidLabel m3 l3 -> ValidLabel m4 l4 ->
          wellHidden m3 l3 -> wellHidden m4 l4 ->
          Hidden l3 -> Hidden l4 ->
          EquivalentLabelWithout (liftToMap1 vp) fs l3 l4 ->
          Dual (restrictLabel l1 fs) (restrictLabel l3 fs) ->
          Dual (restrictLabel l2 fs) (restrictLabel l4 fs) ->
          equivalentLabel (liftToMap1 vp) (hide (mergeLabel l1 l3)) (hide (mergeLabel l2 l4)).
    Proof.
      intros.
      assert (Hdl13: DisjLabel l1 l3)
        by (inv H; inv H6; eapply disjList_KeysSubset_DisjLabel; eauto).
      assert (Hdl24: DisjLabel l2 l4)
        by (inv H0; inv H7; eapply disjList_KeysSubset_DisjLabel; eauto).
      rewrite dual_restrictLabel_hide_mergeLabel_complementLabel
      with (d:= fs) (l1:= l1) (l2:= l3); try assumption.
      rewrite dual_restrictLabel_hide_mergeLabel_complementLabel
      with (d:= fs) (l1:= l2) (l2:= l4); try assumption.

      rewrite 2! disjLabel_NonInteractingLabel_hide_mergeLabel;
        [|apply disjLabel_complementLabel; auto|
         |apply disjLabel_complementLabel; auto|].

      - replace (hide (complementLabel l1 fs)) with (complementLabel l1 fs)
          by (apply eq_sym, hidden_complementLabel; assumption).
        replace (hide (complementLabel l2 fs)) with (complementLabel l2 fs)
          by (apply eq_sym, hidden_complementLabel; assumption).
        replace (hide (complementLabel l3 fs)) with (complementLabel l3 fs)
          by (apply eq_sym, hidden_complementLabel; assumption).
        replace (hide (complementLabel l4 fs)) with (complementLabel l4 fs)
          by (apply eq_sym, hidden_complementLabel; assumption).

        unfold EquivalentLabelWithout in H5, H12.
        apply disjLabel_complementLabel with (d1:= fs) (d2:= fs) in Hdl13.
        apply disjLabel_complementLabel with (d1:= fs) (d2:= fs) in Hdl24.
        unfold DisjLabel in Hdl13, Hdl24.
        unfold complementLabel in *; simpl in *.

        dest; subst; unfold equivalentLabel; simpl; repeat split.
        + rewrite <-H5, <-H12; apply liftToMap1_union; assumption.
        + rewrite <-H19, <-H21; apply liftToMap1_union; assumption.
        + destruct (annot l1), (annot l2), (annot l3), (annot l4); auto.

      - inv Hai; dest.
        eapply validLabel_complementLabel_NonInteractingLabel.
        + eapply validLabel_wellHidden_getExtDefs; eauto.
        + eapply validLabel_wellHidden_getExtCalls; eauto.
        + eapply validLabel_wellHidden_getExtDefs; eauto.
        + eapply validLabel_wellHidden_getExtCalls; eauto.
        + assumption.
        + assumption.
      - inv Hai; dest.
        eapply validLabel_complementLabel_NonInteractingLabel.
        + eapply validLabel_wellHidden_getExtDefs; eauto.
        + eapply validLabel_wellHidden_getExtCalls; eauto.
        + eapply validLabel_wellHidden_getExtDefs; eauto.
        + eapply validLabel_wellHidden_getExtCalls; eauto.
        + assumption.
        + assumption.
    Qed.

    Lemma equivalentLabelSeqWithout_dualSeq_equivalentLabelSeq:
      forall vp ll1 ll2,
        EquivalentLabelSeqWithout (liftToMap1 vp) fs ll1 ll2 ->
        Forall (fun l1 => ValidLabel m1 l1) ll1 ->
        Forall (fun l2 => ValidLabel m2 l2) ll2 ->
        Forall (fun l1 => wellHidden m1 l1) ll1 ->
        Forall (fun l2 => wellHidden m2 l2) ll2 ->
        HiddenSeq ll1 -> HiddenSeq ll2 ->
        forall ll3 ll4,
          Forall (fun l3 => ValidLabel m3 l3) ll3 ->
          Forall (fun l4 => ValidLabel m4 l4) ll4 ->
          Forall (fun l3 => wellHidden m3 l3) ll3 ->
          Forall (fun l4 => wellHidden m4 l4) ll4 ->
          HiddenSeq ll3 -> HiddenSeq ll4 ->
          EquivalentLabelSeqWithout (liftToMap1 vp) fs ll3 ll4 ->
          DualSeq (restrictLabelSeq ll1 fs) (restrictLabelSeq ll3 fs) ->
          DualSeq (restrictLabelSeq ll2 fs) (restrictLabelSeq ll4 fs) ->
          equivalentLabelSeq (liftToMap1 vp) (composeLabels ll1 ll3) (composeLabels ll2 ll4).
    Proof.
      induction 1; simpl; intros; [constructor|].
      destruct ll3 as [|l3 ll3]; inv H14.
      destruct ll4 as [|l4 ll4]; inv H15.
      inv H1; inv H2; inv H3; inv H4; inv H5; inv H6.
      inv H7; inv H8; inv H9; inv H10; inv H11; inv H12.
      inv H13; constructor; auto.
      eauto using equivalentLabelWithout_dual_equivalentLabel.
    Qed.

    Theorem traceRefinesAmort_modular_interacting:
      forall vp,
        traceRefinesAmort (liftToMap1 vp) fs m1 m2 ->
        traceRefinesAmortA (liftToMap1 vp) fs m3 m4 ->
        (m1 ++ m3)%kami <<=[vp] (m2 ++ m4)%kami.
    Proof.
      unfold traceRefines, traceRefinesAmort, traceRefinesAmortA in *; intros ? ? ? s13 ll13 ?.

      apply behavior_split in H1; auto; [|constructor; auto].
      destruct H1 as [s1 [ll1 [s3 [ll3 ?]]]]; dest; subst.

      specialize (H _ _ H1).
      destruct H as [s2 [ll2 ?]]; dest.
      specialize (H0 _ _ H2).

      pose proof H6.
      apply wellHiddenConcatSeq_restrictLabelSeq_DualSeq with (fs:= fs) in H6;
        eauto using behavior_ValidLabel, behavior_wellHidden.

      specialize (H0 (dualSeqOf x) (dualSeqOf (restrictLabelSeq ll2 fs))).

      assert (Hdamt: AmortizedSeq (dualSeqOf x) (restrictLabelSeq ll3 fs)
                                  (dualSeqOf (restrictLabelSeq ll2 fs))).
      { eapply amortizedSeq_dual; eauto.
        { apply dualSeqOf_dualSeq. }
        { apply dualSeqOf_dualSeq. }
        { apply dualSeqOf_methLabelSeq.
          eapply amortizedSeq_methLabelSeq; eauto;
            apply restrictLabelSeq_MethLabelSeq.
        }
        { apply restrictLabelSeq_MethLabelSeq. }
        { apply dualSeqOf_methLabelSeq, restrictLabelSeq_MethLabelSeq. }
      }
      specialize (H0 Hdamt).
      destruct H0 as [s4 [ll4 ?]]; dest.
      rewrite H10 in Hdamt.

      do 2 eexists; split.
      - apply behavior_modular; auto.
        + constructor; auto.
        + eassumption.
        + eassumption.
        + inv H; inv H0; eauto using equivalentLabelSeqWithout_CanCombineLabelSeq.
        + apply amortizedInteracting_wellHiddenModularSeq.
          * inv H; eauto using multistep_hiddenSeq.
          * inv H0; eauto using multistep_hiddenSeq.
          * rewrite <-H10; apply dualSeqOf_dualSeq.
      - apply equivalentLabelSeqWithout_dualSeq_equivalentLabelSeq;
          eauto using behavior_ValidLabel, behavior_wellHidden, behavior_hiddenSeq.
        rewrite <-H10; apply dualSeqOf_dualSeq.
    Qed.

  End AmortizedInteracting.
  
End Modularity.

Section Substitution.
  Variables (m1 m2 ctxt: Modules).
  Variable fs: list string.
  
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hwfc: ModEquiv type typeUT ctxt)
             (Hrdisj1: DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits ctxt)))
             (Hrdisj2: DisjList (namesOf (getRegInits m2)) (namesOf (getRegInits ctxt)))
             (Hddisj1: DisjList (getDefs m1) (getDefs ctxt))
             (Hcdisj1: DisjList (getCalls m1) (getCalls ctxt))
             (Hddisj2: DisjList (getDefs m2) (getDefs ctxt))
             (Hcdisj2: DisjList (getCalls m2) (getCalls ctxt))
             (Hvr1: ValidRegsModules type m1)
             (Hvr2: ValidRegsModules type m2)
             (Hvrc: ValidRegsModules type ctxt)
             (Hfs1: SubList (getExtMeths ctxt) fs)
             (Hfs2: DisjList fs (getExtMeths (m1 ++ ctxt)%kami))
             (Hcr: getRules ctxt = nil).

  Corollary traceRefinesAmort_refl_modular:
    traceRefinesAmort id fs m1 m2 ->
    (m1 ++ ctxt)%kami <<== (m2 ++ ctxt)%kami.
  Proof.
    intros.
    eapply traceRefinesAmort_modular_interacting; eauto.
    - repeat split; intros; dest; apply Hfs1; auto; apply in_or_app; auto.
    - rewrite idElementwiseId; eauto.
    - rewrite idElementwiseId.
      apply traceRefinesAmortA_refl; auto.
  Qed.

End Substitution.

