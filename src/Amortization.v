Require Import Bool List String Omega.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.
Require Import Kami.ModularFacts Kami.RefinementFacts.

Set Implicit Arguments.
Set Asymmetric Patterns.

(*** Move to SemFacts.v *)

Lemma multistep_app:
  forall m ll1 ll2 o n,
    Multistep m o n (ll1 ++ ll2) ->
    exists n', Multistep m o n' ll2 /\ Multistep m n' n ll1.
Proof.
  induction ll1; simpl; intros.
  - eexists; split; eauto.
    constructor; auto.
  - inv H; specialize (IHll1 _ _ _ HMultistep); dest.
    eexists; split; eauto.
    constructor; auto.
Qed.

Lemma multistep_app_inv:
  forall m ll1 ll2 o n n',
    Multistep m o n' ll2 ->
    Multistep m n' n ll1 ->
    Multistep m o n (ll1 ++ ll2).
Proof.
  induction ll1; simpl; intros.
  - inv H0; auto.
  - inv H0; constructor; eauto.
Qed.

Section NoRules.
  Variable m: Modules.
  Hypothesis (Hrules: getRules m = nil).

  Lemma substep_getRules_nil:
    forall o u ul cs,
      Substep m o u ul cs -> ul = Rle None \/ exists d, ul = Meth d.
  Proof.
    destruct 1; auto.
    - right; eexists; auto.
    - rewrite Hrules in HInRules; inv HInRules.
    - right; eexists; auto.
  Qed.

  Lemma substepsInd_getRules_nil:
    forall o u l,
      SubstepsInd m o u l -> annot l = Some None \/ annot l = None.
  Proof.
    induction 1; auto.
    apply substep_getRules_nil in H0; destruct H0; dest; subst.
    - destruct l as [a d c]; simpl in *.
      destruct IHSubstepsInd; subst; simpl; auto.
    - destruct l as [a d c]; simpl in *; auto.
  Qed.

  Lemma step_getRules_nil:
    forall o u l,
      Step m o u l -> annot l = Some None \/ annot l = None.
  Proof.
    intros; apply step_consistent in H.
    inv H; apply substepsInd_getRules_nil in HSubSteps.
    destruct l0 as [a d c]; simpl in *; auto.
  Qed.

  Lemma substepsInd_rule_annot_1:
    forall o u ds cs,
      SubstepsInd m o u {| annot := None; defs := ds; calls := cs |} ->
      SubstepsInd m o u {| annot := Some None; defs := ds; calls := cs |}.
  Proof.
    intros.
    econstructor.
    - eassumption.
    - apply EmptyRule.
    - repeat split; auto.
    - auto.
    - reflexivity.
  Qed.

  Lemma substepsInd_rule_annot_2:
    forall o u l,
      SubstepsInd m o u l ->
      forall ds cs,
        l = {| annot := Some None; defs := ds; calls := cs |} ->
        SubstepsInd m o u {| annot := None; defs := ds; calls := cs |}.
  Proof.
    induction 1; simpl; intros; [inv H|].
    subst; inv H0.
    - mred; replace {| annot := None; defs := ds; calls := cs |} with l; auto.
      destruct l as [ann d c]; inv H1; simpl in *; dest; inv H4.
      destruct ann; intuition idtac.
    - destruct l as [ann d c]; inv H1; simpl in *; dest; inv H4.
      mred; auto.
    - rewrite Hrules in HInRules; inv HInRules.
    - destruct l as [ann d c]; inv H1; simpl in *; dest; inv H4.
      econstructor.
      + apply IHSubstepsInd; auto.
      + eapply SingleMeth; eauto.
      + repeat split; auto.
      + auto.
      + reflexivity.
  Qed.

  Lemma step_rule_annot_1:
    forall o u ds cs,
      Step m o u {| annot := None; defs := ds; calls := cs |} ->
      Step m o u {| annot := Some None; defs := ds; calls := cs |}.
  Proof.
    intros.
    apply step_consistent; apply step_consistent in H.
    inv H.
    destruct l as [a d c]; simpl in *; subst.
    change {| annot := _; defs := _; calls := _ |}
    with (hide {| annot := Some None; defs := d; calls := c |}).
    constructor; auto.
    apply substepsInd_rule_annot_1; auto.
  Qed.

  Lemma step_rule_annot_2:
    forall o u ds cs,
      Step m o u {| annot := Some None; defs := ds; calls := cs |} ->
      Step m o u {| annot := None; defs := ds; calls := cs |}.
  Proof.
    intros.
    apply step_consistent; apply step_consistent in H.
    inv H.
    destruct l as [a d c]; simpl in *; subst.
    change {| annot := _; defs := _; calls := _ |}
    with (hide {| annot := None; defs := d; calls := c |}).
    constructor; auto.
    eapply substepsInd_rule_annot_2; eauto.
  Qed.

End NoRules.

Lemma Forall_app:
  forall {A} (l1 l2: list A) P, Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; simpl; intros; auto.
  inv H; constructor; auto.
Qed.

(*** End *)

(** Extension of the restrict notion *)

(* TODO: should consider to remove annotation (to force to be None). *)
Definition restrictLabel (l: LabelT) (d: list string): LabelT :=
  {| defs := M.restrict (defs l) d;
     calls := M.restrict (calls l) d;
     annot := (* annot l *) None |}.

Definition restrictLabelSeq (ll: LabelSeqT) (d: list string): LabelSeqT :=
  map (fun l => restrictLabel l d) ll.

Lemma restrictLabelSeq_nil:
  forall ll d, restrictLabelSeq ll d = nil -> ll = nil.
Proof.
  induction ll; simpl; intros; auto; inv H.
Qed.

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

Section AboutCertainMethods.
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
    forall s1 sig1,
      Behavior m1 s1 sig1 ->
      exists s2 sig2,
        Behavior m2 s2 sig2 /\
        EquivalentLabelSeqWithout sig1 sig2 /\
        exists amt, AmortizedSeq amt (restrictLabelSeq sig1 fs) (restrictLabelSeq sig2 fs).

  Definition traceRefinesAmortA m1 m2 :=
    forall s1 sig1,
      Behavior m1 s1 sig1 ->
      forall amt col2,
        AmortizedSeq amt (restrictLabelSeq sig1 fs) (restrictLabelSeq col2 fs) ->
        exists s2 sig2,
          Behavior m2 s2 sig2 /\
          EquivalentLabelSeqWithout sig1 sig2 /\
          restrictLabelSeq col2 fs = restrictLabelSeq sig2 fs.

End AboutCertainMethods.

Notation "ma <<~[ p ]{ fs } mb" :=
  (traceRefinesAmort (liftToMap1 p) fs ma mb)
    (at level 100, format "ma  <<~[  p  ]{  fs  }  mb").

Notation "ma <|~[ p ]{ fs } mb" :=
  (traceRefinesAmortA (liftToMap1 p) fs ma mb)
    (at level 100, format "ma  <|~[  p  ]{  fs  }  mb").

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

(** * This is an interacting case within amortized labels. *)
(* NOTE1: we need one more interacting case within non-amortizing labels.
 * Informally, the statement should be like:
 * m1 <<~[p]{fs1} m2 -> m3 <<~[p]{fs2} m4 -> m1 ++ m3 <<~[id]{fs1 ++ fs2} m2 ++ m4.
 *)
(* NOTE2: we certainly also need a non-interacting case.
 * Informally, the statement should be like:
 * m1 <<~[p]{fs1} m2 -> m3 <<~[p]{fs2} m4 -> m1 ++ m3 <<~[p]{fs1 ++ fs2} m2 ++ m4.
 *)
Section Modularity.
  Variables (m1 m2 m3 m4: Modules).
  Variable fs: list string.
  
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hwf3: ModEquiv type typeUT m3)
             (Hwf4: ModEquiv type typeUT m4).
  (* (Hrdisj: DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2))) *)
  (* (Hddisj: DisjList (getDefs m1) (getDefs m2)) *)
  (* (Hcdisj: DisjList (getCalls m1) (getCalls m2)) *)
  (* (Hvr1: ValidRegsModules type m1) *)
  (* (Hvr2: ValidRegsModules type m2) *)

  Theorem traceRefinesAmort_absorbed_modular:
    forall vp,
      traceRefinesAmort (liftToMap1 vp) fs m1 m2 ->
      traceRefinesAmortA (liftToMap1 vp) fs m3 m4 ->
      (m1 ++ m3)%kami <<=[vp] (m2 ++ m4)%kami.
  Proof.
  Admitted.

End Modularity.

Corollary traceRefinesAmort_refl_modular:
  forall m1 m2 fs,
    ModEquiv type typeUT m1 ->
    ModEquiv type typeUT m2 ->
    traceRefinesAmort id fs m1 m2 ->
    forall ctxt,
      ModEquiv type typeUT ctxt ->
      SubList (getExtMeths ctxt) fs ->
      getRules ctxt = nil ->
      (m1 ++ ctxt)%kami <<== (m2 ++ ctxt)%kami.
Proof.
  intros.
  eapply traceRefinesAmort_absorbed_modular; eauto; rewrite idElementwiseId; eauto.
  apply traceRefinesAmortA_refl; auto.
Qed.

