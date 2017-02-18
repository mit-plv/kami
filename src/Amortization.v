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

(*** End *)

(** Extension of the restrict notion *)

Definition restrictLabel (l: LabelT) (d: list string): LabelT :=
  {| defs := M.restrict (defs l) d;
     calls := M.restrict (calls l) d;
     annot := annot l |}.

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

Section AboutCertainMethods.
  Variable p: MethsT -> MethsT.
  Variable fs: list string.

  Definition EquivalentLabelWithout l1 l2 :=
    p (defs l1) = defs l2 /\
    p (M.restrict (calls l1) fs) = M.restrict (calls l2) fs /\
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

  Lemma equivalentLabelSeqWithout_with:
    forall ll1 ll2,
      Forall (fun l => M.KeysSubset (defs l) fs) ll1 ->
      Forall (fun l => M.KeysSubset (calls l) fs) ll1 ->
      Forall (fun l => M.KeysSubset (defs l) fs) ll2 ->
      Forall (fun l => M.KeysSubset (calls l) fs) ll2 ->
      EquivalentLabelSeqWithout ll1 ll2.
  Proof.
  Admitted.

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
        AmortizedSeq amt (restrictLabelSeq sig1 fs) col2 ->
        exists s2 sig2,
          Behavior m2 s2 sig2 /\
          EquivalentLabelSeqWithout sig1 sig2 /\
          col2 = restrictLabelSeq sig2 fs.

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
             (Habs: SubList (getExtMeths m) fs).

  Lemma absorber_behavior_restrictLabelSeq:
    forall n ll,
      Multistep m (initRegs (getRegInits m)) n ll ->
      restrictLabelSeq ll fs = ll.
  Proof.
    intros.
    pose proof (multistep_defs_ext_in Hwf H).
    pose proof (multistep_calls_ext_in Hwf H).
    clear H.
    induction ll; simpl; intros; auto.
    inv H0; inv H1.
    f_equal; auto.
    destruct a as [a d c]; unfold restrictLabel; simpl in *.
    f_equal; auto.
    - apply M.restrict_KeysSubset; auto.
      eapply M.KeysSubset_SubList; eauto.
    - apply M.restrict_KeysSubset; auto.
      eapply M.KeysSubset_SubList; eauto.
  Qed.

  Lemma absorber_amortizeSeq_invariant:
    forall amt ll1 ll2,
      AmortizedSeq amt ll1 ll2 ->
      forall n1,
        Multistep m (initRegs (getRegInits m)) n1 ll1 ->
        forall n2,
          Multistep m (initRegs (getRegInits m)) n2 ll2 ->
          Multistep m (initRegs (getRegInits m)) n1 ((rev amt) ++ ll2).
  Proof.
    induction 1; simpl; intros; auto.
    - rewrite rev_app_distr; simpl.
      inv H0; inv H1.
      specialize (IHAmortizedSeq _ HMultistep _ HMultistep0).
      apply multistep_app in IHAmortizedSeq; dest.
      constructor; auto.
      apply multistep_app_inv with (n':= x).
      + replace x with (M.union (M.empty _) x) by meq.
        constructor; auto.
        apply step_empty; auto.
      + auto.
    - inv H0; inv H1.
      rewrite rev_app_distr; simpl.
      constructor; auto.
      replace (rev amt ++ l2 :: ll2) with (rev (l2 :: amt) ++ ll2)
        by (simpl; rewrite <-app_assoc; simpl; reflexivity).
      eapply IHAmortizedSeq; eauto.
    - inv H0; inv H1.
      constructor; eauto.
  Qed.

  Lemma traceRefinesAmortA_refl':
    forall amt sig1 sig2,
      AmortizedSeq amt sig1 sig2 ->
      forall s1,
        Multistep m (initRegs (getRegInits m)) s1 sig1 ->
        exists s2, Behavior m s2 sig2.
  Proof.
    induction 1; simpl; intros.
    - inv H; eexists; repeat constructor.
    - inv H0; specialize (IHAmortizedSeq _ HMultistep).
      destruct IHAmortizedSeq as [s2 ?].
      eexists; repeat constructor.
      + inv H0; eauto.
      + apply step_empty; auto.
    - inv H0; specialize (IHAmortizedSeq _ HMultistep); destruct IHAmortizedSeq as [s2 ?].
      inv H0; pose proof (absorber_amortizeSeq_invariant H HMultistep HMultistepBeh).
      simpl in H0.
      rewrite <-app_assoc in H0; apply multistep_app in H0.
      dest; simpl in *.
      eexists; econstructor; eauto.
    - inv H0; specialize (IHAmortizedSeq _ HMultistep); destruct IHAmortizedSeq as [s2 ?].
      inv H0; pose proof (absorber_amortizeSeq_invariant H HMultistep HMultistepBeh).
      simpl in H0.
      eexists; repeat constructor; eauto.
  Qed.

  Lemma traceRefinesAmortA_refl:
    traceRefinesAmortA id fs m m.
  Proof.
    unfold traceRefinesAmortA; intros.
    erewrite absorber_behavior_restrictLabelSeq in H0; eauto; [|inv H; eauto].
    inv H.
    pose proof (traceRefinesAmortA_refl' H0 HMultistepBeh).
    destruct H as [s2 ?].
    exists s2; exists col2; split; auto.
    split.
    - inv H.
      apply equivalentLabelSeqWithout_with.
      + pose proof (multistep_defs_ext_in Hwf HMultistepBeh).
        clear -Habs H; induction sig1; simpl; intros; auto.
        inv H; constructor; auto.
        eauto using M.KeysSubset_SubList.
      + pose proof (multistep_calls_ext_in Hwf HMultistepBeh).
        clear -Habs H; induction sig1; simpl; intros; auto.
        inv H; constructor; auto.
        eauto using M.KeysSubset_SubList.
      + pose proof (multistep_defs_ext_in Hwf HMultistepBeh0).
        clear -Habs H; induction col2; simpl; intros; auto.
        inv H; constructor; auto.
        eauto using M.KeysSubset_SubList.
      + pose proof (multistep_calls_ext_in Hwf HMultistepBeh0).
        clear -Habs H; induction col2; simpl; intros; auto.
        inv H; constructor; auto.
        eauto using M.KeysSubset_SubList.
    - inv H; eapply eq_sym, absorber_behavior_restrictLabelSeq; eauto.
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
      (m1 ++ ctxt)%kami <<== (m2 ++ ctxt)%kami.
Proof.
  intros.
  eapply traceRefinesAmort_absorbed_modular; eauto; rewrite idElementwiseId; eauto.
  apply traceRefinesAmortA_refl; auto.
Qed.

