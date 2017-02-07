Require Import Bool List String Omega.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.
Require Import Kami.ModularFacts Kami.RefinementFacts.

Set Implicit Arguments.
Set Asymmetric Patterns.

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

(** The notion of dual *)

Definition Dual (l1 l2: LabelT): Prop :=
  defs l1 = calls l2 /\ calls l1 = defs l2.

Inductive DualSeq: LabelSeqT -> LabelSeqT -> Prop :=
| DualSeqNil: DualSeq nil nil
| DualSeqCons:
    forall ll1 ll2,
      DualSeq ll1 ll2 ->
      forall l1 l2,
        Dual l1 l2 -> DualSeq (l1 :: ll1) (l2 :: ll2).

Definition DualComm (q: LabelSeqT -> LabelSeqT) :=
  forall ll1 ll2,
    DualSeq ll1 ll2 ->
    DualSeq (q ll1) (q ll2).

Lemma dual_restrictLabel:
  forall l1 l2 fs,
    Dual (restrictLabel l1 fs) (restrictLabel l2 fs) ->
    forall f, In f fs -> M.find f (defs l1) = M.find f (calls l2) /\
                         M.find f (calls l1) = M.find f (defs l2).
Proof.
  unfold Dual, restrictLabel; simpl; intros; dest; split.
  - apply M.Equal_val with (k:= f) in H.
    rewrite 2! M.restrict_find in H.
    destruct (in_dec _ f fs); intuition idtac.
  - apply M.Equal_val with (k:= f) in H1.
    rewrite 2! M.restrict_find in H1.
    destruct (in_dec _ f fs); intuition idtac.
Qed.

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

  Definition traceRefinesSep q m1 m2 :=
    forall s1 sig1,
      Behavior m1 s1 sig1 ->
      exists s2 sig2, Behavior m2 s2 sig2 /\
                      EquivalentLabelSeqWithout sig1 sig2 /\
                      q (restrictLabelSeq sig1 fs) = restrictLabelSeq sig2 fs.

End AboutCertainMethods.

Notation "ma <<~[ p ]{ q , fs } mb" :=
  (traceRefinesSep (liftToMap1 p) fs q ma mb)
    (at level 100, format "ma  <<~[  p  ]{  q ,  fs  }  mb").

(*** TODO: move to SemFacts.v *)

Lemma validLabel_wellHidden_getExtDefs:
  forall m l, ValidLabel m l -> wellHidden m l -> M.KeysSubset (defs l) (getExtDefs m).
Proof.
  unfold ValidLabel, wellHidden; intros; dest.
  clear H1 H2.
  unfold M.KeysSubset, M.KeysDisj in *; intros.
  specialize (H k H1).
  specialize (H0 k).
  destruct (in_dec string_dec k (getCalls m)); intuition idtac.
  apply filter_In; split; auto.
  apply negb_true_iff.
  remember (string_in k (getCalls m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; elim n; auto.
Qed.

Lemma validLabel_wellHidden_getExtCalls:
  forall m l, ValidLabel m l -> wellHidden m l -> M.KeysSubset (calls l) (getExtCalls m).
Proof.
  unfold ValidLabel, wellHidden; intros; dest.
  clear H H0.
  unfold M.KeysSubset, M.KeysDisj in *; intros.
  specialize (H2 k H).
  specialize (H1 k).
  destruct (in_dec string_dec k (getDefs m)); intuition idtac.
  apply filter_In; split; auto.
  apply negb_true_iff.
  remember (string_in k (getDefs m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; elim n; auto.
Qed.

Definition Hidden (l: LabelT) := hide l = l.
Definition HiddenSeq (ll: LabelSeqT) := Forall (fun l => Hidden l) ll.

Lemma hide_hidden: forall l, Hidden (hide l).
Proof.
  unfold Hidden; intros.
  apply eq_sym, hide_idempotent.
Qed.

Lemma step_hidden: forall m o u l, Step m o u l -> Hidden l.
Proof.
  intros; inv H.
  apply hide_hidden.
Qed.

Lemma multistep_hiddenSeq: forall m o ll n, Multistep m o n ll -> HiddenSeq ll.
Proof.
  induction ll; simpl; intros; [constructor|].
  constructor; inv H.
  - eauto using step_hidden.
  - eapply IHll; eauto.
Qed.

Lemma extDefs_calls_disj:
  forall m, DisjList (getExtDefs m) (getCalls m).
Proof.
  unfold DisjList; intros.
  destruct (in_dec string_dec e (getExtDefs m)) as [Hin|Hin].
  - right; intro Hx; unfold getExtDefs in *.
    apply filter_In in Hin; dest.
    apply negb_true_iff, eq_sym, string_in_dec_not_in in H0; auto.
  - left; auto.
Qed.

Lemma extCalls_defs_disj:
  forall m, DisjList (getExtCalls m) (getDefs m).
Proof.
  unfold DisjList; intros.
  destruct (in_dec string_dec e (getExtCalls m)) as [Hin|Hin].
  - right; intro Hx; unfold getExtCalls in *.
    apply filter_In in Hin; dest.
    apply negb_true_iff, eq_sym, string_in_dec_not_in in H0; auto.
  - left; auto.
Qed.

Lemma extDefs_extCalls_disj:
  forall m, DisjList (getExtDefs m) (getExtCalls m).
Proof.
  intros; apply DisjList_comm, DisjList_SubList with (l1:= getCalls m).
  - apply getExtCalls_getCalls.
  - apply DisjList_comm, extDefs_calls_disj.
Qed.

Lemma getCalls_not_getDefs_getExtCalls:
  forall m k, In k (getCalls m) -> ~ In k (getDefs m) -> In k (getExtCalls m).
Proof.
  intros; unfold getExtCalls.
  apply filter_In; split; auto.
  remember (string_in k (getDefs m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; auto.
Qed.

Lemma getDefs_not_getCalls_getExtDefs:
  forall m k, In k (getDefs m) -> ~ In k (getCalls m) -> In k (getExtDefs m).
Proof.
  intros; unfold getExtCalls.
  apply filter_In; split; auto.
  remember (string_in k (getCalls m)) as kin; destruct kin; auto.
  apply string_in_dec_in in Heqkin; auto.
Qed.

(*** End *)

Definition NonInteractingExcept (fs: list string) (m1 m2: Modules) :=
  (forall f, In f (getExtCalls m1) -> In f (getExtDefs m2) -> In f fs) /\
  (forall f, In f (getExtDefs m1) -> In f (getExtCalls m2) -> In f fs).

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

  Lemma nonInteractingExcept_Dual:
    forall fs,
      NonInteractingExcept fs m1 m2 ->
      forall l1 l2,
        Hidden l1 -> Hidden l2 ->
        Dual (restrictLabel l1 fs) (restrictLabel l2 fs) ->
        WellHiddenModular m1 m2 l1 l2.
  Proof.
    unfold WellHiddenModular; intros.

    rewrite H0 in H5; rewrite H1 in H6; clear H0 H1.

    assert (M.Disj (defs l1) (defs l2)) by
        (eapply M.DisjList_KeysSubset_Disj; [exact Hddisj|apply H3|apply H4]).
    assert (M.Disj (calls l1) (calls l2)) by
        (eapply M.DisjList_KeysSubset_Disj; [exact Hcdisj|apply H3|apply H4]).

    pose proof (validLabel_wellHidden_getExtDefs H3 H5).
    pose proof (validLabel_wellHidden_getExtCalls H3 H5).
    pose proof (validLabel_wellHidden_getExtDefs H4 H6).
    pose proof (validLabel_wellHidden_getExtCalls H4 H6).
    clear H3 H4 H5 H6.

    assert (M.Disj (defs l1) (calls l1)) by
        (eapply M.DisjList_KeysSubset_Disj;
         [eapply extDefs_extCalls_disj with (m:= m1)|assumption|assumption]).
    assert (M.Disj (defs l2) (calls l2)) by
        (eapply M.DisjList_KeysSubset_Disj;
         [eapply extDefs_extCalls_disj with (m:= m2)|assumption|assumption]).

    destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2]; unfold wellHidden; simpl in *.
    split.

    - rewrite M.subtractKV_disj_union_1 by assumption.
      rewrite 2! M.subtractKV_disj_union_2 by assumption.
      rewrite M.subtractKV_disj_invalid with (m3:= d1) (m4:= c1) by assumption.
      rewrite M.subtractKV_disj_invalid with (m3:= (M.subtractKV signIsEq d2 c1))
        by (apply M.subtractKV_disj_1; auto).
      apply M.KeysDisj_union.
      + eapply M.KeysDisj_SubList; [|eapply getCalls_subList_2].
        apply M.KeysDisj_app.
        * apply M.subtractKV_KeysDisj_1.
          eapply DisjList_KeysSubset_KeysDisj.
          -- apply extDefs_calls_disj.
          -- assumption.
        * pose proof (dual_restrictLabel H2) as Hdr; simpl in Hdr.
          apply M.subtractKV_KeysDisj_2; intros.
          apply Hdr, (proj2 H).
          -- apply H7; findeq.
          -- apply getCalls_not_getDefs_getExtCalls; auto.
             destruct (Hddisj k); auto.
             elim H11; apply getExtDefs_getDefs; apply H7; findeq.
      + eapply M.KeysDisj_SubList; [|eapply getCalls_subList_2].
        apply M.KeysDisj_app.
        * pose proof (dual_restrictLabel H2) as Hdr; simpl in Hdr.
          apply M.subtractKV_KeysDisj_2; intros.
          apply eq_sym, Hdr, (proj1 H).
          -- apply getCalls_not_getDefs_getExtCalls; auto.
             destruct (Hddisj k); auto.
             elim H11; apply getExtDefs_getDefs; apply H9; findeq.
          -- apply H9; findeq.
        * apply M.subtractKV_KeysDisj_1.
          eapply DisjList_KeysSubset_KeysDisj.
          -- apply extDefs_calls_disj.
          -- assumption.
    - rewrite M.subtractKV_disj_union_1 by assumption.
      rewrite 2! M.subtractKV_disj_union_2 by assumption.
      rewrite M.subtractKV_disj_invalid with (m3:= c1) (m4:= d1)
        by (apply M.Disj_comm; assumption).
      rewrite M.subtractKV_disj_invalid with (m3:= (M.subtractKV signIsEq c2 d1))
        by (apply M.subtractKV_disj_1; auto).
      apply M.KeysDisj_union.
      + rewrite getDefs_app; apply M.KeysDisj_app.
        * apply M.subtractKV_KeysDisj_1.
          eapply DisjList_KeysSubset_KeysDisj.
          -- apply extCalls_defs_disj.
          -- assumption.
        * pose proof (dual_restrictLabel H2) as Hdr; simpl in Hdr.
          apply M.subtractKV_KeysDisj_2; intros.
          apply Hdr, (proj1 H).
          -- apply H8; findeq.
          -- apply getDefs_not_getCalls_getExtDefs; auto.
             destruct (Hcdisj k); auto.
             elim H11; apply getExtCalls_getCalls; apply H8; findeq.
      + rewrite getDefs_app; apply M.KeysDisj_app.
        * pose proof (dual_restrictLabel H2) as Hdr; simpl in Hdr.
          apply M.subtractKV_KeysDisj_2; intros.
          apply eq_sym, Hdr, (proj2 H).
          -- apply getDefs_not_getCalls_getExtDefs; auto.
             destruct (Hcdisj k); auto.
             elim H11; apply getExtCalls_getCalls; apply H10; findeq.
          -- apply H10; findeq.
        * apply M.subtractKV_KeysDisj_1.
          eapply DisjList_KeysSubset_KeysDisj.
          -- apply extCalls_defs_disj.
          -- assumption.
  Qed.

  Lemma nonInteractingExcept_DualSeq:
    forall fs,
      NonInteractingExcept fs m1 m2 ->
      forall ll1 ll2,
        HiddenSeq ll1 -> HiddenSeq ll2 ->
        DualSeq (restrictLabelSeq ll1 fs) (restrictLabelSeq ll2 fs) ->
        WellHiddenModularSeq m1 m2 ll1 ll2.
  Proof.
    induction ll1 as [|l1 ll1]; simpl; intros;
      [inv H2; apply eq_sym, restrictLabelSeq_nil in H3; subst; constructor|].

    destruct ll2 as [|l2 ll2]; inv H2.
    inv H0; inv H1.
    constructor; auto.
    eauto using nonInteractingExcept_Dual.
  Qed.

  Lemma equivalentLabelSeqWithout_WellHiddenModularSeq:
    forall p fs ll1 ll2 lsa lsb,
      NonInteractingExcept fs m1 m2 ->
      HiddenSeq ll1 -> HiddenSeq ll2 ->
      EquivalentLabelSeqWithout p fs lsa ll1 ->
      EquivalentLabelSeqWithout p fs lsb ll2 ->
      forall q,
        DualComm q ->
        q (restrictLabelSeq lsa fs) = restrictLabelSeq ll1 fs ->
        q (restrictLabelSeq lsb fs) = restrictLabelSeq ll2 fs ->
        DisjList (getExtMeths (m1 ++ m2)%kami) fs ->
        WellHiddenConcatSeq m1 m2 lsa lsb ->
        forall m3 m4 n3 n4,
          (* SubInterface m3 m1 -> SubInterface m4 m2 -> *)
          Multistep m3 (initRegs (getRegInits m3)) n3 ll1 ->
          Multistep m4 (initRegs (getRegInits m4)) n4 ll2 ->
          WellHiddenModularSeq m3 m4 ll1 ll2.
  Proof.
    intros.

    (* Step 1: All internal communication should belong to "fs." *)
    assert (DualSeq (restrictLabelSeq lsa fs) (restrictLabelSeq lsb fs)).
    { admit. }
    
    (* Step 2: "q" preserves duality. *)
    assert (DualSeq (restrictLabelSeq ll1 fs) (restrictLabelSeq ll2 fs)).
    { rewrite <-H5, <-H6; apply H4; auto. }
    
    (* Step 3: We don't need to consider external defs/calls for this lemma.
     In other words, we only need the duality for proving the well-hidden property! *)
    (* clear -H H10. *)
    eauto using nonInteractingExcept_DualSeq.
  Admitted.

End TwoModuleFacts.
  
Section Modularity.
  
  Variables (m1 m2 m3 m4: Modules).
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hwf3: ModEquiv type typeUT m3)
             (Hwf4: ModEquiv type typeUT m4)
             (Hrdisj12: DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2)))
             (Hrdisj34: DisjList (namesOf (getRegInits m3)) (namesOf (getRegInits m4)))
             (Hddisj12: DisjList (getDefs m1) (getDefs m2))
             (Hcdisj12: DisjList (getCalls m1) (getCalls m2))
             (Hddisj34: DisjList (getDefs m3) (getDefs m4))
             (Hcdisj34: DisjList (getCalls m3) (getCalls m4))
             (Hvr12: ValidRegsModules type (m1 ++ m2)%kami)
             (Hvr34: ValidRegsModules type (m3 ++ m4)%kami).

  Section NonInteractingExcept.
    Variable fs: list string.
    Hypothesis (Hpni: NonInteractingExcept fs m1 m2).

    Theorem traceRefinesSep_modular:
      forall vp q,
        DualComm q ->
        traceRefinesSep (liftToMap1 vp) fs q m1 m3 ->
        traceRefinesSep (liftToMap1 vp) fs q m2 m4 ->
        DisjList (getExtMeths (m1 ++ m2)%kami) fs ->
        (m1 ++ m2)%kami <<=[vp] (m3 ++ m4)%kami.
    Proof.
      unfold traceRefines; intros.
      
      apply behavior_split in H3; auto.
      destruct H3 as [sa [lsa [sb [lsb ?]]]]; dest; subst.

      specialize (H0 _ _ H3); clear H3; destruct H0 as [s3 [ll3 ?]]; dest.
      specialize (H1 _ _ H4); clear H4; destruct H1 as [s4 [ll4 ?]]; dest.

      exists (M.union s3 s4).
      exists (composeLabels ll3 ll4).

      split.
      - apply behavior_modular; auto.
        + inv H0; inv H1; eauto using equivalentLabelSeqWithout_CanCombineLabelSeq.
        + inv H0; inv H1.
          pose proof (multistep_hiddenSeq HMultistepBeh).
          pose proof (multistep_hiddenSeq HMultistepBeh0).
          eauto using equivalentLabelSeqWithout_WellHiddenModularSeq.
      - admit.
    Admitted.

  End NonInteractingExcept.

End Modularity.

