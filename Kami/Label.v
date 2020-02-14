Require Import Bool List String.
Require Import Lib.CommonTactics Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** This file contains following definitions/facts about label manipulation.
 * - Lifting M.restrict and M.complement to the level of labels
 * - Disjoint labels / Non-interacting labels
 * - Method labels
 * - Duality of Labels
 * - Hidden labels
 *)

(** * Lifting M.restrict and M.complement to the level of labels *)

(* Note that annot is restricted to [None]. *)
Definition restrictLabel (l: LabelT) (d: list string): LabelT :=
  {| defs := M.restrict (defs l) d;
     calls := M.restrict (calls l) d;
     annot := None |}.

Definition restrictLabelSeq (ll: LabelSeqT) (d: list string): LabelSeqT :=
  map (fun l => restrictLabel l d) ll.

Lemma restrictLabelSeq_nil:
  forall ll d, restrictLabelSeq ll d = nil -> ll = nil.
Proof.
  induction ll; simpl; intros; auto; inv H.
Qed.

Lemma restrictLabel_mergeLabel_comm:
  forall l1 l2 d, restrictLabel (mergeLabel l1 l2) d =
                  mergeLabel (restrictLabel l1 d) (restrictLabel l2 d).
Proof.
  unfold restrictLabel, mergeLabel; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2];
    simpl; intros; f_equal; apply M.restrict_union.
Qed.

Definition complementLabel (l: LabelT) (d: list string): LabelT :=
  {| defs := M.complement (defs l) d;
     calls := M.complement (calls l) d;
     annot := annot l |}.

Definition complementLabelSeq (ll: LabelSeqT) (d: list string): LabelSeqT :=
  map (fun l => complementLabel l d) ll.

Lemma complementLabel_mergeLabel_comm:
  forall l1 l2 d, complementLabel (mergeLabel l1 l2) d =
                  mergeLabel (complementLabel l1 d) (complementLabel l2 d).
Proof.
  unfold complementLabel, mergeLabel; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2];
    simpl; intros; f_equal; apply M.complement_union.
Qed.

Lemma restrictLabel_complementLabel_mergeLabel:
  forall l d, l = mergeLabel (restrictLabel l d) (complementLabel l d).
Proof.
  unfold mergeLabel, restrictLabel, complementLabel; destruct l;
    simpl; intros; f_equal; apply M.restrict_complement_union.
Qed.

(** * Disjoint / Non-interacting labels: see the below definitions for difference *)

Definition DisjLabel (l1 l2: LabelT) :=
  M.Disj (defs l1) (defs l2) /\ M.Disj (calls l1) (calls l2).
Definition NonInteractingLabel (l1 l2: LabelT) :=
  M.Disj (defs l1) (calls l2) /\ M.Disj (defs l2) (calls l1).
Inductive DisjLabelSeq: LabelSeqT -> LabelSeqT -> Prop :=
| DLSNil: DisjLabelSeq nil nil
| DLSCons: forall ll1 ll2,
    DisjLabelSeq ll1 ll2 ->
    forall l1 l2,
      DisjLabel l1 l2 -> DisjLabelSeq (l1 :: ll1) (l2 :: ll2).

Lemma disjLabel_restrictLabel:
  forall l1 l2,
    DisjLabel l1 l2 ->
    forall d1 d2, DisjLabel (restrictLabel l1 d1) (restrictLabel l2 d2).
Proof.
  unfold DisjLabel, restrictLabel; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2];
    simpl; intros; split.
  - apply M.DomainSubset_Disj with (m2:= d1); [|apply M.restrict_DomainSubset].
    apply M.Disj_comm, M.DomainSubset_Disj with (m2:= d2); [|apply M.restrict_DomainSubset].
    apply M.Disj_comm; auto.
  - apply M.DomainSubset_Disj with (m2:= c1); [|apply M.restrict_DomainSubset].
    apply M.Disj_comm, M.DomainSubset_Disj with (m2:= c2); [|apply M.restrict_DomainSubset].
    apply M.Disj_comm; auto.
Qed.

Lemma disjLabel_complementLabel:
  forall l1 l2,
    DisjLabel l1 l2 ->
    forall d1 d2, DisjLabel (complementLabel l1 d1) (complementLabel l2 d2).
Proof.
  unfold DisjLabel, complementLabel; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2];
    simpl; intros; split.
  - apply M.DomainSubset_Disj with (m2:= d1); [|apply M.complement_DomainSubset].
    apply M.Disj_comm, M.DomainSubset_Disj with (m2:= d2); [|apply M.complement_DomainSubset].
    apply M.Disj_comm; auto.
  - apply M.DomainSubset_Disj with (m2:= c1); [|apply M.complement_DomainSubset].
    apply M.Disj_comm, M.DomainSubset_Disj with (m2:= c2); [|apply M.complement_DomainSubset].
    apply M.Disj_comm; auto.
Qed.

Lemma restrictLabel_complementLabel_DisjLabel:
  forall l d, DisjLabel (restrictLabel l d) (complementLabel l d).
Proof.
  unfold DisjLabel, restrictLabel, complementLabel; destruct l as [a d c]; simpl; intros.
  split; apply M.restrict_complement_disj.
Qed.
  
Lemma restrictLabel_complementLabel_NonInteractingLabel:
  forall l d, NonInteractingLabel (restrictLabel l d) (complementLabel l d).
Proof.
  unfold NonInteractingLabel, restrictLabel, complementLabel;
    destruct l as [a d c]; simpl; intros.
  split; auto using M.Disj_comm, M.restrict_complement_disj.
Qed.

Lemma disjLabel_NonInteractingLabel_hide_mergeLabel:
  forall l1 l2,
    DisjLabel l1 l2 -> NonInteractingLabel l1 l2 ->
    hide (mergeLabel l1 l2) = mergeLabel (hide l1) (hide l2).
Proof.
  unfold DisjLabel, NonInteractingLabel, hide, mergeLabel;
    destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2]; simpl; intros; dest.
  f_equal.
  - repeat rewrite M.subtractKV_disj_union_1 by assumption.
    rewrite M.union_comm with (m1:= c1) (m2:= c2) at 1 by assumption.
    repeat rewrite M.subtractKV_disj_union_2 by eauto using M.Disj_comm.
    rewrite M.subtractKV_disj_invalid with (m1:= d1) (m2:= c2) by assumption.
    rewrite M.subtractKV_disj_invalid with (m1:= d2) (m2:= c1) by assumption.
    reflexivity.
  - repeat rewrite M.subtractKV_disj_union_1 by assumption.
    rewrite M.union_comm with (m1:= d1) (m2:= d2) at 1 by assumption.
    repeat rewrite M.subtractKV_disj_union_2 by eauto using M.Disj_comm.
    rewrite M.subtractKV_disj_invalid with (m1:= c1) (m2:= d2) by eauto using M.Disj_comm.
    rewrite M.subtractKV_disj_invalid with (m1:= c2) (m2:= d1) by eauto using M.Disj_comm.
    reflexivity.
Qed.

Lemma disjList_KeysSubset_DisjLabel:
  forall l1 l2 d1 c1 d2 c2,
    M.KeysSubset (defs l1) d1 -> M.KeysSubset (calls l1) c1 ->
    M.KeysSubset (defs l2) d2 -> M.KeysSubset (calls l2) c2 ->
    DisjList d1 d2 -> DisjList c1 c2 ->
    DisjLabel l1 l2.
Proof.
  unfold DisjLabel; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2]; simpl; intros.
  split; eauto using M.DisjList_KeysSubset_Disj.
Qed.

Lemma disjList_KeysSubset_NonInteractingLabel:
  forall l1 l2 d1 c1 d2 c2,
    M.KeysSubset (defs l1) d1 -> M.KeysSubset (calls l1) c1 ->
    M.KeysSubset (defs l2) d2 -> M.KeysSubset (calls l2) c2 ->
    DisjList d1 c2 -> DisjList d2 c1 ->
    NonInteractingLabel l1 l2.
Proof.
  unfold NonInteractingLabel; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2]; simpl; intros.
  split; eauto using M.DisjList_KeysSubset_Disj.
Qed.

Lemma validLabel_complementLabel_NonInteractingLabel:
  forall d1 c1 d2 c2 fs l1 l2,
    M.KeysSubset (defs l1) d1 -> M.KeysSubset (calls l1) c1 ->
    M.KeysSubset (defs l2) d2 -> M.KeysSubset (calls l2) c2 ->
    (forall f, In f c1 /\ In f d2 -> In f fs) ->
    (forall f, In f d1 /\ In f c2 -> In f fs) ->
    NonInteractingLabel (complementLabel l1 fs) (complementLabel l2 fs).
Proof.
  unfold NonInteractingLabel, complementLabel;
    destruct l1 as [la1 ld1 lc1], l2 as [la2 ld2 lc2]; simpl; intros; split.
  - intro y.
    repeat rewrite M.F.P.F.not_find_in_iff, M.complement_find.
    destruct (in_dec M.F.P.F.eq_dec y fs); auto.
    remember (M.find y ld1) as dv1; destruct dv1; auto.
    remember (M.find y lc2) as cv2; destruct cv2; auto.
    elim n; apply H4; split.
    + apply H; findeq.
    + apply H2; findeq.
  - intro y.
    repeat rewrite M.F.P.F.not_find_in_iff, M.complement_find.
    destruct (in_dec M.F.P.F.eq_dec y fs); auto.
    remember (M.find y ld2) as dv2; destruct dv2; auto.
    remember (M.find y lc1) as cv1; destruct cv1; auto.
    elim n; apply H3; split.
    + apply H0; findeq.
    + apply H1; findeq.
Qed.

(** * Method labels *)

Definition MethLabel (l: LabelT) := annot l = None.

Inductive MethLabelSeq: LabelSeqT -> Prop :=
| MLSNil: MethLabelSeq nil
| MLSCons: forall ll,
    MethLabelSeq ll ->
    forall l, MethLabel l -> MethLabelSeq (l :: ll).

Lemma methLabelSeq_app:
  forall ll1 ll2,
    MethLabelSeq ll1 -> MethLabelSeq ll2 -> MethLabelSeq (ll1 ++ ll2).
Proof.
  induction ll1; simpl; intros; auto.
  inv H; constructor; auto.
Qed.

Lemma methLabelSeq_rev:
  forall ll, MethLabelSeq ll -> MethLabelSeq (rev ll).
Proof.
  induction 1; simpl; intros; [constructor|].
  apply methLabelSeq_app; auto.
  constructor; auto.
  constructor.
Qed.

Lemma restrictLabel_MethLabel: forall l fs, MethLabel (restrictLabel l fs).
Proof. firstorder. Qed.

Lemma restrictLabelSeq_MethLabelSeq: forall ll fs, MethLabelSeq (restrictLabelSeq ll fs).
Proof.
  induction ll; simpl; constructor.
  - intuition.
  - apply restrictLabel_MethLabel.
Qed.

(** * Duality of Labels *)

Definition Dual (l1 l2: LabelT) := defs l1 = calls l2 /\ calls l1 = defs l2.
Inductive DualSeq: LabelSeqT -> LabelSeqT -> Prop :=
| DSNil: DualSeq nil nil
| DSCons: forall ll1 ll2,
    DualSeq ll1 ll2 ->
    forall l1 l2,
      Dual l1 l2 ->
      DualSeq (l1 :: ll1) (l2 :: ll2).

Definition dualOf (l: LabelT) :=
  {| annot := annot l; defs := calls l; calls := defs l |}.
Fixpoint dualSeqOf (ll: LabelSeqT) :=
  match ll with
  | nil => nil
  | l :: ll' => dualOf l :: dualSeqOf ll'
  end.

Lemma dualOf_dual: forall l, Dual l (dualOf l).
Proof. firstorder. Qed.

Lemma dualSeqOf_dualSeq: forall ll, DualSeq ll (dualSeqOf ll).
Proof. induction ll; simpl; constructor; firstorder. Qed.

Lemma dualOf_methLabel: forall l, MethLabel l -> MethLabel (dualOf l).
Proof. firstorder. Qed.

Lemma dualSeqOf_methLabelSeq: forall ll, MethLabelSeq ll -> MethLabelSeq (dualSeqOf ll).
Proof.
  induction ll; simpl; intros; auto.
  inv H; constructor; auto.
Qed.

Lemma dual_sym: forall l1 l2, Dual l1 l2 -> Dual l2 l1.
Proof. firstorder. Qed.

Lemma dual_methLabel_trans:
  forall l1 l2 l3, Dual l1 l2 -> Dual l1 l3 -> MethLabel l2 -> MethLabel l3 -> l2 = l3.
Proof.
  destruct l1, l2, l3; unfold Dual, MethLabel; simpl;
    intros; dest; repeat subst; auto.
Qed.

Lemma dual_emptyMethLabel:
  forall l, Dual emptyMethLabel l -> MethLabel l -> l = emptyMethLabel.
Proof.
  destruct l; unfold Dual, MethLabel; simpl; intros; dest; subst; auto.
Qed.

Lemma restrictLabel_dual_implies:
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

Lemma dualSeqOf_app:
  forall all1 bll1 all2 bll2,
    DualSeq all1 all2 -> DualSeq bll1 bll2 -> DualSeq (all1 ++ bll1) (all2 ++ bll2).
Proof.
  induction 1; simpl; intros; auto.
  constructor; auto.
Qed.

Lemma dualSeqOf_rev:
  forall ll1 ll2, DualSeq ll1 ll2 -> DualSeq (rev ll1) (rev ll2).
Proof.
  induction 1; simpl; intros; [constructor|].
  apply dualSeqOf_app; auto.
  constructor; auto.
  constructor.
Qed.

Lemma dualSeqOf_cons_rev:
  forall ll1 l1 mll2,
    DualSeq (ll1 ++ [l1]) mll2 ->
    exists ll2 l2, mll2 = ll2 ++ [l2] /\ DualSeq ll1 ll2 /\ Dual l1 l2.
Proof.
  induction ll1; simpl; intros.
  - inv H; inv H2.
    exists nil, l2; intuition.
    constructor.
  - inv H.
    specialize (IHll1 _ _ H2); dest; subst.
    exists (l2 :: x), x0; intuition.
    constructor; auto.
Qed.

Lemma dual_DisjLabel_hide_mergeLabel:
  forall l1 l2,
    Dual l1 l2 -> DisjLabel l1 l2 ->
    defs (hide (mergeLabel l1 l2)) = M.empty _ /\
    calls (hide (mergeLabel l1 l2)) = M.empty _.
Proof.
  unfold Dual, DisjLabel, hide, mergeLabel;
    destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2]; simpl; intros; dest; subst.
  rewrite M.union_comm by assumption.
  rewrite M.subtractKV_empty_3; auto.
Qed.

Lemma dual_restrictLabel_hide_mergeLabel_complementLabel:
  forall d l1 l2,
    Dual (restrictLabel l1 d) (restrictLabel l2 d) ->
    DisjLabel l1 l2 ->
    hide (mergeLabel l1 l2) =
    hide (mergeLabel (complementLabel l1 d) (complementLabel l2 d)).
Proof.
  intros.
  rewrite restrictLabel_complementLabel_mergeLabel with (l:= mergeLabel l1 l2) (d:= d).
  pose proof (restrictLabel_complementLabel_NonInteractingLabel (mergeLabel l1 l2) d).
  inv H1; rewrite hide_mergeLabel_disj by eauto using M.Disj_comm; clear H2 H3.
  rewrite restrictLabel_mergeLabel_comm.
  apply disjLabel_restrictLabel with (d1:= d) (d2:= d) in H0.
  pose proof (dual_DisjLabel_hide_mergeLabel H H0).
  remember (hide (mergeLabel (restrictLabel l1 d) (restrictLabel l2 d))) as rl.
  rewrite complementLabel_mergeLabel_comm.
  remember (hide (complementLabel (mergeLabel l1 l2) d)) as cl.
  destruct rl as [ra rd rc], cl as [ca cd cc]; simpl in *; dest; subst; mred.
  f_equal.
  destruct ra, ca; auto; inv Heqrl.
Qed.

(** * Hidden Labels *)

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

Lemma behavior_hiddenSeq: forall m ll n, Behavior m n ll -> HiddenSeq ll.
Proof. intros; inv H; eapply multistep_hiddenSeq; eauto. Qed.

Lemma hidden_complementLabel:
  forall l, Hidden l -> forall dom, Hidden (complementLabel l dom).
Proof.
  unfold Hidden, hide, complementLabel; destruct l as [a d c]; simpl; intros.
  f_equal.
  - assert (M.subtractKV signIsEq d c = d) by (inversion_clear H; auto); clear H.
    M.ext y; apply M.Equal_val with (k:= y) in H0.
    findeq; repeat rewrite M.complement_find.
    destruct (in_dec M.F.P.F.eq_dec y dom); auto.
  - assert (M.subtractKV signIsEq c d = c) by (inversion_clear H; auto); clear H.
    M.ext y; apply M.Equal_val with (k:= y) in H0.
    findeq; repeat rewrite M.complement_find.
    destruct (in_dec M.F.P.F.eq_dec y dom); auto.
Qed.

