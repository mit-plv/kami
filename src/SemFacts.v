Require Import String List Program.Equality.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Syntax Semantics.

Set Implicit Arguments.

Theorem staticDynCallsRules m o name a u cs r:
  In (name :: a)%struct (getRules m) ->
  SemAction o (a type) u cs r ->
  forall f, M.In f cs -> In f (getCalls m).
Proof.
  admit.
Qed.

Theorem staticDynCallsMeths m o name a u cs r:
  In (name :: a)%struct (getDefsBodies m) ->
  forall argument,
    SemAction o (projT2 a type argument) u cs r ->
    forall f, M.In f cs -> In f (getCalls m).
Proof.
  admit.
Qed.

Theorem staticDynCallsSubstep m o u rm cs:
  Substep m o u rm cs ->
  forall f, M.In f cs -> In f (getCalls m).
Proof.
  intro H.
  dependent induction H; simpl in *; intros.
  - apply (M.F.P.F.empty_in_iff) in H; intuition.
  - apply (M.F.P.F.empty_in_iff) in H; intuition.
  - eapply staticDynCallsRules; eauto.
  - destruct f as [name a]; simpl in *.
    eapply staticDynCallsMeths; eauto.
Qed.

Theorem staticDynDefsSubstep m o u far cs:
  Substep m o u (Meth (Some far)) cs ->
  List.In (attrName far) (getDefs m).
Proof.
  intros.
  dependent induction H; simpl in *.
  unfold getDefs in *.
  clear - HIn.
  induction (getDefsBodies m).
  - intuition.
  - simpl in *.
    destruct HIn.
    + subst.
      left; intuition.
    + right; intuition.
Qed.

Theorem staticDynCallsSubsteps m o ss:
  forall f, M.In f (calls (foldSSLabel (m := m) (o := o) ss)) -> In f (getCalls m).
Proof.
  intros.
  induction ss; simpl in *.
  - exfalso.
    apply (proj1 (M.F.P.F.empty_in_iff _ _) H).
  - unfold addLabelLeft, mergeLabel in *.
    destruct a.
    simpl in *.
    destruct unitAnnot.
    + destruct (foldSSLabel ss); simpl in *.
      pose proof (M.union_In H) as sth.
      destruct sth.
      * apply (staticDynCallsSubstep substep); intuition.
      * intuition.
    + destruct (foldSSLabel ss); simpl in *.
      dependent destruction o0; simpl in *.
      * dependent destruction a; simpl in *.
        pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply (staticDynCallsSubstep substep); intuition.
          - intuition.
        }
      * pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply (staticDynCallsSubstep substep); intuition.
          - intuition.
        }
Qed.

Theorem staticDynDefsSubsteps m o ss:
  forall f, M.In f (defs (foldSSLabel (m := m) (o := o) ss)) -> In f (getDefs m).
Proof.
  intros.
  induction ss; simpl in *.
  - exfalso.
    apply (proj1 (M.F.P.F.empty_in_iff _ _) H).
  - unfold addLabelLeft, mergeLabel in *.
    destruct a.
    simpl in *.
    destruct unitAnnot.
    + destruct (foldSSLabel ss); simpl in *.
      rewrite M.union_empty_L in H.
      intuition.
    + destruct (foldSSLabel ss); simpl in *.
      dependent destruction o0; simpl in *.
      * dependent destruction a; simpl in *.
        pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply M.F.P.F.add_in_iff in H0.
            destruct H0.
            + subst.
              apply (staticDynDefsSubstep substep).
            + exfalso; apply ((proj1 (M.F.P.F.empty_in_iff _ _)) H0).
          - intuition.
        }
      * rewrite M.union_empty_L in H.
        intuition.
Qed.

Lemma hide_mergeLabel:
  forall l1 l2,
    M.Disj (defs l1) (defs l2) ->
    M.Disj (calls l1) (calls l2) ->
    hide (mergeLabel l1 l2) = mergeLabel (hide l1) (hide l2).
Proof.
  destruct l1 as [ann1 ds1 cs1], l2 as [ann2 ds2 cs2].
  unfold hide, mergeLabel; simpl; f_equal; admit.
Qed.

Lemma substep_rule_dms_weakening:
  forall regs rules dms1 or u r cs,
    Substep (Mod regs rules dms1) or u (Rle r) cs ->
    forall dms2,
      Substep (Mod regs rules dms2) or u (Rle r) cs.
Proof.
  intros; inv H.
  - constructor; auto.
  - eapply SingleRule; eauto.
Qed.

Lemma substep_meth_none_dms_weakening:
  forall regs rules dms1 or u cs,
    Substep (Mod regs rules dms1) or u (Meth None) cs ->
    forall dms2,
      Substep (Mod regs rules dms2) or u (Meth None) cs.
Proof. intros; inv H; constructor; auto. Qed.

Lemma substepsInd_dms_weakening:
  forall regs rules dms or u l,
    SubstepsInd (Mod regs rules dms) or u l ->
    forall filt,
      M.KeysDisj (defs (hide l)) filt ->
      SubstepsInd (Mod regs rules (filterDms dms filt)) or u (hide l).
Proof.
  induction 1; intros; [constructor|subst].
  destruct sul as [sr|[[sdmn sdmv]|]].

  - eapply SubstepsCons.
    Focus 5.
    + rewrite hide_mergeLabel.
      * f_equal.
        instantiate (1:= scs); instantiate (1:= Rle sr).
        unfold hide, getLabel; simpl; f_equal.
        apply M.subtractKV_empty_2.
      * simpl; apply M.Disj_empty_1.
      * inv H1; dest; simpl; auto.
    + apply IHSubstepsInd.
      admit.
    + eapply substep_rule_dms_weakening; eauto.
    + admit.
    + auto.

  - admit.
    
  - eapply SubstepsCons.
    Focus 5.
    + rewrite hide_mergeLabel.
      * f_equal.
        instantiate (1:= scs); instantiate (1:= Meth None).
        unfold hide, getLabel; simpl; f_equal.
        apply M.subtractKV_empty_2.
      * simpl; apply M.Disj_empty_1.
      * inv H1; dest; simpl; auto.
    + apply IHSubstepsInd.
      admit.
    + eapply substep_meth_none_dms_weakening; eauto.
    + admit.
    + auto.
Qed.

Lemma hide_idempotent:
  forall (l: LabelT), hide l = hide (hide l).
Proof.
  intros; destruct l as [ann ds cs].
  unfold hide; simpl; f_equal;
  apply M.subtractKV_idempotent.
Qed.

Lemma stepInd_dms_weakening:
  forall regs rules dms or nr l,
    StepInd (Mod regs rules dms) or nr l ->
    forall filt,
      M.KeysDisj (defs l) filt ->
      StepInd (Mod regs rules (filterDms dms filt)) or nr l.
Proof.
  induction 1; intros.
  rewrite hide_idempotent.
  constructor.
  - apply substepsInd_dms_weakening; auto.
  - rewrite <-hide_idempotent.
    admit.
Qed.

Lemma step_dms_weakening:
  forall regs rules dms or nr l,
    Step (Mod regs rules dms) or nr l ->
    forall filt,
      M.KeysDisj (defs l) filt ->
      Step (Mod regs rules (filterDms dms filt)) or nr l.
Proof.
  intros; apply step_consistent; apply step_consistent in H.
  apply stepInd_dms_weakening; auto.
Qed.

Lemma merge_preserves_step:
  forall m or nr l,
    Step m or nr l ->
    Step (Mod (getRegInits m) (getRules m) (getDefsBodies m)) or nr l.
Proof.
  admit.
Qed.

