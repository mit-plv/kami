Require Import List String.
Require Import Lib.CommonTactics Lib.FMap.
Require Import Syntax Semantics SemFacts.

Set Implicit Arguments.

Fixpoint composeLabels (ls1 ls2: LabelSeqT) :=
  match ls1, ls2 with
    | l1 :: ls1', l2 :: ls2' =>
      (hide (mergeLabel l1 l2)) :: (composeLabels ls1' ls2')
    | _, _ => nil
  end.

Lemma multistep_split:
  forall ma mb s ls ir,
    Multistep (ConcatMod ma mb) ir s ls ->
    ir = initRegs (getRegInits ma ++ getRegInits mb) ->
    exists sa lsa sb lsb,
      Multistep ma (initRegs (getRegInits ma)) sa lsa /\
      Multistep mb (initRegs (getRegInits mb)) sb lsb /\
      s = M.union sa sb /\ ls = composeLabels lsa lsb.
Proof.
  induction 1.
  - do 2 (eexists; exists nil); repeat split; try constructor.
    subst. admit.

  - intros; subst.
    specialize (IHMultistep eq_refl).
    destruct IHMultistep as [sa [lsa [sb [lsb [? [? [? ?]]]]]]]; subst.
    admit.
Qed.

Lemma behavior_split:
  forall ma mb s ls,
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
  forall ma mb sa sb lsa lsb,
    Behavior ma sa lsa ->
    Behavior mb sb lsb ->
    Behavior (ConcatMod ma mb) (M.union sa sb) (composeLabels lsa lsb).
Proof.
  admit.
Qed.

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
