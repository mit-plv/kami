Require Import Bool List String Structures.Equalities FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax Semantics SemFacts Refinement Equiv.

Set Implicit Arguments.

Section Decomposition.
  Variable m: Modules.

  Variable P: RegsT -> Prop.

  Hypothesis HinitP: P (initRegs (getRegInits m)).

  Hypothesis HruleP:
    forall o u rule cs,
      P o ->
      Substep m o u (Rle (Some rule)) cs ->
      P (M.union u o).

  Hypothesis HmethP:
    forall o u meth cs,
      P o ->
      Substep m o u (Meth (Some meth)) cs ->
      P (M.union u o).

  Lemma substep_P:
    forall o u ul cs,
      P o ->
      Substep m o u ul cs ->
      P (M.union u o).
  Proof.
    intros; destruct ul as [[r|]|[dm|]].
    - eapply HruleP; eauto.
    - inv H0; mred.
    - eapply HmethP; eauto.
    - inv H0; mred.
  Qed.

  Hypothesis HcanCombine:
    forall o u1 u2 ul1 ul2 cs1 cs2,
      Substep m o u1 ul1 cs1 ->
      Substep m o u2 ul2 cs2 ->
      CanCombineUL u1 u2 (getLabel ul1 cs1) (getLabel ul2 cs2) ->
      u1 = M.empty _ \/ u2 = M.empty _.

  Lemma substeps_updates:
    forall o (s: SubstepRec m o)
           (ss: Substeps m o),
      (forall s' : SubstepRec m o, In s' ss -> canCombine s s') ->
      foldSSUpds ss = M.empty _ \/ upd s = M.empty _.
  Proof.
    induction ss; simpl; intros; [auto|].
    assert (forall s' : SubstepRec m o, In s' ss -> canCombine s s').
    { intros; apply H; auto. }
    specialize (IHss H0); clear H0.
    destruct IHss; auto.
    rewrite H0; mred.
    specialize (H a (or_introl eq_refl)).
    apply or_comm.
    destruct s, a; simpl in *.
    eapply HcanCombine; eauto.
    eapply canCombine_CanCombineUL; eauto.
  Qed.

  Lemma substeps_P:
    forall o,
      P o ->
      forall (ss: Substeps m o),
        substepsComb ss ->
        P (M.union (foldSSUpds ss) o).
  Proof.
    induction 2; simpl; intros; [mred|].
    apply substeps_updates in H1; destruct H1; rewrite H1.
    - mred.
      destruct s; simpl in *.
      eapply substep_P; eauto.
    - mred.
  Qed.

  Lemma multistep_P:
    forall init n ll,
      init = initRegs (getRegInits m) ->
      Multistep m init n ll ->
      P n.
  Proof.
    induction 2; [repeat subst; auto|].
    specialize (IHMultistep H); subst; clear H0.
    inv HStep; clear HWellHidden.
    apply substeps_P; auto.
  Qed.

  Lemma decompositionInv:
    forall o,
      reachable o m ->
      P o.
  Proof.
    intros; inv H; inv H0.
    eapply multistep_P; eauto.
  Qed.
      
End Decomposition.

