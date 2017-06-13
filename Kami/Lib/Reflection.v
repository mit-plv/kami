Require Import Bool String List.
Require Import Lib.CommonTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Fixpoint noDupStr (l: list string) :=
  match l with
  | nil => true
  | h :: t =>
    if in_dec string_dec h t then false else noDupStr t
  end.

Lemma noDupStr_NoDup:
  forall l, noDupStr l = true -> NoDup l.
Proof.
  induction l; simpl; intros; [constructor|].
  destruct (in_dec string_dec _ _); [inv H|].
  constructor; auto.
Qed.

Ltac noDup_tac :=
  vm_compute; apply noDupStr_NoDup; reflexivity.

Section BoolListReflection.
  Variable A: Type.
  Variable f: A -> bool.

  Definition evalBoolList ls := fold_left (fun b a => b && f a) ls true.

  Lemma fold_left_true ls: forall v, fold_left (fun b a => b && f a) ls v = true -> v = true.
  Proof.
    induction ls; simpl in *; intros; auto.
    specialize (IHls _ H).
    destruct v; auto.
  Qed.

  Lemma fold_left_and_true ls: forall v1 v2,
      fold_left (fun b a => b && f a) ls (v1 && v2) = true ->
      v2 = true /\ fold_left (fun b a => b && f a) ls v1 = true.
  Proof.
    induction ls; simpl in *; intros; auto.
    destruct v1, v2; auto.
    assert (v1 && v2 && f a = (v1 && f a) && v2) by (destruct v1, v2, (f a); auto).
    rewrite H0 in H.
    specialize (IHls _ _ H); dest; auto.
  Qed.

  Lemma evalBoolList_cons ls: forall a, evalBoolList (a :: ls) = true ->
                                        f a = true /\ evalBoolList ls = true.
  Proof.
    unfold evalBoolList.
    induction ls; auto; intros; simpl in *.
    pose proof (fold_left_true _ _ H).
    apply andb_true_iff in H0; dest.
    apply fold_left_and_true in H; dest.
    constructor; auto; subst.
    rewrite H1.
    specialize (IHls _ H2); dest.
    auto.
  Qed.
  
  Lemma boolListReflection ls: evalBoolList ls = true -> forall x, In x ls -> f x = true.
  Proof.
    induction ls; simpl in *; auto; intros; simpl in *.
    apply evalBoolList_cons in H; dest.
    destruct H0; subst; auto.
  Qed.
  
End BoolListReflection.

