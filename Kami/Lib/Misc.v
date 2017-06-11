Require Import String StringAsList.

Set Implicit Arguments.
Set Asymmetric Patterns.

Theorem true_False_false: forall v, (v = true -> False) -> v = false.
Proof.
  intros.
  destruct v; intuition auto.
Qed.

Theorem false_False_true: forall v, (v = false -> False) -> v = true.
Proof.
  intros.
  destruct v; intuition auto.
Qed.

Ltac simplBool :=
  match goal with
    | H: ?v = true -> False |- _ =>
      apply true_False_false in H
    | H: ?v = false -> False |- _ =>
      apply false_False_true in H
  end.

Open Scope string.

Lemma not_in_string_uneq':
  forall a x n s, ~ S_In a s -> s <> x ++ (String a n).
Proof.
  induction x; simpl; auto; intros; intro; subst; simpl in *; [intuition auto|].
  assert (sth: ~ S_In a (x ++ String a n)) by intuition auto.
  clear - sth.
  assert ((S_In a x \/ S_In a (String a n)) -> False) by
      (intros H; apply S_in_or_app in H; intuition auto).
  assert (sth2: S_In a (String a n) -> False) by intuition auto.
  simpl in sth2.
  intuition auto.
Qed.

Lemma not_in_string_uneq:
  forall a x n s, index 0 (String a EmptyString) s = None -> s <> x ++ (String a n).
Proof.
  intros.
  apply not_in_string_uneq'.
  apply index_not_in; auto.
Qed.

Close Scope string.

