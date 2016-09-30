Require Import List String.

Set Implicit Arguments.
Set Asymmetric Patterns.

Fixpoint concat A (ls: list (list A)): list A :=
  match ls with
    | x :: xs => x ++ concat xs
    | nil => nil
  end.

Section concat_app.
  Variable A: Type.
  Lemma concat_app: forall l1 l2: list (list A), concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof.
    induction l1; simpl in *; auto; intros.
    rewrite <- app_assoc.
    f_equal; auto.
  Qed.
End concat_app.

Section NoDup.
  Variable A: Type.
  Lemma noDupApp l1: forall l2, NoDup l1 -> NoDup l2 ->
                                (forall i: A, In i l1 -> ~ In i l2) ->
                                NoDup (l1 ++ l2).
  Proof.
    induction l1; simpl in *; intros.
    - intuition.
    - inversion H; clear H; subst.
      specialize (IHl1 _ H5 H0).
      assert (forall i, In i l1 -> ~ In i l2) by (intros; apply H1; intuition).
      specialize (IHl1 H).
      assert (~ In a l2) by (intros; apply H1; auto).
      constructor; auto.
      unfold not; intros K; apply in_app_or in K.
      destruct K; intuition auto.
  Qed.
End NoDup.

Section AboutConcat.
  Variable A: Type.

  Lemma in_concat_iff (ls: list (list A)):
    forall x,
      In x (concat ls) <-> exists l, In l ls /\ In x l.
  Proof.
    induction ls; simpl in *; auto; intros; intuition auto.
    destruct H as [? [? ?]]; auto.
    apply in_app_or in H.
    destruct H.
    exists a; intuition auto.
    pose proof (proj1 (IHls _) H).
    destruct H0 as [? [? ?]].
    exists x0; auto.
    destruct H as [? [? ?]].
    destruct H; subst; auto; apply in_or_app; auto.
    pose proof (proj2 (IHls _) (ex_intro _ x0 (conj H H0))).
    auto.
  Qed.

  Lemma in_concat_iff2 (ls: list (list A)):
    forall x,
      In x (concat ls) <-> exists i, In x (nth i ls nil).
  Proof.
    induction ls; simpl in *; auto; intros; intuition auto.
    destruct H as [? ?].
    destruct x0; intuition auto.
    apply in_app_or in H.
    destruct H.
    exists 0; intuition auto.
    pose proof (proj1 (IHls _) H).
    destruct H0 as [? ?]. 
    exists (S x0); auto.
    destruct H; subst; auto; apply in_or_app; auto.
    destruct x0; auto.
    pose proof (proj2 (IHls _) (ex_intro _ x0 H)).
    auto.
  Qed.


  Variable B: Type.
  Variable f: A -> B.
  Lemma map_concat: forall (l: list (list A)) x, In x (map f (concat l)) ->
                                                 In x (concat (map (map f) l)).
  Proof.
    induction l; simpl in *; auto; intros.
    rewrite map_app in *.
    apply in_app_or in H.
    apply in_or_app.
    destruct H; auto.
  Qed.
End AboutConcat.

