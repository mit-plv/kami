Require Import Coq.Structures.OrderedType String Lib.StringAsOT.

Module StringString_as_OT <: OrderedType.
  Definition t := (string * string)%type.

  Definition string_compare str1 str2 :=
    match String_as_OT.string_compare (fst str1) (fst str2), String_as_OT.string_compare (snd str1) (snd str2) with
      | Lt, _ => Lt
      | Eq, x => x
      | Gt, _ => Gt
    end.

  Lemma string_compare_eq_refl : forall x, string_compare x x = Eq.
    unfold string_compare; intros.
    rewrite? String_as_OT.string_compare_eq_refl.
    reflexivity.
  Qed.

  Definition eq := @eq (string * string).

  Lemma eq_Eq : forall x y, x = y -> string_compare x y = Eq.
  Proof.
    intros; subst.
    rewrite string_compare_eq_refl; reflexivity.
  Qed.

  Lemma Eq_eq : forall x y, string_compare x y = Eq -> x = y.
  Proof.
    intros.
    destruct x, y.
    unfold string_compare in *; simpl in *.
    repeat match goal with
             | H: context[match ?P with _ => _ end] |- _ => case_eq P; let x := fresh in intros x; rewrite x in *; try discriminate
           end.
    apply String_as_OT.Eq_eq in H.
    apply String_as_OT.Eq_eq in H0.
    subst; reflexivity.
  Qed.

  Lemma Eq_eq_iff : forall x y, x = y <-> string_compare x y = Eq.
  Proof.
    intros; split; eauto using eq_Eq, Eq_eq.
  Qed.

  Definition eq_refl := @eq_refl (string * string).

  Definition eq_sym := @eq_sym (string * string).

  Definition eq_trans := @eq_trans (string * string).

  Definition lt x y :=
    string_compare x y = Lt.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt, string_compare in *.
    destruct x, y, z; simpl in *.
    repeat match goal with
             | H: context[match ?P with _ => _ end] |- _ => case_eq P; let x := fresh in intros x; rewrite? x in *
             | |- context[match ?P with _ => _ end] => case_eq P; let x := fresh in intros x; rewrite? x in *
           end; try eapply String_as_OT.lt_trans; repeat (rewrite <-?String_as_OT.Eq_eq_iff, ?String_as_OT.string_compare_eq_refl in *;
                                                           subst; try discriminate; eauto).
    rewrite H2 in H3; discriminate.
    rewrite H1 in H3; discriminate.
    pose proof (String_as_OT.lt_trans _ _ _ H1 H2).
    unfold String_as_OT.lt in *.
    rewrite String_as_OT.string_compare_eq_refl in *.
    discriminate.
    pose proof (String_as_OT.lt_trans _ _ _ H1 H2).
    unfold String_as_OT.lt in *.
    rewrite String_as_OT.string_compare_eq_refl in *.
    discriminate.
    pose proof (String_as_OT.lt_trans _ _ _ H2 H1).
    unfold String_as_OT.lt in *.
    rewrite H3 in H4.
    discriminate.
    Unshelve.
    apply ""%string.
    apply ""%string.
    apply ""%string.
    apply ""%string.
    apply ""%string.
  Qed.

  Lemma lt_not_eq : forall x y: (string * string), lt x y -> ~ eq x y.
  Proof.
    unfold lt, not in *;
    intros;
    rewrite Eq_eq_iff in *.
    rewrite H in H0; discriminate.
  Qed.

  Lemma Lt_Gt : forall x y, string_compare x y = Gt <-> string_compare y x = Lt.
  Proof.
    intros.
    destruct x, y.
    unfold string_compare; simpl.
    repeat match goal with
             | |- context [match ?P with _ => _ end] => case_eq P; intros
           end.
    apply (String_as_OT.Lt_Gt s0 s2).
    rewrite <- String_as_OT.Eq_eq_iff in H.
    subst.
    rewrite String_as_OT.string_compare_eq_refl in H0.
    discriminate.
    rewrite <- String_as_OT.Eq_eq_iff in H.
    subst.
    rewrite String_as_OT.string_compare_eq_refl in H0.
    discriminate.
    rewrite <- String_as_OT.Eq_eq_iff in H0.
    subst.
    rewrite String_as_OT.string_compare_eq_refl in H.
    discriminate.
    pose proof (String_as_OT.lt_trans _ _ _ H H0).
    apply String_as_OT.lt_not_eq in H1.
    unfold String_as_OT.eq in H1.
    tauto.
    split; intros; discriminate.
    rewrite <- String_as_OT.Eq_eq_iff in H0.
    subst.
    rewrite String_as_OT.string_compare_eq_refl in H.
    discriminate.
    split; intros; auto.
    rewrite String_as_OT.Lt_Gt in *.
    pose proof (String_as_OT.lt_trans _ _ _ H H0).
    apply String_as_OT.lt_not_eq in H1.
    unfold String_as_OT.eq in H1.
    tauto.
  Qed.

  Definition compare x y : OrderedType.Compare lt eq x y.
  Proof.
    destruct (string_compare x y) eqn:comp;
      unfold lt;
      [ constructor 2; apply Eq_eq
      | constructor 1
      | constructor 3; apply Lt_Gt];
      trivial.
  Defined.

  Definition eq_dec : forall (x y: (string * string)), { x = y } + { x <> y }.
    decide equality; apply string_dec.
  Defined.
End StringString_as_OT.


