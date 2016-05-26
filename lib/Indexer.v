Require Import Bool Ascii String Eqdep Omega.
Require Import CommonTactics.

(** Some string manipulation lemmas *)

Open Scope string_scope.

Lemma string_append_assoc:
  forall {a b c : string}, (a ++ b ++ c)%string = ((a ++ b) ++ c)%string.
Proof.
  intros.
  induction a.
  simpl. reflexivity.
  simpl. rewrite IHa. reflexivity.
Qed.

Lemma append_length:
  forall s1 s2,
    length (s1 ++ s2) = length s1 + length s2.
Proof. induction s1; simpl; intros; auto. Qed.

Lemma prepend_same: forall x a b, x ++ a = x ++ b -> a = b.
Proof.
  induction x; intros; intuition.
  inv H; auto.
Qed.

Lemma append_empty: forall s, s ++ "" = s.
Proof.
  induction s; simpl; intros; auto.
  f_equal; auto.
Qed.

Fixpoint string_rev (s: string) :=
  match s with
  | EmptyString => EmptyString
  | String a s' => ((string_rev s') ++ (String a EmptyString))%string
  end.

Lemma string_rev_empty:
  forall s, string_rev s = EmptyString -> s = EmptyString.
Proof.
  destruct s; simpl; intros; auto.
  assert (length (string_rev s ++ String a "") = length "")
    by (rewrite H; reflexivity).
  rewrite append_length in H0; simpl in H0.
  omega.
Qed.

Lemma string_append_same_singleton:
  forall s1 s2 a1 a2,
    s1 ++ String a1 "" = s2 ++ String a2 "" ->
    s1 = s2 /\ a1 = a2.
Proof.
  induction s1; simpl; intros.
  - destruct s2; simpl in *.
    + inv H; auto.
    + inv H; destruct s2; inv H2.
  - destruct s2; simpl in *.
    + exfalso.
      assert (length (String a (s1 ++ String a1 "")) =
              length (String a1 "")) by (rewrite H; reflexivity); clear H.
      simpl in H0; rewrite append_length in H0; simpl in H0.
      omega.
    + inv H.
      specialize (IHs1 _ _ _ H2); dest; subst; auto.
Qed.

Lemma string_rev_same:
  forall s1 s2, string_rev s1 = string_rev s2 -> s1 = s2.
Proof.
  induction s1; simpl; intros.
  - apply eq_sym, string_rev_empty in H; auto.
  - destruct s2.
    + simpl in H.
      assert (length (string_rev s1 ++ String a "") = length "")
        by (rewrite H; reflexivity).
      rewrite append_length in H0; simpl in H0.
      omega.
    + simpl in H.
      apply string_append_same_singleton in H; dest; subst.
      f_equal; auto.
Qed.

Lemma string_rev_app:
  forall s1 s2, string_rev (s1 ++ s2) = ((string_rev s2) ++ (string_rev s1))%string.
Proof.
  induction s1; simpl; intros.
  - destruct s2; auto.
    simpl; rewrite <-string_append_assoc; f_equal.
  - destruct s2; simpl in *.
    + rewrite append_empty; auto.
    + rewrite IHs1; simpl.
      rewrite string_append_assoc; auto.
Qed.

Lemma append_same: forall x a b, (a ++ x)%string = (b ++ x)%string -> a = b.
Proof.
  intros; apply string_rev_same.
  assert (string_rev (a ++ x) = string_rev (b ++ x))
    by (rewrite H; reflexivity).
  do 2 rewrite string_rev_app in H0.
  eapply prepend_same; eauto.
Qed.
    
Lemma substring_append_1:
  forall s1 s2 n,
    substring (String.length s1) n (s1 ++ s2) = substring 0 n s2.
Proof. induction s1; simpl; intros; auto. Qed.

Lemma substring_empty:
  forall s, substring 0 0 s = ""%string.
Proof. induction s; simpl; intros; auto. Qed.

(** End of string manipulation lemmas *)

Fixpoint string_of_nat (n: nat) :=
  match n with
    | O => "a"%string
    | S n' => append "a"%string (string_of_nat n')
  end.

Lemma string_of_nat_length: forall i, String.length (string_of_nat i) = S i.
Proof. induction i; simpl; intros; auto. Qed.

Lemma string_of_nat_into: forall i j, string_of_nat i = string_of_nat j -> i = j.
Proof.
  intros.
  assert (length (string_of_nat i) = length (string_of_nat j))
    by (rewrite H; reflexivity).
  do 2 rewrite string_of_nat_length in H0.
  inv H0; auto.
Qed.

Definition indexSymbol: string := "__"%string.
Definition prefixSymbol: string := "."%string.

Definition withIndex str idx := 
  append str (append indexSymbol (string_of_nat idx)).
Definition withPrefix pre str :=
  append str (append prefixSymbol pre).

Theorem withIndex_eq : withIndex = fun str idx =>
  append str (append indexSymbol (string_of_nat idx)).
Proof.
  reflexivity.
Qed.

Lemma string_of_nat_index_1:
  forall i j, j <= i -> forall s, get j (string_of_nat i ++ s) = Some "a"%char.
Proof.
  induction i; simpl; intros.
  - destruct j; try omega; auto.
  - destruct j; auto.
    apply IHi; omega.
Qed.

Lemma string_of_nat_index_2:
  forall i s, get (S i) (string_of_nat i ++ s) = get 0 s.
Proof.
  induction i; simpl; intros; auto.
Qed.

Lemma string_of_nat_rev:
  forall i, string_rev (string_of_nat i) = string_of_nat i.
Proof.
  induction i; simpl; intros; auto.
  rewrite IHi.
  clear; induction i; auto.
  simpl; f_equal; auto.
Qed.

Lemma withIndex_neq:
  forall a b i j,
    i <> j ->
    withIndex a i <> withIndex b j.
Proof.
  unfold withIndex; intros; intro Hx; elim H; clear H.
  assert (string_rev (a ++ indexSymbol ++ string_of_nat i) =
          string_rev (b ++ indexSymbol ++ string_of_nat j))
    by (rewrite Hx; reflexivity); clear Hx.
  repeat rewrite string_rev_app in H.
  repeat rewrite string_of_nat_rev in H.

  destruct (gt_eq_gt_dec i j); auto.
  - destruct s; auto; exfalso.
    simpl in H.
    do 2 rewrite <-string_append_assoc in H.
    match type of H with
    | ?l = ?r => assert (get (S i) l = get (S i) r) by (rewrite H; reflexivity)
    end; clear H.
    rewrite string_of_nat_index_2 in H0; simpl in H0.
    rewrite string_of_nat_index_1 in H0; inv H0; omega.
  - exfalso; simpl in H.
    do 2 rewrite <-string_append_assoc in H.
    match type of H with
    | ?l = ?r => assert (get (S j) l = get (S j) r) by (rewrite H; reflexivity)
    end; clear H.
    rewrite string_of_nat_index_2 in H0; simpl in H0.
    rewrite string_of_nat_index_1 in H0; inv H0; omega.
Qed.

Lemma withIndex_index_eq:
  forall s t i j,
    withIndex s i = withIndex t j -> s = t /\ i = j.
Proof.
  unfold withIndex; intros.
  destruct (eq_nat_dec i j).
  - subst; split; auto.
    assert (string_rev (s ++ indexSymbol ++ string_of_nat j) =
            string_rev (t ++ indexSymbol ++ string_of_nat j))
      by (rewrite H; reflexivity).
    repeat rewrite string_rev_app in H0.
    apply string_rev_same.
    eapply prepend_same; eauto.
  - apply withIndex_neq with (a:= s) (b:= t) in n.
    elim n; auto.
Qed.

Global Opaque withIndex.

Notation "str '__' idx" := (withIndex str idx) (at level 0).
Notation "pre '--' str" := (withPrefix pre str) (at level 0).

Close Scope string_scope.

