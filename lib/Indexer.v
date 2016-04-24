Require Import Bool Ascii String List Eqdep Omega.
Require Import CommonTactics.

(** Some string manipulation lemmas *)

Lemma prepend_same: forall x a b, (x ++ a)%string = (x ++ b)%string -> a = b.
Proof.
  induction x; intros; intuition.
  inv H; auto.
Qed.

Lemma substring_append_1:
  forall s1 s2 n,
    substring (String.length s1) n (s1 ++ s2) = substring 0 n s2.
Proof. induction s1; simpl; intros; auto. Qed.

Lemma substring_empty:
  forall s, substring 0 0 s = ""%string.
Proof. induction s; simpl; intros; auto. Qed.

Lemma string_append_assoc:
  forall {a b c : string}, (a ++ b ++ c)%string = ((a ++ b) ++ c)%string.
Proof.
  intros.
  induction a.
  simpl. reflexivity.
  simpl. rewrite IHa. reflexivity.
Qed.

(** End of string manipulation lemmas *)

Fixpoint string_of_nat (n: nat) :=
  match n with
    | O => "a"%string
    | S n' => append "a"%string (string_of_nat n')
  end.

Lemma string_of_nat_length: forall i, String.length (string_of_nat i) = S i.
Proof. induction i; simpl; intros; auto. Qed.

Definition indexSymbol: string := "__"%string.
Definition prefixSymbol: string := "."%string.

Definition withIndex str idx := 
  append (append (string_of_nat idx) indexSymbol) str.
Definition withPrefix pre str :=
  append (append pre prefixSymbol) str.

Theorem withIndex_eq : withIndex = fun str idx =>
  append (append (string_of_nat idx) indexSymbol) str.
Proof.
  reflexivity.
Qed.

Lemma string_of_nat_index_1:
  forall i j, j <= i -> get j (string_of_nat i) = Some "a"%char.
Proof.
  induction i; simpl; intros.
  - destruct j; try omega; auto.
  - destruct j; auto.
    apply IHi; omega.
Qed.

Lemma string_of_nat_index_2:
  forall i j, j > i -> get j (string_of_nat i) = None.
Proof.
  induction i; simpl; intros.
  - destruct j; try omega; auto.
  - destruct j; try omega; auto.
    apply IHi; omega.
Qed.

Lemma append_length:
  forall s1 s2,
    String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof. induction s1; simpl; intros; auto. Qed.

Lemma withIndex_index_1:
  forall s i j, j <= i -> get j (withIndex s i) = Some "a"%char.
Proof.
  unfold withIndex; intros.
  rewrite <-append_correct1.
  - rewrite <-append_correct1.
    + apply string_of_nat_index_1; auto.
    + rewrite string_of_nat_length; omega.
  - rewrite append_length.
    rewrite string_of_nat_length; omega.
Qed.

Lemma withIndex_index_2:
  forall s i, get (S i) (withIndex s i) = Some "_"%char.
Proof.
  induction i; simpl; intros; auto.
Qed.

Lemma withIndex_neq:
  forall a b i j,
    i <> j ->
    withIndex a i <> withIndex b j.
Proof.
  intros; destruct (gt_eq_gt_dec i j).
  - destruct s.
    + intro Hx.
      assert (get (S i) (withIndex a i) = get (S i) (withIndex b j)) by (rewrite Hx; auto).
      rewrite withIndex_index_2 with (i:= i) in H0 by omega.
      rewrite withIndex_index_1 in H0 by omega.
      inv H0.
    + elim H; auto.
  - intro Hx.
    assert (get (S j) (withIndex a i) = get (S j) (withIndex b j)) by (rewrite Hx; auto).
    rewrite withIndex_index_2 with (i:= j) in H0 by omega.
    rewrite withIndex_index_1 in H0 by omega.
    inv H0.
Qed.

Lemma withIndex_neq_prefix:
  forall a b i j,
    a <> b ->
    withIndex a i <> withIndex b j.
Proof.
  intros; destruct (eq_nat_dec i j); [subst|].
  - apply discr_var; auto.
  - apply withIndex_neq; auto.
Qed.

Global Opaque withIndex.

Notation "str '__' idx" := (withIndex str idx) (at level 0).
Notation "pre '..' str" := (withPrefix pre str) (at level 0).
                           
