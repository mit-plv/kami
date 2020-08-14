Require Import Arith Lib.Word Lib.Nlia Lia.

Set Asymmetric Patterns.
Set Implicit Arguments.
Local Open Scope word_scope.

Lemma wordToNat_eq1: forall sz (a b: word sz), a = b -> wordToNat a = wordToNat b.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wordToNat_eq2: forall sz (a b: word sz), wordToNat a = wordToNat b -> a = b.
Proof.
  intros.
  rewrite <- natToWord_wordToNat with (w := a).
  rewrite <- natToWord_wordToNat with (w := b).
  rewrite H.
  reflexivity.
Qed.

Lemma wordToN_to_nat sz: forall (w: word sz), BinNat.N.to_nat (wordToN w) = wordToNat w.
Proof.
  intros.
  rewrite wordToN_nat.
  rewrite Nnat.Nat2N.id.
  reflexivity.
Qed.

Lemma wordToNat_lt1: forall sz (a b: word sz), a < b -> (wordToNat a < wordToNat b)%nat.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_lt2: forall sz (a b: word sz), (wordToNat a < wordToNat b)%nat -> a < b.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_gt1: forall sz (a b: word sz), a > b -> (wordToNat a > wordToNat b)%nat.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_gt2: forall sz (a b: word sz), (wordToNat a > wordToNat b)%nat -> a > b.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_le1: forall sz (a b: word sz), a <= b -> (wordToNat a <= wordToNat b)%nat.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_le2: forall sz (a b: word sz), (wordToNat a <= wordToNat b)%nat -> a <= b.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_ge1: forall sz (a b: word sz), a >= b -> (wordToNat a >= wordToNat b)%nat.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_ge2: forall sz (a b: word sz), (wordToNat a >= wordToNat b)%nat -> a >= b.
Proof.
  intros.
  pre_nlia.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_neq1: forall sz (a b: word sz), a <> b -> wordToNat a <> wordToNat b.
Proof.
  unfold not.
  intros.
  apply wordToNat_eq2 in H0.
  tauto.
Qed.

Lemma wordToNat_neq2: forall sz (a b: word sz), wordToNat a <> wordToNat b -> a <> b.
Proof.
  unfold not.
  intros.
  subst.
  tauto.
Qed.

Lemma wordNotNot: forall sz (a b: word sz), (a <> b -> False) -> a = b.
Proof.
  intros.
  destruct (weq a b); subst; tauto.
Qed.

Ltac pre_word_lia :=
  unfold wzero, wone in *;
  repeat match goal with
           | H: @eq ?T ?a ?b |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_eq1 sz a b) in H;
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
                   simpl in H
             end
           | |- @eq ?T ?a ?b =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_eq2 sz a b);
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
                   simpl
             end
           | H: ?a < ?b |- _ =>
             apply wordToNat_lt1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a < ?b =>
             apply wordToNat_lt2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a > ?b |- _ =>
             apply wordToNat_gt1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a > ?b =>
             apply wordToNat_gt2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a <= ?b |- _ =>
             apply wordToNat_le1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a <= ?b =>
             apply wordToNat_le2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a > ?b -> False |- _ =>
             apply wordToNat_le1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a > ?b -> False =>
             apply wordToNat_le2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: ?a < ?b -> False |- _ =>
             apply wordToNat_ge1 in H;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
               simpl in H
           | |- ?a < ?b -> False =>
             apply wordToNat_ge2;
               rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
               simpl
           | H: not (@eq ?T ?a ?b) |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq1 sz a b) in H;
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
                   simpl in H
             end
           | |- not (@eq ?T ?a ?b) =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq2 sz a b);
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
                   simpl
             end
           | H: @eq ?T ?a ?b -> False |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq1 sz a b) in H;
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one in H;
                   simpl in H
             end
           | |- @eq ?T ?a ?b -> False =>
             match T with
               | word ?sz =>
                 apply (@wordToNat_neq2 sz a b);
                   rewrite ?roundTrip_0, ?roundTrip_1, ?wones_pow2_minus_one;
                   simpl
             end
           | H: (@eq ?T ?a ?b -> False) -> False |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
           | H: (not (@eq ?T ?a ?b)) -> False |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
           | H: not (@eq ?T ?a ?b -> False) |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
           | H: not (not (@eq ?T ?a ?b)) |- _ =>
             match T with
               | word ?sz =>
                 apply (@wordNotNot sz a b) in H
             end
         end.

Ltac word_lia := pre_word_lia; lia.

Lemma word_le_ge_eq sz (w1 w2: word sz): w1 <= w2 -> w1 >= w2 -> w1 = w2.
Proof.
  intros; word_lia.
Qed.

Lemma word_le_zero sz (w: word sz): w <= wzero sz -> w = wzero sz.
Proof.
  intros;
  word_lia.
Qed.

