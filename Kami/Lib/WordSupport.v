Require Import Arith Lib.Word Lib.Nlia Lia.

Set Asymmetric Patterns.
#[warning="-unknown-option"] Set Asymmetric Patterns No Implicits.
Set Implicit Arguments.
Local Open Scope word_scope.

Lemma wordToNat_eq1: forall sz (a b: word sz), a = b -> wordToNat a = wordToNat b.
Proof. word_lia_Z. Qed.

Lemma wordToNat_eq2: forall sz (a b: word sz), wordToNat a = wordToNat b -> a = b.
Proof. word_lia_Z. Qed.

Lemma wordToN_to_nat sz: forall (w: word sz), BinNat.N.to_nat (wordToN w) = wordToNat w.
Proof. word_lia_Z. Qed.

Lemma wordToNat_lt1: forall sz (a b: word sz), a < b -> (wordToNat a < wordToNat b)%nat.
Proof. word_lia_Z. Qed.

Lemma wordToNat_lt2: forall sz (a b: word sz), (wordToNat a < wordToNat b)%nat -> a < b.
Proof. word_lia_Z. Qed.

Lemma wordToNat_gt1: forall sz (a b: word sz), a > b -> (wordToNat a > wordToNat b)%nat.
Proof. word_lia_Z. Qed.

Lemma wordToNat_gt2: forall sz (a b: word sz), (wordToNat a > wordToNat b)%nat -> a > b.
Proof. word_lia_Z. Qed.

Lemma wordToNat_le1: forall sz (a b: word sz), a <= b -> (wordToNat a <= wordToNat b)%nat.
Proof. word_lia_Z. Qed.

Lemma wordToNat_le2: forall sz (a b: word sz), (wordToNat a <= wordToNat b)%nat -> a <= b.
Proof. word_lia_Z. Qed.

Lemma wordToNat_ge1: forall sz (a b: word sz), a >= b -> (wordToNat a >= wordToNat b)%nat.
Proof. word_lia_Z. Qed.

Lemma wordToNat_ge2: forall sz (a b: word sz), (wordToNat a >= wordToNat b)%nat -> a >= b.
Proof. word_lia_Z. Qed.

Lemma wordToNat_neq1: forall sz (a b: word sz), a <> b -> wordToNat a <> wordToNat b.
Proof. word_lia_Z. Qed.

Lemma wordToNat_neq2: forall sz (a b: word sz), wordToNat a <> wordToNat b -> a <> b.
Proof. word_lia_Z. Qed.

Lemma wordNotNot: forall sz (a b: word sz), (a <> b -> False) -> a = b.
Proof.
  intros.
  destruct (weq a b); subst; tauto.
Qed.

Ltac pre_word_lia := word_to_Z.

Ltac word_lia := word_lia_Z.

Lemma word_le_ge_eq sz (w1 w2: word sz): w1 <= w2 -> w1 >= w2 -> w1 = w2.
Proof.
  intros; word_lia.
Qed.

Lemma word_le_zero sz (w: word sz): w <= wzero sz -> w = wzero sz.
Proof.
  intros;
  word_lia.
Qed.
