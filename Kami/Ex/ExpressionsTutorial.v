Require Import Arith NatLib Ring ArithRing Omega.
Require Import Kami.


(** * Warm-up: words (bitvectors) *)

Definition B := word 8.
Definition multibyte := list B.

Fixpoint mbToNat (mb : multibyte) : nat :=
  match mb with
  | nil => 0
  | b :: mb' => wordToNat b + mbToNat mb' * 256
  end.

Fixpoint applyCarry (carry : word 1) (mb : multibyte) : multibyte :=
  match mb with
  | nil =>
    if whd carry
    then natToWord 8 1 :: nil
    else nil
  | b :: mb' =>
    let carry_9 := combine carry (wzero 8) in
    let b_9 := combine b (wzero 1) in
    let sum_9 := carry_9 ^+ b_9 in
    let sum_8 := split1 8 1 sum_9 in
    let carry' := split2 8 1 sum_9 in
    sum_8 :: applyCarry carry' mb'
  end.

Fixpoint mbAdd' (carry : word 1) (mb1 mb2 : multibyte) : multibyte :=
  match mb1, mb2 with
  | nil, _ => applyCarry carry mb2
  | _, nil => applyCarry carry mb1
  | b1 :: mb1', b2 :: mb2' =>
    let carry_9 := combine carry (wzero 8) in
    let b1_9 := combine b1 (wzero 1) in
    let b2_9 := combine b2 (wzero 1) in
    let sum_9 := carry_9 ^+ b1_9 ^+ b2_9 in
    let sum_8 := split1 8 1 sum_9 in
    let carry' := split2 8 1 sum_9 in
    sum_8 :: mbAdd' carry' mb1' mb2'
  end.

Definition mbAdd := mbAdd' (wzero 1).

Lemma split_plus : forall b a (w : word (a + b)),
    wordToNat (split1 a b w) + wordToNat (split2 a b w) * pow2 a = wordToNat w.
Proof.
  induction a; simpl; intuition.

  pose proof (shatter_word_S w).
  destruct H as [bit [c Heq]]; subst; simpl.
  destruct bit.

  {
    rewrite <- IHa.
    ring.
  }

  {
    rewrite <- IHa.
    ring.
  }
Qed.

Lemma wplus_nowrap : forall a (w1 w2 : word a),
    (wordToNat w1 + wordToNat w2 < pow2 a)%nat
    -> wordToNat (w1 ^+ w2) = wordToNat w1 + wordToNat w2.
Proof.
  intros.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  apply wordToNat_natToWord_idempotent.
  pre_nomega.
  rewrite Npow2_nat.
  assumption.
Qed.

Lemma pad_with_zero : forall a (w : word a) b,
    wordToNat (combine w (wzero b)) = wordToNat w.
Proof.
  induction w; simpl; intros.

  {
    apply wordToNat_wzero.
  }

  {
    rewrite IHw.
    reflexivity.
  }
Qed.

Opaque wordToNat natToWord split1 split2 combine.

Lemma applyCarry_ok : forall mb carry,
    mbToNat (applyCarry carry mb)
    = wordToNat carry + mbToNat mb.
Proof.
  induction mb; simpl; intuition.

  {
    pose proof (shatter_word_S carry).
    destruct H as [b [c Heq]]; subst.
    simpl.
    pose proof (shatter_word_0 c); subst.
    destruct b; simpl.
    reflexivity.
    reflexivity.
  }

  {
    rewrite IHmb.
    ring_simplify.
    pose proof (split_plus 1 8 (combine carry (wzero 8) ^+ combine a (wzero 1))).
    change (pow2 8) with 256 in *.
    pose proof (pad_with_zero _ carry 8).
    pose proof (pad_with_zero _ a 1).
    simpl in H, H0, H1.
    rewrite wplus_nowrap in H.

    {
      rewrite H0, H1 in H.
      rewrite <- (plus_assoc _ _ (wordToNat a)).
      rewrite <- H.
      ring.
    }

    {
      rewrite H0, H1.
      pose proof (wordToNat_bound carry).
      pose proof (wordToNat_bound a).
      simpl in *.
      omega.
    }
  }
Qed.

Lemma mbAdd'_ok : forall mb1 mb2 carry,
    mbToNat (mbAdd' carry mb1 mb2)
    = wordToNat carry + mbToNat mb1 + mbToNat mb2.
Proof.
  induction mb1; destruct mb2; simpl; intuition.

  {
    pose proof (shatter_word_S carry).
    destruct H as [b [c Heq]]; subst.
    simpl.
    pose proof (shatter_word_0 c); subst.
    destruct b; simpl.
    reflexivity.
    reflexivity.
  }    
  
  {
    rewrite applyCarry_ok.
    ring_simplify.
    pose proof (split_plus 1 8 (combine carry (wzero 8) ^+ combine b (wzero 1))).
    change (pow2 8) with 256 in *.
    pose proof (pad_with_zero _ carry 8).
    pose proof (pad_with_zero _ b 1).
    simpl in H, H0, H1.
    rewrite wplus_nowrap in H.

    {
      rewrite H0, H1 in H.
      rewrite <- (plus_assoc _ _ (wordToNat b)).
      rewrite <- H.
      ring.
    }

    {
      rewrite H0, H1.
      pose proof (wordToNat_bound carry).
      pose proof (wordToNat_bound b).
      simpl in *.
      omega.
    }
  }

  {
    rewrite applyCarry_ok.
    ring_simplify.
    pose proof (split_plus 1 8 (combine carry (wzero 8) ^+ combine a (wzero 1))).
    change (pow2 8) with 256 in *.
    pose proof (pad_with_zero _ carry 8).
    pose proof (pad_with_zero _ a 1).
    simpl in H, H0, H1.
    rewrite wplus_nowrap in H.

    {
      rewrite H0, H1 in H.
      rewrite <- (plus_assoc _ _ (wordToNat a)).
      rewrite <- H.
      ring.
    }

    {
      rewrite H0, H1.
      pose proof (wordToNat_bound carry).
      pose proof (wordToNat_bound a).
      simpl in *.
      omega.
    }
  }

  {
    rewrite IHmb1.
    ring_simplify.
    pose proof (split_plus 1 8 (combine carry (wzero 8) ^+ combine a (wzero 1) ^+ combine b (wzero 1))).
    change (pow2 8) with 256 in *.
    pose proof (pad_with_zero _ carry 8).
    pose proof (pad_with_zero _ a 1).
    pose proof (pad_with_zero _ b 1).
    simpl in H, H0, H1, H2.
    rewrite 2 wplus_nowrap in H.

    {
      rewrite H0, H1, H2 in H.
      replace (256 * mbToNat mb1 + 256 * mbToNat mb2 + # (carry) + # (a) + # (b))
              with (256 * mbToNat mb1 + 256 * mbToNat mb2 + (# (carry) + # (a) + # (b))) by omega.
      rewrite <- H.
      ring.
    }

    {
      rewrite H0, H1.
      pose proof (wordToNat_bound carry).
      pose proof (wordToNat_bound a).
      simpl in *.
      omega.
    }

    {
      rewrite wplus_nowrap.

      {
        rewrite H0, H1, H2.
        pose proof (wordToNat_bound carry).
        pose proof (wordToNat_bound a).
        pose proof (wordToNat_bound b).
        simpl in *.
        omega.
      }

      {
        rewrite H0, H1.
        pose proof (wordToNat_bound carry).
        pose proof (wordToNat_bound a).
        simpl in *.
        omega.
      }
    }
  }
Qed.

Theorem mbAdd_ok : forall mb1 mb2,
    mbToNat (mbAdd mb1 mb2)
    = mbToNat mb1 + mbToNat mb2.
Proof.
  intros; unfold mbAdd.
  rewrite mbAdd'_ok.
  reflexivity.
Qed.
