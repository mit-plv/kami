(** Derived facts used by the Kami examples (Fifo, Multiplier, Divider). *)
From Stdlib Require Import ZArith Lia Eqdep_dec EqdepFacts.
From Kami Require Import NatLib Word.

Set Implicit Arguments.
Local Open Scope Z_scope.

(** [z] just below a multiple [2*p*t] of [2*p] reduces to [z - 2*p*t + 2*p]. *)
Lemma Zmod_upper : forall z p t, 0 < p -> 0 < t ->
    2 * p * t - p <= z < 2 * p * t -> z mod (2 * p) = z - 2 * p * t + 2 * p.
Proof.
  intros; rewrite <- (Z.mod_add z (1 - t) (2 * p)) by lia.
  rewrite Z.mod_small by nia. lia.
Qed.

(** The most significant bit of [combine]: the two directions, as [Z] facts. *)
Lemma msb_combine_lt : forall p1 p2 z0 z, 0 < p1 -> 0 < p2 -> p2 mod 2 = 0 ->
    0 <= z0 < p1 -> 2 * z < p2 -> 2 * (z0 + p1 * z) < p1 * p2.
Proof.
  intros. assert (2 * z <= p2 - 2) by lia.
  assert (p1 * (2 * z) <= p1 * (p2 - 2)) by (apply Z.mul_le_mono_nonneg_l; lia). nia.
Qed.

Lemma msb_combine_ge : forall p1 p2 z0 z, 0 < p1 -> 0 < p2 ->
    0 <= z0 -> p2 <= 2 * z -> p1 * p2 <= 2 * (z0 + p1 * z).
Proof.
  intros. assert (p1 * p2 <= p1 * (2 * z)) by (apply Z.mul_le_mono_nonneg_l; lia). nia.
Qed.

Ltac msb_combine_contra :=
  match goal with
  | H : (?p1 * ?p2 <= 2 * (?z0 + ?p1 * ?z))%Z, H' : (2 * ?z < ?p2)%Z |- _ =>
    exfalso; pose proof (@msb_combine_lt p1 p2 z0 z); lia
  | H : (2 * (?z0 + ?p1 * ?z) < ?p1 * ?p2)%Z, H' : (?p2 <= 2 * ?z)%Z |- _ =>
    exfalso; pose proof (@msb_combine_ge p1 p2 z0 z); lia
  end.

Local Close Scope Z_scope.

Lemma WO_combine : forall sz (w : word sz), combine WO w = w.
Proof. word_lia_Z. Qed.

Lemma WS_true_natToWord_0 : forall sz, WS true (natToWord sz 0) = natToWord (S sz) 1.
Proof. word_lia_Z. Qed.

Lemma ZToWord_wordToZ : forall sz (w : word sz), ZToWord sz (wordToZ w) = w.
Proof. word_lia_Z. Qed.

Lemma combine_assoc_existT :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2) sz3 (w3 : word sz3),
    existT word (sz1 + (sz2 + sz3)) (combine w1 (combine w2 w3)) =
    existT word (sz1 + sz2 + sz3) (combine (combine w1 w2) w3).
Proof. word_lia_Z. Qed.

Lemma combine_one : forall n m, combine (natToWord (S n) 1) (natToWord m 0) = natToWord _ 1.
Proof. word_lia_Z. Qed.

Lemma combine_sext :
  forall sz1 (w1 : word sz1) sz2 (w2 : word (S sz2)) n,
    existT word _ (combine w1 (sext w2 n)) = existT word _ (sext (combine w1 w2) n).
Proof. word_lia_Z. Qed.

Lemma combine_wplus_1 :
  forall sl (w1 : word sl) su (w2 w3 : word su),
    combine w1 (w2 ^+ w3) = combine w1 w2 ^+ extz w3 sl.
Proof. word_lia_Z. Qed.

Lemma combine_wplus_2 :
  forall sl (w1 : word sl) su (w2 w3 : word su),
    combine w1 (w2 ^+ w3) = extz w2 sl ^+ combine w1 w3.
Proof. word_lia_Z. Qed.

Lemma existT_sext :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (sext w1 n) = existT word _ (sext w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_wlshift :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wlshift w1 n) = existT word _ (wlshift w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_wminus :
  forall sz (w1 w2 : word sz) sz' (w3 w4 : word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^- w2) = existT word _ (w3 ^- w4).
Proof.
  intros; apply existT_word_inv in H; apply existT_word_inv in H0; destruct H, H0; subst.
  apply Zmod.unsigned_inj in H1; apply Zmod.unsigned_inj in H2; subst; reflexivity.
Qed.

Lemma existT_wordToNat :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2),
    existT word _ w1 = existT word _ w2 -> wordToNat w1 = wordToNat w2.
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_wplus :
  forall sz (w1 w2 : word sz) sz' (w3 w4 : word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^+ w2) = existT word _ (w3 ^+ w4).
Proof.
  intros; apply existT_word_inv in H; apply existT_word_inv in H0; destruct H, H0; subst.
  apply Zmod.unsigned_inj in H1; apply Zmod.unsigned_inj in H2; subst; reflexivity.
Qed.

Lemma existT_wrshifta :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wrshifta w1 n) = existT word _ (wrshifta w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma extz_combine : forall sz (w : word sz) n, extz w n = combine (natToWord n 0) w.
Proof. word_lia_Z. Qed.

Lemma extz_extz :
  forall sz (w : word sz) n1 n2,
    existT word _ (extz (extz w n1) n2) = existT word _ (extz w (n2 + n1)).
Proof. word_lia_Z. Qed.

Lemma extz_pow2_wordToZ :
  forall sz (w : word sz) n, wordToZ (extz w n) = (wordToZ w * Z.of_nat (pow2 n))%Z.
Proof. word_lia_Z. Qed.

Lemma extz_sext :
  forall sz (w : word sz) n1 n2,
    existT word _ (extz (sext w n1) n2) = existT word _ (sext (extz w n2) n1).
Proof. word_lia_Z. Qed.

Lemma extz_zero : forall sz n, extz (natToWord sz 0) n = wzero _.
Proof. word_lia_Z. Qed.

Theorem natToWord_inj : forall sz n m, natToWord sz n = natToWord sz m
  -> (n < pow2 sz)%nat -> (m < pow2 sz)%nat -> n = m.
Proof. word_lia_Z. Qed.

Lemma pow2_minus_one_wones : forall {sz} (w : word sz),
    wordToNat w = (pow2 sz - 1)%nat -> w = wones sz.
Proof. word_lia_Z. Qed.

Lemma sext_combine :
  forall sz n (w : word (sz + n)) sz1 (w1 : word sz1) sz2 (Hsz2 : sz2 <> 0) (w2 : word sz2),
    existT word _ w = existT word _ (combine w1 (sext w2 n)) ->
    exists sw, w = sext sw n /\ existT word _ sw = existT word _ (combine w1 w2).
Proof.
  intros. apply existT_word_inv in H; destruct H.
  assert (sz = sz1 + sz2)%nat by lia. subst sz.
  exists (combine w1 w2). split; [|reflexivity].
  apply Zmod.unsigned_inj. rewrite H0. clear H0 H.
  word_to_Z; pose proof (Zpow2_even sz2 ltac:(lia)).
  all: try msb_combine_contra.
  all: word_mod_simpl; nia.
Qed.

Lemma sext_size :
  forall sz n (w : word (sz + n)),
    sz <> 0 ->
    (- Z.of_nat (pow2 (sz - 1)) <= wordToZ w < Z.of_nat (pow2 (sz - 1)))%Z ->
    exists sw, w = sext sw n.
Proof.
  intros; destruct sz; [lia|].
  replace (S sz - 1)%nat with sz in H0 by lia.
  exists (split1 (S sz) n w).
  word_to_Z.
  - rewrite (Z.mod_small z) by lia; rewrite Z.mod_small by lia; reflexivity.
  - rewrite (Z.mod_small z) in * by lia; lia.
  - rewrite (@Zmod_upper z (Zpow2 sz) (Zpow2 n)) in * by lia; lia.
  - rewrite (@Zmod_upper z (Zpow2 sz) (Zpow2 n)) by lia.
    replace (z - 2 * Zpow2 sz * Zpow2 n + 2 * Zpow2 sz - 2 * Zpow2 sz)%Z
       with (z + (-1) * (2 * Zpow2 sz * Zpow2 n))%Z by ring.
    rewrite Z.mod_add by lia; rewrite Z.mod_small by lia; reflexivity.
Qed.

Lemma sext_split1 : forall sz (w : word sz) n, split1 sz _ (sext w n) = w.
Proof. word_lia_Z. Qed.

Lemma sext_wordToZ : forall sz n (w : word sz), wordToZ (sext w n) = wordToZ w.
Proof. word_lia_Z. Qed.

Lemma sext_wplus_exist :
  forall sz (w1 w2 : word sz) n,
  exists w : word (S sz),
    existT word _ (sext w1 (S n) ^+ sext w2 (S n)) = existT word _ (sext w n).
Proof.
  intros; exists (ZToWord (S sz) (wordToZ w1 + wordToZ w2)).
  word_lia_Z.
Qed.

Lemma sext_wplus_wordToZ_distr :
  forall sz (w1 w2 : word sz) n,
    n <> 0 -> wordToZ (sext w1 n ^+ sext w2 n) = (wordToZ (sext w1 n) + wordToZ (sext w2 n))%Z.
Proof. word_lia_Z. Qed.

Lemma sext_wzero : forall sz n, sext (wzero sz) n = wzero (sz + n).
Proof. word_lia_Z. Qed.

Lemma shatter_word_0 : forall a : word 0, a = WO.
Proof. intros; apply word0. Qed.

Lemma shatter_word_1 : forall (w : word 1), w = WS (whd w) WO.
Proof. intros; rewrite (shatter_word w) at 1; f_equal; apply shatter_word_0. Qed.

Lemma shatter_word_2 : forall (w : word 2), w = WS (whd w) (WS (whd (wtl w)) WO).
Proof. intros; rewrite (shatter_word w) at 1; f_equal; apply shatter_word_1. Qed.

Lemma shatter_word_3 : forall (w : word 3),
    w = WS (whd w) (WS (whd (wtl w)) (WS (whd (wtl (wtl w))) WO)).
Proof. intros; rewrite (shatter_word w) at 1; f_equal; apply shatter_word_2. Qed.

Theorem split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split1 sz1 sz2 (combine w z) = w.
Proof. word_lia_Z. Qed.

Lemma split1_combine_existT :
  forall sz n (w : word (n + sz)) sl (wl : word (n + sl)) su (wu : word su),
    existT word _ w = existT word _ (combine wl wu) ->
    split1 n _ w = split1 n _ wl.
Proof.
  intros; apply existT_word_inv in H; destruct H.
  apply Zmod.unsigned_inj; rewrite !unsigned_split1, H0, unsigned_combine.
  rewrite <- (Z.mod_add (Zmod.unsigned wl) (Zpow2 sl * Zmod.unsigned wu) (Zpow2 n))
    by (pose proof (Zpow2_pos n); lia).
  f_equal; f_equal; rewrite (Zpow2_add n sl); ring.
Qed.

Theorem split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split2 sz1 sz2 (combine w z) = z.
Proof. word_lia_Z. Qed.

Lemma split2_split1_combine1 : forall n m (x : word 1) (y : word (n + m)),
    split2 1 n (split1 (S n) m (combine x y)) = split1 n m y.
Proof. word_lia_Z. Qed.

Lemma sub_0_eq : forall sz (a b : word sz), a ^- b = wzero _ -> a = b.
Proof. word_lia_Z. Qed.

Lemma whd_split1 : forall n m (w : word (S n + m)), whd (split1 (S n) m w) = whd w.
Proof. word_lia_Z. Qed.

Lemma wtl_split1 : forall n m (w : word (S n + m)),
    wtl (split1 (S n) m w) = split1 n m (wtl w).
Proof. word_lia_Z. Qed.

Lemma wlshift_combine_extz :
  forall sn sl (wl : word sl) ssu (wu : word (ssu + sn)),
    existT word (sl + (ssu + sn)) (wlshift (combine wl wu) sn) =
    existT word (sn + (sl + ssu)) (extz (combine wl (split1 ssu _ wu)) sn).
Proof.
  word_to_Z; pose proof (Zpow2_pos sl); pose proof (Zpow2_pos sn); pose proof (Zpow2_pos ssu).
  replace (Zpow2 sl * (Zpow2 ssu * Zpow2 sn))%Z with ((Zpow2 sl * Zpow2 ssu) * Zpow2 sn)%Z by ring.
  rewrite Z.mul_mod_distr_r by nia.
  f_equal.
  assert (Hq : z = (Zpow2 ssu * (z / Zpow2 ssu) + z mod Zpow2 ssu)%Z) by (apply Z.div_mod; lia).
  assert (Hm : (0 <= z mod Zpow2 ssu < Zpow2 ssu)%Z) by (apply Z.mod_pos_bound; lia).
  rewrite Hq at 1.
  replace (z0 + Zpow2 sl * (Zpow2 ssu * (z / Zpow2 ssu) + z mod Zpow2 ssu))%Z
     with ((z0 + Zpow2 sl * (z mod Zpow2 ssu)) + (z / Zpow2 ssu) * (Zpow2 sl * Zpow2 ssu))%Z by ring.
  rewrite Z.mod_add by nia.
  apply Z.mod_small; nia.
Qed.

Lemma wlshift_sext_extz :
  forall sz (w : word sz) n, existT word _ (wlshift (sext w n) n) = existT word _ (extz w n).
Proof. word_lia_Z. Qed.

Theorem wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
Proof. intros; symmetry; apply Zmod.add_opp_r. Qed.

Theorem wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.
Proof. intros; apply Zmod.add_opp_same_r. Qed.

Lemma wminus_plus_distr : forall {sz} (x y z : word sz), x ^- (y ^+ z) = x ^- y ^- z.
Proof. word_lia_Z. Qed.

Lemma wordToZ_wordToNat_pos :
  forall sz (w : word sz), wmsb w false = false -> Z.of_nat (wordToNat w) = wordToZ w.
Proof. word_lia_Z. Qed.

Corollary wmsb_Zabs_pos :
  forall sz (w : word sz), wmsb w false = false -> Z.abs (wordToZ w) = wordToZ w.
Proof. intros; rewrite <- wordToZ_wordToNat_pos by assumption; lia. Qed.

Lemma wmsb_combine :
  forall sz1 sz2 (w1 : word sz1) (w2 : word sz2) b1 b2,
    sz2 <> 0 -> wmsb (combine w1 w2) b1 = wmsb w2 b2.
Proof.
  word_to_Z; try reflexivity; exfalso; try lia;
    pose proof (Zpow2_even sz2 ltac:(lia)); first [ nia | msb_combine_contra ].
Qed.

Lemma wmsb_combine_existT :
  forall sz (w : word sz) sz1 (w1 : word sz1) sz2 (w2 : word sz2) b1 b2,
    sz2 <> 0 -> existT word _ w = existT word _ (combine w1 w2) -> wmsb w b1 = wmsb w2 b2.
Proof.
  intros; apply existT_word_inv in H0; destruct H0; subst.
  apply Zmod.unsigned_inj in H1; subst; apply wmsb_combine; assumption.
Qed.

Lemma wmsb_existT :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2),
    existT word _ w1 = existT word _ w2 -> forall b, wmsb w1 b = wmsb w2 b.
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma wmsb_extz : forall sz (w : word sz) n, wmsb (extz w n) false = wmsb w false.
Proof. word_lia_Z. Qed.

Lemma wmsb_false_pos : forall sz (w : word sz), wmsb w false = false <-> (wordToZ w >= 0)%Z.
Proof. split; word_lia_Z. Qed.

Lemma wmsb_split1_sext :
  forall sz (w : word (sz + 1)),
    wmsb w false = wmsb (split1 _ 1 w) false -> exists sw, sext sw 1 = w.
Proof. intros; exists (split1 sz 1 w). word_lia_Z. Qed.

Lemma wmsb_split2 :
  forall sz (w : word (sz + 1)) b,
    wmsb w b = if weq (split2 _ 1 w) (natToWord _ 0) then false else true.
Proof. intros; destruct (weq (split2 sz 1 w) (natToWord 1 0)); word_lia_Z. Qed.

Lemma wmsb_true_neg : forall sz (w : word sz), wmsb w false = true <-> (wordToZ w < 0)%Z.
Proof. split; word_lia_Z. Qed.

Lemma wmsb_wlshift_sext :
  forall sz (w : word sz) n, wmsb (sext w n) false = wmsb (wlshift (sext w n) n) false.
Proof.
  intros.
  assert (E : Zmod.unsigned (wlshift (sext w n) n) = (Zmod.unsigned w * Zpow2 n)%Z).
  { rewrite unsigned_wlshift, unsigned_sext, Zpow2_add.
    pose proof (Zpow2_pos sz); pose proof (Zpow2_pos n).
    rewrite Z.mul_mod_distr_r by lia.
    rewrite Z.mod_mod_divide by (exists (Zpow2 n); ring).
    rewrite <- (Zmod.mod_signed w); reflexivity. }
  rewrite !wmsb_eqn, E, unsigned_sext, signed_eqn, Zpow2_add.
  pose proof (unsigned_range w); pose proof (Zpow2_pos sz); pose proof (Zpow2_pos n);
    pose proof (Zpow2_prod sz n).
  destruct (Z.eqb_spec (Z.of_nat (sz + n)) 0) as [E0|E0].
  - reflexivity.
  - destruct (Z.ltb_spec (2 * Zmod.unsigned w) (Zpow2 sz)).
    + rewrite Z.mod_small by nia.
      destruct (Z.leb_spec (Zpow2 sz * Zpow2 n) (2 * Zmod.unsigned w));
        destruct (Z.leb_spec (Zpow2 sz * Zpow2 n) (2 * (Zmod.unsigned w * Zpow2 n))); try reflexivity; nia.
    + rewrite (@Zmod_small_neg (Zmod.unsigned w - Zpow2 sz)) by nia.
      destruct (Z.leb_spec (Zpow2 sz * Zpow2 n) (2 * (Zmod.unsigned w - Zpow2 sz + Zpow2 sz * Zpow2 n)));
        destruct (Z.leb_spec (Zpow2 sz * Zpow2 n) (2 * (Zmod.unsigned w * Zpow2 n))); try reflexivity; nia.
Qed.

Lemma wmsb_wneg_zext :
  forall sz (w : word sz) b n, n <> 0 -> wordToNat w <> 0 -> wmsb (wneg (zext w n)) b = true.
Proof. word_lia_Z. Qed.

Lemma wmsb_wzero : forall sz, wmsb (wzero sz) false = false.
Proof. word_lia_Z. Qed.

Lemma wmsb_zext : forall sz (w : word sz) b n, n <> 0 -> wmsb (zext w n) b = false.
Proof. word_lia_Z. Qed.

Lemma wneg_idempotent : forall {sz} (w : word sz), ^~ (^~ w) = w.
Proof. word_lia_Z. Qed.

Lemma wneg_wnot : forall sz (w : word sz), wnot w = wneg w ^- (natToWord _ 1).
Proof. word_lia_Z. Qed.

Lemma wneg_wordToZ :
  forall sz (w : word (S sz)), w <> wpow2 sz -> wordToZ (wneg w) = (- wordToZ w)%Z.
Proof. word_lia_Z. Qed.

Lemma wneg_zero : forall {sz} (w : word sz), ^~ w = natToWord sz 0 -> w = natToWord sz 0.
Proof. word_lia_Z. Qed.

Lemma wones_wneg_one : forall {sz}, wones sz = ^~ (natToWord sz 1).
Proof. word_lia_Z. Qed.

Theorem wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.
Proof. intros; apply Zmod.add_assoc. Qed.

Lemma wplus_cancel : forall sz (a b c : word sz), a ^+ c = b ^+ c -> a = b.
Proof. word_lia_Z. Qed.

Theorem wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.
Proof. intros; apply Zmod.add_comm. Qed.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.
Proof. word_lia_Z. Qed.

Lemma wplus_wzero_1 : forall sz (w : word sz), w ^+ wzero sz = w.
Proof. word_lia_Z. Qed.

Lemma wpow2_wmsb : forall sz, wmsb (wpow2 sz) false = true.
Proof. word_lia_Z. Qed.

Lemma wrshifta_extz_sext :
  forall sz (w : word sz) n1 n2,
    existT word _ (wrshifta (extz w (n1 + n2)) n1) = existT word _ (sext (extz w n2) n1).
Proof. word_lia_Z. Qed.

Lemma split1_zext : forall sz (w : word sz) n, split1 sz n (zext w n) = w.
Proof. word_lia_Z. Qed.

Lemma wordToNat_wdivN : forall sz (x y : word sz), wordToNat (wdivN x y) = (wordToNat x / wordToNat y)%nat.
Proof.
  intros; cbv [wordToNat]; rewrite unsigned_wdivN.
  apply Z2Nat.inj_div; apply unsigned_range.
Qed.

Lemma wordToNat_wremN : forall sz (x y : word sz), wordToNat (wremN x y) = (wordToNat x mod wordToNat y)%nat.
Proof.
  intros; cbv [wordToNat]; rewrite unsigned_wremN.
  apply Z2Nat.inj_mod; apply unsigned_range.
Qed.

Lemma unsigned_natToWord_small :
  forall sz n, (n < pow2 sz)%nat -> uwordToZ (natToWord sz n) = Z.of_nat n.
Proof. word_lia_Z. Qed.

Lemma wrshifta_wzero : forall sz n, wrshifta (wzero sz) n = wzero _.
Proof. word_lia_Z. Qed.

Lemma wordToNat_combine :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2),
    wordToNat (combine w1 w2) = (wordToNat w1 + pow2 sz1 * wordToNat w2)%nat.
Proof. word_lia_Z. Qed.

Lemma wordToNat_existT :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2) (Hsz : sz1 = sz2),
    wordToNat w1 = wordToNat w2 -> existT word _ w1 = existT word _ w2.
Proof. intros; subst; f_equal; apply wordToNat_inj; assumption. Qed.

Lemma wordToNat_natToWord_2 : forall sz w : nat,
    (w < pow2 sz)%nat -> wordToNat (natToWord sz w) = w.
Proof. word_lia_Z. Qed.

Lemma wordToNat_natToWord_pred :
  forall {sz} (w : word sz), w <> wzero sz -> pred (wordToNat w) = wordToNat (w ^- (natToWord sz 1)).
Proof. word_lia_Z. Qed.

Lemma wordToNat_wrshifta :
  forall sz (w : word sz) n, wordToNat (wrshifta w n) = Nat.div (wordToNat (sext w n)) (pow2 n).
Proof. word_lia_Z. Qed.

Lemma wordToNat_wtl : forall sz (w : word (S sz)), wordToNat (wtl w) = (wordToNat w / 2)%nat.
Proof. word_lia_Z. Qed.

Lemma wordToNat_zext : forall sz (w : word sz) n, wordToNat (zext w n) = wordToNat w.
Proof. word_lia_Z. Qed.

Lemma wordToZ_bound_weakened : forall z n, (Z.abs z < n)%Z -> (- n <= z < n)%Z.
Proof. intros; lia. Qed.

Lemma wordToZ_distr_diff_wmsb :
  forall sz (w1 w2 : word sz),
    wmsb w1 false = negb (wmsb w2 false) -> wordToZ (w1 ^+ w2) = (wordToZ w1 + wordToZ w2)%Z.
Proof. word_lia_Z. Qed.

Lemma wordToZ_eq_rect :
  forall sz (w : word sz) nsz Hsz, wordToZ (eq_rect _ word w nsz Hsz) = wordToZ w.
Proof. intros; subst; reflexivity. Qed.

Lemma wordToZ_existT :
  forall sz1 (w1 : word sz1) sz2 (w2 : word sz2) (Hsz : sz1 = sz2),
    wordToZ w1 = wordToZ w2 -> existT word _ w1 = existT word _ w2.
Proof. intros; subst; f_equal; apply Zmod.signed_inj; assumption. Qed.

Lemma wordToZ_one : forall (w : word 1), wordToZ w = (if whd w then -1 else 0)%Z.
Proof. word_lia_Z. Qed.

Lemma wordToZ_size' :
  forall sz (w : word (S sz)), (- Z.of_nat (pow2 sz) <= wordToZ w < Z.of_nat (pow2 sz))%Z.
Proof. word_lia_Z. Qed.

Lemma wordToZ_succ : forall sz (w : word (S (S sz))),
    wordToZ w = (2 * wordToZ (wtl w) + (if whd w then 1 else 0))%Z.
Proof. word_lia_Z. Qed.

Lemma wordToZ_wplus_bound :
  forall sz (w1 w2 : word (S sz)),
    (- Z.of_nat (pow2 sz) <= wordToZ w1 + wordToZ w2 < Z.of_nat (pow2 sz))%Z ->
    (wordToZ w1 + wordToZ w2 = wordToZ (w1 ^+ w2))%Z.
Proof. word_lia_Z. Qed.

Lemma wordToZ_wzero : forall sz, wordToZ (wzero sz) = 0%Z.
Proof. word_lia_Z. Qed.

Lemma zext_size :
  forall sz n (w : word (sz + n)),
    (- Z.of_nat (pow2 sz) <= wordToZ w < Z.of_nat (pow2 sz))%Z ->
    wmsb w false = false -> exists sw, w = zext sw n.
Proof.
  intros; exists (split1 sz n w).
  word_to_Z; try lia; rewrite Z.mod_small by lia; lia.
Qed.

Lemma zext_size_1 :
  forall sz (w : word (sz + 1)), wmsb w false = false -> exists sw, w = zext sw 1.
Proof. intros; exists (split1 sz 1 w). word_lia_Z. Qed.

Lemma zext_wordToNat_equal_Z :
  forall sz (w : word sz) n, n <> 0 -> wordToZ (zext w n) = Z.of_nat (wordToNat w).
Proof. word_lia_Z. Qed.


(** * Facts the bedrock2 processor proofs use *)

Notation wzero' sz := (wzero sz).

Lemma wordToN_bound : forall sz (w : word sz), (wordToN w < Npow2 sz)%N.
Proof. word_lia_Z. Qed.

Theorem combine_split : forall sz1 sz2 (w : word (sz1 + sz2)),
  combine (split1 sz1 sz2 w) (split2 sz1 sz2 w) = w.
Proof. word_lia_Z. Qed.

Lemma wordToZ_inj : forall sz (w1 w2 : word sz), wordToZ w1 = wordToZ w2 -> w1 = w2.
Proof. intros; apply Zmod.signed_inj; assumption. Qed.

Lemma wordToN_inj : forall sz (a b : word sz), wordToN a = wordToN b -> a = b.
Proof. word_lia_Z. Qed.

Lemma wordToZ_ZToWord : forall z sz,
    (- Z.of_nat (pow2 sz) <= z < Z.of_nat (pow2 sz))%Z -> wordToZ (ZToWord (S sz) z) = z.
Proof. word_lia_Z. Qed.

Lemma wordToN_combine : forall sz1 (w1 : word sz1) sz2 (w2 : word sz2),
    wordToN (combine w1 w2) = (wordToN w1 + Npow2 sz1 * wordToN w2)%N.
Proof. word_lia_Z. Qed.

Lemma wordToN_NToWord_2 : forall sz n, (n < Npow2 sz)%N -> wordToN (NToWord sz n) = n.
Proof. word_lia_Z. Qed.

Theorem split1_0 : forall n w Heq, split1 n 0 (eq_rect _ word w _ Heq) = w.
Proof. word_lia_Z. Qed.

Lemma wordToZ_combine_WO : forall sz (w : word sz), wordToZ (combine w WO) = wordToZ w.
Proof. word_lia_Z. Qed.

Lemma wordToN_0 : forall sz, wordToN (natToWord sz 0) = 0%N.
Proof. word_lia_Z. Qed.

Lemma wordToN_wzero : forall sz, wordToN (wzero sz) = 0%N.
Proof. word_lia_Z. Qed.

Lemma wordToNat_natToWord_le : forall sz n, (wordToNat (natToWord sz n) <= n)%nat.
Proof.
  intros; cbv [wordToNat]; rewrite unsigned_natToWord; pose proof (Zpow2_pos sz).
  pose proof (Z.mod_le (Z.of_nat n) (Zpow2 sz) ltac:(lia) ltac:(lia)).
  pose proof (Z.mod_pos_bound (Z.of_nat n) (Zpow2 sz) ltac:(lia)); lia.
Qed.

Lemma wordToZ_ZToWord_full sz (H: (0 < sz)%nat) (z:Z) :
  wordToZ (ZToWord sz z) = ((z + 2 ^ (Z.of_nat sz - 1)) mod (2 ^ Z.of_nat sz) - 2 ^ (Z.of_nat sz - 1))%Z.
Proof.
  destruct sz; [lia|].
  replace (Z.of_nat (S sz) - 1)%Z with (Z.of_nat sz) by lia.
  rewrite <- !Zpow2_eqn, signed_eqn, Zmod.unsigned_of_Z, Zpow2_S.
  pose proof (Zpow2_pos sz).
  pose proof (Z.mod_pos_bound z (2 * Zpow2 sz) ltac:(lia)).
  rewrite Zplus_mod, (Z.mod_small (Zpow2 sz)) by lia.
  set (r := (z mod (2 * Zpow2 sz))%Z) in *; clearbody r.
  destruct (Z.ltb_spec (2 * r) (2 * Zpow2 sz)).
  - rewrite Z.mod_small by lia; lia.
  - rewrite Zmod_small_2 by lia; lia.
Qed.

Theorem wordToN_nat : forall sz (w : word sz), wordToN w = N_of_nat (wordToNat w).
Proof. word_lia_Z. Qed.

Theorem wnot_zero : forall sz, wnot (wzero sz) = wones sz.
Proof. intros; apply bits.not_0. Qed.

Lemma lt_wlt : forall sz (n m : word sz), (wordToNat n < wordToNat m)%nat -> n < m.
Proof. word_lia_Z. Qed.

Lemma wordToNat_split1 : forall sz1 sz2 (w : word (sz1 + sz2)),
    wordToNat (split1 _ _ w) = Nat.modulo (wordToNat w) (pow2 sz1).
Proof.
  intros; cbv [wordToNat]; rewrite unsigned_split1.
  pose proof (unsigned_range w); pose proof (Zpow2_pos sz1).
  rewrite Z2Nat.inj_mod by lia. rewrite <- (pow2_Z sz1), Nat2Z.id; reflexivity.
Qed.

Lemma wordToNat_natToWord_eqn : forall sz n, wordToNat (natToWord sz n) = (n mod pow2 sz)%nat.
Proof.
  intros; cbv [wordToNat]; rewrite unsigned_natToWord; pose proof (Zpow2_pos sz).
  rewrite Z2Nat.inj_mod by lia. rewrite <- (pow2_Z sz), !Nat2Z.id; reflexivity.
Qed.

Lemma wordToNat_eq_rect : forall sz (w : word sz) nsz Hsz,
    wordToNat (eq_rect _ word w nsz Hsz) = wordToNat w.
Proof. intros; subst; reflexivity. Qed.

Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).
Proof. word_lia_Z. Qed.

Lemma unsigned_wzero : forall sz, uwordToZ (wzero sz) = 0%Z.
Proof. intros; apply Zmod.unsigned_0. Qed.

Lemma unsigned_ZToWord : forall sz z, uwordToZ (ZToWord sz z) = (z mod Zpow2 sz)%Z.
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Theorem weqb_true_iff : forall sz x y, @weqb sz x y = true <-> x = y.
Proof. intros; apply Zmod.eqb_eq. Qed.

Lemma wordToN_to_nat : forall sz (w : word sz), N.to_nat (wordToN w) = wordToNat w.
Proof. word_lia_Z. Qed.

Lemma pow2_pos_Z : forall n, (0 < 2 ^ Z.of_nat n)%Z.
Proof. intros; rewrite <- Zpow2_eqn; apply Zpow2_pos. Qed.

Lemma pow2_add_Z : forall a b, (2 ^ Z.of_nat (a + b) = 2 ^ Z.of_nat a * 2 ^ Z.of_nat b)%Z.
Proof. intros; rewrite <- !Zpow2_eqn; apply Zpow2_add. Qed.

Lemma ZToWord_Z_of_N : forall sz n, ZToWord sz (Z.of_N n) = NToWord sz n.
Proof. reflexivity. Qed.

Theorem combine_assoc : forall n1 (w1 : word n1) n2 n3 (w2 : word n2) (w3 : word n3) Heq,
  combine (combine w1 w2) w3
  = match Heq in _ = N return word N with
      | refl_equal => combine w1 (combine w2 w3)
    end.
Proof. word_lia_Z. Qed.

Lemma rewrite_weq : forall sz (a b : word sz) (pf : a = b), weq a b = left _ pf.
Proof.
  intros; destruct (weq a b) as [e|n]; [f_equal; apply weq_dec_eq | elim n; exact pf].
Qed.

Lemma wordToZ_size : forall sz (w : word (S sz)), (Z.abs (wordToZ w) <= Z.of_nat (pow2 sz))%Z.
Proof. word_lia_Z. Qed.

Lemma wordToZ_ZToWord'' : forall (sz : nat), (0 < sz)%nat ->
    forall n : Z, (- 2 ^ (Z.of_nat sz - 1) <= n < 2 ^ (Z.of_nat sz - 1))%Z ->
      wordToZ (ZToWord sz n) = n.
Proof.
  intros; rewrite wordToZ_ZToWord_full by assumption.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat sz - 1) ltac:(lia) ltac:(lia)).
  replace (2 ^ Z.of_nat sz)%Z with (2 * 2 ^ (Z.of_nat sz - 1))%Z
    by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  rewrite Z.mod_small by lia; lia.
Qed.
