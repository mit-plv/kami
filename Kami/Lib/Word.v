(** Fixed precision machine words.

    [word n] is the standard library's [bits (Z.of_nat n)] (that is,
    [Zmod (2 ^ Z.of_nat n)]).  Every operation is a named wrapper, marked
    [simpl never], around a [Zmod.of_Z] of its integer specification, and
    every fact is proved by moving to [Zmod.unsigned] and reasoning in [Z]
    (see [word_to_Z] below).  Do not compute with words in proofs: rewrite
    with the [unsigned_*] lemmas instead.

    Side effect on importers: this file requires [ZifyNat] and [ZifyN], so
    importing it registers those [Zify] instances globally and [lia]/[nia]
    will understand [Nat.pow]/[Nat.div]/[Nat.mod] and their [N] counterparts
    everywhere downstream.  The [simpl never] declarations below cover only
    Kami's own operations, not stdlib's [Zmod.unsigned]/[Zmod.signed]/
    [Zmod.of_Z]. *)

From Stdlib Require Import Arith NArith ZArith Bool Lia ZifyNat ZifyN.
From Stdlib Require Import Eqdep_dec EqdepFacts.
From Stdlib Require Import Ring Ring_polynom.
From Stdlib Require Export Zmod.
From Stdlib Require Export Zmod.Bits.
From Kami Require Import Nlia NatLib DepEq N_Z_nat_conversions.

Set Implicit Arguments.

(*! Definitions *)

(** * [word] *)

Definition word (n : nat) : Set := bits (Z.of_nat n).

Declare Scope word_scope.
Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Open Scope word_scope.

(** [unsigned] is the defining projection; everything else is specified
    through it. *)
Local Notation unsigned := Zmod.unsigned (only parsing).
Local Notation ofZ := Zmod.of_Z (only parsing).

(** [WO] and [WS] build a word bit by bit, least significant bit first. *)
Notation WO := (@Zmod.zero (2 ^ Z.of_nat 0) : word 0) (only parsing).
Definition WS (b : bool) (n : nat) (w : word n) : word (S n) :=
  ofZ _ (Z.b2z b + 2 * unsigned w).

(** * Conversion to and from [nat] (or [N]), zero and one *)

Definition wordToNat sz (w : word sz) : nat := Z.to_nat (unsigned w).

Definition natToWord (sz n : nat) : word sz := ofZ _ (Z.of_nat n).

Definition wordToN sz (w : word sz) : N := Z.to_N (unsigned w).

Definition NToWord (sz : nat) (n : N) : word sz := ofZ _ (Z.of_N n).

(** * MSB, LSB, head, and tail *)

(** The sign bit; [a] is the answer for the empty word. *)
Definition wmsb sz (w : word sz) (a : bool) : bool :=
  match sz with
  | O => a
  | S _ => (Zmod.signed w <? 0)%Z
  end.

Definition whd sz (w : word (S sz)) : bool := Z.odd (unsigned w).

Definition wtl sz (w : word (S sz)) : word sz := ofZ _ (unsigned w / 2).

(** * Decidable equality *)

Definition weq : forall sz (x y : word sz), {x = y} + {x <> y}.
  refine (fun sz x y =>
            match Zmod.eqb x y as b return Zmod.eqb x y = b -> {x = y} + {x <> y} with
            | true => fun H => left _
            | false => fun H => right _
            end eq_refl);
    abstract (destruct (Zmod.eqb_spec x y); congruence).
Defined.

(** * Combining and splitting *)

Definition combine (sz1 : nat) (w : word sz1) (sz2 : nat) (w' : word sz2)
  : word (sz1 + sz2) :=
  ofZ _ (unsigned w + 2 ^ Z.of_nat sz1 * unsigned w').

Definition split1 (sz1 sz2 : nat) (w : word (sz1 + sz2)) : word sz1 :=
  Zmod.firstn (Z.of_nat sz1) w.

Definition split2 (sz1 sz2 : nat) (w : word (sz1 + sz2)) : word sz2 :=
  ofZ _ (unsigned w / 2 ^ Z.of_nat sz1).

(** * Extension operators *)

Definition sext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  ofZ _ (Zmod.signed w).

Definition zext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  ofZ _ (unsigned w).

(** * Arithmetic *)

Definition wdivN sz (x y : word sz) : word sz := natToWord sz (wordToNat x / wordToNat y).
Definition wremN sz (x y : word sz) : word sz := natToWord sz (wordToNat x mod wordToNat y).

Notation "w ~ 1" := (WS true w) : word_scope.
Notation "w ~ 0" := (WS false w) : word_scope.

Notation "^~" := Zmod.opp.
Notation "l ^+ r" := (Zmod.add l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (Zmod.mul l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (Zmod.sub l%word r%word) (at level 50, left associativity).

(** * Bitwise operators *)

(** * Conversion to and from [Z] *)

(** * Arithmetic by [Z] *)

(** Signed division by zero yields zero (the standard library's [squot]
    yields [-1]); the remainder agrees with [srem] everywhere. *)
Definition wdivZ sz (x y : word sz) : word sz :=
  if Zmod.eqb y ((@Zmod.zero (2 ^ Z.of_nat sz))) then (@Zmod.zero (2 ^ Z.of_nat sz)) else Zmod.squot x y.

(** * Comparison predicates and deciders *)

Definition wlt sz (l r : word sz) : Prop :=
  Z.lt (Zmod.unsigned l) (Zmod.unsigned r).

Notation "w1 > w2" := (@wlt _ w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(@wlt _ w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (@wlt _ w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(@wlt _ w2%word w1%word)) : word_scope.

Notation "$ n" := (natToWord _ n) (at level 1, format "$ n").
Notation "# n" := (wordToNat n) (at level 5, format "# n").

(** * Bit shifting *)

Definition extz {sz} (w: word sz) (n: nat) : word (n + sz) :=
  ofZ _ (2 ^ Z.of_nat n * unsigned w).

Definition wpow2 sz : word (S sz) := ofZ _ (2 ^ Z.of_nat sz).

(** * Setting an individual bit *)

(** Never compute with any of the above; rewrite with the [unsigned_*]
    facts instead (reducing through [Zmod.of_Z] duplicates subterms at
    every nesting level). *)
Arguments WS _ [_] _ : simpl never.
Arguments wordToNat [_] _ : simpl never.
Arguments natToWord _ _ : simpl never.
Arguments wordToN [_] _ : simpl never.
Arguments NToWord _ _ : simpl never.
Arguments wmsb [_] _ _ : simpl never.
Arguments whd [_] _ : simpl never.
Arguments wtl [_] _ : simpl never.
Arguments weq [_] _ _ : simpl never.
Arguments combine [_] _ [_] _ : simpl never.
Arguments split1 _ _ _ : simpl never.
Arguments split2 _ _ _ : simpl never.
Arguments sext [_] _ _ : simpl never.
Arguments zext [_] _ _ : simpl never.
Arguments wdivN [_] _ _ : simpl never.
Arguments wremN [_] _ _ : simpl never.
Arguments wdivZ [_] _ _ : simpl never.
Arguments wlt [_] _ _ : simpl never.
Arguments extz [_] _ _ : simpl never.
Arguments wpow2 _ : simpl never.

(*! Facts *)

(** * The [unsigned] characterization of every operation *)

Local Open Scope Z_scope.

Lemma pow2_Z : forall n, Z.of_nat (pow2 n) = 2 ^ Z.of_nat n.
Proof. intros; apply Nat2Z.inj_pow. Qed.

(** [lia] sees [Npow2] as [2 ^ _] ([pow2] is [Nat.pow 2], already known). *)
#[global] Instance Op_Npow2 : ZifyClasses.UnOp Npow2 :=
  { ZifyClasses.TUOp := fun x => 2 ^ x; ZifyClasses.TUOpInj := NatLib.Z_of_N_Npow2 }.
Add Zify UnOp Op_Npow2.

Lemma unsigned_range : forall sz (w : word sz), 0 <= unsigned w < 2 ^ Z.of_nat sz.
Proof. intros; apply bits.unsigned_range, Nat2Z.is_nonneg. Qed.

Lemma unsigned_eq_rect : forall n n' (w : word n) (H : n = n'),
    unsigned (eq_rect n word w n' H) = unsigned w.
Proof. intros; destruct H; reflexivity. Qed.

Lemma unsigned_eq_rec : forall n n' (w : word n) (H : n = n'),
    unsigned (eq_rec n word w n' H) = unsigned w.
Proof. intros; destruct H; reflexivity. Qed.

Lemma unsigned_match_eq : forall n n' (w : word n) (H : n = n'),
    unsigned (match H in _ = N return word N with eq_refl => w end) = unsigned w.
Proof. intros; destruct H; reflexivity. Qed.

(** [signed] in terms of [unsigned]. *)
Lemma signed_eqn : forall sz (w : word sz),
    Zmod.signed w = if 2 * unsigned w <? 2 ^ Z.of_nat sz then unsigned w else unsigned w - 2 ^ Z.of_nat sz.
Proof.
  intros; cbv [Zmod.signed]; pose proof (unsigned_range w).
  rewrite Z.double_spec, !Z.abs_eq by lia.
  reflexivity.
Qed.

Lemma pow2_S_Z : forall n, 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n.
Proof. intros; rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia. Qed.

Lemma pow2_add_Z : forall a b, 2 ^ Z.of_nat (a + b) = 2 ^ Z.of_nat a * 2 ^ Z.of_nat b.
Proof. intros; rewrite Nat2Z.inj_add, Z.pow_add_r; lia. Qed.

Lemma pow2_mul_Z : forall a b, 2 ^ Z.of_nat (a * b) = (2 ^ Z.of_nat a) ^ Z.of_nat b.
Proof. intros; rewrite Nat2Z.inj_mul, Z.pow_mul_r; lia. Qed.

Lemma pow2_pos_Z : forall n, 0 < 2 ^ Z.of_nat n.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_eq1_Z : forall x : nat, Z.of_nat x = 0 -> 2 ^ Z.of_nat x = 1.
Proof. intros x H; rewrite H; reflexivity. Qed.

Lemma pow2_ge2_Z : forall x : nat, Z.of_nat x <> 0 -> 2 <= 2 ^ Z.of_nat x.
Proof. intros x H; destruct x; [lia|]; rewrite pow2_S_Z; pose proof (pow2_pos_Z x); lia. Qed.

Lemma pow2_even_Z : forall x : nat, Z.of_nat x <> 0 -> (2 ^ Z.of_nat x) mod 2 = 0.
Proof. intros x H; destruct x; [lia|]; rewrite pow2_S_Z, Z.mul_comm; apply Z.mod_mul; lia. Qed.

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

(** Range facts whose width is a compound expression, stated so that the
    width arithmetic is already done (the width also occurs in the type of
    [w], which blocks rewriting it inside [unsigned w]). *)
Lemma unsigned_range_S : forall sz (w : word (S sz)), 0 <= unsigned w < 2 * 2 ^ Z.of_nat sz.
Proof.
  intros; pose proof (unsigned_range w) as H.
  set (x := unsigned w) in *; clearbody x. rewrite pow2_S_Z in H; lia.
Qed.

Lemma unsigned_range_add : forall sz1 sz2 (w : word (sz1 + sz2)),
    0 <= unsigned w < 2 ^ Z.of_nat sz1 * 2 ^ Z.of_nat sz2.
Proof.
  intros; pose proof (unsigned_range w) as H.
  set (x := unsigned w) in *; clearbody x. rewrite pow2_add_Z in H; lia.
Qed.
Arguments unsigned_range_add {_ _} _.
Arguments unsigned_range_S {_} _.

Lemma unsigned_WS : forall b n (w : word n), unsigned (WS b w) = Z.b2z b + 2 * unsigned w.
Proof.
  intros; cbv [WS]; apply Zmod.unsigned_of_Z_small.
  pose proof (unsigned_range w); rewrite pow2_S_Z.
  destruct b; cbn [Z.b2z]; lia.
Qed.

Lemma unsigned_natToWord : forall sz n, unsigned (natToWord sz n) = Z.of_nat n mod 2 ^ Z.of_nat sz.
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_NToWord : forall sz n, unsigned (NToWord sz n) = Z.of_N n mod 2 ^ Z.of_nat sz.
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_wtl : forall sz (w : word (S sz)), unsigned (wtl w) = unsigned w / 2.
Proof.
  intros; cbv [wtl]; apply Zmod.unsigned_of_Z_small.
  pose proof (unsigned_range_S w).
  Z.div_mod_to_equations; lia.
Qed.

Lemma whd_eqn : forall sz (w : word (S sz)), whd w = Z.odd (unsigned w).
Proof. reflexivity. Qed.

Lemma unsigned_combine : forall sz1 (w : word sz1) sz2 (w' : word sz2),
    unsigned (combine w w') = unsigned w + 2 ^ Z.of_nat sz1 * unsigned w'.
Proof.
  intros; cbv [combine]; apply Zmod.unsigned_of_Z_small.
  pose proof (unsigned_range w); pose proof (unsigned_range w').
  rewrite pow2_add_Z. nia.
Qed.

Lemma unsigned_split1 : forall sz1 sz2 (w : word (sz1 + sz2)),
    unsigned (split1 sz1 sz2 w) = unsigned w mod 2 ^ Z.of_nat sz1.
Proof. intros; apply bits.unsigned_firstn. Qed.

Lemma unsigned_split2 : forall sz1 sz2 (w : word (sz1 + sz2)),
    unsigned (split2 sz1 sz2 w) = unsigned w / 2 ^ Z.of_nat sz1.
Proof.
  intros; cbv [split2]; apply Zmod.unsigned_of_Z_small.
  pose proof (unsigned_range_add w).
  pose proof (pow2_pos_Z sz1); pose proof (pow2_pos_Z sz2).
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

Lemma unsigned_zext : forall sz (w : word sz) sz',
    unsigned (zext w sz') = unsigned w.
Proof.
  intros; cbv [zext]; apply Zmod.unsigned_of_Z_small.
  pose proof (unsigned_range w); pose proof (pow2_pos_Z sz'); rewrite pow2_add_Z; nia.
Qed.

Lemma unsigned_extz : forall sz (w : word sz) n,
    unsigned (extz w n) = 2 ^ Z.of_nat n * unsigned w.
Proof.
  intros; cbv [extz]; apply Zmod.unsigned_of_Z_small.
  pose proof (unsigned_range w); pose proof (pow2_pos_Z n); rewrite pow2_add_Z; nia.
Qed.

Lemma unsigned_wnot : forall sz (w : word sz), unsigned (Zmod.not w) = 2 ^ Z.of_nat sz - 1 - unsigned w.
Proof.
  intros; cbv [Zmod.not]; rewrite Zmod.unsigned_of_Z.
  pose proof (unsigned_range w).
  replace (Z.lnot (unsigned w)) with (2 ^ Z.of_nat sz - 1 - unsigned w + (-1) * 2 ^ Z.of_nat sz) by (unfold Z.lnot; lia).
  rewrite Z.mod_add by lia; apply Z.mod_small; lia.
Qed.

Lemma unsigned_wlshift : forall sz (w : word sz) n,
    unsigned (Zmod.slu w (Z.of_nat n)) = (unsigned w * 2 ^ Z.of_nat n) mod 2 ^ Z.of_nat sz.
Proof. intros; rewrite Zmod.unsigned_slu, Z.shiftl_mul_pow2 by lia; reflexivity. Qed.

Lemma unsigned_wrshift : forall sz (w : word sz) n,
    unsigned (Zmod.sru w (Z.of_nat n)) = unsigned w / 2 ^ Z.of_nat n.
Proof. intros; rewrite Zmod.unsigned_sru, Z.shiftr_div_pow2 by lia; reflexivity. Qed.

Lemma unsigned_wrshifta : forall sz (w : word sz) n,
    unsigned (Zmod.srs w (Z.of_nat n)) = (Zmod.signed w / 2 ^ Z.of_nat n) mod 2 ^ Z.of_nat sz.
Proof. intros; rewrite Zmod.unsigned_srs, Z.shiftr_div_pow2 by lia; reflexivity. Qed.

Lemma unsigned_wpow2 : forall sz, unsigned (wpow2 sz) = 2 ^ Z.of_nat sz.
Proof.
  intros; cbv [wpow2]; apply Zmod.unsigned_of_Z_small.
  rewrite pow2_S_Z; pose proof (pow2_pos_Z sz); lia.
Qed.

Lemma wmsb_S : forall sz (w : word sz) a, sz <> 0%nat -> wmsb w a = (Zmod.signed w <? 0).
Proof. intros; destruct sz; [lia | reflexivity]. Qed.

Lemma wmsb_eqn : forall sz (w : word (S sz)) a, wmsb w a = (2 ^ Z.of_nat sz <=? unsigned w).
Proof.
  intros; cbv [wmsb]; rewrite signed_eqn; pose proof (unsigned_range_S w); pose proof (pow2_S_Z sz).
  destruct (Z.ltb_spec (2 * unsigned w) (2 ^ Z.of_nat (S sz))); cbv iota;
    destruct (Z.leb_spec (2 ^ Z.of_nat sz) (unsigned w));
    [ destruct (Z.ltb_spec (unsigned w) 0) | destruct (Z.ltb_spec (unsigned w) 0)
    | destruct (Z.ltb_spec (unsigned w - 2 ^ Z.of_nat (S sz)) 0)
    | destruct (Z.ltb_spec (unsigned w - 2 ^ Z.of_nat (S sz)) 0) ];
    first [ reflexivity | lia ].
Qed.

Lemma Zmod_small_neg : forall a m, 0 < m -> - m <= a < 0 -> a mod m = a + m.
Proof.
  intros. rewrite <- (Z.mod_add a 1 m), Z.mod_small by lia. lia.
Qed.

Lemma unsigned_opp_one : forall sz, unsigned (@Zmod.opp (2 ^ Z.of_nat sz) Zmod.one) = 2 ^ Z.of_nat sz - 1.
Proof.
  intros; rewrite Zmod.unsigned_m1, (@Zmod_small_neg (-1)) by (pose proof (pow2_pos_Z sz); lia).
  lia.
Qed.

Lemma Zmod_small_2 : forall a m, 0 < m -> m <= a < 2 * m -> a mod m = a - m.
Proof.
  intros. rewrite <- (Z.mod_add a (-1) m), Z.mod_small by lia. lia.
Qed.

Lemma Zmod_2mul_odd : forall a p, 0 < p -> (2 * a + 1) mod (2 * p) = 1 + 2 * (a mod p).
Proof.
  intros. rewrite Z.rem_mul_r by lia.
  replace (2 * a + 1) with (1 + a * 2) by lia. rewrite Z.mod_add, Z.div_add by lia.
  rewrite Z.mod_small, Z.div_small by lia. f_equal; f_equal; f_equal; lia.
Qed.

Lemma Zmod_2mul_odd' : forall a p, 0 < p -> (1 + 2 * a) mod (2 * p) = 1 + 2 * (a mod p).
Proof.
  intros. rewrite <- Zmod_2mul_odd by lia. f_equal; lia.
Qed.

Lemma Zmod_2mul_split : forall a p, 0 < p -> a mod (2 * p) = a mod 2 + 2 * ((a / 2) mod p).
Proof.
  intros. apply Z.rem_mul_r; lia.
Qed.

Lemma Zmod_mul2_split : forall a p, 0 < p -> a mod (p * 2) = a mod 2 + 2 * ((a / 2) mod p).
Proof.
  intros. rewrite Z.mul_comm. apply Z.rem_mul_r; lia.
Qed.

Lemma Zdiv_add_mul_l : forall a b c, c <> 0 -> (a + c * b) / c = a / c + b.
Proof.
  intros. rewrite Z.mul_comm. apply Z.div_add; assumption.
Qed.

Lemma Zmod_add_mul_l : forall a b c, c <> 0 -> (a + c * b) mod c = a mod c.
Proof.
  intros. rewrite Z.mul_comm. apply Z.mod_add; assumption.
Qed.

Lemma existT_word_eq : forall n1 (w1 : word n1) n2 (w2 : word n2),
    n1 = n2 -> unsigned w1 = unsigned w2 -> existT word n1 w1 = existT word n2 w2.
Proof.
  intros; subst; f_equal; apply Zmod.unsigned_inj; assumption.
Qed.

Lemma existT_word_inv : forall n1 (w1 : word n1) n2 (w2 : word n2),
    existT word n1 w1 = existT word n2 w2 -> n1 = n2 /\ unsigned w1 = unsigned w2.
Proof.
  intros. pose proof (eq_sigT_fst H). subst.
  apply inj_pair2_eq_dec in H; [subst; auto | apply Nat.eq_dec].
Qed.

Lemma wmsb_eqn_gen : forall sz (w : word sz) b,
    wmsb w b = if Z.of_nat sz =? 0 then b else (2 ^ Z.of_nat sz <=? 2 * unsigned w).
Proof.
  intros; destruct sz; [reflexivity|].
  rewrite wmsb_eqn. destruct (Z.eqb_spec (Z.of_nat (S sz)) 0); [lia|].
  set (x := unsigned w) in *; clearbody x. rewrite pow2_S_Z.
  destruct (Z.leb_spec (2 ^ Z.of_nat sz) x);
    destruct (Z.leb_spec (2 * 2 ^ Z.of_nat sz) (2 * x)); lia.
Qed.

Lemma unsigned_sext : forall sz (w : word sz) sz',
    unsigned (sext w sz') = Zmod.signed w mod 2 ^ Z.of_nat (sz + sz').
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

(** * A few facts about [mod] and [div] by products (for split/combine) *)

Lemma Zmod_mul_split : forall a p q, 0 < p -> 0 < q -> a mod (p * q) = a mod p + p * ((a / p) mod q).
Proof.
  intros. apply Z.rem_mul_r; lia.
Qed.

Lemma Zmod_opp_sub : forall z p, p <> 0 -> (- z) mod p = (p - z) mod p.
Proof.
  intros. replace (p - z) with (- z + 1 * p) by lia. rewrite Z.mod_add; lia.
Qed.

(** [z] just below a multiple [2*p*t] of [2*p] reduces to [z - 2*p*t + 2*p]. *)
Lemma Zmod_upper : forall z p t, 0 < p -> 0 < t ->
    2 * p * t - p <= z < 2 * p * t -> z mod (2 * p) = z - 2 * p * t + 2 * p.
Proof.
  intros; rewrite <- (Z.mod_add z (1 - t) (2 * p)) by lia.
  rewrite Z.mod_small by nia. lia.
Qed.

Lemma Zopp_mod_idemp : forall a p, p <> 0 -> (- (a mod p)) mod p = (- a) mod p.
Proof.
  intros. rewrite <- (Z.sub_0_l (a mod p)), Zminus_mod_idemp_r, Z.sub_0_l. reflexivity.
Qed.

Lemma Zadd_mod_cancel_r : forall a b c p, 0 < p -> 0 <= a < p -> 0 <= b < p ->
    (a + c) mod p = (b + c) mod p -> a = b.
Proof.
  intros.
  rewrite <- (Z.mod_small a p), <- (Z.mod_small b p) by lia.
  replace a with (a + c - c) by lia. replace b with (b + c - c) by lia.
  rewrite (Zminus_mod (a + c)), (Zminus_mod (b + c)), H2. reflexivity.
Qed.

Lemma Zmod_sub_eq : forall a b p, 0 < p -> 0 <= a < p -> 0 <= b < p -> (a - b) mod p = 0 -> a = b.
Proof.
  intros. destruct (Z.le_gt_cases b a).
  - rewrite Z.mod_small in H2; lia.
  - rewrite <- (Z.mod_add (a - b) 1 p), Z.mod_small in H2 by lia. lia.
Qed.

(** * Moving word goals to [Z] *)

#[global] Hint Rewrite Zmod.unsigned_0 unsigned_WS unsigned_natToWord unsigned_NToWord
  Zmod.unsigned_of_Z Zmod.unsigned_1
  unsigned_opp_one unsigned_wtl whd_eqn unsigned_combine unsigned_split1 unsigned_split2
  unsigned_sext unsigned_zext unsigned_extz Zmod.unsigned_opp Zmod.unsigned_add Zmod.unsigned_sub
  Zmod.unsigned_mul Zmod.unsigned_umod unsigned_wnot bits.unsigned_or bits.unsigned_and
  bits.unsigned_xor unsigned_wlshift unsigned_wrshift unsigned_wrshifta unsigned_wpow2
  wmsb_eqn_gen signed_eqn unsigned_eq_rect unsigned_eq_rec unsigned_match_eq
  : unsigned_word.

(** Turn equalities and disequalities of words into ones of [unsigned]. *)
(** The width of a word type, however it is spelled. *)
Ltac word_width T :=
  lazymatch T with
  | word ?n => n
  | bits (Z.of_nat ?n) => n
  | Zmod (2 ^ Z.of_nat ?n) => n
  end.

Ltac word_eq_to_unsigned :=
  repeat match goal with
         | |- @eq ?T _ _ => let n := word_width T in apply Zmod.unsigned_inj
         | |- not (@eq ?T _ _) =>
           let n := word_width T in
           let H := fresh "Hw" in intro H; apply (f_equal (@Zmod.unsigned _)) in H
         | |- (@eq ?T _ _) -> False =>
           let n := word_width T in
           let H := fresh "Hw" in intro H; apply (f_equal (@Zmod.unsigned _)) in H
         | H : @eq ?T _ _ |- _ =>
           let n := word_width T in apply (f_equal (@Zmod.unsigned _)) in H
         | H : not (@eq ?T ?a ?b) |- _ =>
           let n := word_width T in
           let H' := fresh "Hw" in
           assert (H' : unsigned a <> unsigned b)
             by (let E := fresh in intro E; apply H; apply Zmod.unsigned_inj; exact E);
           clear H
         | H : (@eq ?T ?a ?b) -> False |- _ =>
           let n := word_width T in
           let H' := fresh "Hw" in
           assert (H' : unsigned a <> unsigned b)
             by (let E := fresh in intro E; apply H; apply Zmod.unsigned_inj; exact E);
           clear H
         | |- existT word _ _ = existT word _ _ => apply existT_word_eq; [ lia | ]
         | H : existT word _ _ = existT word _ _ |- _ =>
           apply existT_word_inv in H; destruct H
         end.

(** Case-split the boolean tests produced by [wmsb_eqn], [signed_eqn], [whd_eqn]. *)
Ltac word_split_bools :=
  repeat match goal with
         | H : context [Z.leb _ _] |- _ => revert H
         | H : context [Z.ltb _ _] |- _ => revert H
         | H : context [Z.eqb _ _] |- _ => revert H
         | H : context [Z.odd _] |- _ => revert H
         end;
  repeat match goal with
         | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
         | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
         | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
         | |- context [Z.odd ?u] =>
           let E := fresh "Hodd" in
           pose proof (Z.div2_odd u) as E; rewrite Z.div2_div in E; revert E;
           destruct (Z.odd u); intro E
         end;
  intros; cbn [Z.b2z] in *.

(** Replace every [unsigned w] by a fresh integer in range, so that the
    width arithmetic can be rewritten afterwards. *)
Ltac gen_unsigned :=
  repeat match goal with
         | H : context [@Zmod.unsigned _ _] |- _ => revert H
         end;
  repeat match goal with
         | |- context [@Zmod.unsigned ?m ?w] =>
           let H := fresh "Hr" in
           pose proof (unsigned_range w) as H;
           (* The modulus is an implicit argument and may be spelled
              differently at different occurrences (e.g. [0 + n] vs [n]);
              make every occurrence use the one from [w]'s type. *)
           let m0 := match type of H with
                     | context [@Zmod.unsigned ?m0 w] => m0
                     end in
           repeat match goal with
                  | |- context [@Zmod.unsigned ?m' w] =>
                    tryif constr_eq m' m0 then fail
                    else (let E := fresh in
                          assert (E : @Zmod.unsigned m' w = @Zmod.unsigned m0 w) by reflexivity;
                          rewrite E; clear E)
                  end;
           revert H; generalize (@Zmod.unsigned m0 w)
         end;
  intros.

(** Powers of two and [Z.of_nat]/[Z.of_N] pushed through arithmetic, so that
    the [Z] lemmas apply. *)
#[global] Hint Rewrite pow2_S pow2_add_mul Npow2_S pow2_S_Z pow2_add_Z pow2_mul_Z : word_pow2.
#[global] Hint Rewrite Nat2Z.inj_mul Nat2Z.inj_add Nat2Z.inj_pow Nat2Z.inj_div Nat2Z.inj_mod
  NatLib.Z_of_N_Npow2 N2Z.inj_mul N2Z.inj_add N2Z.inj_div N2Z.inj_mod N2Z.inj_pow nat_N_Z
  : word_inj.
#[global] Hint Rewrite Nat2Z.inj_sub using lia : word_inj.

Ltac pow2_normalize :=
  autorewrite with word_pow2 in *; autorewrite with word_inj in *;
  rewrite ?Z.pow_0_r, ?Z.pow_1_r in *;
  change (Z.of_nat 0) with 0%Z in *; change (Z.of_nat 1) with 1%Z in *;
  change (Z.of_nat 2) with 2%Z in *;
  change (Z.of_N 0) with 0%Z in *; change (Z.of_N 1) with 1%Z in *;
  change (Z.of_N 2) with 2%Z in *.

(** Tell [lia] how [2 ^ Z.of_nat x] relates to [x = 0]. *)
Ltac pow2_fact x :=
  lazymatch goal with
  | _ : Z.of_nat x = 0%Z -> (2 ^ Z.of_nat x)%Z = 1%Z |- _ => fail
  | _ => pose proof (pow2_eq1_Z x); pose proof (pow2_ge2_Z x)
  end.

Ltac pow2_facts :=
  repeat match goal with
         | |- context [(2 ^ Z.of_nat ?x)%Z] => pow2_fact x
         | H : context [(2 ^ Z.of_nat ?x)%Z] |- _ => pow2_fact x
         end.

(** [pow2] is the [nat]-valued power of two; [lia] sees [Z.of_nat (pow2 x)] as
    an opaque atom, so relate it to [2 ^ Z.of_nat x] for every [pow2] around. *)
Ltac pow2_nat_fact x :=
  lazymatch goal with
  | _ : Z.of_nat (pow2 x) = (2 ^ Z.of_nat x)%Z |- _ => fail
  | _ => pose proof (pow2_Z x)
  end.

Ltac pow2_nat_facts :=
  repeat match goal with
         | |- context [pow2 ?x] => pow2_nat_fact x
         | H : context [pow2 ?x] |- _ => pow2_nat_fact x
         end.

(** The implicit modulus of [@Zmod.unsigned m t] must be spelled exactly as
    the width in the type of [t] for the rewrite rules to match (e.g.
    [S sz] vs [1 + sz]); make it so. *)
Ltac canon_unsigned_one m t :=
  let T := type of t in
  let n := word_width T in
  let m0 := constr:((2 ^ Z.of_nat n)%Z) in
  tryif constr_eq m m0 then fail
  else (let E := fresh in
        assert (E : @Zmod.unsigned m t = @Zmod.unsigned m0 t) by reflexivity;
        rewrite E in *; clear E).

Ltac canon_unsigned :=
  repeat match goal with
         | |- context [@Zmod.unsigned ?m ?t] => canon_unsigned_one m t
         | H : context [@Zmod.unsigned ?m ?t] |- _ => canon_unsigned_one m t
         end.

Ltac word_to_Z :=
  intros;
  repeat match goal with x := _ |- _ => subst x end;
  word_eq_to_unsigned;
  cbv [wordToNat wordToN wlt] in *;
  repeat progress (canon_unsigned; autorewrite with unsigned_word in *);
  word_split_bools;
  gen_unsigned;
  pow2_normalize;
  repeat match goal with
         | |- context [Z.of_nat (Z.to_nat ?z)] => rewrite (Z2Nat.id z) in * by lia
         | H : context [Z.of_nat (Z.to_nat ?z)] |- _ => rewrite (Z2Nat.id z) in * by lia
         | |- context [Z.of_N (Z.to_N ?z)] => rewrite (Z2N.id z) in * by lia
         | H : context [Z.of_N (Z.to_N ?z)] |- _ => rewrite (Z2N.id z) in * by lia
         end;
  repeat match goal with b : bool |- _ => destruct b end;
  cbn [Z.b2z] in *;
  rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l, ?Z.mul_1_r, ?Z.mul_0_l, ?Z.mul_0_r in *;
  rewrite <- ?Z.mul_opp_r in *;
  pow2_facts; pow2_nat_facts.

(** Simplify [mod]/[div] by a power of two whose argument is known to be
    in range, then finish with [lia]/[nia]. *)
Ltac word_side := first [ lia | nia ].

(** Value-range conditioned rules, tried at every occurrence. *)
Ltac word_mod_small_all :=
  repeat match goal with
         | |- context [(?a mod ?p)%Z] =>
           first [ rewrite (Z.mod_small a p) in * by word_side
                 | rewrite (@Zmod_small_neg a p) in * by word_side
                 | rewrite (@Zmod_small_2 a p) in * by word_side ]
         | H : context [(?a mod ?p)%Z] |- _ =>
           first [ rewrite (Z.mod_small a p) in * by word_side
                 | rewrite (@Zmod_small_neg a p) in * by word_side
                 | rewrite (@Zmod_small_2 a p) in * by word_side ]
         | |- context [(?a / ?p)%Z] => rewrite (Z.div_small a p) in * by word_side
         | H : context [(?a / ?p)%Z] |- _ => rewrite (Z.div_small a p) in * by word_side
         end.

(** Shape-conditioned rules (side conditions are positivity of moduli), in
    priority order: one step of the first rule that applies, then again from
    the top.  As an [autorewrite] database (each rule exhaustively, in list
    order) the normal forms differ and proofs below stop closing. *)
Ltac word_mod_rules :=
  (rewrite Z.mod_0_l in * by word_side) || (rewrite Z.div_0_l in * by word_side)
  || (rewrite Z.mod_mod in * by word_side)
  || rewrite Zplus_mod_idemp_l in * || rewrite Zplus_mod_idemp_r in *
  || rewrite Zmult_mod_idemp_l in * || rewrite Zmult_mod_idemp_r in *
  || (rewrite Z.mul_mod_distr_l in * by word_side) || (rewrite Z.mul_mod_distr_r in * by word_side)
  || (rewrite Z.div_mul_cancel_l in * by word_side) || (rewrite Z.div_mul_cancel_r in * by word_side)
  || (rewrite Z.mod_add in * by word_side) || (rewrite Z.div_add in * by word_side)
  || (rewrite Zmod_add_mul_l in * by word_side) || (rewrite Zdiv_add_mul_l in * by word_side)
  || (rewrite Z.div_div in * by word_side)
  || rewrite Zminus_mod_idemp_l in * || rewrite Zminus_mod_idemp_r in *
  || (rewrite Zopp_mod_idemp in * by word_side)
  || (rewrite Zmod_2mul_odd in * by word_side) || (rewrite Zmod_2mul_odd' in * by word_side)
  || (rewrite Zmod_opp_sub in * by word_side)
  || (rewrite Zmod_2mul_split in * by word_side)
  || (rewrite Zmod_mul2_split in * by word_side)
  || (rewrite Zmod_mul_split in * by word_side).

Ltac word_mod_simpl :=
  repeat progress (word_mod_small_all; repeat word_mod_rules).

Ltac mod_args_unify_1 x y :=
  tryif constr_eq x y then fail else
    lazymatch x with
    | context [y] => fail
    | _ => lazymatch y with
           | context [x] => fail
           | _ => replace y with x in * by lia
           end
    end.

Ltac mod_args_unify :=
  repeat match goal with
         | |- context [(?x mod ?p)%Z] =>
           match goal with
           | |- context [(?y mod ?p)%Z] => mod_args_unify_1 x y
           | H : context [(?y mod ?p)%Z] |- _ => mod_args_unify_1 x y
           end
         | H : context [(?x mod ?p)%Z] |- _ =>
           match goal with
           | |- context [(?y mod ?p)%Z] => mod_args_unify_1 x y
           | H' : context [(?y mod ?p)%Z] |- _ => mod_args_unify_1 x y
           end
         end.

(** The hammers: to [Z], simplify [mod]/[div], then [lia] (or [nia]). *)
Ltac word_lia_Z :=
  word_to_Z; try subst; rewrite ?Z.sub_diag in *;
  first [ lia
        | (word_mod_simpl; mod_args_unify; first [ lia | (f_equal; lia) | congruence ]) ].

Ltac word_nia_Z :=
  word_to_Z; try subst; rewrite ?Z.sub_diag in *;
  first [ lia
        | (word_mod_simpl; mod_args_unify; first [ lia | (f_equal; lia) | congruence | nia ])
        | nia ].

Local Close Scope Z_scope.

(** * Facts about [WO] and [WS] *)

#[global] Hint Rewrite div2_double div2_S_double: div2.
Local Hint Resolve mod2_S_double mod2_double.

Theorem word0: forall (w : word 0), w = WO.
Proof.
  word_lia_Z.
Qed.

Lemma shatter_word : forall n (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.
Proof.
  destruct n; intros; [apply word0|].
  apply Zmod.unsigned_inj. rewrite unsigned_WS, unsigned_wtl, whd_eqn.
  pose proof (Z.div2_odd (unsigned a)); rewrite Z.div2_div in H; lia.
Qed.

Lemma shatter_word_S : forall n (a : word (S n)),
  exists b, exists c, a = WS b c.
Proof.
  intros; repeat eexists; apply (shatter_word a).
Qed.
#[global] Hint Resolve word0.

Theorem natToWord_wordToNat : forall sz w, natToWord sz (wordToNat w) = w.
Proof.
  word_lia_Z.
Qed.

Theorem roundTrip_0 : forall sz, wordToNat (natToWord sz 0) = 0.
Proof.
  word_lia_Z.
Qed.

#[global] Hint Rewrite roundTrip_0 : wordToNat.

Lemma wordToNat_natToWord_2: forall sz w : nat,
    (w < pow2 sz)%nat -> wordToNat (natToWord sz w) = w.
Proof.
  word_lia_Z.
Qed.

Theorem combine_split : forall sz1 sz2 (w : word (sz1 + sz2)),
  combine (split1 sz1 sz2 w) (split2 sz1 sz2 w) = w.
Proof.
  word_to_Z; Z.div_mod_to_equations; nia.
Qed.

Theorem split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split1 sz1 sz2 (combine w z) = w.
Proof.
  word_to_Z. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Theorem split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split2 sz1 sz2 (combine w z) = z.
Proof.
  word_to_Z. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

#[global] Hint Rewrite combine_split.
#[global] Hint Rewrite split1_combine.
#[global] Hint Rewrite split2_combine.

Theorem combine_assoc : forall n1 (w1 : word n1) n2 n3 (w2 : word n2) (w3 : word n3) Heq,
  combine (combine w1 w2) w3
  = match Heq in _ = N return word N with
      | refl_equal => combine w1 (combine w2 w3)
    end.
Proof.
  word_lia_Z.
Qed.

Theorem split1_0 : forall n w Heq,
  split1 n 0 (eq_rect _ word w _ Heq) = w.
Proof.
  word_to_Z. apply Z.mod_small; lia.
Qed.

Theorem wordToN_nat : forall sz (w : word sz), wordToN w = N_of_nat (wordToNat w).
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_to_nat sz: forall (w: word sz), BinNat.N.to_nat (wordToN w) = wordToNat w.
Proof.
  word_lia_Z.
Qed.

Local Hint Extern 1 (@eq nat _ _) => lia.

Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).
Proof.
  word_lia_Z.
Qed.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.
Proof.
  word_lia_Z.
Qed.

Local Hint Extern 1 (_ <= _)%nat => lia.

Theorem roundTrip_1 : forall sz, wordToNat (natToWord (S sz) 1) = 1.
Proof.
  word_to_Z. pose proof (pow2_pos_Z sz). rewrite Z.mod_small; lia.
Qed.

Theorem wordToNat_bound : forall sz (w : word sz), (wordToNat w < pow2 sz)%nat.
Proof.
  word_lia_Z.
Qed.

Theorem natToWord_pow2 : forall sz, natToWord sz (pow2 sz) = natToWord sz 0.
Proof.
  word_lia_Z.
Qed.

Ltac is_nat_cst n :=
  match eval hnf in n with
    | O => constr:(true)
    | S ?n' => is_nat_cst n'
    | _ => constr:(false)
  end.

(** Constant recognition for [ring] on words: a term built from [WO], [WS]
    with literal bits, or [natToWord] of a literal.  The word itself is not
    put in [hnf], which would unfold [WO]/[WS]. *)
Ltac isWcst w :=
  match w with
    | WO => constr:(true)
    | WS ?b ?w' =>
      match eval hnf in b with
        | true => isWcst w'
        | false => isWcst w'
        | _ => constr:(false)
      end
    | natToWord _ ?n => is_nat_cst n
    | _ => constr:(false)
  end.

Ltac wcst w :=
  let b := isWcst w in
    match b with
      | true => w
      | _ => constr:(NotConstant)
    end.

Add Ring wring8 : (@Zmod.ring_theory (2 ^ Z.of_nat 8)) (decidable (fun x y : word 8 => proj1 (Zmod.eqb_eq x y)), constants [wcst]).

(* Here's how you can add a ring for a specific bit-width.
   There doesn't seem to be a polymorphic method, so this code really does need to be copied. *)

(*
Add Ring wring8 : (@Zmod.ring_theory (2 ^ Z.of_nat 8)) (decidable (fun x y : word 8 => proj1 (Zmod.eqb_eq x y)), constants [wcst]).
*)

(** * Bitwise operators: reasoning bit by bit *)

Local Open Scope Z_scope.

Local Close Scope Z_scope.

(** * Inequality proofs *)

Theorem word_neq : forall sz (w1 w2 : word sz),
  w1 ^- w2 <> (@Zmod.zero (2 ^ Z.of_nat sz))
  -> w1 <> w2.
Proof.
  word_lia_Z.
Qed.

Ltac word_neq := apply word_neq; let H := fresh "H" in intro H; simpl in H; ring_simplify in H; try discriminate.

Lemma lt_le : forall sz (a b : word sz),
  a < b -> a <= b.
Proof.
  word_lia_Z.
Qed.

Lemma eq_le : forall sz (a b : word sz),
  a = b -> a <= b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_inj : forall sz (a b : word sz),
  wordToN a = wordToN b -> a = b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_inj : forall sz (a b : word sz),
  wordToNat a = wordToNat b -> a = b.
Proof.
  word_lia_Z.
Qed.

Lemma sub_0_eq : forall sz (a b : word sz),
  a ^- b = Zmod.zero -> a = b.
Proof.
  intros; word_to_Z.
  match goal with H : ((?a - ?b) mod ?p)%Z = 0%Z |- _ => apply Zmod_sub_eq in H; lia end.
Qed.

Lemma le_neq_lt : forall sz (a b : word sz),
  b <= a -> a <> b -> b < a.
Proof.
  word_lia_Z.
Qed.

#[global] Hint Resolve word_neq lt_le eq_le sub_0_eq le_neq_lt : worder.

Ltac shatter_word x :=
  match type of x with
    | word 0 => try rewrite (word0 x) in *
    | word (S ?N) =>
      let x' := fresh in
      let H := fresh in
      destruct (@shatter_word_S N x) as [ ? [ x' H ] ];
      rewrite H in *; clear H; shatter_word x'
  end.

(** Uniqueness of equality proofs **)
Lemma rewrite_weq : forall sz (a b : word sz)
  (pf : a = b),
  weq a b = left _ pf.
Proof.
  intros; destruct (weq a b) as [e|n]; [f_equal; apply UIP_dec; apply weq | exfalso; exact (n pf)].
Qed.

(** * Some more useful derived facts *)

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = natToWord _ n ^+ natToWord _ m.
Proof.
  word_lia_Z.
Qed.

Lemma WS_true_natToWord_0 : forall sz, WS true (natToWord sz 0) = natToWord (S sz) 1.
Proof.
  word_lia_Z.
Qed.

Lemma natToWord_S : forall sz n, natToWord sz (S n) = natToWord _ 1 ^+ natToWord _ n.
Proof.
  intros; rewrite <- natToWord_plus; f_equal; lia.
Qed.

Theorem natToWord_inj : forall sz n m, natToWord sz n = natToWord sz m
  -> (n < pow2 sz)%nat
  -> (m < pow2 sz)%nat
  -> n = m.
Proof.
  word_lia_Z.
Qed.

Lemma wplus_cancel : forall sz (a b c : word sz),
  a ^+ c = b ^+ c
  -> a = b.
Proof.
  intros; word_to_Z.
  match goal with H : _ = _ |- _ => apply Zadd_mod_cancel_r in H; lia end.
Qed.

Lemma wminus_plus_distr:
  forall {sz} (x y z: word sz), x ^- (y ^+ z) = x ^- y ^- z.
Proof.
  word_lia_Z.
Qed.

Lemma wneg_zero:
  forall {sz} (w: word sz), ^~ w = (natToWord sz 0) -> w = natToWord sz 0.
Proof.
  intros; word_to_Z; rewrite Z.mod_0_l in * by lia.
  destruct (Z.eq_dec z 0); [lia|].
  rewrite Zmod_opp_sub, Z.mod_small in H by lia; lia.
Qed.

Lemma wplus_one_neq: forall {sz} (w: word (S sz)), w ^+ (natToWord (S sz) 1) <> w.
Proof.
  word_lia_Z.
Qed.

Lemma wones_pow2_minus_one: forall {sz}, wordToNat ((@Zmod.opp (2 ^ Z.of_nat sz) Zmod.one)) = pow2 sz - 1.
Proof.
  word_lia_Z.
Qed.

Lemma pow2_minus_one_wones: forall {sz} (w: word sz),
  wordToNat w = pow2 sz - 1 -> w = (@Zmod.opp (2 ^ Z.of_nat sz) Zmod.one).
Proof.
  word_lia_Z.
Qed.

Lemma wones_natToWord: forall sz,
  (@Zmod.opp (2 ^ Z.of_nat sz) Zmod.one) = $ (pow2 sz - 1).
Proof.
  word_lia_Z.
Qed.

Lemma wones_wneg_one: forall {sz}, (@Zmod.opp (2 ^ Z.of_nat sz) Zmod.one) = ^~ (natToWord sz 1).
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_natToWord_pred:
  forall {sz} (w: word sz), w <> (@Zmod.zero (2 ^ Z.of_nat sz)) ->
    pred (wordToNat w) =
    wordToNat (w ^- (natToWord sz 1)).
Proof.
  intros; destruct sz; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

Lemma wlt_lt: forall sz (a b : word sz), a < b ->
  (wordToNat a < wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma lt_word_lt_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n < m)%nat.
Proof.
  word_to_Z. pose proof (Z.mod_le (Z.of_nat m) (2 ^ Z.of_nat sz) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma lt_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.
Proof.
  intros; apply Nat.lt_le_incl; apply lt_word_lt_nat; assumption.
Qed.

#[global] Hint Resolve lt_word_le_nat.

Lemma wordToNat_natToWord_le : forall sz n,
  (wordToNat (natToWord sz n) <= n)%nat.
Proof.
  word_to_Z. pose proof (Z.mod_le (Z.of_nat n) (2 ^ Z.of_nat sz) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma lt_wlt: forall sz (n : word sz) m, (wordToNat n < wordToNat m)%nat ->
  n < m.
Proof.
  word_lia_Z.
Qed.

Theorem wordToNat_plusone: forall sz w w', w < w' ->
  wordToNat (w ^+ natToWord sz 1) = S (wordToNat w).
Proof.
  intros; destruct sz; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

(** * Shifts, single bits, msb, extensions, [N] and [Z] round trips *)

Local Open Scope Z_scope.

Local Close Scope Z_scope.

Lemma wordToNat_wzero:
  forall sz, wordToNat ((@Zmod.zero (2 ^ Z.of_nat sz))) = 0.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_wzero:
  forall sz, wordToN ((@Zmod.zero (2 ^ Z.of_nat sz))) = 0%N.
Proof.
  word_lia_Z.
Qed.

Lemma combine_one:
  forall n m, combine (natToWord (S n) 1) (natToWord m 0) = natToWord _ 1.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_existT: (* Note: not axiom free *)
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word _ w1 = existT word _ w2 ->
    forall b, wmsb w1 b = wmsb w2 b.
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma split2_split1_combine1 : forall n m (x : word 1) (y : word (n + m)),
    split2 1 n (split1 (S n) m (combine x y)) = split1 n m y.
Proof.
  word_nia_Z.
Qed.

Lemma WO_combine : forall sz (w : word sz), combine WO w = w.
Proof.
  word_lia_Z.
Qed.

Lemma shatter_word_1 : forall (w : word 1), w = WS (whd w) WO.
Proof.
  intros; rewrite (shatter_word w) at 1; f_equal; apply word0.
Qed.

Lemma shatter_word_2 : forall (w : word 2),
    w = WS (whd w) (WS (whd (wtl w)) WO).
Proof.
  intros; rewrite (shatter_word w) at 1; f_equal; apply shatter_word_1.
Qed.

Lemma shatter_word_3 : forall (w : word 3),
    w = WS (whd w) (WS (whd (wtl w)) (WS (whd (wtl (wtl w))) WO)).
Proof.
  intros; rewrite (shatter_word w) at 1; f_equal; apply shatter_word_2.
Qed.

Lemma whd_split1 : forall n m (w : word (S n + m)), whd (split1 (S n) m w) = whd w.
Proof.
  word_lia_Z.
Qed.

Lemma wtl_split1 : forall n m (w : word (S n + m)),
    wtl (split1 (S n) m w) = split1 n m (wtl w).
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_one : forall (w : word 1), Zmod.signed w = (if whd w then -1 else 0)%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_succ : forall sz (w : word (S (S sz))),
    Zmod.signed w = (2 * Zmod.signed (wtl w) + (if whd w then 1 else 0))%Z.
Proof.
  word_lia_Z.
Qed.

Lemma whd_WS : forall b sz (w : word sz), whd (WS b w) = b.
Proof.
  word_lia_Z.
Qed.

Lemma wtl_WS : forall b sz (w : word sz), wtl (WS b w) = w.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_wtl : forall sz (w : word (S sz)), wordToNat (wtl w) = wordToNat w / 2.
Proof.
  intros; cbv [wordToNat]; rewrite unsigned_wtl.
  apply Z2Nat.inj_div; [apply unsigned_range | lia].
Qed.

(** * Structural recursion over words *)

Lemma wmsb_extz:
  forall sz (w: word sz) n,
    wmsb (extz w n) false = wmsb w false.
Proof.
  word_to_Z; try lia.
  all: try (exfalso; nia).
  all: try reflexivity.
Qed.

Lemma wmsb_split2:
  forall sz (w: word (sz + 1)) b,
    wmsb w b = if weq (split2 _ 1 w) (natToWord _ 0) then false else true.
Proof.
  intros; destruct (weq (split2 sz 1 w) (natToWord 1 0)); word_lia_Z.
Qed.

Lemma wmsb_split1_sext:
  forall sz (w: word (sz + 1)),
    wmsb w false = wmsb (split1 _ 1 w) false ->
    exists sw, sext sw 1 = w.
Proof.
  intros; exists (split1 sz 1 w).
  word_to_Z; word_mod_simpl; try lia; try (exfalso; lia).
  all: try (rewrite Zmod_small_neg by lia); lia.
Qed.

Lemma wmsb_combine:
  forall sz1 sz2 (w1: word sz1) (w2: word sz2) b1 b2,
    sz2 <> 0 ->
    wmsb (combine w1 w2) b1 = wmsb w2 b2.
Proof.
  word_to_Z; try reflexivity; try lia; exfalso; pose proof (pow2_even_Z sz2 ltac:(lia));
    first [ nia
          | match goal with
            | H : (?p1 * ?p2 <= 2 * (?z0 + ?p1 * ?z))%Z |- _ => pose proof (@msb_combine_lt p1 p2 z0 z); lia
            | H : (2 * (?z0 + ?p1 * ?z) < ?p1 * ?p2)%Z |- _ => pose proof (@msb_combine_ge p1 p2 z0 z); lia
            end ].
Qed.

Lemma wmsb_combine_existT:
  forall sz (w: word sz) sz1 (w1: word sz1) sz2 (w2: word sz2) b1 b2,
    sz2 <> 0 ->
    existT word _ w = existT word _ (combine w1 w2) ->
    wmsb w b1 = wmsb w2 b2.
Proof.
  intros; apply existT_word_inv in H0; destruct H0; subst.
  apply Zmod.unsigned_inj in H1; subst; apply wmsb_combine; assumption.
Qed.

Lemma wmsb_zext:
  forall sz (w: word sz) b n, n <> 0 -> wmsb (zext w n) b = false.
Proof.
  word_to_Z; try reflexivity; try lia; exfalso; nia.
Qed.

Lemma wordToNat_zext:
  forall sz (w: word sz) n,
    wordToNat (zext w n) = wordToNat w.
Proof.
  word_lia_Z.
Qed.

Lemma zext_wordToNat_equal_Z:
  forall sz (w: word sz) n,
    n <> 0 -> Zmod.signed (zext w n) = Z.of_nat (wordToNat w).
Proof.
  word_to_Z; try reflexivity; try lia; exfalso; nia.
Qed.

Lemma wordToN_NToWord_2:
  forall sz n, (n < Npow2 sz)%N -> wordToN (NToWord sz n) = n.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_bound:
  forall sz (w: word sz), (wordToN w < Npow2 sz)%N.
Proof.
  word_lia_Z.
Qed.

Lemma wneg_wnot:
  forall sz (w: word sz), Zmod.not w = Zmod.opp w ^- (natToWord _ 1).
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_eq_rect:
  forall sz (w: word sz) nsz Hsz,
    wordToNat (eq_rect _ word w nsz Hsz) = wordToNat w.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wordToNat_existT:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) (Hsz: sz1 = sz2),
    wordToNat w1 = wordToNat w2 ->
    existT word _ w1 = existT word _ w2.
Proof.
  intros; subst; f_equal; apply wordToNat_inj; assumption.
Qed.

Lemma existT_wordToNat:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word _ w1 = existT word _ w2 ->
    wordToNat w1 = wordToNat w2.
Proof.
  intros; apply existT_word_inv in H; destruct H; subst; apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma wordToZ_eq_rect:
  forall sz (w: word sz) nsz Hsz,
    Zmod.signed (eq_rect _ word w nsz Hsz) = Zmod.signed w.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wordToZ_existT:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) (Hsz: sz1 = sz2),
    Zmod.signed w1 = Zmod.signed w2 ->
    existT word _ w1 = existT word _ w2.
Proof.
  intros; subst; f_equal; apply Zmod.signed_inj; assumption.
Qed.

Lemma wpow2_wmsb:
  forall sz, wmsb (wpow2 sz) false = true.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wneg_zext:
  forall sz (w: word sz) b n,
    n <> 0 -> wordToNat w <> 0 ->
    wmsb (Zmod.opp (zext w n)) b = true.
Proof.
  word_to_Z; word_mod_simpl; try reflexivity; try lia; exfalso; nia.
Qed.

Lemma extz_combine:
  forall sz (w: word sz) n, extz w n = combine (natToWord n 0) w.
Proof.
  word_lia_Z.
Qed.

Lemma combine_assoc_existT:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) sz3 (w3: word sz3),
    existT word (sz1 + (sz2 + sz3)) (combine w1 (combine w2 w3)) =
    existT word (sz1 + sz2 + sz3) (combine (combine w1 w2) w3).
Proof.
  word_lia_Z.
Qed.

Lemma sext_combine:
  forall sz n (w: word (sz + n)) sz1 (w1: word sz1)
         sz2 (Hsz2: sz2 <> 0) (w2: word sz2),
    existT word _ w = existT word _ (combine w1 (sext w2 n)) ->
    exists sw, w = sext sw n /\ existT word _ sw = existT word _ (combine w1 w2).
Proof.
  intros. apply existT_word_inv in H; destruct H.
  assert (sz = sz1 + sz2) by lia. subst sz.
  exists (combine w1 w2). split; [|reflexivity].
  apply Zmod.unsigned_inj. rewrite H0. clear H0 H.
  word_to_Z; pose proof (pow2_even_Z sz2 ltac:(lia)).
  all: try match goal with
           | H : (?p1 * ?p2 <= 2 * (?z0 + ?p1 * ?z))%Z, H' : (2 * ?z < ?p2)%Z |- _ =>
             exfalso; pose proof (@msb_combine_lt p1 p2 z0 z); lia
           | H : (2 * (?z0 + ?p1 * ?z) < ?p1 * ?p2)%Z, H' : (?p2 <= 2 * ?z)%Z |- _ =>
             exfalso; pose proof (@msb_combine_ge p1 p2 z0 z); lia
           end.
  all: word_mod_simpl; nia.
Qed.

Lemma combine_wplus_1:
  forall sl (w1: word sl) su (w2 w3: word su),
    combine w1 (w2 ^+ w3) = combine w1 w2 ^+ extz w3 sl.
Proof.
  word_lia_Z.
Qed.

Lemma combine_wplus_2:
  forall sl (w1: word sl) su (w2 w3: word su),
    combine w1 (w2 ^+ w3) = extz w2 sl ^+ combine w1 w3.
Proof.
  intros; rewrite (Zmod.add_comm w2 w3), combine_wplus_1, Zmod.add_comm; reflexivity.
Qed.

Lemma existT_wplus:
  forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^+ w2) = existT word _ (w3 ^+ w4).
Proof.
  intros; apply existT_word_inv in H; apply existT_word_inv in H0; destruct H, H0; subst.
  apply Zmod.unsigned_inj in H1; apply Zmod.unsigned_inj in H2; subst; reflexivity.
Qed.

Lemma existT_wminus:
  forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^- w2) = existT word _ (w3 ^- w4).
Proof.
  intros; apply existT_word_inv in H; apply existT_word_inv in H0; destruct H, H0; subst.
  apply Zmod.unsigned_inj in H1; apply Zmod.unsigned_inj in H2; subst; reflexivity.
Qed.

Lemma existT_sext:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (sext w1 n) = existT word _ (sext w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_wrshifta:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (Zmod.srs w1 (Z.of_nat n)) = existT word _ (Zmod.srs w2 (Z.of_nat n)).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_wlshift:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (Zmod.slu w1 (Z.of_nat n)) = existT word _ (Zmod.slu w2 (Z.of_nat n)).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply Zmod.unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma sext_wzero:
  forall sz n, sext ((@Zmod.zero (2 ^ Z.of_nat sz))) n = (@Zmod.zero (2 ^ Z.of_nat (sz + n))).
Proof.
  word_lia_Z.
Qed.

Lemma wrshifta_wzero:
  forall sz n, Zmod.srs ((@Zmod.zero (2 ^ Z.of_nat sz))) (Z.of_nat n) = Zmod.zero.
Proof.
  word_lia_Z.
Qed.

Lemma extz_sext:
  forall sz (w: word sz) n1 n2,
    existT word _ (extz (sext w n1) n2) =
    existT word _ (sext (extz w n2) n1).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); nia.
Qed.

Lemma sext_wordToZ:
  forall sz n (w: word sz),
    Zmod.signed (sext w n) = Zmod.signed w.
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); nia.
Qed.

Lemma wordToNat_split1:
  forall sz1 sz2 (w: word (sz1 + sz2)),
    wordToNat (split1 _ _ w) =
    Nat.modulo (wordToNat w) (pow2 sz1).
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz1); pose proof (pow2_pos_Z sz2).
  assert (0 <= z mod 2 ^ Z.of_nat sz1)%Z by (apply Z.mod_pos_bound; lia).
  apply Nat2Z.inj; rewrite Nat2Z.inj_mod, pow2_Z, !Z2Nat.id by lia; reflexivity.
Qed.

Lemma wordToNat_wrshifta:
  forall sz (w: word sz) n,
    wordToNat (Zmod.srs w (Z.of_nat n)) =
    Nat.div (wordToNat (sext w n)) (pow2 n).
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz); pose proof (pow2_pos_Z n); pose proof (pow2_Z n).
  - rewrite (Z.mod_small z) by nia.
    assert (0 <= z / 2 ^ Z.of_nat n < 2 ^ Z.of_nat sz)%Z
      by (split; [apply Z.div_pos; lia
                 | apply Z.le_lt_trans with z; [apply Z.div_le_upper_bound; nia | lia]]).
    rewrite (Z.mod_small (z / 2 ^ Z.of_nat n)%Z) by lia.
    replace (pow2 n) with (Z.to_nat (2 ^ Z.of_nat n)) by lia.
    rewrite Z2Nat.inj_div by lia; reflexivity.
  - rewrite (@Zmod_small_neg (z - 2 ^ Z.of_nat sz)%Z
                             (2 ^ Z.of_nat sz * 2 ^ Z.of_nat n)%Z) by nia.
    replace (pow2 n) with (Z.to_nat (2 ^ Z.of_nat n)) by lia.
    rewrite <- Z2Nat.inj_div by nia.
    f_equal.
    rewrite Z.div_add by lia.
    apply (@Zmod_small_neg); [lia|].
    split.
    + apply Z.div_le_lower_bound; nia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

Lemma wordToNat_combine:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    wordToNat (combine w1 w2) =
    wordToNat w1 + pow2 sz1 * wordToNat w2.
Proof.
  word_lia_Z.
Qed.

Lemma combine_sext:
  forall sz1 (w1: word sz1) sz2 (w2: word (S sz2)) n,
    existT word _ (combine w1 (sext w2 n)) =
    existT word _ (sext (combine w1 w2) n).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); nia.
Qed.

Lemma extz_extz:
  forall sz (w: word sz) n1 n2,
    existT word _ (extz (extz w n1) n2) =
    existT word _ (extz w (n2 + n1)).
Proof.
  word_lia_Z.
Qed.

Lemma wrshifta_extz_sext:
  forall sz (w: word sz) n1 n2,
    existT word _ (Zmod.srs (extz w (n1 + n2)) (Z.of_nat n1)) =
    existT word _ (sext (extz w n2) n1).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); try nia.
Qed.

Lemma wlshift_sext_extz:
  forall sz (w: word sz) n,
    existT word _ (Zmod.slu (sext w n) (Z.of_nat n)) =
    existT word _ (extz w n).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); try nia.
Qed.

Lemma wlshift_combine_extz:
  forall sn sl (wl: word sl) ssu (wu: word (ssu + sn)),
    existT word (sl + (ssu + sn)) (Zmod.slu (combine wl wu) (Z.of_nat sn)) =
    existT word (sn + (sl + ssu)) (extz (combine wl (split1 ssu _ wu)) sn).
Proof.
  word_to_Z; pose proof (pow2_pos_Z sl); pose proof (pow2_pos_Z sn);
    pose proof (pow2_pos_Z ssu).
  replace (2 ^ Z.of_nat sl * (2 ^ Z.of_nat ssu * 2 ^ Z.of_nat sn))%Z
     with ((2 ^ Z.of_nat sl * 2 ^ Z.of_nat ssu) * 2 ^ Z.of_nat sn)%Z by ring.
  rewrite Z.mul_mod_distr_r by nia.
  rewrite (Z.mul_comm _ (2 ^ Z.of_nat sn)%Z); f_equal.
  assert (Hq : z = (2 ^ Z.of_nat ssu * (z / 2 ^ Z.of_nat ssu) + z mod 2 ^ Z.of_nat ssu)%Z)
    by (apply Z.div_mod; lia).
  assert (Hm : (0 <= z mod 2 ^ Z.of_nat ssu < 2 ^ Z.of_nat ssu)%Z)
    by (apply Z.mod_pos_bound; lia).
  rewrite Hq at 1.
  replace (z0 + 2 ^ Z.of_nat sl *
             (2 ^ Z.of_nat ssu * (z / 2 ^ Z.of_nat ssu) + z mod 2 ^ Z.of_nat ssu))%Z
     with ((z0 + 2 ^ Z.of_nat sl * (z mod 2 ^ Z.of_nat ssu))
           + (z / 2 ^ Z.of_nat ssu) * (2 ^ Z.of_nat sl * 2 ^ Z.of_nat ssu))%Z by ring.
  rewrite Z.mod_add by nia.
  apply Z.mod_small; nia.
Qed.

Lemma split1_zext:
  forall sz (w: word sz) n,
    split1 sz n (zext w n) = w.
Proof.
  word_lia_Z.
Qed.

Lemma sext_split1:
  forall sz (w: word sz) n,
    split1 sz _ (sext w n) = w.
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); try lia.
Qed.

(** * [Z] round trips and signed arithmetic *)

Lemma wordToZ_ZToWord:
  forall z sz,
    (- Z.of_nat (pow2 sz) <= z < Z.of_nat (pow2 sz))%Z ->
    Zmod.signed (bits.of_Z (Z.of_nat (S sz)) z) = z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z_lt_le_dec z 0) as [Hs|Hs];
     [ rewrite (@Zmod_small_neg z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia
     | rewrite (Z.mod_small z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia ]);
    lia.
Qed.

Lemma wordToZ_ZToWord'': forall (sz: nat),
    (0 < sz)%nat ->
    forall n: Z,
      (- 2 ^ (Z.of_nat sz - 1) <= n < 2 ^ (Z.of_nat sz - 1))%Z ->
      Zmod.signed (bits.of_Z (Z.of_nat sz) n) = n.
Proof.
  intros; destruct sz; [lia|].
  replace (Z.of_nat (S sz) - 1)%Z with (Z.of_nat sz) in H0 by lia.
  apply wordToZ_ZToWord; rewrite pow2_Z; assumption.
Qed.

Lemma ZToWord_Z_of_N:
  forall sz n,
    bits.of_Z (Z.of_nat sz) (Z.of_N n) = NToWord sz n.
Proof.
  reflexivity.
Qed.

Lemma wordToZ_wplus_bound:
  forall sz (w1 w2: word (S sz)),
    (- Z.of_nat (pow2 sz) <= Zmod.signed w1 + Zmod.signed w2 < Z.of_nat (pow2 sz))%Z ->
    (Zmod.signed w1 + Zmod.signed w2 = Zmod.signed (w1 ^+ w2))%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z_lt_le_dec (z0 + z)%Z (2 * 2 ^ Z.of_nat sz)%Z) as [Hs|Hs];
     [ rewrite (Z.mod_small (z0 + z)%Z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia
     | rewrite (@Zmod_small_2 (z0 + z)%Z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia ]);
    lia.
Qed.

Lemma wordToZ_size':
  forall sz (w: word (S sz)),
    (- Z.of_nat (pow2 sz) <= Zmod.signed w < Z.of_nat (pow2 sz))%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_false_pos:
  forall sz (w: word sz),
    wmsb w false = false <-> (Zmod.signed w >= 0)%Z.
Proof.
  split; word_lia_Z.
Qed.

Lemma wmsb_true_neg:
  forall sz (w: word sz),
    wmsb w false = true <-> (Zmod.signed w < 0)%Z.
Proof.
  split; word_lia_Z.
Qed.

Lemma wordToZ_distr_diff_wmsb:
  forall sz (w1 w2: word sz),
    wmsb w1 false = negb (wmsb w2 false) ->
    Zmod.signed (w1 ^+ w2) = (Zmod.signed w1 + Zmod.signed w2)%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z_lt_le_dec (z0 + z)%Z (2 ^ Z.of_nat sz)%Z) as [Hs|Hs];
     [ rewrite (Z.mod_small (z0 + z)%Z (2 ^ Z.of_nat sz)%Z) in * by lia
     | rewrite (@Zmod_small_2 (z0 + z)%Z (2 ^ Z.of_nat sz)%Z) in * by lia ]);
    lia.
Qed.

Lemma sext_wplus_wordToZ_distr:
  forall sz (w1 w2: word sz) n,
    n <> 0 -> Zmod.signed (sext w1 n ^+ sext w2 n) =
              (Zmod.signed (sext w1 n) + Zmod.signed (sext w2 n))%Z.
Proof.
  intros; rewrite !sext_wordToZ.
  word_to_Z; pose proof (pow2_pos_Z sz); pose proof (pow2_pos_Z n);
    assert (Hq : (2 <= 2 ^ Z.of_nat n)%Z)
      by (replace 2%Z with (2 ^ 1)%Z at 1 by reflexivity; apply Z.pow_le_mono_r; lia);
    assert (HM : (2 * 2 ^ Z.of_nat sz <= 2 ^ Z.of_nat sz * 2 ^ Z.of_nat n)%Z)
      by (rewrite (Z.mul_comm 2 (2 ^ Z.of_nat sz)); apply Z.mul_le_mono_nonneg_l; lia);
    rewrite <- Zplus_mod in *;
    (match goal with
     | |- context [ (?s mod (2 ^ Z.of_nat sz * 2 ^ Z.of_nat n))%Z ] =>
       destruct (Z_lt_le_dec s 0) as [Hs|Hs];
       [ rewrite (@Zmod_small_neg s (2 ^ Z.of_nat sz * 2 ^ Z.of_nat n)%Z) in * by lia
       | rewrite (Z.mod_small s (2 ^ Z.of_nat sz * 2 ^ Z.of_nat n)%Z) in * by lia ]
     end);
    lia.
Qed.

Lemma split1_combine_existT:
  forall sz n (w: word (n + sz)) sl (wl: word (n + sl)) su (wu: word su),
    existT word _ w = existT word _ (combine wl wu) ->
    split1 n _ w = split1 n _ wl.
Proof.
  intros; apply existT_word_inv in H; destruct H.
  apply Zmod.unsigned_inj; rewrite !unsigned_split1, H0, unsigned_combine.
  rewrite <- (Z.mod_add (unsigned wl) (2 ^ Z.of_nat sl * unsigned wu) (2 ^ Z.of_nat n))
    by (pose proof (pow2_pos_Z n); lia).
  f_equal; f_equal; rewrite (pow2_add_Z n sl); ring.
Qed.

Lemma extz_pow2_wordToZ:
  forall sz (w: word sz) n,
    Zmod.signed (extz w n) = (Zmod.signed w * Z.of_nat (pow2 n))%Z.
Proof.
  word_to_Z; try lia; try (exfalso; nia); nia.
Qed.

Lemma wneg_wordToZ:
  forall sz (w: word (S sz)),
    w <> wpow2 sz ->
    Zmod.signed (Zmod.opp w) = (- Zmod.signed w)%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z.eq_dec z 0) as [->|];
     [ rewrite Z.opp_0, Z.mod_0_l in * by lia
     | rewrite (@Zmod_small_neg (- z)%Z) in * by lia ]);
    lia.
Qed.

Lemma extz_zero:
  forall sz n, extz (natToWord sz 0) n = Zmod.zero.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wlshift_sext:
  forall sz (w: word sz) n,
    wmsb (sext w n) false = wmsb (Zmod.slu (sext w n) (Z.of_nat n)) false.
Proof.
  intros; pose proof (pow2_pos_Z n).
  destruct sz; [destruct n|]; [reflexivity| |];
    rewrite !wmsb_S by lia;
    rewrite <- (bits.smod_unsigned (Zmod.slu _ _)), Zmod.unsigned_slu, Z.smod_mod,
      unsigned_sext, Z.shiftl_mul_pow2, sext_wordToZ by lia;
    rewrite (Z.smod_inj_mod _ (Zmod.signed w * 2 ^ Z.of_nat _)) by apply Zmult_mod_idemp_l.
  - pose proof (Zmod.signed_pos_bound w (pow2_pos_Z 0)) as H0.
    replace (2 ^ Z.of_nat 0)%Z with 1%Z in H0 by reflexivity.
    replace (Zmod.signed w) with 0%Z by lia.
    rewrite Z.mul_0_l, Z.smod_0_l; reflexivity.
  - pose proof (Zmod.signed_pos_bound w (pow2_pos_Z (S sz))) as H0.
    rewrite Z.smod_pow2_small by first [ lia | (rewrite pow2_add_Z; nia) ].
    destruct (Z.ltb_spec (Zmod.signed w) 0), (Z.ltb_spec (Zmod.signed w * 2 ^ Z.of_nat n) 0);
      first [ reflexivity | nia ].
Qed.

Lemma wordToZ_wordToNat_pos:
  forall sz (w: word sz),
    wmsb w false = false ->
    Z.of_nat (wordToNat w) = Zmod.signed w.
Proof.
  word_lia_Z.
Qed.

Corollary wmsb_Zabs_pos:
  forall sz (w: word sz),
    wmsb w false = false -> Z.abs (Zmod.signed w) = Zmod.signed w.
Proof.
  intros; rewrite <- wordToZ_wordToNat_pos by assumption; lia.
Qed.

Lemma wordToN_combine:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    wordToN (combine w1 w2) = (wordToN w1 + Npow2 sz1 * wordToN w2)%N.
Proof.
  word_lia_Z.
Qed.

Lemma sext_size:
  forall sz n (w: word (sz + n)),
    sz <> 0 ->
    (- Z.of_nat (pow2 (sz - 1)) <= Zmod.signed w < Z.of_nat (pow2 (sz - 1)))%Z ->
    exists sw, w = sext sw n.
Proof.
  intros; destruct sz; [lia|].
  replace (S sz - 1) with sz in H0 by lia.
  exists (split1 (S sz) n w).
  word_to_Z.
  - rewrite (Z.mod_small z) by lia; rewrite Z.mod_small by lia; reflexivity.
  - rewrite (Z.mod_small z) in H1 by lia; lia.
  - rewrite (@Zmod_upper z (2 ^ Z.of_nat sz) (2 ^ Z.of_nat n)) in H1 by lia; lia.
  - rewrite (@Zmod_upper z (2 ^ Z.of_nat sz) (2 ^ Z.of_nat n)) by lia.
    replace (z - 2 * 2 ^ Z.of_nat sz * 2 ^ Z.of_nat n + 2 * 2 ^ Z.of_nat sz -
             2 * 2 ^ Z.of_nat sz)%Z
       with (z + (-1) * (2 * 2 ^ Z.of_nat sz * 2 ^ Z.of_nat n))%Z by ring.
    rewrite Z.mod_add by lia; rewrite Z.mod_small by lia; reflexivity.
Qed.

Lemma wordToZ_combine_WO:
  forall sz (w: word sz),
    Zmod.signed (combine w WO) = Zmod.signed w.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_bound_weakened:
  forall z n, (Z.abs z < n)%Z -> (- n <= z < n)%Z.
Proof.
  intros; lia.
Qed.

Lemma zext_size:
  forall sz n (w: word (sz + n)),
    (- Z.of_nat (pow2 sz) <= Zmod.signed w < Z.of_nat (pow2 sz))%Z ->
    wmsb w false = false ->
    exists sw, w = zext sw n.
Proof.
  intros; exists (split1 sz n w).
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
Qed.

Lemma zext_size_1:
  forall sz (w: word (sz + 1)),
    wmsb w false = false ->
    exists sw, w = zext sw 1.
Proof.
  intros; exists (split1 sz 1 w).
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
Qed.

Lemma sext_wplus_exist:
  forall sz (w1 w2: word sz) n,
  exists w: word (S sz),
    existT word _ (sext w1 (S n) ^+ sext w2 (S n)) =
    existT word _ (sext w n).
Proof.
  intros; exists (bits.of_Z (Z.of_nat (S sz)) (Zmod.signed w1 + Zmod.signed w2)).
  word_to_Z; pose proof (pow2_pos_Z sz); pose proof (pow2_pos_Z n);
    replace (2 ^ Z.of_nat sz * (2 * 2 ^ Z.of_nat n))%Z
       with (2 * 2 ^ Z.of_nat sz * 2 ^ Z.of_nat n)%Z by ring;
    rewrite <- Zplus_mod;
    (match goal with
     | |- (?s mod _)%Z = _ =>
       destruct (Z_lt_le_dec s 0) as [Hs|Hs];
       [ rewrite (@Zmod_small_neg s (2 * 2 ^ Z.of_nat sz)%Z) in * by lia
       | rewrite (Z.mod_small s (2 * 2 ^ Z.of_nat sz)%Z) in * by lia ]
     end);
    try lia; f_equal; lia.
Qed.

(** * [wordToNat] transfer lemmas *)

Close Scope word_scope.

Open Scope word_scope.
Local Open Scope nat.

Lemma wordToNat_natToWord_eqn sz:
  forall n,
    wordToNat (natToWord sz n) = n mod (pow2 sz).
Proof.
  word_lia_Z.
Qed.

Section ZScope.
Import Zdiv.

Lemma wordToZ_ZToWord_full sz (H: (0 < sz)%nat) (z:Z) :
  Zmod.signed (bits.of_Z (Z.of_nat sz) z) =
  (( z
    + 2 ^ (Z.of_nat sz - 1)
    ) mod (2 ^ Z.of_nat sz)
    - 2 ^ (Z.of_nat sz - 1))%Z.
Proof.
  destruct sz; [lia|].
  replace (Z.of_nat (S sz) - 1)%Z with (Z.of_nat sz) by lia.
  word_to_Z; pose proof (pow2_pos_Z sz);
    assert (Hb : (0 <= z mod (2 * 2 ^ Z.of_nat sz) < 2 * 2 ^ Z.of_nat sz)%Z)
      by (apply Z.mod_pos_bound; lia);
    rewrite <- (Zplus_mod_idemp_l z (2 ^ Z.of_nat sz)%Z (2 * 2 ^ Z.of_nat sz)%Z).
  - rewrite (Z.mod_small (z mod (2 * 2 ^ Z.of_nat sz) + 2 ^ Z.of_nat sz)%Z) by lia; lia.
  - rewrite (@Zmod_small_2 (z mod (2 * 2 ^ Z.of_nat sz) + 2 ^ Z.of_nat sz)%Z) by lia; lia.
Qed.

End ZScope.

Lemma wordToN_0: forall sz,
    wordToN (natToWord sz 0) = 0%N.
Proof.
  word_lia_Z.
Qed.
