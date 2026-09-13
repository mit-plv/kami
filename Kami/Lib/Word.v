(** Fixed precision machine words.

    [word n] is the standard library's [Zmod (Zpow2 n)] where [Zpow2 n] is
    [2 ^ Z.of_nat n], i.e. it is [bits (Z.of_nat n)], and Kami's operations
    are the [Zmod] operations themselves: [wplus] is [Zmod.add], [wneg] is
    [Zmod.opp], [wzero sz] is [Zmod.zero], [wordToZ] is [Zmod.signed], [wlt]
    is [Z.lt] on [Zmod.unsigned], and so on, so the standard library's
    [unsigned_*]/[signed_*] lemmas apply to Kami terms as they are.  Only the
    operations whose shape the standard library does not have (a [nat] index
    or value, a width that changes, Kami's division-by-zero and shift
    conventions) are definitions of their own, each with an [unsigned_*]
    lemma.

    Facts about words are proved by moving to [Zmod.unsigned] and reasoning
    in [Z]: [word_to_Z] rewrites every operation into its [unsigned]
    specification, [word_lia_Z] follows it with [lia]/[nia].

    Side effect on importers: this file requires [ZifyNat] and [ZifyN], so
    importing it registers those [Zify] instances globally and [lia]/[nia]
    will understand [Nat.pow]/[Nat.div]/[Nat.mod] and their [N] counterparts
    everywhere downstream.  It also declares the standard library's [Zmod]
    operations [simpl never] (see below). *)

From Stdlib Require Import Arith NArith ZArith Bool Lia ZifyNat ZifyN.
From Stdlib Require Import Eqdep_dec EqdepFacts.
From Stdlib Require Export Zmod.
From Stdlib Require Export Zmod.Bits.
From Kami Require Import Nlia NatLib DepEq N_Z_nat_conversions.

Set Implicit Arguments.

(*! Definitions *)

(** * [word] *)

(** The modulus of an [n]-bit word.  A named constant so that [simpl] does not
    compute inside it: [2 ^ Z.of_nat (S n)] would become
    [Z.pow_pos 2 (Pos.of_succ_nat n)], which no lemma matches any more. *)
Definition Zpow2 (n : nat) : Z := 2 ^ Z.of_nat n.
Arguments Zpow2 _ : simpl never.

Definition word (n : nat) : Set := Zmod (Zpow2 n).

Declare Scope word_scope.
Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Open Scope word_scope.

Local Notation unsigned := Zmod.unsigned.
Local Notation signed := Zmod.signed.

(** * The standard library's operations under Kami's names *)

Notation ZToWord sz z := (Zmod.of_Z (Zpow2 sz) z).
Notation wordToZ := Zmod.signed.
Notation uwordToZ := Zmod.unsigned.

Notation wzero sz := (@Zmod.zero (Zpow2 sz)).
Notation wone sz := (@Zmod.one (Zpow2 sz)).
Notation wones sz := (@Zmod.opp (Zpow2 sz) Zmod.one).
Notation WO := (@Zmod.zero (Zpow2 0)).

Notation wneg := Zmod.opp.
Notation wplus := Zmod.add.
Notation wminus := Zmod.sub.
Notation wmult := Zmod.mul.
Notation wnot := Zmod.not.
Notation wor := Zmod.or.
Notation wand := Zmod.and.
Notation wxor := Zmod.xor.
Notation weqb := Zmod.eqb.

Notation wlt l r := (Z.lt (Zmod.unsigned l) (Zmod.unsigned r)).
Notation wslt l r := (Z.lt (Zmod.signed l) (Zmod.signed r)).
Notation wlt_dec l r := (Z_lt_dec (Zmod.unsigned l) (Zmod.unsigned r)).
Notation wslt_dec l r := (Z_lt_dec (Zmod.signed l) (Zmod.signed r)).

(** * Operations whose shape the standard library does not have *)

(** Conversions with [nat] and [N]. *)
Definition natToWord (sz n : nat) : word sz := Zmod.of_Z _ (Z.of_nat n).
Definition NToWord (sz : nat) (n : N) : word sz := Zmod.of_Z _ (Z.of_N n).
Definition wordToNat [sz] (w : word sz) : nat := Z.to_nat (unsigned w).
Definition wordToN [sz] (w : word sz) : N := Z.to_N (unsigned w).

(** [WS b w] is [w] with [b] appended as the new least significant bit. *)
Definition WS (b : bool) [n : nat] (w : word n) : word (S n) :=
  Zmod.of_Z _ (Z.b2z b + 2 * unsigned w).

Definition whd [sz] (w : word (S sz)) : bool := Z.odd (unsigned w).
Definition wtl [sz] (w : word (S sz)) : word sz := Zmod.of_Z _ (unsigned w / 2).
Definition wlsb [sz] (w : word (S sz)) : bool := whd w.

(** The most significant bit, or [a] for the empty word. *)
Definition wmsb [sz] (w : word sz) (a : bool) : bool :=
  match sz with
  | O => a
  | S _ => (signed w <? 0)%Z
  end.

Definition weq : forall [sz] (x y : word sz), {x = y} + {x <> y}.
  refine (fun sz x y =>
            match Zmod.eqb x y as b return Zmod.eqb x y = b -> {x = y} + {x <> y} with
            | true => fun H => left _
            | false => fun H => right _
            end eq_refl);
    abstract (destruct (Zmod.eqb_spec x y); congruence).
Defined.

(** [combine w w'] has [w] in its low bits and [w'] in its high bits. *)
Definition combine [sz1 : nat] (w : word sz1) [sz2 : nat] (w' : word sz2)
  : word (sz1 + sz2) :=
  Zmod.of_Z _ (unsigned w + Zpow2 sz1 * unsigned w').

Definition split1 (sz1 sz2 : nat) (w : word (sz1 + sz2)) : word sz1 :=
  Zmod.of_Z _ (unsigned w).

Definition split2 (sz1 sz2 : nat) (w : word (sz1 + sz2)) : word sz2 :=
  Zmod.of_Z _ (unsigned w / Zpow2 sz1).

Definition sext [sz : nat] (w : word sz) (sz' : nat) : word (sz + sz') :=
  Zmod.of_Z _ (signed w).

Definition zext [sz : nat] (w : word sz) (sz' : nat) : word (sz + sz') :=
  Zmod.of_Z _ (unsigned w).

Definition extz [sz : nat] (w : word sz) (n : nat) : word (n + sz) :=
  Zmod.of_Z _ (unsigned w * Zpow2 n).

(** Shifts by a [nat]. *)
Definition wlshift [sz : nat] (w : word sz) (n : nat) : word sz := Zmod.slu w (Z.of_nat n).
Definition wrshift [sz : nat] (w : word sz) (n : nat) : word sz := Zmod.sru w (Z.of_nat n).
Definition wrshifta [sz : nat] (w : word sz) (n : nat) : word sz := Zmod.srs w (Z.of_nat n).

Definition wpow2 sz : word (S sz) := Zmod.of_Z _ (Zpow2 sz).

(** Division and remainder with Kami's conventions for a zero divisor
    ([x / 0 = 0], [x mod 0 = x], as in [nat] and [Z]); the standard
    library's [udiv]/[squot] return all ones there. *)
Definition wdivN [sz] (x y : word sz) : word sz := Zmod.of_Z _ (unsigned x / unsigned y).
Definition wremN [sz] (x y : word sz) : word sz := Zmod.of_Z _ (unsigned x mod unsigned y).
Definition wdivZ [sz] (x y : word sz) : word sz := Zmod.of_Z _ (Z.quot (signed x) (signed y)).
Definition wremZ [sz] (x y : word sz) : word sz := Zmod.of_Z _ (Z.rem (signed x) (signed y)).

(** * Notations *)

Notation "w ~ 1" := (WS true w) : word_scope.
Notation "w ~ 0" := (WS false w) : word_scope.

Notation "^~" := Zmod.opp.
Notation "l ^+ r" := (Zmod.add l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (Zmod.mul l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (Zmod.sub l%word r%word) (at level 50, left associativity).
Notation "l ^| r" := (Zmod.or l%word r%word) (at level 50, left associativity).
Notation "l ^& r" := (Zmod.and l%word r%word) (at level 40, left associativity).

Notation "w1 > w2" := (wlt w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(wlt w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (wlt w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(wlt w2%word w1%word)) : word_scope.

Notation "w1 '>s' w2" := (wslt w2%word w1%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '>s=' w2" := (~(wslt w1%word w2%word)) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s' w2" := (wslt w1%word w2%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s=' w2" := (~(wslt w2%word w1%word)) (at level 70, w2 at next level) : word_scope.

Notation "$ n" := (natToWord _ n) (at level 1, format "$ n").
Notation "# n" := (wordToNat n) (at level 5, format "# n").

Notation "l ^<< r" := (wlshift l%word r%word) (at level 35).
Notation "l ^>> r" := (wrshift l%word r%word) (at level 35).

(** Kami's tactics [simpl] freely; reducing through [Zmod.of_Z] turns a
    word into an [if small ... then ... else 0] over its integer
    specification, duplicating the specification at every nesting level.
    Words are reasoned about through the [unsigned_*] lemmas instead, so
    the standard library's operations are [simpl never] for every importer,
    and so are the definitions above. *)
Arguments Zmod.unsigned {_} _ : simpl never.
Arguments Zmod.signed {_} _ : simpl never.
Arguments Zmod.of_Z _ _ : simpl never.
Arguments Zmod.of_small_Z _ _ : simpl never.
Arguments Zmod.add {_} _ _ : simpl never.
Arguments Zmod.sub {_} _ _ : simpl never.
Arguments Zmod.opp {_} _ : simpl never.
Arguments Zmod.mul {_} _ _ : simpl never.
Arguments Zmod.and {_} _ _ : simpl never.
Arguments Zmod.or {_} _ _ : simpl never.
Arguments Zmod.xor {_} _ _ : simpl never.
Arguments Zmod.not {_} _ : simpl never.
Arguments Zmod.slu {_} _ _ : simpl never.
Arguments Zmod.sru {_} _ _ : simpl never.
Arguments Zmod.srs {_} _ _ : simpl never.
Arguments Zmod.eqb {_} _ _ : simpl never.
Arguments natToWord _ _ : simpl never.
Arguments NToWord _ _ : simpl never.
Arguments wordToNat [_] _ : simpl never.
Arguments wordToN [_] _ : simpl never.
Arguments WS _ [_] _ : simpl never.
Arguments whd [_] _ : simpl never.
Arguments wtl [_] _ : simpl never.
Arguments wlsb [_] _ : simpl never.
Arguments wmsb [_] _ _ : simpl never.
Arguments weq [_] _ _ : simpl never.
Arguments combine [_] _ [_] _ : simpl never.
Arguments split1 _ _ _ : simpl never.
Arguments split2 _ _ _ : simpl never.
Arguments sext [_] _ _ : simpl never.
Arguments zext [_] _ _ : simpl never.
Arguments extz [_] _ _ : simpl never.
Arguments wlshift [_] _ _ : simpl never.
Arguments wrshift [_] _ _ : simpl never.
Arguments wrshifta [_] _ _ : simpl never.
Arguments wpow2 _ : simpl never.
Arguments wdivN [_] _ _ : simpl never.
Arguments wremN [_] _ _ : simpl never.
Arguments wdivZ [_] _ _ : simpl never.
Arguments wremZ [_] _ _ : simpl never.

(*! Facts *)

(** * [Zpow2] *)

Local Open Scope Z_scope.

Lemma Zpow2_eqn : forall n, Zpow2 n = 2 ^ Z.of_nat n.
Proof. reflexivity. Qed.

Lemma pow2_Z : forall n, Z.of_nat (pow2 n) = Zpow2 n.
Proof. intros; apply Nat2Z.inj_pow. Qed.

Lemma Npow2_Z : forall n, Z.of_N (Npow2 n) = Zpow2 n.
Proof. apply NatLib.Z_of_N_Npow2. Qed.

(** [lia] sees [Npow2] as [2 ^ _] ([pow2] is [Nat.pow 2], already known). *)
Lemma Npow2_Z' : forall n, Z.of_N (Npow2 n) = 2 ^ Z.of_nat n.
Proof. apply NatLib.Z_of_N_Npow2. Qed.
#[global] Instance Op_Npow2 : ZifyClasses.UnOp Npow2 :=
  { ZifyClasses.TUOp := fun x => 2 ^ x; ZifyClasses.TUOpInj := Npow2_Z' }.
Add Zify UnOp Op_Npow2.

Lemma Zpow2_0 : Zpow2 0 = 1.
Proof. reflexivity. Qed.

Lemma Zpow2_S : forall n, Zpow2 (S n) = 2 * Zpow2 n.
Proof. intros; cbv [Zpow2]; rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia. Qed.

Lemma Zpow2_add : forall a b, Zpow2 (a + b) = Zpow2 a * Zpow2 b.
Proof. intros; cbv [Zpow2]; rewrite Nat2Z.inj_add, Z.pow_add_r; lia. Qed.

Lemma Zpow2_mul : forall a b, Zpow2 (a * b) = (Zpow2 a) ^ Z.of_nat b.
Proof. intros; cbv [Zpow2]; rewrite Nat2Z.inj_mul, Z.pow_mul_r; lia. Qed.

Lemma Zpow2_pos : forall n, 0 < Zpow2 n.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

Lemma Zpow2_eq1 : forall x : nat, Z.of_nat x = 0 -> Zpow2 x = 1.
Proof. intros x H; cbv [Zpow2]; rewrite H; reflexivity. Qed.

Lemma Zpow2_ge2 : forall x : nat, Z.of_nat x <> 0 -> 2 <= Zpow2 x.
Proof. intros x H; destruct x; [lia|]; rewrite Zpow2_S; pose proof (Zpow2_pos x); lia. Qed.

Lemma Zpow2_even : forall x : nat, Z.of_nat x <> 0 -> Zpow2 x mod 2 = 0.
Proof. intros x H; destruct x; [lia|]; rewrite Zpow2_S, Z.mul_comm; apply Z.mod_mul; lia. Qed.

(** * [unsigned] of every operation, in [lia]'s language *)

Lemma unsigned_range : forall sz (w : word sz), 0 <= unsigned w < Zpow2 sz.
Proof. intros; apply Zmod.unsigned_pos_bound, Zpow2_pos. Qed.

(** Range facts whose width is a compound expression, stated so that the
    width arithmetic is already done (the width also occurs in the type of
    [w], which blocks rewriting it inside [unsigned w]). *)
Lemma unsigned_range_S : forall sz (w : word (S sz)), 0 <= unsigned w < 2 * Zpow2 sz.
Proof.
  intros; pose proof (unsigned_range w) as H.
  set (x := unsigned w) in *; clearbody x. rewrite Zpow2_S in H; lia.
Qed.

Lemma unsigned_range_add : forall sz1 sz2 (w : word (sz1 + sz2)),
    0 <= unsigned w < Zpow2 sz1 * Zpow2 sz2.
Proof.
  intros; pose proof (unsigned_range w) as H.
  set (x := unsigned w) in *; clearbody x. rewrite Zpow2_add in H; lia.
Qed.
Arguments unsigned_range_add {_ _} _.
Arguments unsigned_range_S {_} _.

Lemma unsigned_ofZ_small : forall sz z, 0 <= z < Zpow2 sz -> unsigned (ZToWord sz z) = z.
Proof. intros; apply Zmod.unsigned_of_Z_small; assumption. Qed.

(** [signed] as a case split on [unsigned], for [lia]. *)
Lemma signed_eqn : forall sz (w : word sz),
    signed w = if 2 * unsigned w <? Zpow2 sz then unsigned w else unsigned w - Zpow2 sz.
Proof.
  intros; pose proof (unsigned_range w).
  destruct (Z.ltb_spec (2 * unsigned w) (Zpow2 sz));
    [apply Zmod.signed_small | apply Zmod.signed_large]; lia.
Qed.

Lemma unsigned_wones : forall sz, unsigned (wones sz) = Zpow2 sz - 1.
Proof.
  intros; rewrite Zmod.unsigned_m1. pose proof (Zpow2_pos sz).
  rewrite <- (Z.mod_add (-1) 1 _), Z.mod_small by lia. lia.
Qed.

Lemma unsigned_natToWord : forall sz n, unsigned (natToWord sz n) = Z.of_nat n mod Zpow2 sz.
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_NToWord : forall sz n, unsigned (NToWord sz n) = Z.of_N n mod Zpow2 sz.
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_WS : forall b n (w : word n), unsigned (WS b w) = Z.b2z b + 2 * unsigned w.
Proof.
  intros; cbv [WS]; apply unsigned_ofZ_small.
  pose proof (unsigned_range w); rewrite Zpow2_S.
  destruct b; cbn [Z.b2z]; lia.
Qed.

Lemma unsigned_wtl : forall sz (w : word (S sz)), unsigned (wtl w) = unsigned w / 2.
Proof.
  intros; cbv [wtl]; apply unsigned_ofZ_small.
  pose proof (unsigned_range_S w).
  Z.div_mod_to_equations; lia.
Qed.

Lemma whd_eqn : forall sz (w : word (S sz)), whd w = Z.odd (unsigned w).
Proof. reflexivity. Qed.

Lemma wmsb_eqn : forall sz (w : word sz) b,
    wmsb w b = if Z.of_nat sz =? 0 then b else (Zpow2 sz <=? 2 * unsigned w).
Proof.
  intros; destruct sz; [reflexivity|]; cbv [wmsb].
  destruct (Z.eqb_spec (Z.of_nat (S sz)) 0); [lia|].
  rewrite signed_eqn. pose proof (unsigned_range w).
  destruct (Z.ltb_spec (2 * unsigned w) (Zpow2 (S sz)));
    destruct (Z.leb_spec (Zpow2 (S sz)) (2 * unsigned w));
    destruct (Z.ltb_spec (unsigned w) 0); destruct (Z.ltb_spec (unsigned w - Zpow2 (S sz)) 0);
    lia.
Qed.

Lemma unsigned_combine : forall sz1 (w : word sz1) sz2 (w' : word sz2),
    unsigned (combine w w') = unsigned w + Zpow2 sz1 * unsigned w'.
Proof.
  intros; cbv [combine]; apply unsigned_ofZ_small.
  pose proof (unsigned_range w); pose proof (unsigned_range w').
  rewrite Zpow2_add. nia.
Qed.

Lemma unsigned_split1 : forall sz1 sz2 (w : word (sz1 + sz2)),
    unsigned (split1 sz1 sz2 w) = unsigned w mod Zpow2 sz1.
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_split2 : forall sz1 sz2 (w : word (sz1 + sz2)),
    unsigned (split2 sz1 sz2 w) = unsigned w / Zpow2 sz1.
Proof.
  intros; cbv [split2]; apply unsigned_ofZ_small.
  pose proof (unsigned_range_add w).
  pose proof (Zpow2_pos sz1); pose proof (Zpow2_pos sz2).
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

Lemma unsigned_sext : forall sz (w : word sz) sz',
    unsigned (sext w sz') = signed w mod Zpow2 (sz + sz').
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_zext : forall sz (w : word sz) sz', unsigned (zext w sz') = unsigned w.
Proof.
  intros; cbv [zext]; apply unsigned_ofZ_small.
  pose proof (unsigned_range w); pose proof (Zpow2_pos sz'). rewrite Zpow2_add; nia.
Qed.

Lemma unsigned_extz : forall sz (w : word sz) n, unsigned (extz w n) = unsigned w * Zpow2 n.
Proof.
  intros; cbv [extz]; apply unsigned_ofZ_small.
  pose proof (unsigned_range w); pose proof (Zpow2_pos n). rewrite Zpow2_add; nia.
Qed.

Lemma unsigned_wlshift : forall sz (w : word sz) n,
    unsigned (wlshift w n) = (unsigned w * Zpow2 n) mod Zpow2 sz.
Proof.
  intros; cbv [wlshift Zpow2]; rewrite Zmod.unsigned_slu, Z.shiftl_mul_pow2 by lia; reflexivity.
Qed.

Lemma unsigned_wrshift : forall sz (w : word sz) n,
    unsigned (wrshift w n) = unsigned w / Zpow2 n.
Proof.
  intros; cbv [wrshift Zpow2]; rewrite Zmod.unsigned_sru, Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma unsigned_wrshifta : forall sz (w : word sz) n,
    unsigned (wrshifta w n) = (signed w / Zpow2 n) mod Zpow2 sz.
Proof.
  intros; cbv [wrshifta Zpow2]; rewrite Zmod.unsigned_srs, Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma unsigned_wpow2 : forall sz, unsigned (wpow2 sz) = Zpow2 sz.
Proof.
  intros; cbv [wpow2]; apply unsigned_ofZ_small.
  rewrite Zpow2_S; pose proof (Zpow2_pos sz); lia.
Qed.

Lemma unsigned_wdivN : forall sz (x y : word sz), unsigned (wdivN x y) = unsigned x / unsigned y.
Proof.
  intros; cbv [wdivN]; apply unsigned_ofZ_small.
  pose proof (unsigned_range x); pose proof (unsigned_range y).
  destruct (Z.eq_dec (unsigned y) 0) as [E|E]; [rewrite E, Z.div_0_r; lia|].
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; nia.
Qed.

Lemma unsigned_wremN : forall sz (x y : word sz), unsigned (wremN x y) = unsigned x mod unsigned y.
Proof.
  intros; cbv [wremN]; apply unsigned_ofZ_small.
  pose proof (unsigned_range x); pose proof (unsigned_range y).
  destruct (Z.eq_dec (unsigned y) 0) as [E|E]; [rewrite E, Z.mod_0_r; lia|].
  pose proof (Z.mod_pos_bound (unsigned x) (unsigned y) ltac:(lia)). lia.
Qed.

Lemma unsigned_not : forall sz (w : word sz), unsigned (wnot w) = Zpow2 sz - 1 - unsigned w.
Proof.
  intros; cbv [Zpow2]; rewrite bits.unsigned_not', Z.ones_equiv; lia.
Qed.

Lemma unsigned_or : forall sz (x y : word sz), unsigned (wor x y) = Z.lor (unsigned x) (unsigned y).
Proof. intros; cbv [Zpow2]; apply bits.unsigned_or. Qed.

Lemma unsigned_and : forall sz (x y : word sz), unsigned (wand x y) = Z.land (unsigned x) (unsigned y).
Proof. intros; cbv [Zpow2]; apply bits.unsigned_and. Qed.

Lemma unsigned_xor : forall sz (x y : word sz), unsigned (wxor x y) = Z.lxor (unsigned x) (unsigned y).
Proof. intros; cbv [Zpow2]; apply bits.unsigned_xor. Qed.

Lemma unsigned_eq_rec : forall n n' (w : word n) (H : n = n'),
    unsigned (eq_rec n word w n' H) = unsigned w.
Proof. intros; destruct H; reflexivity. Qed.

Lemma unsigned_match_eq : forall n n' (w : word n) (H : n = n'),
    unsigned (match H in _ = N return word N with eq_refl => w end) = unsigned w.
Proof. intros; destruct H; reflexivity. Qed.

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

(** * A few facts about [mod] and [div] *)

Lemma Zmod_small_neg : forall a m, 0 < m -> - m <= a < 0 -> a mod m = a + m.
Proof.
  intros. rewrite <- (Z.mod_add a 1 m), Z.mod_small by lia. lia.
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

Lemma Zmod_mul_split : forall a p q, 0 < p -> 0 < q -> a mod (p * q) = a mod p + p * ((a / p) mod q).
Proof.
  intros. apply Z.rem_mul_r; lia.
Qed.

Lemma Zopp_mod_idemp : forall a p, p <> 0 -> (- (a mod p)) mod p = (- a) mod p.
Proof.
  intros. rewrite <- (Z.sub_0_l (a mod p)), Zminus_mod_idemp_r, Z.sub_0_l. reflexivity.
Qed.

Lemma Zmod_opp_sub : forall z p, p <> 0 -> (- z) mod p = (p - z) mod p.
Proof.
  intros. replace (p - z) with (- z + 1 * p) by lia. rewrite Z.mod_add; lia.
Qed.

(** [a mod M] for [a] within one modulus of the range [0, M): three cases. *)
Lemma Zmod_cases : forall a M, 0 < M -> - M <= a < 2 * M ->
    (0 <= a < M /\ a mod M = a) \/ (a < 0 /\ a mod M = a + M) \/ (M <= a /\ a mod M = a - M).
Proof.
  intros. destruct (Z_lt_le_dec a 0); [right; left | destruct (Z_lt_le_dec a M); [left | right; right]];
    (split; [lia|]); [apply Zmod_small_neg | apply Z.mod_small | apply Zmod_small_2]; lia.
Qed.

(** * Moving word goals to [Z] *)

Create HintDb unsigned_word.
#[global] Hint Rewrite
  unsigned_wones
  Zmod.unsigned_of_Z Zmod.unsigned_0 Zmod.unsigned_1
  Zmod.unsigned_add Zmod.unsigned_sub Zmod.unsigned_mul Zmod.unsigned_opp
  unsigned_and unsigned_or unsigned_xor unsigned_not
  Zmod.unsigned_eq_rect unsigned_eq_rec unsigned_match_eq
  unsigned_natToWord unsigned_NToWord
  unsigned_WS unsigned_wtl whd_eqn wmsb_eqn
  unsigned_combine unsigned_split1 unsigned_split2
  unsigned_sext unsigned_zext unsigned_extz
  unsigned_wlshift unsigned_wrshift unsigned_wrshifta unsigned_wpow2
  unsigned_wdivN unsigned_wremN
  signed_eqn
  : unsigned_word.

(** Turn equalities and disequalities of words into ones of [unsigned].
    The type of the equality may be spelled [word n], [Zmod _], or anything
    that reduces to it (Kami's [type (Bit n)]). *)
Ltac is_word_type T :=
  lazymatch eval hnf in T with
  | Zmod _ => idtac
  | _ => fail
  end.

Ltac word_eq_to_unsigned :=
  repeat match goal with
         | |- @eq ?T _ _ => is_word_type T; apply Zmod.unsigned_inj
         | |- not (@eq ?T _ _) =>
           is_word_type T;
           let H := fresh "Hw" in intro H; apply (f_equal (@Zmod.unsigned _)) in H
         | |- (@eq ?T _ _) -> False =>
           is_word_type T;
           let H := fresh "Hw" in intro H; apply (f_equal (@Zmod.unsigned _)) in H
         | H : @eq ?T _ _ |- _ => is_word_type T; apply (f_equal (@Zmod.unsigned _)) in H
         | H : not (@eq ?T ?a ?b) |- _ =>
           is_word_type T;
           let H' := fresh "Hw" in
           assert (H' : unsigned a <> unsigned b)
             by (let E := fresh in intro E; apply H; apply Zmod.unsigned_inj; exact E);
           clear H
         | H : (@eq ?T ?a ?b) -> False |- _ =>
           is_word_type T;
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

(** Push [Z.of_nat]/[Z.of_N] through arithmetic so that the [Z] lemmas apply. *)
Ltac push_inj :=
  repeat match goal with
         | |- context [Z.of_nat (?a - ?b)] => rewrite (Nat2Z.inj_sub a b) by lia
         | H : context [Z.of_nat (?a - ?b)] |- _ => rewrite (Nat2Z.inj_sub a b) in H by lia
         end;
  repeat first [ rewrite Nat2Z.inj_mul in * | rewrite Nat2Z.inj_add in * | rewrite pow2_Z in *
               | rewrite Nat2Z.inj_div in * | rewrite Nat2Z.inj_mod in * | rewrite Npow2_Z in *
               | rewrite N2Z.inj_mul in * | rewrite N2Z.inj_add in * | rewrite N2Z.inj_div in *
               | rewrite N2Z.inj_mod in * | rewrite N2Z.inj_pow in * | rewrite nat_N_Z in * ];
  change (Z.of_nat 0) with 0%Z in *; change (Z.of_nat 1) with 1%Z in *;
  change (Z.of_nat 2) with 2%Z in *;
  change (Z.of_N 0) with 0%Z in *; change (Z.of_N 1) with 1%Z in *;
  change (Z.of_N 2) with 2%Z in *.

(** A closed [Zpow2 n] is a numeral. *)
Ltac Zpow2_compute_one x :=
  let v := eval vm_compute in (Zpow2 x) in
  lazymatch v with
  | Zpos _ => replace (Zpow2 x) with v in * by (vm_compute; reflexivity)
  | _ => fail
  end.

Ltac Zpow2_compute :=
  repeat match goal with
         | |- context [Zpow2 ?x] => Zpow2_compute_one x
         | H : context [Zpow2 ?x] |- _ => Zpow2_compute_one x
         end.

Ltac pow2_normalize :=
  repeat first [ rewrite pow2_S in * | rewrite pow2_add_mul in * | rewrite Npow2_S in *
               | rewrite Zpow2_S in * | rewrite Zpow2_add in * | rewrite Zpow2_mul in * ];
  push_inj;
  rewrite ?Zpow2_0, ?Z.pow_0_r, ?Z.pow_1_r in *;
  Zpow2_compute.

(** [lia] is exponentially slow in the number of [mod] terms it sees;
    prove side conditions with the [mod]-carrying hypotheses cleared. *)
Ltac clear_mods :=
  repeat match goal with H : context [Z.modulo _ _] |- _ => clear H end.

(** Tell [lia] that [Zpow2 x] is positive, and what it is when the context
    already knows whether [x] is zero.  (Posing the two implications
    unconditionally makes [lia] case-split, which is exponential once [mod]
    terms are around.) *)
Ltac pow2_fact x :=
  lazymatch goal with
  | _ : (0 < Zpow2 x)%Z |- _ => fail
  | _ => pose proof (Zpow2_pos x);
         let Hx := fresh "Hx" in
         first [ assert (Hx : Z.of_nat x = 0%Z) by (clear_mods; lia);
                 pose proof (Zpow2_eq1 x Hx); clear Hx
               | assert (Hx : Z.of_nat x <> 0%Z) by (clear_mods; lia);
                 pose proof (Zpow2_ge2 x Hx); clear Hx
               | idtac ]
  end.

(** A product of two powers of two dominates both factors; [lia] treats the
    product as an atom, so say it. *)
Lemma Zpow2_prod : forall a b,
    0 < Zpow2 a * Zpow2 b /\ Zpow2 a <= Zpow2 a * Zpow2 b /\ Zpow2 b <= Zpow2 a * Zpow2 b.
Proof. intros; pose proof (Zpow2_pos a); pose proof (Zpow2_pos b); nia. Qed.

Ltac pow2_prod_fact a b :=
  lazymatch goal with
  | _ : 0 < Zpow2 a * Zpow2 b /\ _ |- _ => fail
  | _ => pose proof (Zpow2_prod a b)
  end.

Ltac pow2_facts :=
  repeat match goal with
         | |- context [Zpow2 ?x] => pow2_fact x
         | H : context [Zpow2 ?x] |- _ => pow2_fact x
         end;
  repeat match goal with
         | |- context [(Zpow2 ?a * Zpow2 ?b)%Z] => pow2_prod_fact a b
         | H : context [(Zpow2 ?a * Zpow2 ?b)%Z] |- _ => pow2_prod_fact a b
         end.

(** [pow2]/[Npow2] are the [nat]/[N]-valued powers of two; [lia] sees their
    injections as [2 ^ _], so relate them to [Zpow2]. *)
Ltac pow2_nat_fact x :=
  lazymatch goal with
  | _ : Z.of_nat (pow2 x) = Zpow2 x |- _ => fail
  | _ => pose proof (pow2_Z x)
  end.

Ltac Npow2_fact x :=
  lazymatch goal with
  | _ : Z.of_N (Npow2 x) = Zpow2 x |- _ => fail
  | _ => pose proof (Npow2_Z x)
  end.

Ltac pow2_nat_facts :=
  repeat match goal with
         | |- context [pow2 ?x] => pow2_nat_fact x
         | H : context [pow2 ?x] |- _ => pow2_nat_fact x
         | |- context [Npow2 ?x] => Npow2_fact x
         | H : context [Npow2 ?x] |- _ => Npow2_fact x
         end.

(** The implicit modulus of [@Zmod.unsigned m t] must be spelled exactly as
    the width in the type of [t] for the rewrite rules to match (e.g.
    [S sz] vs [1 + sz]); make it so. *)
Ltac canon_unsigned_one m t :=
  let T := type of t in
  lazymatch T with
  | word ?n =>
    let m0 := constr:(Zpow2 n) in
    tryif constr_eq m m0 then fail
    else (let E := fresh in
          assert (E : @Zmod.unsigned m t = @Zmod.unsigned m0 t) by reflexivity;
          rewrite E in *; clear E)
  | _ => fail
  end.

Ltac canon_unsigned :=
  repeat match goal with
         | |- context [@Zmod.unsigned ?m ?t] => canon_unsigned_one m t
         | H : context [@Zmod.unsigned ?m ?t] |- _ => canon_unsigned_one m t
         end.

Ltac word_to_Z :=
  intros;
  repeat match goal with x := _ |- _ => subst x end;
  word_eq_to_unsigned;
  cbv [wordToNat wordToN wlsb] in *;
  rewrite ?unsigned_wones in *;
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
  pow2_nat_facts; pow2_facts.

Ltac word_side := clear_mods; first [ lia | nia ].

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

(** Shape-conditioned rules (side conditions are positivity of moduli). *)
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

(** Replace every innermost [a mod M] whose argument is within one modulus of
    range by a variable and the three-way case split of [Zmod_cases], so that
    [lia] can finish. *)
Ltac word_mod_case a M :=
  let HM := fresh "HM" in
  let HB := fresh "HB" in
  let r := fresh "r" in
  let H := fresh "Hmod" in
  assert (HM : (0 < M)%Z) by (clear_mods; first [ lia | nia ]);
  assert (HB : (- M <= a < 2 * M)%Z) by (clear_mods; first [ lia | nia ]);
  pose proof (@Zmod_cases a M HM HB) as H; clear HM HB;
  set (r := (a mod M)%Z) in *; clearbody r.

Ltac word_mod_cases :=
  repeat match goal with
         | |- context [(?a mod ?M)%Z] =>
           lazymatch a with context [Z.modulo _ _] => fail | _ => word_mod_case a M end
         | H : context [(?a mod ?M)%Z] |- _ =>
           lazymatch a with context [Z.modulo _ _] => fail | _ => word_mod_case a M end
         end.

(** A big hammer: the case split, the rewrite rules, then [nia]. *)
Ltac word_lia_Z :=
  word_to_Z; try subst; rewrite ?Z.sub_diag in *;
  lazymatch goal with
  | |- @eq bool _ _ => first [ reflexivity | exfalso ]
  | _ => idtac
  end;
  first [ (word_mod_cases; first [ lia | nia ])
        | (word_mod_simpl; mod_args_unify; first [ lia | (f_equal; lia) | congruence | nia ])
        | (word_mod_simpl; word_mod_cases; first [ lia | nia ])
        | nia
        | (zify; Z.div_mod_to_equations; nia) ].

(** * Structural views *)

Lemma word0 : forall (w : word 0), w = WO.
Proof. intros; apply Zmod.unsigned_inj; rewrite bits.unsigned_width0; reflexivity. Qed.

Lemma shatter_word : forall n (w : word (S n)), w = WS (whd w) (wtl w).
Proof. word_lia_Z. Qed.

Lemma whd_WS : forall b n (w : word n), whd (WS b w) = b.
Proof. word_lia_Z. Qed.

Lemma wtl_WS : forall b n (w : word n), wtl (WS b w) = w.
Proof. word_lia_Z. Qed.

(** The eliminator of [word] seen as built from [WO] and [WS]; use it as
    [induction w using word_rect]. *)
Fixpoint word_rect (P : forall n, word n -> Type)
  (HO : P O WO)
  (HS : forall (b : bool) (n : nat) (w : word n), P n w -> P (S n) (WS b w))
  (n : nat) {struct n} : forall w : word n, P n w :=
  match n return forall w : word n, P n w with
  | O => fun w => eq_rect_r (P O) HO (word0 w)
  | S n' => fun w =>
      eq_rect_r (P (S n'))
                (HS (whd w) n' (wtl w) (word_rect P HO HS (wtl w)))
                (shatter_word w)
  end.

Definition word_ind (P : forall n, word n -> Prop) := word_rect P.
Definition word_rec (P : forall n, word n -> Set) := word_rect P.

Lemma destruct_word_S : forall n (w : word (S n)), exists (v : word n) (b : bool), w = WS b v.
Proof. intros; exists (wtl w), (whd w); apply shatter_word. Qed.

(** [word_destruct w] splits a [word (S _)] into its head bit, named [b],
    and its tail, which reuses the name [w]. *)
Tactic Notation "word_destruct" ident(w) :=
  (try (intros until w));
  let b := fresh "b" in
  let v := fresh "v" in
  let Hv := fresh "Hv" in
  destruct (destruct_word_S w) as [v [b Hv]]; subst w; rename v into w.

Local Close Scope Z_scope.

(** * The [nat] view *)

Lemma wordToNat_bound : forall sz (w : word sz), (#w < pow2 sz)%nat.
Proof. word_lia_Z. Qed.

Lemma natToWord_wordToNat : forall sz (w : word sz), $ (#w) = w.
Proof. word_lia_Z. Qed.

Lemma wordToNat_natToWord_idempotent' : forall sz n, (n < pow2 sz)%nat -> #(natToWord sz n) = n.
Proof. word_lia_Z. Qed.

Lemma wordToNat_inj : forall sz (a b : word sz), #a = #b -> a = b.
Proof. word_lia_Z. Qed.

Lemma roundTrip_0 : forall sz, #(natToWord sz 0) = 0.
Proof. word_lia_Z. Qed.

Lemma roundTrip_1 : forall sz, #(natToWord (S sz) 1) = 1.
Proof. word_lia_Z. Qed.

Lemma wones_pow2_minus_one : forall sz, #(wones sz) = pow2 sz - 1.
Proof. word_lia_Z. Qed.

Lemma natToWord_S : forall sz n, natToWord sz (S n) = $1 ^+ natToWord sz n.
Proof. word_lia_Z. Qed.

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = $n ^+ $m.
Proof. word_lia_Z. Qed.

Lemma wones_natToWord : forall sz, wones sz = natToWord sz (pow2 sz - 1).
Proof. word_lia_Z. Qed.

Lemma wplus_one_neq : forall sz (w : word (S sz)), w ^+ $1 <> w.
Proof. word_lia_Z. Qed.

(** Close a goal from a hypothesis [w ^+ $1 = w] or [w = w ^+ $1]. *)
Ltac wplus_one_contra :=
  exfalso; eapply wplus_one_neq;
  match goal with
  | H : _ = _ |- _ => first [ exact H | exact (eq_sym H) ]
  end.

(** * Uniqueness of equality proofs on words *)

Lemma weq_dec_eq : forall sz (a b : word sz) (pf1 pf2 : a = b), pf1 = pf2.
Proof. intros; apply UIP_dec, weq. Qed.
