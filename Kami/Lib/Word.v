(** Fixed precision machine words.

    [word n] is the standard library's [bits (Z.of_nat n)] (that is,
    [Zmod (2 ^ Z.of_nat n)]).  Every operation is a named wrapper, marked
    [simpl never], around a [Zmod.of_Z] of its integer specification, and
    every fact is proved by moving to [Zmod.unsigned] and reasoning in [Z]
    (see [word_to_Z] below).  Do not compute with words in proofs: rewrite
    with the [unsigned_*] lemmas instead. *)

From Stdlib Require Import Arith NArith ZArith Bool Lia ZifyNat ZifyN.
From Stdlib Require Import Eqdep_dec EqdepFacts.
From Stdlib Require Import Ring Ring_polynom.
From Stdlib Require Import Zmod.
From Stdlib Require Import Zmod.Bits.
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
Local Notation unsigned := Zmod.unsigned.
Local Notation ofZ := Zmod.of_Z.

(** The two constructors of the former inductive [word], as functions. *)
Definition WO : word 0 := ofZ _ 0.
Definition WS (b : bool) (n : nat) (w : word n) : word (S n) :=
  ofZ _ (Z.b2z b + 2 * unsigned w).

(** * Conversion to and from [nat] (or [N]), zero and one *)

Definition wordToNat sz (w : word sz) : nat := Z.to_nat (unsigned w).

Definition wordToNat' sz (w : word sz) : nat := wordToNat w.

Definition natToWord (sz n : nat) : word sz := ofZ _ (Z.of_nat n).

Definition wordToN sz (w : word sz) : N := Z.to_N (unsigned w).

Definition wzero sz := natToWord sz 0.

Definition wzero' (sz : nat) : word sz := ofZ _ 0.

Definition posToWord (sz : nat) (p : positive) : word sz := ofZ _ (Zpos p).

Definition NToWord (sz : nat) (n : N) : word sz := ofZ _ (Z.of_N n).

Definition wone sz := natToWord sz 1.

Definition wones (sz : nat) : word sz := ofZ _ (2 ^ Z.of_nat sz - 1).

(** * MSB, LSB, head, and tail *)

Definition wmsb sz (w : word sz) (a : bool) : bool :=
  match sz as s return word s -> bool with
  | O => fun _ => a
  | S sz' => fun w => Z.testbit (unsigned w) (Z.of_nat sz')
  end w.

Definition whd sz (w : word (S sz)) : bool := Z.odd (unsigned w).

Definition wlsb sz (w : word (S sz)) : bool := whd w.

Definition wtl sz (w : word (S sz)) : word sz := ofZ _ (unsigned w / 2).

Definition rep_bit (n : nat) (b : word 1) : word n :=
  if whd b then wones n else wzero n.

(** * Decidable equality *)

Definition weqb sz (x : word sz) (y : word sz) : bool := Zmod.eqb x y.

Definition weq : forall sz (x y : word sz), {x = y} + {x <> y}.
  refine (fun sz x y =>
            match weqb x y as b return weqb x y = b -> {x = y} + {x <> y} with
            | true => fun H => left _
            | false => fun H => right _
            end eq_refl);
    abstract (unfold weqb in H; destruct (Zmod.eqb_spec x y); congruence).
Defined.

(** * Combining and splitting *)

Definition combine (sz1 : nat) (w : word sz1) (sz2 : nat) (w' : word sz2)
  : word (sz1 + sz2) :=
  ofZ _ (unsigned w + 2 ^ Z.of_nat sz1 * unsigned w').

Definition split1 (sz1 sz2 : nat) (w : word (sz1 + sz2)) : word sz1 :=
  ofZ _ (unsigned w).

Definition split2 (sz1 sz2 : nat) (w : word (sz1 + sz2)) : word sz2 :=
  ofZ _ (unsigned w / 2 ^ Z.of_nat sz1).

(** * Extension operators *)

(** Kept literally as in the inductive-[word] version: several Kami example
    proofs rely on [sext]/[zext]/[extz] being [combine]s definitionally. *)
Definition sext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  if wmsb w false then combine w (wones sz') else combine w (wzero sz').

Definition zext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  combine w (wzero sz').

(** * Arithmetic *)

Definition wneg sz (x : word sz) : word sz := Zmod.opp x.

Definition wordBin (f : N -> N -> N) sz (x y : word sz) : word sz :=
  NToWord sz (f (wordToN x) (wordToN y)).

Definition wplus sz (x y : word sz) : word sz := Zmod.add x y.
Definition wmult sz (x y : word sz) : word sz := Zmod.mul x y.
Definition wdiv sz (x y : word sz) : word sz := ofZ _ (unsigned x / unsigned y).
Definition wmod sz (x y : word sz) : word sz := ofZ _ (unsigned x mod unsigned y).
Definition wmult' sz (x y : word sz) : word sz :=
  split2 sz sz (NToWord (sz + sz) (Nmult (wordToN x) (wordToN y))).
Definition wminus sz (x y : word sz) : word sz := Zmod.sub x y.
Definition wnegN sz (x : word sz) : word sz :=
  natToWord sz (pow2 sz - wordToNat x).

Definition wordBinN (f : nat -> nat -> nat) sz (x y : word sz) : word sz :=
  natToWord sz (f (wordToNat x) (wordToNat y)).

Definition wplusN := wordBinN plus.

Definition wmultN := wordBinN mult.
Definition wmultN' sz (x y : word sz) : word sz :=
  split2 sz sz (natToWord (sz + sz) (mult (wordToNat x) (wordToNat y))).

Definition wdivN := wordBinN Nat.div.
Definition wremN := wordBinN Nat.modulo.

Definition wminusN sz (x y : word sz) : word sz := wplusN x (wnegN y).

Notation "w ~ 1" := (WS true w) : word_scope.
Notation "w ~ 0" := (WS false w) : word_scope.

Notation "^~" := wneg.
Notation "l ^+ r" := (@wplus _ l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (@wmult _ l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (@wminus _ l%word r%word) (at level 50, left associativity).
Notation "l ^/ r" := (@wdiv _ l%word r%word) (at level 50, left associativity).
Notation "l ^% r" := (@wmod _ l%word r%word) (at level 50, left associativity).

(** * Bitwise operators *)

Definition wnot sz (w : word sz) : word sz := Zmod.not w.

(** [bitwp f] applies [f] bit by bit; it is only used to state facts about
    the bitwise operators below, which are the [Zmod] ones. *)
Fixpoint bitwp (f : bool -> bool -> bool) (sz : nat) : word sz -> word sz -> word sz :=
  match sz with
  | O => fun _ _ => WO
  | S sz' => fun w1 w2 => WS (f (whd w1) (whd w2)) (@bitwp f sz' (wtl w1) (wtl w2))
  end.

Definition wnot' sz := bitwp xorb (wones sz).
Definition wor sz (x y : word sz) : word sz := Zmod.or x y.
Definition wand sz (x y : word sz) : word sz := Zmod.and x y.
Definition wxor sz (x y : word sz) : word sz := Zmod.xor x y.

Notation "l ^| r" := (@wor _ l%word r%word) (at level 50, left associativity).
Notation "l ^& r" := (@wand _ l%word r%word) (at level 40, left associativity).

(** * Conversion to and from [Z] *)

Definition wordToZ sz (w : word sz) : Z := Zmod.signed w.

Definition uwordToZ sz (w : word sz) : Z := unsigned w.

Definition ZToWord (sz : nat) (z : Z) : word sz := ofZ _ z.

(** * Arithmetic by [Z] *)

Definition wordBinZ (f : Z -> Z -> Z) sz (x y : word sz) : word sz :=
  ZToWord sz (f (wordToZ x) (wordToZ y)).

Definition wplusZ := wordBinZ Z.add.
Definition wminusZ := wordBinZ Z.sub.
Definition wmultZ := wordBinZ Z.mul.
Definition wmultZsu sz (x y : word sz) :=
  ZToWord sz (Z.mul (wordToZ x) (Z.of_N (wordToN y))).
Definition wdivZ := wordBinZ Z.quot.
Definition wdivZsu sz (x y : word sz) :=
  ZToWord sz (Z.div (wordToZ x) (Z.of_N (wordToN y))).
Definition wremZ := wordBinZ Z.rem.
Definition wremZsu sz (x y : word sz) :=
  ZToWord sz (Z.modulo (wordToZ x) (Z.of_N (wordToN y))).

(** * Comparison predicates and deciders *)

Definition wlt sz (l r : word sz) : Prop :=
  N.lt (wordToN l) (wordToN r).
Definition wslt sz (l r : word sz) : Prop :=
  Z.lt (wordToZ l) (wordToZ r).

Notation "w1 > w2" := (@wlt _ w2%word w1%word) : word_scope.
Notation "w1 >= w2" := (~(@wlt _ w1%word w2%word)) : word_scope.
Notation "w1 < w2" := (@wlt _ w1%word w2%word) : word_scope.
Notation "w1 <= w2" := (~(@wlt _ w2%word w1%word)) : word_scope.

Notation "w1 '>s' w2" := (@wslt _ w2%word w1%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '>s=' w2" := (~(@wslt _ w1%word w2%word)) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s' w2" := (@wslt _ w1%word w2%word) (at level 70, w2 at next level) : word_scope.
Notation "w1 '<s=' w2" := (~(@wslt _ w2%word w1%word)) (at level 70, w2 at next level) : word_scope.

Definition wlt_dec : forall sz (l r : word sz), {l < r} + {l >= r}.
  refine (fun sz l r =>
    match N.compare (wordToN l) (wordToN r) as k return N.compare (wordToN l) (wordToN r) = k -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

Definition wslt_dec : forall sz (l r : word sz), {l <s r} + {l >s= r}.
  refine (fun sz l r =>
    match Z.compare (wordToZ l) (wordToZ r) as c return Z.compare (wordToZ l) (wordToZ r) = c -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

Notation "$ n" := (natToWord _ n) (at level 1, format "$ n").
Notation "# n" := (wordToNat n) (at level 5, format "# n").

(** * Bit shifting *)

Fact sz_minus_nshift : forall sz nshift, (nshift < sz)%nat -> sz = sz - nshift + nshift.
Proof.
  intros; lia.
Qed.

Fact nshift_plus_nkeep : forall sz nshift, (nshift < sz)%nat -> nshift + (sz - nshift) = sz.
Proof.
  intros; lia.
Qed.

Definition wlshift (sz : nat) (w : word sz) (n : nat) : word sz :=
  ofZ _ (unsigned w * 2 ^ Z.of_nat n).

Definition wrshift (sz : nat) (w : word sz) (n : nat) : word sz :=
  ofZ _ (unsigned w / 2 ^ Z.of_nat n).

Definition wrshifta (sz : nat) (w : word sz) (n : nat) : word sz :=
  ofZ _ (Zmod.signed w / 2 ^ Z.of_nat n).

Definition extz {sz} (w: word sz) (n: nat) : word (n + sz) := combine (wzero n) w.

Definition wpow2 sz : word (S sz) := ofZ _ (2 ^ Z.of_nat sz).

Notation "l ^<< r" := (@wlshift _ _ l%word r%word) (at level 35).
Notation "l ^>> r" := (@wrshift _ _ l%word r%word) (at level 35).

(** * Setting an individual bit *)

Definition wbit sz sz' (n : word sz') := natToWord sz (pow2 (wordToNat n)).

(** Never compute with any of the above; rewrite with the [unsigned_*]
    facts instead (reducing through [Zmod.of_Z] duplicates subterms at
    every nesting level). *)
Arguments WO : simpl never.
Arguments WS _ {_} _ : simpl never.
Arguments wordToNat {_} _ : simpl never.
Arguments wordToNat' {_} _ : simpl never.
Arguments natToWord _ _ : simpl never.
Arguments wordToN {_} _ : simpl never.
Arguments wzero _ : simpl never.
Arguments wzero' _ : simpl never.
Arguments posToWord _ _ : simpl never.
Arguments NToWord _ _ : simpl never.
Arguments wone _ : simpl never.
Arguments wones _ : simpl never.
Arguments wmsb {_} _ _ : simpl never.
Arguments whd {_} _ : simpl never.
Arguments wlsb {_} _ : simpl never.
Arguments wtl {_} _ : simpl never.
Arguments rep_bit _ _ : simpl never.
Arguments weqb {_} _ _ : simpl never.
Arguments weq {_} _ _ : simpl never.
Arguments combine {_} _ {_} _ : simpl never.
Arguments split1 _ _ _ : simpl never.
Arguments split2 _ _ _ : simpl never.
Arguments sext {_} _ _ : simpl never.
Arguments zext {_} _ _ : simpl never.
Arguments wneg {_} _ : simpl never.
Arguments wordBin _ {_} _ _ : simpl never.
Arguments wplus {_} _ _ : simpl never.
Arguments wmult {_} _ _ : simpl never.
Arguments wdiv {_} _ _ : simpl never.
Arguments wmod {_} _ _ : simpl never.
Arguments wmult' {_} _ _ : simpl never.
Arguments wminus {_} _ _ : simpl never.
Arguments wnegN {_} _ : simpl never.
Arguments wordBinN _ {_} _ _ : simpl never.
Arguments wplusN {_} _ _ : simpl never.
Arguments wmultN {_} _ _ : simpl never.
Arguments wmultN' {_} _ _ : simpl never.
Arguments wdivN {_} _ _ : simpl never.
Arguments wremN {_} _ _ : simpl never.
Arguments wminusN {_} _ _ : simpl never.
Arguments wnot {_} _ : simpl never.
Arguments bitwp _ {_} _ _ : simpl never.
Arguments wnot' {_} _ : simpl never.
Arguments wor {_} _ _ : simpl never.
Arguments wand {_} _ _ : simpl never.
Arguments wxor {_} _ _ : simpl never.
Arguments wordToZ {_} _ : simpl never.
Arguments uwordToZ {_} _ : simpl never.
Arguments ZToWord _ _ : simpl never.
Arguments wordBinZ _ {_} _ _ : simpl never.
Arguments wplusZ {_} _ _ : simpl never.
Arguments wminusZ {_} _ _ : simpl never.
Arguments wmultZ {_} _ _ : simpl never.
Arguments wmultZsu {_} _ _ : simpl never.
Arguments wdivZ {_} _ _ : simpl never.
Arguments wdivZsu {_} _ _ : simpl never.
Arguments wremZ {_} _ _ : simpl never.
Arguments wremZsu {_} _ _ : simpl never.
Arguments wlt {_} _ _ : simpl never.
Arguments wslt {_} _ _ : simpl never.
Arguments wlt_dec {_} _ _ : simpl never.
Arguments wslt_dec {_} _ _ : simpl never.
Arguments wlshift {_} _ _ : simpl never.
Arguments wrshift {_} _ _ : simpl never.
Arguments wrshifta {_} _ _ : simpl never.
Arguments extz {_} _ _ : simpl never.
Arguments wpow2 _ : simpl never.
Arguments wbit _ {_} _ : simpl never.
Arguments Zmod.unsigned {_} _ : simpl never.
Arguments Zmod.signed {_} _ : simpl never.
Arguments Zmod.of_Z _ _ : simpl never.

(*! Facts *)

(** * The [unsigned] characterization of every operation *)

Local Open Scope Z_scope.

Lemma pow2_Z : forall n, Z.of_nat (pow2 n) = 2 ^ Z.of_nat n.
Proof. intros; apply Nat2Z.inj_pow. Qed.

Lemma Npow2_Z : forall n, Z.of_N (Npow2 n) = 2 ^ Z.of_nat n.
Proof. apply NatLib.Z_of_N_Npow2. Qed.

(** [lia] sees [Npow2] as [2 ^ _] ([pow2] is [Nat.pow 2], already known). *)
#[global] Instance Op_Npow2 : ZifyClasses.UnOp Npow2 :=
  { ZifyClasses.TUOp := fun x => 2 ^ x; ZifyClasses.TUOpInj := Npow2_Z }.
Add Zify UnOp Op_Npow2.

Lemma unsigned_range : forall sz (w : word sz), 0 <= unsigned w < 2 ^ Z.of_nat sz.
Proof. intros; apply bits.unsigned_range, Nat2Z.is_nonneg. Qed.

Lemma unsigned_inj : forall sz (a b : word sz), unsigned a = unsigned b -> a = b.
Proof. intros; apply Zmod.unsigned_inj; assumption. Qed.

Lemma unsigned_ofZ : forall sz z, unsigned (@ofZ (2 ^ Z.of_nat sz) z) = z mod 2 ^ Z.of_nat sz.
Proof. intros; apply Zmod.unsigned_of_Z. Qed.

Lemma unsigned_ofZ_small : forall sz z, 0 <= z < 2 ^ Z.of_nat sz -> unsigned (@ofZ (2 ^ Z.of_nat sz) z) = z.
Proof. intros; rewrite unsigned_ofZ; apply Z.mod_small; assumption. Qed.

Lemma ofZ_unsigned : forall sz (w : word sz), @ofZ (2 ^ Z.of_nat sz) (unsigned w) = w.
Proof. intros; apply Zmod.of_Z_unsigned. Qed.

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

Lemma unsigned_WO : unsigned WO = 0.
Proof. reflexivity. Qed.

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

(** Kill the branches where the sign of a [combine] disagrees with the sign
    of its high part. *)
Ltac msb_combine_contra :=
  try match goal with
      | H : (?p1 * ?p2 <= 2 * (?z0 + ?p1 * ?z))%Z, H' : (2 * ?z < ?p2)%Z |- _ =>
        exfalso; pose proof (@msb_combine_lt p1 p2 z0 z); lia
      | H : (2 * (?z0 + ?p1 * ?z) < ?p1 * ?p2)%Z, H' : (?p2 <= 2 * ?z)%Z |- _ =>
        exfalso; pose proof (@msb_combine_ge p1 p2 z0 z); lia
      end.

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
  intros; cbv [WS]; apply unsigned_ofZ_small.
  pose proof (unsigned_range w); rewrite pow2_S_Z.
  destruct b; cbn [Z.b2z]; lia.
Qed.

Lemma unsigned_natToWord : forall sz n, unsigned (natToWord sz n) = Z.of_nat n mod 2 ^ Z.of_nat sz.
Proof. intros; apply unsigned_ofZ. Qed.

Lemma unsigned_NToWord : forall sz n, unsigned (NToWord sz n) = Z.of_N n mod 2 ^ Z.of_nat sz.
Proof. intros; apply unsigned_ofZ. Qed.

Lemma unsigned_ZToWord : forall sz z, unsigned (ZToWord sz z) = z mod 2 ^ Z.of_nat sz.
Proof. intros; apply unsigned_ofZ. Qed.

Lemma unsigned_posToWord : forall sz p, unsigned (posToWord sz p) = Zpos p mod 2 ^ Z.of_nat sz.
Proof. intros; apply unsigned_ofZ. Qed.

Lemma unsigned_wzero : forall sz, unsigned (wzero sz) = 0.
Proof. intros; cbv [wzero]; rewrite unsigned_natToWord; apply Z.mod_0_l; lia. Qed.

Lemma unsigned_wzero' : forall sz, unsigned (wzero' sz) = 0.
Proof. intros; cbv [wzero']; rewrite unsigned_ofZ; apply Z.mod_0_l; lia. Qed.

Lemma unsigned_wone : forall sz, unsigned (wone sz) = 1 mod 2 ^ Z.of_nat sz.
Proof. intros; apply unsigned_natToWord. Qed.

Lemma unsigned_wones : forall sz, unsigned (wones sz) = 2 ^ Z.of_nat sz - 1.
Proof. intros; cbv [wones]; apply unsigned_ofZ_small; lia. Qed.

Lemma unsigned_wtl : forall sz (w : word (S sz)), unsigned (wtl w) = unsigned w / 2.
Proof.
  intros; cbv [wtl]; apply unsigned_ofZ_small.
  pose proof (unsigned_range_S w).
  Z.div_mod_to_equations; lia.
Qed.

Lemma whd_eqn : forall sz (w : word (S sz)), whd w = Z.odd (unsigned w).
Proof. reflexivity. Qed.

Lemma unsigned_combine : forall sz1 (w : word sz1) sz2 (w' : word sz2),
    unsigned (combine w w') = unsigned w + 2 ^ Z.of_nat sz1 * unsigned w'.
Proof.
  intros; cbv [combine]; apply unsigned_ofZ_small.
  pose proof (unsigned_range w); pose proof (unsigned_range w').
  rewrite pow2_add_Z. nia.
Qed.

Lemma unsigned_split1 : forall sz1 sz2 (w : word (sz1 + sz2)),
    unsigned (split1 sz1 sz2 w) = unsigned w mod 2 ^ Z.of_nat sz1.
Proof. intros; apply unsigned_ofZ. Qed.

Lemma unsigned_split2 : forall sz1 sz2 (w : word (sz1 + sz2)),
    unsigned (split2 sz1 sz2 w) = unsigned w / 2 ^ Z.of_nat sz1.
Proof.
  intros; cbv [split2]; apply unsigned_ofZ_small.
  pose proof (unsigned_range_add w).
  pose proof (pow2_pos_Z sz1); pose proof (pow2_pos_Z sz2).
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.

Lemma unsigned_zext : forall sz (w : word sz) sz',
    unsigned (zext w sz') = unsigned w.
Proof.
  intros; cbv [zext]; rewrite unsigned_combine, unsigned_wzero; ring.
Qed.

Lemma unsigned_extz : forall sz (w : word sz) n,
    unsigned (extz w n) = 2 ^ Z.of_nat n * unsigned w.
Proof.
  intros; cbv [extz]; rewrite unsigned_combine, unsigned_wzero; ring.
Qed.

Lemma unsigned_wneg : forall sz (x : word sz), unsigned (wneg x) = (- unsigned x) mod 2 ^ Z.of_nat sz.
Proof. intros; apply Zmod.unsigned_opp. Qed.

Lemma unsigned_wplus : forall sz (x y : word sz), unsigned (wplus x y) = (unsigned x + unsigned y) mod 2 ^ Z.of_nat sz.
Proof. intros; apply Zmod.unsigned_add. Qed.

Lemma unsigned_wminus : forall sz (x y : word sz), unsigned (wminus x y) = (unsigned x - unsigned y) mod 2 ^ Z.of_nat sz.
Proof. intros; apply Zmod.unsigned_sub. Qed.

Lemma unsigned_wmult : forall sz (x y : word sz), unsigned (wmult x y) = (unsigned x * unsigned y) mod 2 ^ Z.of_nat sz.
Proof. intros; apply Zmod.unsigned_mul. Qed.

Lemma unsigned_wdiv : forall sz (x y : word sz), unsigned (wdiv x y) = unsigned x / unsigned y.
Proof.
  intros; cbv [wdiv]; apply unsigned_ofZ_small.
  pose proof (unsigned_range x); pose proof (unsigned_range y).
  destruct (Z.eq_dec (unsigned y) 0) as [E|E]; [rewrite E, Z.div_0_r; lia|].
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; nia.
Qed.

Lemma unsigned_wmod : forall sz (x y : word sz), unsigned (wmod x y) = unsigned x mod unsigned y.
Proof.
  intros; cbv [wmod]; apply unsigned_ofZ_small.
  pose proof (unsigned_range x); pose proof (unsigned_range y).
  destruct (Z.eq_dec (unsigned y) 0) as [E|E]; [rewrite E, Z.mod_0_r; lia|].
  pose proof (Z.mod_pos_bound (unsigned x) (unsigned y) ltac:(lia)). lia.
Qed.

Lemma unsigned_wnot : forall sz (w : word sz), unsigned (wnot w) = 2 ^ Z.of_nat sz - 1 - unsigned w.
Proof.
  intros; cbv [wnot Zmod.not]; rewrite unsigned_ofZ.
  pose proof (unsigned_range w).
  replace (Z.lnot (unsigned w)) with (2 ^ Z.of_nat sz - 1 - unsigned w + (-1) * 2 ^ Z.of_nat sz) by (unfold Z.lnot; lia).
  rewrite Z.mod_add by lia; apply Z.mod_small; lia.
Qed.

Lemma unsigned_wor : forall sz (x y : word sz), unsigned (wor x y) = Z.lor (unsigned x) (unsigned y).
Proof. intros; apply bits.unsigned_or; try apply Nat2Z.is_nonneg. Qed.

Lemma unsigned_wand : forall sz (x y : word sz), unsigned (wand x y) = Z.land (unsigned x) (unsigned y).
Proof. intros; apply bits.unsigned_and. Qed.

Lemma unsigned_wxor : forall sz (x y : word sz), unsigned (wxor x y) = Z.lxor (unsigned x) (unsigned y).
Proof. intros; apply bits.unsigned_xor; try apply Nat2Z.is_nonneg. Qed.

Lemma unsigned_wlshift : forall sz (w : word sz) n,
    unsigned (wlshift w n) = (unsigned w * 2 ^ Z.of_nat n) mod 2 ^ Z.of_nat sz.
Proof. intros; apply unsigned_ofZ. Qed.

Lemma unsigned_wrshift : forall sz (w : word sz) n,
    unsigned (wrshift w n) = unsigned w / 2 ^ Z.of_nat n.
Proof.
  intros; cbv [wrshift]; apply unsigned_ofZ_small.
  pose proof (unsigned_range w). pose proof (pow2_pos_Z n).
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; nia.
Qed.

Lemma unsigned_wrshifta : forall sz (w : word sz) n,
    unsigned (wrshifta w n) = (Zmod.signed w / 2 ^ Z.of_nat n) mod 2 ^ Z.of_nat sz.
Proof. intros; apply unsigned_ofZ. Qed.

Lemma unsigned_wpow2 : forall sz, unsigned (wpow2 sz) = 2 ^ Z.of_nat sz.
Proof.
  intros; cbv [wpow2]; apply unsigned_ofZ_small.
  rewrite pow2_S_Z; pose proof (pow2_pos_Z sz); lia.
Qed.

Lemma wmsb_eqn : forall sz (w : word (S sz)) a, wmsb w a = (2 ^ Z.of_nat sz <=? unsigned w).
Proof.
  intros; cbv [wmsb].
  pose proof (unsigned_range_S w).
  rewrite Z.testbit_eqb by lia.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat sz) ltac:(lia) ltac:(lia)).
  assert (Hq : unsigned w / 2 ^ Z.of_nat sz = if 2 ^ Z.of_nat sz <=? unsigned w then 1 else 0).
  { destruct (Z.leb_spec (2 ^ Z.of_nat sz) (unsigned w)); Z.div_mod_to_equations; nia. }
  rewrite Hq; destruct (Z.leb_spec (2 ^ Z.of_nat sz) (unsigned w)); reflexivity.
Qed.

Lemma wmsb_0_eqn : forall (w : word 0) a, wmsb w a = a.
Proof. reflexivity. Qed.

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

Lemma existT_word_eq : forall n1 (w1 : word n1) n2 (w2 : word n2),
    n1 = n2 -> unsigned w1 = unsigned w2 -> existT word n1 w1 = existT word n2 w2.
Proof.
  intros; subst; f_equal; apply unsigned_inj; assumption.
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
Proof.
  intros; cbv [sext]; pose proof (unsigned_range w);
    pose proof (pow2_pos_Z sz); pose proof (pow2_pos_Z sz');
    pose proof (pow2_pos_Z (sz + sz')).
  assert (Hm : (2 ^ Z.of_nat (sz + sz') = 2 ^ Z.of_nat sz * 2 ^ Z.of_nat sz')%Z)
    by (apply pow2_add_Z).
  rewrite wmsb_eqn_gen, signed_eqn.
  destruct (Z.eqb_spec (Z.of_nat sz) 0) as [E|E].
  - assert (Es : sz = 0%nat) by lia; subst sz.
    assert (P0 : (2 ^ Z.of_nat 0 = 1)%Z) by reflexivity.
    assert (Eu : unsigned w = 0%Z) by lia.
    rewrite unsigned_combine, unsigned_wzero, Eu.
    destruct (Z.ltb_spec (2 * 0) (2 ^ Z.of_nat 0)); [|lia].
    rewrite Z.mod_0_l by lia; ring.
  - destruct (Z.leb_spec (2 ^ Z.of_nat sz) (2 * unsigned w)).
    + rewrite unsigned_combine, unsigned_wones.
      destruct (Z.ltb_spec (2 * unsigned w) (2 ^ Z.of_nat sz)); [lia|].
      rewrite (@Zmod_small_neg (unsigned w - 2 ^ Z.of_nat sz)
                               (2 ^ Z.of_nat (sz + sz'))) by nia.
      rewrite Hm; ring.
    + rewrite unsigned_combine, unsigned_wzero.
      destruct (Z.ltb_spec (2 * unsigned w) (2 ^ Z.of_nat sz)); [|lia].
      rewrite (Z.mod_small (unsigned w)) by nia; ring.
Qed.


(** * A few facts about [mod] and [div] by products (for split/combine) *)

Lemma Zmod_mul_div : forall a p q, 0 < p -> 0 < q -> (a mod (p * q)) / p = (a / p) mod q.
Proof.
  intros. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm p ((a / p) mod q)), Z.div_add by lia.
  rewrite (Z.div_small (a mod p) p) by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma Zmod_mul_div' : forall a p q, 0 < p -> 0 < q -> (a mod (q * p)) / p = (a / p) mod q.
Proof.
  intros. rewrite Z.mul_comm. apply Zmod_mul_div; assumption.
Qed.

Lemma Zmod_mul_mod : forall a p q, 0 < p -> 0 < q -> (a mod (p * q)) mod p = a mod p.
Proof.
  intros. apply Z.mod_mod_divide. exists q; lia.
Qed.

Lemma Zdiv_div_mul : forall a p q, 0 < p -> 0 < q -> a / p / q = a / (p * q).
Proof.
  intros. apply Z.div_div; lia.
Qed.

Lemma Zmod_mul_split : forall a p q, 0 < p -> 0 < q -> a mod (p * q) = a mod p + p * ((a / p) mod q).
Proof.
  intros. apply Z.rem_mul_r; lia.
Qed.

Lemma Zdiv_mod_mul_recompose : forall a p q, 0 < p -> 0 < q ->
    (a / p) mod q + q * (a / (p * q)) = a / p.
Proof.
  intros. rewrite <- Zdiv_div_mul by lia.
  pose proof (Z.div_mod (a / p) q ltac:(lia)). lia.
Qed.

Lemma Zminus_mul_mod : forall a k p, p <> 0 -> (a - k * p) mod p = a mod p.
Proof.
  intros. replace (a - k * p) with (a + (- k) * p) by lia. apply Z.mod_add; lia.
Qed.

Lemma Zplus_mul_mod : forall a k p, p <> 0 -> (a + k * p) mod p = a mod p.
Proof.
  intros. apply Z.mod_add; lia.
Qed.

Lemma Zmod_opp_sub : forall z p, p <> 0 -> (- z) mod p = (p - z) mod p.
Proof.
  intros. replace (p - z) with (- z + 1 * p) by lia. rewrite Z.mod_add; lia.
Qed.

Lemma Zplus_pminus_mod : forall a b p, p <> 0 -> (a + (p - b)) mod p = (a - b) mod p.
Proof.
  intros. replace (a + (p - b)) with (a - b + 1 * p) by lia. rewrite Z.mod_add; lia.
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

Lemma Zcombine_inj : forall p a b c d, 0 < p -> 0 <= a < p -> 0 <= c < p ->
    a + p * b = c + p * d -> a = c /\ b = d.
Proof.
  intros.
  assert (a = c).
  { rewrite <- (Z.mod_small a p), <- (Z.mod_small c p) by lia.
    rewrite <- (Z.mod_add a b p), <- (Z.mod_add c d p) by lia.
    f_equal; lia. }
  split; [assumption | apply (Z.mul_reg_l b d p); lia].
Qed.

(** * Moving word goals to [Z] *)

#[global] Hint Rewrite unsigned_WO unsigned_WS unsigned_natToWord unsigned_NToWord
  unsigned_ZToWord unsigned_posToWord unsigned_wzero unsigned_wzero' unsigned_wone
  unsigned_wones unsigned_wtl whd_eqn unsigned_combine unsigned_split1 unsigned_split2
  unsigned_sext unsigned_zext unsigned_extz unsigned_wneg unsigned_wplus unsigned_wminus
  unsigned_wmult unsigned_wdiv unsigned_wmod unsigned_wnot unsigned_wor unsigned_wand
  unsigned_wxor unsigned_wlshift unsigned_wrshift unsigned_wrshifta unsigned_wpow2
  wmsb_eqn_gen signed_eqn unsigned_eq_rect unsigned_eq_rec unsigned_match_eq
  : unsigned_word.

(** Turn equalities and disequalities of words into ones of [unsigned]. *)
Ltac word_eq_to_unsigned :=
  repeat match goal with
         | |- @eq (word _) _ _ => apply unsigned_inj
         | |- not (@eq (word _) _ _) =>
           let H := fresh "Hw" in intro H; apply (f_equal (@Zmod.unsigned _)) in H
         | |- (@eq (word _) _ _) -> False =>
           let H := fresh "Hw" in intro H; apply (f_equal (@Zmod.unsigned _)) in H
         | H : @eq (word _) _ _ |- _ => apply (f_equal (@Zmod.unsigned _)) in H
         | H : not (@eq (word ?sz) ?a ?b) |- _ =>
           let H' := fresh "Hw" in
           assert (H' : unsigned a <> unsigned b)
             by (let E := fresh in intro E; apply H; apply unsigned_inj; exact E);
           clear H
         | H : (@eq (word ?sz) ?a ?b) -> False |- _ =>
           let H' := fresh "Hw" in
           assert (H' : unsigned a <> unsigned b)
             by (let E := fresh in intro E; apply H; apply unsigned_inj; exact E);
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
  repeat first [ rewrite Nat2Z.inj_mul in * | rewrite Nat2Z.inj_add in * | rewrite Nat2Z.inj_pow in *
               | rewrite Nat2Z.inj_div in * | rewrite Nat2Z.inj_mod in * | rewrite Npow2_Z in *
               | rewrite N2Z.inj_mul in * | rewrite N2Z.inj_add in * | rewrite N2Z.inj_div in *
               | rewrite N2Z.inj_mod in * | rewrite N2Z.inj_pow in * | rewrite nat_N_Z in * ];
  change (Z.of_nat 0) with 0%Z in *; change (Z.of_nat 1) with 1%Z in *;
  change (Z.of_nat 2) with 2%Z in *;
  change (Z.of_N 0) with 0%Z in *; change (Z.of_N 1) with 1%Z in *;
  change (Z.of_N 2) with 2%Z in *.

Ltac pow2_normalize :=
  repeat first [ rewrite pow2_S in * | rewrite pow2_add_mul in * | rewrite Npow2_S in *
               | rewrite pow2_S_Z in * | rewrite pow2_add_Z in * | rewrite pow2_mul_Z in * ];
  push_inj;
  rewrite ?Z.pow_0_r, ?Z.pow_1_r in *.

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
  lazymatch T with
  | word ?n =>
    let m0 := constr:((2 ^ Z.of_nat n)%Z) in
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
  cbv [wordToNat wordToNat' wordToN uwordToZ wordToZ wlt wslt] in *;
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

(** A big hammer: [lia], then [nia], then [nia] with division facts. *)
Ltac word_lia_Z :=
  word_to_Z; try subst; rewrite ?Z.sub_diag in *;
  first [ lia
        | (word_mod_simpl; mod_args_unify; first [ lia | (f_equal; lia) | congruence | nia ])
        | nia
        | (zify; Z.div_mod_to_equations; nia) ].

(** The legacy statements below are written in [nat_scope], as they were. *)
Local Close Scope Z_scope.

(** * Facts about the former constructors *)

#[global] Hint Rewrite div2_double div2_S_double: div2.
Local Hint Resolve mod2_S_double mod2_double.

Theorem eq_rect_word_offset : forall n n' offset w Heq,
  eq_rect n (fun n => word (offset + n)) w n' Heq =
  eq_rect (offset + n) (fun n => word n) w (offset + n') (eq_rect_word_offset_helper _ _ _ Heq).
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec Nat.eq_dec (eq_rect_word_offset_helper _ _ offset eq_refl) eq_refl).
  reflexivity.
Qed.

Theorem eq_rect_word_mult : forall n n' scale w Heq,
  eq_rect n (fun n => word (n * scale)) w n' Heq =
  eq_rect (n * scale) (fun n => word n) w (n' * scale) (eq_rect_word_mult_helper _ _ _ Heq).
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec Nat.eq_dec (eq_rect_word_mult_helper _ _ scale eq_refl) eq_refl).
  reflexivity.
Qed.

Theorem eq_rect_word_match : forall n n' (w : word n) (H : n = n'),
  match H in (_ = N) return (word N) with
  | eq_refl => w
  end = eq_rect n (fun n => word n) w n' H.
Proof.
  intros.
  destruct H.
  rewrite <- (eq_rect_eq_dec Nat.eq_dec).
  reflexivity.
Qed.

Theorem whd_match : forall n n' (w : word (S n)) (Heq : S n = S n'),
  whd w = whd (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
  intros; rewrite !whd_eqn, unsigned_match_eq; reflexivity.
Qed.

Theorem wtl_match : forall n n' (w : word (S n)) (Heq : S n = S n') (Heq' : n = n'),
  (match Heq' in (_ = N) return (word N) with
   | eq_refl => wtl w
   end) = wtl (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
  intros; apply unsigned_inj.
  rewrite unsigned_match_eq, !unsigned_wtl, unsigned_match_eq; reflexivity.
Qed.

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
  apply unsigned_inj. rewrite unsigned_WS, unsigned_wtl, whd_eqn.
  pose proof (Z.div2_odd (unsigned a)); rewrite Z.div2_div in H; lia.
Qed.

Lemma shatter_word_S : forall n (a : word (S n)),
  exists b, exists c, a = WS b c.
Proof.
  intros; repeat eexists; apply (shatter_word a).
Qed.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.
Proof.
  intros a; apply (shatter_word a).
Qed.

#[global] Hint Resolve shatter_word_0.

Theorem wordToNat_wordToNat' : forall sz (w : word sz),
  wordToNat w = wordToNat' w.
Proof.
  reflexivity.
Qed.

Theorem natToWord_wordToNat : forall sz w, natToWord sz (wordToNat w) = w.
Proof.
  word_lia_Z.
Qed.

Theorem roundTrip_0 : forall sz, wordToNat (natToWord sz 0) = 0.
Proof.
  word_lia_Z.
Qed.

#[global] Hint Rewrite roundTrip_0 : wordToNat.

Lemma wordToNat_natToWord' : forall sz w, exists k, wordToNat (natToWord sz w) + k * pow2 sz = w.
Proof.
  intros; exists (w / pow2 sz).
  word_lia_Z.
Qed.

Theorem wordToNat_natToWord:
  forall sz w, exists k, wordToNat (natToWord sz w) = w - k * pow2 sz /\ (k * pow2 sz <= w)%nat.
Proof.
  intros; exists (w / pow2 sz).
  word_lia_Z.
Qed.

Lemma wordToNat_natToWord_2: forall sz w : nat,
    (w < pow2 sz)%nat -> wordToNat (natToWord sz w) = w.
Proof.
  word_lia_Z.
Qed.

Lemma natToWord_times2: forall sz x,
  ((natToWord sz x)~0)%word = natToWord (S sz) (2 * x).
Proof.
  word_lia_Z.
Qed.

Theorem WS_neq : forall b1 b2 sz (w1 w2 : word sz),
  (b1 <> b2 \/ w1 <> w2)
  -> WS b1 w1 <> WS b2 w2.
Proof.
  intros; intro E; apply (f_equal (@Zmod.unsigned _)) in E; rewrite !unsigned_WS in E.
  destruct H as [H|H]; [ | apply H; apply unsigned_inj ]; destruct b1, b2; cbn [Z.b2z] in E; try congruence; lia.
Qed.

Theorem weqb_true_iff : forall sz x y,
  @weqb sz x y = true <-> x = y.
Proof.
  intros; cbv [weqb]; destruct (Zmod.eqb_spec x y); intuition congruence.
Qed.

Ltac shatterer := simpl; intuition;
  match goal with
    | [ w : _ |- _ ] => rewrite (shatter_word w); simpl
  end; f_equal; auto.

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

Theorem split1_iter : forall n1 n2 n3 Heq w,
  split1 n1 n2 (split1 (n1 + n2) n3 w)
  = split1 n1 (n2 + n3) (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
Proof.
  word_to_Z. apply Z.mod_mod_divide. exists (2 ^ Z.of_nat n2)%Z; lia.
Qed.

Theorem split2_iter : forall n1 n2 n3 Heq w,
  split2 n2 n3 (split2 n1 (n2 + n3) w)
  = split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
Proof.
  word_to_Z. rewrite Z.div_div by lia. reflexivity.
Qed.

Theorem split1_split2 : forall n1 n2 n3 Heq w,
  split1 n2 n3 (split2 n1 (n2 + n3) w) =
  split2 n1 n2 (split1 (n1 + n2) n3 (match Heq in _ = N return word N with
                                       | refl_equal => w
                                     end)).
Proof.
  word_to_Z. rewrite Zmod_mul_div by lia. reflexivity.
Qed.

Theorem split2_split1 : forall n1 n2 n3 Heq w,
  split2 n1 n2 (split1 (n1+n2) n3 w) =
  split1 n2 n3 (split2 n1 (n2+n3) (match Heq in _ = N return word N with
                                     | refl_equal => w
                                   end)).
Proof.
  word_to_Z. rewrite Zmod_mul_div by lia. reflexivity.
Qed.

Theorem combine_0_n : forall sz2 (w: word 0) (v: word sz2),
  combine w v = v.
Proof.
  word_lia_Z.
Qed.

Lemma WS_eq_rect : forall b n (w: word n) n' H H',
  eq_rect _ word (@WS b n w) _ H = @WS b n' (eq_rect _ word w _ H').
Proof.
  word_lia_Z.
Qed.

Theorem combine_eq_rect2 : forall sz n n'
  (H: n = n') H'
  (a: word sz) (b: word n),
  combine a b =
    eq_rect _ word (combine a (eq_rect _ word b _ H)) _ H'.
Proof.
  word_lia_Z.
Qed.

Theorem combine_n_0 : forall sz1 (w : word sz1) (v : word 0),
  combine w v = eq_rect _ word w _ (plus_n_O sz1).
Proof.
  word_lia_Z.
Qed.

Lemma whd_eq_rect : forall n w Heq,
  whd (eq_rect (S n) word w (S (n + 0)) Heq) =
  whd w.
Proof.
  intros; rewrite !whd_eqn, unsigned_eq_rect; reflexivity.
Qed.

Lemma wtl_eq_rect : forall n w Heq Heq',
  wtl (eq_rect (S n) word w (S (n + 0)) Heq) =
  eq_rect n word (wtl w) (n + 0) Heq'.
Proof.
  word_lia_Z.
Qed.

Lemma whd_eq_rect_mul : forall n w Heq,
  whd (eq_rect (S n) word w (S (n * 1)) Heq) =
  whd w.
Proof.
  intros; rewrite !whd_eqn, unsigned_eq_rect; reflexivity.
Qed.

Lemma wtl_eq_rect_mul : forall n w b Heq Heq',
  wtl (eq_rect (S n) word (WS b w) (S (n * 1)) Heq) =
  eq_rect _ word w _ Heq'.
Proof.
  word_to_Z; Z.div_mod_to_equations; nia.
Qed.

Theorem split1_0 : forall n w Heq,
  split1 n 0 (eq_rect _ word w _ Heq) = w.
Proof.
  word_to_Z. apply Z.mod_small; lia.
Qed.

Theorem split2_0 : forall n w Heq,
  split2 0 n (eq_rect _ word w _ Heq) = w.
Proof.
  word_to_Z. cbn. apply Z.div_1_r.
Qed.

Theorem combine_end : forall n1 n2 n3 Heq w,
  combine (split1 n2 n3 (split2 n1 (n2 + n3) w))
  (split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                          | refl_equal => w
                        end))
  = split2 n1 (n2 + n3) w.
Proof.
  word_to_Z. apply Zdiv_mod_mul_recompose; lia.
Qed.

Lemma Private_plus_reg_l : forall n m p, p + n = p + m -> n = m.
Proof. lia. Qed.

Theorem eq_rect_combine : forall n1 n2 n2' (w1 : word n1) (w2 : word n2') Heq,
  eq_rect (n1 + n2') (fun n => word n)
    (combine w1 w2) (n1 + n2) Heq =
  combine w1 (eq_rect n2' (fun n => word n) w2 n2 (Private_plus_reg_l _ _ _ Heq)).
Proof.
  word_lia_Z.
Qed.

Lemma eq_rect_combine_assoc' : forall a b c H wa wb wc,
  eq_rect (a + (b + c)) word (combine wa (combine wb wc)) _ H = combine (combine wa wb) wc.
Proof.
  word_lia_Z.
Qed.

Lemma eq_rect_split2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; lia.
Qed.

Theorem eq_rect_split2 : forall n1 n2 n2' (w : word (n1 + n2')) Heq,
  eq_rect n2' (fun n => word n)
    (split2 n1 n2' w) n2 Heq =
  split2 n1 n2 (eq_rect (n1+n2') (fun n => word n) w (n1+n2) (eq_rect_split2_helper _ Heq)).
Proof.
  word_lia_Z.
Qed.

Theorem eq_rect_split2_eq2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq Heq2,
  eq_rect n2 (fun n => word n)
    (split2 n1 n2 w) n2' Heq =
  split2 n1 n2' (eq_rect (n1+n2) (fun n => word n) w (n1+n2') Heq2).
Proof.
  word_lia_Z.
Qed.

Theorem eq_rect_split2_eq1 : forall n1 n1' n2 (w: word (n1 + n2)) Heq,
  split2 n1 n2 w = split2 n1' n2
    (eq_rect (n1 + n2) (fun y : nat => word y) w
    (n1' + n2) Heq).
Proof.
  intros; assert (n1 = n1') by lia; subst; word_lia_Z.
Qed.

Theorem combine_split_eq_rect2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq,
  combine (split1 n1 n2 w)
          (eq_rect n2 (fun n => word n) (split2 n1 n2 w)
                   n2' Heq) =
  eq_rect (n1 + n2) (fun n => word n) w
          (n1 + n2') (eq_rect_split2_helper _ Heq).
Proof.
  word_to_Z; Z.div_mod_to_equations; nia.
Qed.

Lemma eq_rect_split1_helper : forall a b c,
  a = b -> a + c = b + c.
Proof.
  intros; lia.
Qed.

Lemma eq_rect_split1_eq2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; lia.
Qed.

Theorem eq_rect_split1 : forall n1 n1' n2 (w : word (n1' + n2)) Heq,
  eq_rect n1' (fun n => word n)
    (split1 n1' n2 w) n1 Heq =
  split1 n1 n2 (eq_rect (n1'+n2) (fun n => word n) w (n1+n2) (eq_rect_split1_helper _ Heq)).
Proof.
  intros; subst; word_lia_Z.
Qed.

Theorem eq_rect_split1_eq1 : forall n1 n1' n2 (w : word (n1 + n2)) Heq Heq1,
  eq_rect n1 (fun n => word n)
    (split1 n1 n2 w) n1' Heq =
  split1 n1' n2 (eq_rect (n1+n2) (fun n => word n) w (n1'+n2) Heq1).
Proof.
  intros; subst; word_lia_Z.
Qed.

Lemma split1_eq_rect_eq1_helper : forall a b c, b = a -> a + c = b + c.
Proof. intros. subst. reflexivity. Qed.

Theorem split1_eq_rect_eq1 : forall a a' b H w,
  split1 a b w = eq_rect _ word (split1 a' b
    (eq_rect _ word w _ (split1_eq_rect_eq1_helper b H))) _ H.
Proof.
  intros; subst; word_lia_Z.
Qed.

Theorem eq_rect_split1_eq2 : forall n1 n2 n2' (w: word (n1 + n2)) Heq,
  split1 n1 n2 w = split1 n1 n2'
    (eq_rect (n1 + n2) (fun y : nat => word y) w
    (n1 + n2') Heq).
Proof.
  word_lia_Z.
Qed.

Fact eq_rect_combine_dist_helper1 : forall a b c d, b * c = d -> (a + b) * c = a * c + d.
Proof. intros; subst; apply Nat.mul_add_distr_r. Qed.

Fact eq_rect_combine_dist_helper2 : forall a b c d, b * c = d -> a * c + d = (a + b) * c.
Proof. intros; subst; symmetry; apply Nat.mul_add_distr_r. Qed.

Theorem eq_rect_combine_dist : forall a b c d (w : word ((a + b) * c)) (H : b * c = d),
  b * c = d ->
  let H1 := (eq_rect_combine_dist_helper1 a b c H) in
  let H2 := (eq_rect_combine_dist_helper2 a b c H) in
  let w' := eq_rec ((a + b) * c) word w _ H1 in
  w = eq_rec _ word (combine (split1 (a * c) d w') (split2 (a * c) d w')) _ H2.
Proof.
  word_to_Z. Z.div_mod_to_equations. nia.
Qed.

Lemma wzero_dist : forall a b c H,
  wzero ((a + b) * c) = eq_rect _ word (wzero (a * c + b * c)) _ H.
Proof.
  word_lia_Z.
Qed.

Lemma wzero_rev : forall (a b : nat) H,
   wzero (a + b) = eq_rect _ word (wzero (b + a)) _ H.
Proof.
  word_lia_Z.
Qed.

Lemma split1_zero : forall sz1 sz2, split1 sz1 sz2 (natToWord _ O) = natToWord _ O.
Proof.
  word_lia_Z.
Qed.

Lemma split2_zero : forall sz1 sz2, split2 sz1 sz2 (natToWord _ O) = natToWord _ O.
Proof.
  word_lia_Z.
Qed.

Theorem combine_inj : forall sz1 sz2 a b c d,
  @combine sz1 a sz2 b = @combine sz1 c sz2 d -> a = c /\ b = d.
Proof.
  intros; split; word_to_Z;
    match goal with H : _ = _ |- _ => apply Zcombine_inj in H; [ | lia | lia | lia ] end;
    intuition lia.
Qed.

Theorem combine_wzero : forall sz1 sz2, combine (wzero sz1) (wzero sz2) = wzero (sz1 + sz2).
Proof.
  word_lia_Z.
Qed.

Theorem combine_wones : forall sz1 sz2, combine (wones sz1) (wones sz2) = wones (sz1 + sz2).
Proof.
  word_lia_Z.
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

Theorem mod2_S : forall n k,
  2 * k = S n
  -> mod2 n = true.
Proof.
  induction n using strong; intros.
  destruct n; simpl in *.
  exfalso; lia.
  destruct n; simpl in *; auto.
  destruct k; simpl in *.
  discriminate.
  apply H with k; auto.
Qed.

Theorem wzero'_def : forall sz, wzero' sz = wzero sz.
Proof.
  word_lia_Z.
Qed.

Theorem posToWord_nat : forall p sz, posToWord sz p = natToWord sz (nat_of_P p).
Proof.
  word_lia_Z.
Qed.

Lemma posToWord_sz0: forall p, posToWord 0 p = $0.
Proof.
  intros; apply word0.
Qed.

Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).
Proof.
  word_lia_Z.
Qed.

Theorem wplus_alt : forall sz (x y : word sz), wplus x y = wplusN x y.
Proof.
  intros; cbv [wplusN wordBinN]; word_lia_Z.
Qed.

Theorem wmult_alt : forall sz (x y : word sz), wmult x y = wmultN x y.
Proof.
  intros; cbv [wmultN wordBinN]; word_lia_Z.
Qed.

Theorem wneg_alt : forall sz (x : word sz), wneg x = wnegN x.
Proof.
  intros; cbv [wnegN]; word_to_Z. rewrite Zmod_opp_sub by lia. f_equal; lia.
Qed.

Theorem wminus_Alt : forall sz (x y : word sz), wminus x y = wminusN x y.
Proof.
  intros; cbv [wminusN wplusN wordBinN wnegN]; word_to_Z.
  word_mod_simpl. rewrite Zplus_pminus_mod by lia. reflexivity.
Qed.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.
Proof.
  word_lia_Z.
Qed.

Theorem wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.
Proof.
  word_to_Z; f_equal; lia.
Qed.

Theorem drop_sub :
  forall sz n k,
    (k * pow2 sz <= n)%nat ->
    natToWord sz (n - k * pow2 sz) = natToWord sz n.
Proof.
  word_to_Z. rewrite Zminus_mul_mod by lia. reflexivity.
Qed.

Local Hint Extern 1 (_ <= _)%nat => lia.

Theorem wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.
Proof.
  word_to_Z. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal; lia.
Qed.

Theorem roundTrip_1 : forall sz, wordToNat (natToWord (S sz) 1) = 1.
Proof.
  word_to_Z. pose proof (pow2_pos_Z sz). rewrite Z.mod_small; lia.
Qed.

Theorem roundTrip_1': forall sz, sz <> 0 -> wordToNat (natToWord sz 1) = 1.
Proof.
  intros; destruct sz; [congruence|]; apply roundTrip_1.
Qed.

Lemma wordToNat_WS : forall sz (x : word sz) b,
    wordToNat (WS b x) = if b then S (2 * wordToNat x) else 2 * wordToNat x.
Proof.
  intros; destruct b; word_lia_Z.
Qed.

Theorem mod2_WS : forall sz (x : word sz) b, mod2 (wordToNat (WS b x)) = b.
Proof.
  intros; rewrite wordToNat_WS; destruct b; auto.
Qed.

Theorem div2_WS : forall sz (x : word sz) b, Nat.div2 (wordToNat (WS b x)) = wordToNat x.
Proof.
  intros; rewrite wordToNat_WS; destruct b; autorewrite with div2; auto.
Qed.

Theorem wmult_unit : forall sz (x : word sz), natToWord sz 1 ^* x = x.
Proof.
  word_lia_Z.
Qed.

Theorem wmult_comm : forall sz (x y : word sz), x ^* y = y ^* x.
Proof.
  word_to_Z; f_equal; lia.
Qed.

Theorem wmult_unit_r : forall sz (x : word sz), x ^* natToWord sz 1 = x.
Proof.
  intros; rewrite wmult_comm; apply wmult_unit.
Qed.

Lemma wmult_neut_l: forall (sz : nat) (x : word sz), $0 ^* x = $0.
Proof.
  word_lia_Z.
Qed.

Lemma wmult_neut_r: forall (sz : nat) (x : word sz), x ^* $0 = $0.
Proof.
  word_lia_Z.
Qed.

Theorem wmult_assoc : forall sz (x y z : word sz), x ^* (y ^* z) = x ^* y ^* z.
Proof.
  word_to_Z. word_mod_simpl. f_equal; lia.
Qed.

Theorem wmult_plus_distr : forall sz (x y z : word sz), (x ^+ y) ^* z = (x ^* z) ^+ (y ^* z).
Proof.
  word_to_Z. word_mod_simpl. f_equal; lia.
Qed.

Theorem wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
Proof.
  word_lia_Z.
Qed.

Theorem wordToNat_bound : forall sz (w : word sz), (wordToNat w < pow2 sz)%nat.
Proof.
  word_lia_Z.
Qed.

Theorem natToWord_pow2 : forall sz, natToWord sz (pow2 sz) = natToWord sz 0.
Proof.
  word_lia_Z.
Qed.

Theorem wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.
Proof.
  word_lia_Z.
Qed.

Lemma wminus_diag: forall sz (w: word sz),
  w ^- w = $0.
Proof.
  word_lia_Z.
Qed.

Lemma wneg_0_wminus: forall {sz: nat} (x: word sz),
  ^~ x = $0 ^- x.
Proof.
  word_lia_Z.
Qed.

Definition wring (sz : nat) : ring_theory (wzero sz) (wone sz) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) (@eq _) :=
  mk_rt _ _ _ _ _ _ _
  (@wplus_unit _) (@wplus_comm _) (@wplus_assoc _)
  (@wmult_unit _) (@wmult_comm _) (@wmult_assoc _)
  (@wmult_plus_distr _) (@wminus_def _) (@wminus_inv _).

Theorem weqb_sound : forall sz (x y : word sz), weqb x y = true -> x = y.
Proof.
  intros; apply weqb_true_iff; assumption.
Qed.

Arguments weqb_sound : clear implicits.

Lemma weqb_eq: forall sz (a b: word sz), a = b -> weqb a b = true.
Proof. intros; apply weqb_true_iff; assumption. Qed.

Lemma weqb_ne: forall sz (a b: word sz), a <> b -> weqb a b = false.
Proof.
  intros; destruct (weqb a b) eqn:E; [exfalso; apply H; apply weqb_true_iff; assumption | reflexivity].
Qed.

Lemma weqb_false: forall sz (a b: word sz), weqb a b = false -> a <> b.
Proof.
  intros; intro; subst; rewrite (weqb_eq (eq_refl _)) in H; discriminate.
Qed.

Ltac is_nat_cst n :=
  match eval hnf in n with
    | O => constr:(true)
    | S ?n' => is_nat_cst n'
    | _ => constr:(false)
  end.

(** Constant recognition for [ring] on words: a term built from [WO], [WS]
    with literal bits, or [natToWord] of a literal.  (No [hnf] on the word
    itself: the former constructors are now ordinary definitions.) *)
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

Definition wring8 := wring 8.
Add Ring wring8 : wring8 (decidable (weqb_sound 8), constants [wcst]).

(* Here's how you can add a ring for a specific bit-width.
   There doesn't seem to be a polymorphic method, so this code really does need to be copied. *)

(*
Definition wring8 := wring 8.
Add Ring wring8 : wring8 (decidable (weqb_sound 8), constants [wcst]).
*)

Ltac noptac x := idtac.

Ltac PackWring sz F :=
  let RNG := (fun proj => proj
    inv_morph_nothing inv_morph_nothing noptac noptac
    (word sz) (@eq (word sz)) (wzero sz) (wone sz)
    (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz)
    (BinNums.Z) (BinNums.N) (id_phi_N)
    (pow_N (wone sz) (@wmult sz))
    (ring_correct (@Eqsth (word sz))
                  (Eq_ext _ _ _)
                  (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                  (pow_N_th _ _ (@Eqsth (word sz)))
                  (triv_div_th (@Eqsth (word sz))
                               (Eq_ext _ _ _)
                               (Rth_ARth (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz))
                               (gen_phiZ_morph (@Eqsth (word sz)) (Eq_ext _ _ _) (wring sz)))
    )
    tt) in
  F RNG (@nil (word sz)) (@nil (word sz)).

Ltac ring_sz sz := PackWring sz Ring_gen.

(** * Bitwise operators: reasoning bit by bit *)

Local Open Scope Z_scope.

Lemma testbit_unsigned_high : forall sz (w : word sz) i,
    Z.of_nat sz <= i -> Z.testbit (unsigned w) i = false.
Proof.
  intros; apply bits.testbit_high; lia.
Qed.
Arguments testbit_unsigned_high {_} _ _ _.

Lemma testbit_pow2m1 : forall sz i, 0 <= i -> Z.testbit (2 ^ Z.of_nat sz - 1) i = (i <? Z.of_nat sz).
Proof.
  intros. replace (2 ^ Z.of_nat sz - 1) with (Z.ones (Z.of_nat sz)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.testbit_ones by lia. destruct (Z.leb_spec 0 i); [reflexivity | lia].
Qed.

Lemma testbit_combine_Z : forall k a b i, 0 <= a < 2 ^ k -> 0 <= b -> 0 <= k -> 0 <= i ->
    Z.testbit (a + 2 ^ k * b) i = if i <? k then Z.testbit a i else Z.testbit b (i - k).
Proof.
  intros. destruct (Z.ltb_spec i k).
  - rewrite <- (Z.mod_pow2_bits_low (a + 2 ^ k * b) k i) by assumption.
    rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia. reflexivity.
  - replace i with (i - k + k) at 1 by lia.
    rewrite <- (Z.div_pow2_bits (a + 2 ^ k * b) k (i - k)) by lia.
    rewrite Z.mul_comm, Z.div_add, Z.div_small by lia.
    f_equal; lia.
Qed.

Lemma testbit_WS_Z : forall b u i, 0 <= i ->
    Z.testbit (Z.b2z b + 2 * u) i = if i =? 0 then b else Z.testbit u (i - 1).
Proof.
  intros. destruct (Z.eqb_spec i 0).
  - subst. destruct b; cbn [Z.b2z].
    + replace (1 + 2 * u) with (2 * u + 1) by lia. apply Z.testbit_odd_0.
    + replace (0 + 2 * u) with (2 * u) by lia. apply Z.testbit_even_0.
  - cbv iota. rewrite !Z.testbit_eqb by lia.
    replace (2 ^ i) with (2 * 2 ^ (i - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    rewrite <- Z.div_div by lia.
    replace ((Z.b2z b + 2 * u) / 2) with u by (destruct b; cbn [Z.b2z]; Z.div_mod_to_equations; lia).
    reflexivity.
Qed.

Lemma testbit_div2 : forall u i, 0 <= i -> Z.testbit (u / 2) i = Z.testbit u (i + 1).
Proof.
  intros. rewrite <- (Z.pow_1_r 2) at 1. apply Z.div_pow2_bits; lia.
Qed.

Lemma bitwp_0 : forall f (w1 w2 : word 0), bitwp f w1 w2 = WO.
Proof. reflexivity. Qed.

Lemma bitwp_S : forall f sz (w1 w2 : word (S sz)),
    bitwp f w1 w2 = WS (f (whd w1) (whd w2)) (bitwp f (wtl w1) (wtl w2)).
Proof. reflexivity. Qed.

Lemma testbit_bitwp : forall f sz (w1 w2 : word sz) i, 0 <= i ->
    Z.testbit (unsigned (bitwp f w1 w2)) i =
    ((i <? Z.of_nat sz) && f (Z.testbit (unsigned w1) i) (Z.testbit (unsigned w2) i))%bool.
Proof.
  induction sz; intros.
  - rewrite bitwp_0, unsigned_WO, Z.bits_0. destruct (Z.ltb_spec i (Z.of_nat 0)); [cbn in *; lia | reflexivity].
  - rewrite bitwp_S, unsigned_WS, testbit_WS_Z by lia.
    destruct (Z.eqb_spec i 0).
    + subst. rewrite !whd_eqn, <- !Z.bit0_odd.
      destruct (Z.ltb_spec 0 (Z.of_nat (S sz))); [reflexivity | lia].
    + rewrite IHsz by lia. rewrite !unsigned_wtl, !testbit_div2 by lia.
      replace (i - 1 + 1) with i by lia.
      destruct (Z.ltb_spec (i - 1) (Z.of_nat sz)); destruct (Z.ltb_spec i (Z.of_nat (S sz))); try lia; reflexivity.
Qed.

Lemma unsigned_wnot_ldiff : forall sz (w : word sz),
    unsigned (wnot w) = Z.ldiff (2 ^ Z.of_nat sz - 1) (unsigned w).
Proof.
  intros; cbv [wnot]; rewrite bits.unsigned_not, Z.ones_equiv; f_equal; lia.
Qed.

Lemma unsigned_wone_S : forall sz, unsigned (wone (S sz)) = 1.
Proof.
  intros; rewrite unsigned_wone, pow2_S_Z; pose proof (pow2_pos_Z sz); apply Z.mod_small; lia.
Qed.

Lemma testbit_1 : forall i, 0 <= i -> Z.testbit 1 i = (i =? 0).
Proof.
  intros. destruct (Z.eqb_spec i 0); [subst; reflexivity|].
  apply Z.bits_above_log2; [lia | cbn; lia].
Qed.

(** Prove an equality of words bit by bit. *)
Ltac word_bits_side :=
  repeat split;
  first [ lia | apply unsigned_range
        | solve [ match goal with
                  | |- context [@Zmod.unsigned _ ?w] => pose proof (unsigned_range w); lia
                  end ] ].

(** Structural operators first (their [testbit] rules need the arguments
    still in the form [unsigned w] for the range side conditions), then the
    bitwise operators. *)
Ltac word_bits_rewrites :=
  repeat first [ rewrite unsigned_split1 | rewrite unsigned_split2
               | rewrite unsigned_combine | rewrite testbit_combine_Z by word_bits_side
               | rewrite unsigned_WS | rewrite testbit_WS_Z by lia
               | rewrite unsigned_WO | rewrite unsigned_zext | rewrite unsigned_extz
               | rewrite unsigned_wlshift | rewrite unsigned_wrshift | rewrite unsigned_eq_rect
               | rewrite unsigned_eq_rec | rewrite unsigned_match_eq | rewrite unsigned_natToWord
               | rewrite testbit_bitwp by lia
               | rewrite unsigned_wones | rewrite unsigned_wzero
               | rewrite unsigned_wzero' | rewrite unsigned_wone_S
               | rewrite Z.testbit_mod_pow2 by lia | rewrite Z.div_pow2_bits by lia
               | rewrite Z.mul_pow2_bits by lia | rewrite Z.testbit_neg_r by lia
               | rewrite Z.bits_0
               | rewrite testbit_pow2m1 by lia | rewrite testbit_1 by lia
               | rewrite unsigned_wor | rewrite unsigned_wand | rewrite unsigned_wxor
               | rewrite unsigned_wnot_ldiff
               | rewrite Z.lor_spec | rewrite Z.land_spec | rewrite Z.lxor_spec
               | rewrite Z.ldiff_spec ].

Ltac word_bits :=
  intros;
  repeat match goal with x := _ |- _ => subst x end;
  apply unsigned_inj;
  apply Z.bits_inj'; let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  word_bits_rewrites.

(** After [word_bits]: split on the index tests and kill the high bits. *)
Ltac word_bits_split :=
  repeat match goal with
         | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
         | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
         end.

Ltac word_bits_cases :=
  word_bits_split; word_bits_rewrites; word_bits_split; word_bits_rewrites; word_bits_split;
  repeat match goal with
         | |- context [Z.testbit (@Zmod.unsigned _ ?w) ?j] =>
           rewrite (testbit_unsigned_high w j) by lia
         end;
  repeat match goal with
         | |- context [Z.testbit ?a ?b] => destruct (Z.testbit a b)
         end;
  repeat match goal with b : bool |- _ => destruct b end;
  cbn; try reflexivity; try lia.

Fact bitwp_wtl : forall sz (w w' : word (S sz)) op, bitwp op (wtl w) (wtl w') = wtl (bitwp op w w').
Proof.
  intros; rewrite bitwp_S; apply unsigned_inj; rewrite unsigned_wtl, unsigned_WS.
  destruct (op (whd w) (whd w')); cbn [Z.b2z]; Z.div_mod_to_equations; lia.
Qed.

Lemma split1_bitwp_dist : forall sz1 sz2 w w' op,
  split1 sz1 sz2 (bitwp op w w') = bitwp op (split1 sz1 sz2 w) (split1 sz1 sz2 w').
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma split2_bitwp_dist : forall sz1 sz2 w w' op,
  split2 sz1 sz2 (bitwp op w w') = bitwp op (split2 sz1 sz2 w) (split2 sz1 sz2 w').
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma combine_bitwp : forall sz1 sz2 (wa wa' : word sz1) (wb wb' : word sz2) op,
  combine (bitwp op wa wa') (bitwp op wb wb') = bitwp op (combine wa wb) (combine wa' wb').
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma eq_rect_bitwp : forall a b Heq f w1 w2,
  bitwp f w1 w2 = eq_rect a word (
    bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq)) b (eq_sym Heq).
Proof.
  intros; subst; reflexivity.
Qed.

Fact eq_rect_bitwp' : forall a b Heq f w1 w2,
  eq_rect b word (bitwp f w1 w2) a Heq = bitwp f (eq_rect b word w1 a Heq) (eq_rect b word w2 a Heq).
Proof.
  intros; subst; reflexivity.
Qed.

Fact eq_rect_bitwp_1 : forall a b Heq f w1 w2,
  bitwp f (eq_rect a word w1 b Heq) w2 = eq_rect a word (bitwp f w1 (eq_rect b word w2 a (eq_sym Heq))) b Heq.
Proof.
  intros; subst; reflexivity.
Qed.

Theorem wnot_wnot'_equiv : forall sz (w : word sz), wnot w = wnot' w.
Proof.
  intros; cbv [wnot']; word_bits; word_bits_cases.
Qed.

Theorem wnot_split1 : forall sz1 sz2 w, wnot (split1 sz1 sz2 w) = split1 sz1 sz2 (wnot w).
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wnot_split2 : forall sz1 sz2 w, wnot (split2 sz1 sz2 w) = split2 sz1 sz2 (wnot w).
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wnot_combine : forall sz1 sz2 (w1 : word sz1) (w2 : word sz2),
  wnot (combine w1 w2) = combine (wnot w1) (wnot w2).
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wnot_zero: forall sz, wnot (wzero sz) = wones sz.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wnot_ones : forall sz, wnot (wones sz) = wzero sz.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wnot_eq_rect : forall a b H (w : word a), wnot (eq_rect a word w b H) = eq_rect a word (wnot w) b H.
Proof.
  intros; subst; reflexivity.
Qed.

Theorem wor_unit : forall sz (x : word sz), wzero sz ^| x = x.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wor_comm : forall sz (x y : word sz), x ^| y = y ^| x.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wor_assoc : forall sz (x y z : word sz), x ^| (y ^| z) = x ^| y ^| z.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wand_unit : forall sz (x : word sz), wones sz ^& x = x.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wand_kill : forall sz (x : word sz), wzero sz ^& x = wzero sz.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wand_comm : forall sz (x y : word sz), x ^& y = y ^& x.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wand_assoc : forall sz (x y z : word sz), x ^& (y ^& z) = x ^& y ^& z.
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wand_or_distr : forall sz (x y z : word sz), (x ^| y) ^& z = (x ^& z) ^| (y ^& z).
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wor_wones : forall sz w, wones sz ^| w = wones sz.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wor_wzero : forall sz w, wzero sz ^| w = w.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wand_wones : forall sz w, wones sz ^& w = w.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wand_wzero : forall sz w, wzero sz ^& w = wzero sz.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wxor_wones : forall sz w, wxor (wones sz) w = wnot w.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wxor_wzero : forall sz w, wxor (wzero sz) w = w.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wxor_comm : forall sz (w1 w2 : word sz), wxor w1 w2 = wxor w2 w1.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wxor_assoc : forall sz (w1 w2 w3 : word sz), wxor w1 (wxor w2 w3) = wxor (wxor w1 w2) w3.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wor_wone : forall sz (w : word sz) b,
  WS b w ^| wone _ = WS true w.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wand_wone : forall sz (w : word sz) b,
  WS b w ^& wone _ = WS b (wzero _).
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma wxor_wone : forall sz (w : word sz) b,
  wxor (WS b w) (wone _) = WS (negb b) w.
Proof.
  word_bits; word_bits_cases.
Qed.

Local Close Scope Z_scope.

Definition wbring (sz : nat) : semi_ring_theory (wzero sz) (wones sz) (@wor sz) (@wand sz) (@eq _) :=
  mk_srt _ _ _ _ _
  (@wor_unit _) (@wor_comm _) (@wor_assoc _)
  (@wand_unit _) (@wand_kill _) (@wand_comm _) (@wand_assoc _)
  (@wand_or_distr _).

(** * Inequality proofs *)

Ltac word_simpl := unfold sext, zext, wzero in *; simpl in *.

Ltac word_eq := ring.

Ltac word_eq1 := match goal with
                   | _ => ring
                   | [ H : _ = _ |- _ ] => ring [H]
                 end.

Theorem word_neq : forall sz (w1 w2 : word sz),
  w1 ^- w2 <> wzero sz
  -> w1 <> w2.
Proof.
  word_lia_Z.
Qed.

Ltac word_neq := apply word_neq; let H := fresh "H" in intro H; simpl in H; ring_simplify in H; try discriminate.

Ltac word_contra := match goal with
                      | [ H : _ <> _ |- False ] => apply H; ring
                    end.

Ltac word_contra1 := match goal with
                       | [ H : _ <> _ |- False ] => apply H;
                         match goal with
                           | _ => ring
                           | [ H' : _ = _ |- _ ] => ring [H']
                         end
                     end.

Lemma not_wlt_ge : forall sz (l r : word sz),
  ((l < r) -> False) -> (r <= l).
Proof.
  word_lia_Z.
Qed.

Lemma not_wle_gt : forall sz (l r : word sz),
  ((l <= r) -> False) -> (r < l).
Proof.
  word_lia_Z.
Qed.

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

Lemma unique_inverse : forall sz (a b1 b2 : word sz),
  a ^+ b1 = wzero _ ->
  a ^+ b2 = wzero _ ->
  b1 = b2.
Proof.
  intros; word_to_Z.
  match goal with H : ((?a + ?b1) mod ?p)%Z = ?z, H' : ((?a + ?b2) mod ?p)%Z = ?z |- _ =>
    rewrite <- H' in H; rewrite (Z.add_comm a b1), (Z.add_comm a b2) in H;
    apply Zadd_mod_cancel_r in H; lia
  end.
Qed.

Lemma sub_0_eq : forall sz (a b : word sz),
  a ^- b = wzero _ -> a = b.
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
    | word 0 => try rewrite (shatter_word_0 x) in *
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

(** With the inductive [word], [$0~1] and [$1] were definitionally equal;
    they are only propositionally equal now. *)
Lemma WS_true_natToWord_0 : forall sz, WS true (natToWord sz 0) = natToWord (S sz) 1.
Proof.
  word_lia_Z.
Qed.

Lemma WS_false_natToWord_0 : forall sz, WS false (natToWord sz 0) = natToWord (S sz) 0.
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

Lemma wordToNat_natToWord_idempotent : forall sz n,
  (N.of_nat n < Npow2 sz)%N
  -> wordToNat (natToWord sz n) = n.
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

Lemma wminus_wplus_undo: forall sz (a b: word sz),
  a ^- b ^+ b = a.
Proof.
  word_lia_Z.
Qed.

Lemma wneg_zero:
  forall {sz} (w: word sz), ^~ w = (natToWord sz 0) -> w = natToWord sz 0.
Proof.
  intros; word_to_Z.
  rewrite Zmod_opp_sub in H by lia.
  match goal with H : ((?p - ?a) mod ?p)%Z = _ |- _ =>
    destruct (Z.eq_dec a 0); [lia | rewrite Z.mod_small in H; lia] end.
Qed.

Lemma wneg_idempotent:
  forall {sz} (w: word sz), ^~ (^~ w) = w.
Proof.
  word_lia_Z.
Qed.

Lemma wneg_zero': forall sz,
  wneg (natToWord sz 0) = natToWord sz 0.
Proof.
  word_lia_Z.
Qed.

Lemma wplus_one_neq: forall {sz} (w: word (S sz)), w ^+ (natToWord (S sz) 1) <> w.
Proof.
  word_lia_Z.
Qed.

Lemma wneg_one_pow2_minus_one: forall {sz}, wordToNat (^~ (natToWord sz 1)) = pow2 sz - 1.
Proof.
  word_lia_Z.
Qed.

Lemma wones_pow2_minus_one: forall {sz}, wordToNat (wones sz) = pow2 sz - 1.
Proof.
  word_lia_Z.
Qed.

Lemma pow2_minus_one_wones: forall {sz} (w: word sz),
  wordToNat w = pow2 sz - 1 -> w = wones sz.
Proof.
  word_lia_Z.
Qed.

Lemma wones_natToWord: forall sz,
  wones sz = $ (pow2 sz - 1).
Proof.
  word_lia_Z.
Qed.

Lemma wones_wneg_one: forall {sz}, wones sz = ^~ (natToWord sz 1).
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_natToWord_pred:
  forall {sz} (w: word sz), w <> wzero sz ->
    pred (wordToNat w) =
    wordToNat (w ^- (natToWord sz 1)).
Proof.
  intros; destruct sz; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

Lemma natToWord_mult : forall sz n m, natToWord sz (n * m) = natToWord _ n ^* natToWord _ m.
Proof.
  word_lia_Z.
Qed.

Lemma wlt_lt: forall sz (a b : word sz), a < b ->
  (wordToNat a < wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma wle_le: forall sz (a b : word sz), (a <= b)%word ->
  (wordToNat a <= wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma wlt_lt': forall sz a b, (a < pow2 sz)%nat
  -> natToWord sz a < b
  -> (wordToNat (natToWord sz a) < wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma lt_word_lt_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n < (natToWord sz m))%word ->
  (wordToNat n < m)%nat.
Proof.
  word_to_Z. pose proof (Z.mod_le (Z.of_nat m) (2 ^ Z.of_nat sz) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma le_word_le_nat : forall (sz:nat) (n:word sz) (m:nat),
  (n <= (natToWord sz m))%word ->
  (wordToNat n <= m)%nat.
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

Lemma wordToNat_natToWord_idempotent' : forall sz n,
  (n < pow2 sz)%nat
  -> wordToNat (natToWord sz n) = n.
Proof.
  word_lia_Z.
Qed.

Lemma le_word_le_nat': forall (sz:nat) n m,
  (n < pow2 sz)%nat ->
  (natToWord sz n <= m)%word ->
  (n <= wordToNat m)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_natToWord_bound : forall sz n (bound : word sz),
  (n <= wordToNat bound)%nat
  -> wordToNat (natToWord sz n) = n.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_natToWord_le : forall sz n,
  (wordToNat (natToWord sz n) <= n)%nat.
Proof.
  word_to_Z. pose proof (Z.mod_le (Z.of_nat n) (2 ^ Z.of_nat sz) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma wordToNat_natToWord_lt : forall sz n b,
  (n < b -> wordToNat (natToWord sz n) < b)%nat.
Proof.
  intros; pose proof (wordToNat_natToWord_le sz n); lia.
Qed.

Lemma wordToNat_eq_natToWord : forall sz (w : word sz) n,
  wordToNat w = n
  -> w = natToWord sz n.
Proof.
  word_lia_Z.
Qed.

Lemma wlt_lt_bound: forall sz (a : word sz) (b bound : nat),
  (a < natToWord sz b)%word
  -> (b <= wordToNat (natToWord sz bound))%nat
  -> (wordToNat a < b)%nat.
Proof.
  intros; apply lt_word_lt_nat; assumption.
Qed.

Lemma natplus1_wordplus1_eq:
  forall sz (a bound : word sz),
    (0 < sz)%nat ->
    (a < bound)%word ->
    (wordToNat a) + 1 = wordToNat (a ^+ (natToWord sz 1)).
Proof.
  intros; destruct sz; [lia|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

Lemma lt_wlt: forall sz (n : word sz) m, (wordToNat n < wordToNat m)%nat ->
  n < m.
Proof.
  word_lia_Z.
Qed.

Lemma le_wle: forall sz (n : word sz) m, (wordToNat n <= wordToNat m)%nat ->
  n <= m.
Proof.
  word_lia_Z.
Qed.

Lemma wlt_wle_incl : forall sz (a b : word sz),
  (a < b)%word -> (a <= b)%word.
Proof.
  word_lia_Z.
Qed.

Lemma wminus_Alt2: forall sz x y, y <= x ->
  @wminusN sz x y = wordBinN minus x y.
Proof.
  intros; cbv [wminusN wplusN wnegN wordBinN]; word_to_Z.
  word_mod_simpl; try (rewrite Zplus_pminus_mod by lia); lia.
Qed.

Theorem wlt_wf:
  forall sz, well_founded (@wlt sz).
Proof.
  intros; apply (well_founded_lt_compat _ (@wordToNat sz)); intros; apply wlt_lt; assumption.
Qed.

Ltac wlt_ind :=
  match goal with
  | [ |- forall (n: word ?len), ?P ] =>
    refine (well_founded_ind (@wlt_wf len) (fun n => P) _)
  end.

Theorem wordToNat_plusone: forall sz w w', w < w' ->
  wordToNat (w ^+ natToWord sz 1) = S (wordToNat w).
Proof.
  intros; destruct sz; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

Theorem wordToNat_minus_one': forall sz n, n <> natToWord sz 0 ->
  S (wordToNat (n ^- natToWord sz 1)) = wordToNat n.
Proof.
  intros; destruct sz; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

Theorem wordToNat_minus_one: forall sz n, n <> natToWord sz 0 ->
  wordToNat (n ^- natToWord sz 1) = wordToNat n - 1.
Proof.
  intros; pose proof (wordToNat_minus_one' H); lia.
Qed.

Lemma lt_minus : forall a b c,
  (b <= a -> b < c -> a < c -> a - b < c)%nat.
Proof.
  intros; lia.
Qed.

Lemma wminus_minus : forall sz (a b : word sz),
  b <= a
  -> wordToNat (a ^- b) = wordToNat a - wordToNat b.
Proof.
  word_to_Z. try (rewrite Z.mod_small by lia). lia.
Qed.

Lemma wminus_minus': forall (sz : nat) (a b : word sz),
    (#b <= #a)%nat ->
    #(a ^- b) = #a - #b.
Proof.
  word_to_Z. try (rewrite Z.mod_small by lia). lia.
Qed.

Lemma wordToNat_neq_inj: forall sz (a b : word sz),
  a <> b <-> wordToNat a <> wordToNat b.
Proof.
  split; word_lia_Z.
Qed.

Lemma natToWord_discriminate: forall sz, (sz > 0)%nat -> natToWord sz 0 <> natToWord sz 1.
Proof.
  intros; destruct sz; [lia|]; word_lia_Z.
Qed.

Definition bit_dec : forall (a : word 1), {a = $0} + {a = $1}.
  intros.
  destruct (weq a $0); [left; assumption | right].
  abstract word_lia_Z.
Defined.

Lemma neq0_wneq0: forall sz (n : word sz),
  wordToNat n <> 0  <-> n <> $0.
Proof.
  split; word_lia_Z.
Qed.

Lemma gt0_wneq0: forall sz (n : word sz),
  (wordToNat n > 0)%nat <-> n <> $0.
Proof.
  split; word_lia_Z.
Qed.

Lemma weq_minus1_wlt: forall sz (a b : word sz),
  (a <> $0 -> a ^- $1 = b -> a > b)%word.
Proof.
  intros; destruct sz; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small in * by lia). lia.
Qed.

Lemma wordnat_minus1_eq : forall sz n (w : word sz),
  (n > 0)%nat
  -> n = wordToNat w
  -> n - 1 = wordToNat (w ^- $1).
Proof.
  intros; destruct sz; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

(** * Shifts, single bits, msb, extensions, [N] and [Z] round trips *)

Local Open Scope Z_scope.

Lemma wbit_testbit : forall sz sz' (n : word sz') i,
    (wordToNat n < sz)%nat -> 0 <= i ->
    Z.testbit (unsigned (wbit sz n)) i = (i =? Z.of_nat (wordToNat n)).
Proof.
  intros; cbv [wbit]; rewrite unsigned_natToWord, pow2_Z, Z.testbit_mod_pow2, Z.pow2_bits_eqb by lia.
  destruct (Z.ltb_spec i (Z.of_nat sz)); destruct (Z.eqb_spec i (Z.of_nat (wordToNat n))); cbn; try reflexivity; lia.
Qed.

Local Close Scope Z_scope.

Theorem wlshift_0 : forall sz (w : word sz), @wlshift sz w 0 = w.
Proof.
  word_lia_Z.
Qed.

Theorem wrshift_0 : forall sz (w : word sz), @wrshift sz w 0 = w.
Proof.
  word_lia_Z.
Qed.

Theorem wlshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wlshift w n = wzero sz.
Proof.
  word_to_Z. replace n with (sz + (n - sz)) by lia. rewrite pow2_add_Z.
  rewrite Z.mul_assoc, Z.mul_comm, Z.mul_assoc, Z.mod_mul by lia. reflexivity.
Qed.

Theorem wrshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wrshift w n = wzero sz.
Proof.
  word_to_Z. pose proof (Z.pow_le_mono_r 2 (Z.of_nat sz) (Z.of_nat n) ltac:(lia) ltac:(lia)).
  apply Z.div_small. lia.
Qed.

Theorem wlshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wlshift (bitwp f w1 w2) n = split1 sz n (
    eq_rec _ word (combine (wzero n) (bitwp f w1 w2)) _ (eq_sym (Nat.add_comm sz n))).
Proof.
  word_lia_Z.
Qed.

Theorem wrshift_bitwp : forall sz (w1 w2 : word sz) f n,
  wrshift (bitwp f w1 w2) n = split2 n sz (
    eq_rect _ word (combine (bitwp f w1 w2) (wzero n)) _ (eq_sym (Nat.add_comm n sz))).
Proof.
  word_lia_Z.
Qed.

Theorem wnot_wlshift : forall sz (w : word sz) n,
  wnot (wlshift w n) = split1 sz n (eq_rect _ word (combine (wones n) (wnot w)) _ (eq_sym (Nat.add_comm sz n))).
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem wnot_wrshift : forall sz (w : word sz) n,
  wnot (wrshift w n) = split2 n sz (eq_rect _ word (combine (wnot w) (wones n)) _ (eq_sym (Nat.add_comm n sz))).
Proof.
  word_bits; word_bits_cases.
Qed.

Theorem div2_pow2_twice: forall n,
  Nat.div2 (pow2 n + (pow2 n + 0)) = pow2 n.
Proof.
  intros. rewrite Nat.div2_div. lia.
Qed.

Theorem zero_or_wordToNat_S: forall sz (n : word sz),
  n = $0 \/
  exists nn, wordToNat n = S nn /\ wordToNat (n ^- $1) = nn.
Proof.
  intros; destruct (weq n $0); [left; assumption | right].
  exists (wordToNat n - 1). destruct sz; [word_lia_Z|].
  split; [word_lia_Z|].
  word_to_Z. word_mod_simpl. try (rewrite Z.mod_small by lia). lia.
Qed.

Theorem wbit_or_same : forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^| (wbit sz n) <> wzero sz.
Proof.
  intros; intro E; apply (f_equal (fun x => Z.testbit (unsigned x) (Z.of_nat (wordToNat n)))) in E.
  rewrite unsigned_wor, Z.lor_spec, !wbit_testbit, unsigned_wzero, Z.bits_0, Z.eqb_refl in E by lia.
  discriminate.
Qed.

Theorem wbit_or_other : forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> (n1 <> n2)
  -> (wbit sz n1) ^& (wbit sz n2) = wzero sz.
Proof.
  intros; apply unsigned_inj; apply Z.bits_inj'; intros i Hi.
  rewrite unsigned_wand, Z.land_spec, !wbit_testbit, unsigned_wzero, Z.bits_0 by lia.
  assert (wordToNat n1 <> wordToNat n2) by (intro; apply H1; apply wordToNat_inj; assumption).
  destruct (Z.eqb_spec i (Z.of_nat (wordToNat n1))); destruct (Z.eqb_spec i (Z.of_nat (wordToNat n2))); cbn; try reflexivity; lia.
Qed.

Theorem wbit_and_not: forall sz sz' (n : word sz'), (wordToNat n < sz)%nat
  -> (wbit sz n) ^& wnot (wbit sz n) = wzero sz.
Proof.
  intros; apply unsigned_inj; apply Z.bits_inj'; intros i Hi.
  rewrite unsigned_wand, Z.land_spec, unsigned_wnot_ldiff, Z.ldiff_spec, !wbit_testbit, unsigned_wzero, Z.bits_0, testbit_pow2m1 by lia.
  destruct (Z.eqb_spec i (Z.of_nat (wordToNat n))); destruct (Z.ltb_spec i (Z.of_nat sz)); cbn; try reflexivity; lia.
Qed.

Theorem wbit_and_not_other: forall sz sz' (n1 n2 : word sz'), (wordToNat n1 < sz)%nat
  -> (wordToNat n2 < sz)%nat
  -> n1 <> n2
  -> (wbit sz n1) ^& wnot (wbit sz n2) = wbit sz n1.
Proof.
  intros; apply unsigned_inj; apply Z.bits_inj'; intros i Hi.
  rewrite unsigned_wand, Z.land_spec, unsigned_wnot_ldiff, Z.ldiff_spec, !wbit_testbit, testbit_pow2m1 by lia.
  assert (wordToNat n1 <> wordToNat n2) by (intro; apply H1; apply wordToNat_inj; assumption).
  destruct (Z.eqb_spec i (Z.of_nat (wordToNat n1))); destruct (Z.eqb_spec i (Z.of_nat (wordToNat n2)));
    destruct (Z.ltb_spec i (Z.of_nat sz)); cbn; try reflexivity; lia.
Qed.

Lemma wordToNat_wzero:
  forall sz, wordToNat (wzero sz) = 0.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_wzero:
  forall sz, wordToN (wzero sz) = 0%N.
Proof.
  word_lia_Z.
Qed.

Lemma combine_zero:
  forall n m, combine (natToWord n 0) (natToWord m 0) = natToWord _ 0.
Proof.
  word_lia_Z.
Qed.

Lemma combine_one:
  forall n m, combine (natToWord (S n) 1) (natToWord m 0) = natToWord _ 1.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wzero':
  forall sz, wmsb (wzero' sz) false = false.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wzero:
  forall sz, wmsb (wzero sz) false = false.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wones:
  forall sz, wmsb (wones (S sz)) false = true.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_0: forall sz (m: word (S sz)) default,
  (# m < pow2 sz)%nat ->
  @wmsb (S sz) m default = false.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_1: forall sz (m: word (S sz)) default,
  pow2 sz <= # m < 2 * pow2 sz ->
  @wmsb (S sz) m default = true.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_0_natToWord: forall sz n default,
  (2 * n < pow2 (S sz))%nat ->
  @wmsb (S sz) (natToWord (S sz) n) default = false.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_1_natToWord: forall sz n default,
  pow2 sz <= n < 2 * pow2 sz ->
  @wmsb (S sz) (natToWord (S sz) n) default = true.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_wzero':
  forall sz, wordToN (wzero' sz) = 0%N.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_wzero':
  forall sz, wordToZ (wzero' sz) = 0%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_wzero:
  forall sz, wordToZ (wzero sz) = 0%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_existT: (* Note: not axiom free *)
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word _ w1 = existT word _ w2 ->
    forall b, wmsb w1 b = wmsb w2 b.
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma destruct_word_S: forall sz (w: word (S sz)),
  exists v b, w = WS b v.
Proof.
  intros; exists (wtl w), (whd w); apply (shatter_word w).
Qed.

Lemma induct_word_S: forall (P : forall n : nat, word (S n) -> Prop),
    (forall b, P 0 (WS b WO)) ->
    (forall b b0 n (w : word n), P n (WS b0 w) -> P (S n) (WS b (WS b0 w))) ->
    forall (n : nat) (w : word (S n)), P n w.
Proof.
  induction n; intros.
  - rewrite (shatter_word w); rewrite (shatter_word_0 (wtl w)); apply H.
  - rewrite (shatter_word w); rewrite (shatter_word (wtl w)); apply H0.
    rewrite <- (shatter_word (wtl w)); apply IHn.
Qed.

Lemma shatter_word_1 : forall (w : word 1), w = WS (whd w) WO.
Proof.
  intros; rewrite (shatter_word w) at 1; f_equal; apply shatter_word_0.
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

Lemma wordToZ_one : forall (w : word 1), wordToZ w = (if whd w then -1 else 0)%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_succ : forall sz (w : word (S (S sz))),
    wordToZ w = (2 * wordToZ (wtl w) + (if whd w then 1 else 0))%Z.
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

(** [word] is no longer an inductive type, but it still has the eliminator
    of the old two-constructor definition; [induction w using word_rect]
    replaces [dependent induction w]. *)
Fixpoint word_rect (P : forall n, word n -> Type)
  (HO : P 0 WO)
  (HS : forall (b : bool) (n : nat) (w : word n), P n w -> P (S n) (WS b w))
  (n : nat) {struct n} : forall w : word n, P n w :=
  match n return forall w : word n, P n w with
  | O => fun w => eq_rect_r (P 0) HO (word0 w)
  | S n' => fun w =>
      eq_rect_r (P (S n'))
                (HS (whd w) n' (wtl w) (word_rect P HO HS (wtl w)))
                (shatter_word w)
  end.

Definition word_ind (P : forall n, word n -> Prop) := word_rect P.
Definition word_rec (P : forall n, word n -> Set) := word_rect P.

(** [word_destruct w] replaces [dependent destruction w] on a [word (S _)]:
    it names the head bit [b] and reuses the name [w] for the tail. *)
Tactic Notation "word_destruct" ident(w) :=
  (try (intros until w));
  let b := fresh "b" in
  let v := fresh "v" in
  let Hv := fresh "Hv" in
  destruct (destruct_word_S w) as [v [b Hv]]; subst w; rename v into w.

Lemma wmsb_eq_rect:
  forall sz1 (w: word sz1) sz2 (Hsz: sz1 = sz2) b,
    wmsb w b = wmsb (eq_rect _ word w _ Hsz) b.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wmsb_ws:
  forall sz (w: word (S sz)) b a, wmsb (WS b w) a = wmsb w a.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_extz:
  forall sz (w: word sz) n,
    wmsb (extz w n) false = wmsb w false.
Proof.
  word_to_Z; try lia.
  all: try (exfalso; nia).
  all: try reflexivity.
Qed.

Lemma wmsb_default:
  forall sz (w: word sz) b1 b2,
    sz <> 0 -> wmsb w b1 = wmsb w b2.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_split2:
  forall sz (w: word (sz + 1)) b,
    wmsb w b = if weq (split2 _ 1 w) (natToWord _ 0) then false else true.
Proof.
  intros; destruct (weq (split2 sz 1 w) (natToWord 1 0)); word_lia_Z.
Qed.

Lemma wmsb_true_split2_wones:
  forall sz (w: word (sz + 1)) b,
    wmsb w b = true ->
    wones 1 = split2 sz 1 w.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_false_split2_wzero:
  forall sz (w: word (sz + 1)) b,
    wmsb w b = false ->
    wzero 1 = split2 sz 1 w.
Proof.
  word_lia_Z.
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

Lemma wmsb_combine_WO:
  forall sz (w: word sz) b,
    wmsb (combine w WO) b = wmsb w b.
Proof.
  word_lia_Z.
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
  apply unsigned_inj in H1; subst; apply wmsb_combine; assumption.
Qed.

Lemma wmsb_zext:
  forall sz (w: word sz) b n, n <> 0 -> wmsb (zext w n) b = false.
Proof.
  word_to_Z; try reflexivity; try lia; exfalso; nia.
Qed.

Lemma wordToN_zext:
  forall sz (w: word sz) n,
    wordToN (zext w n) = wordToN w.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_zext:
  forall sz (w: word sz) n,
    wordToNat (zext w n) = wordToNat w.
Proof.
  word_lia_Z.
Qed.

Lemma zext_wordToNat_equal_Z:
  forall sz (w: word sz) n,
    n <> 0 -> wordToZ (zext w n) = Z.of_nat (wordToNat w).
Proof.
  word_to_Z; try reflexivity; try lia; exfalso; nia.
Qed.

Lemma wordToN_WS_0:
  forall sz (w: word sz), wordToN w~0 = (2 * wordToN w)%N.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_WS_1:
  forall sz (w: word sz), wordToN w~1 = (2 * wordToN w + 1)%N.
Proof.
  word_lia_Z.
Qed.

Lemma NToWord_WS_0:
  forall sz n, NToWord (S sz) (2 * n) = (NToWord sz n)~0.
Proof.
  word_lia_Z.
Qed.

Lemma NToWord_WS_1:
  forall sz n, NToWord (S sz) (2 * n + 1) = (NToWord sz n)~1.
Proof.
  word_lia_Z.
Qed.

Lemma wneg_WS_0:
  forall sz (w: word sz), wneg w~0 = (wneg w)~0.
Proof.
  word_lia_Z.
Qed.

Lemma NToWord_wordToN:
  forall sz (w: word sz), NToWord sz (wordToN w) = w.
Proof.
  word_lia_Z.
Qed.

Lemma roundTripN_0:
  forall sz, wordToN (NToWord sz 0) = 0%N.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_NToWord:
  forall sz n,
  exists k, wordToN (NToWord sz n) = (n - k * Npow2 sz)%N /\ (k * Npow2 sz <= n)%N.
Proof.
  intros; exists (n / Npow2 sz)%N.
  word_lia_Z.
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

Lemma wordToN_plus: forall sz (a b: word sz),
    (wordToN a + wordToN b < Npow2 sz)%N ->
    wordToN (a ^+ b) = (wordToN a + wordToN b)%N.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_mult: forall sz (a b: word sz),
    (wordToN a * wordToN b < Npow2 sz)%N ->
    wordToN (a ^* b) = (wordToN a * wordToN b)%N.
Proof.
  word_lia_Z.
Qed.

Lemma wnot_def:
  forall sz (w: word sz), wnot w = NToWord sz (Npow2 sz - wordToN w - 1).
Proof.
  word_lia_Z.
Qed.

Lemma wneg_wnot:
  forall sz (w: word sz), wnot w = wneg w ^- (natToWord _ 1).
Proof.
  word_lia_Z.
Qed.

Lemma wzero_wneg:
  forall n, wneg (wzero n) = wzero n.
Proof.
  word_lia_Z.
Qed.

Lemma pow2_wneg:
  forall sz, wneg (natToWord (S sz) (pow2 sz)) = natToWord (S sz) (pow2 sz).
Proof.
  word_lia_Z.
Qed.

Lemma wneg_WS_1:
  forall sz (w: word sz), wneg w~1 = (wnot w)~1.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_WS_0:
  forall sz (w: word sz), wordToZ w~0 = (2 * wordToZ w)%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_WS_1:
  forall sz (w: word (S sz)), wordToZ w~1 = (2 * wordToZ w + 1)%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_WS_1':
  forall sz (w: word (sz + 1)), wordToZ w~1 = (2 * wordToZ w + 1)%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_inj:
  forall sz (w1 w2: word sz),
    wordToZ w1 = wordToZ w2 -> w1 = w2.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_wones:
  forall sz, sz <> 0 -> wordToZ (wones sz) = (-1)%Z.
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
  intros; apply existT_word_inv in H; destruct H; subst; apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma wordToZ_eq_rect:
  forall sz (w: word sz) nsz Hsz,
    wordToZ (eq_rect _ word w nsz Hsz) = wordToZ w.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wordToZ_existT:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) (Hsz: sz1 = sz2),
    wordToZ w1 = wordToZ w2 ->
    existT word _ w1 = existT word _ w2.
Proof.
  intros; subst; f_equal; apply wordToZ_inj; assumption.
Qed.

Lemma existT_wordToZ:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    existT word _ w1 = existT word _ w2 ->
    wordToZ w1 = wordToZ w2.
Proof.
  intros; apply existT_word_inv in H; destruct H; subst; apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma wplus_WS_0:
  forall sz (w1 w2: word sz) b, WS b (w1 ^+ w2) = WS b w1 ^+ w2~0.
Proof.
  word_lia_Z.
Qed.

Corollary wplus_WS_0':
  forall sz (w1 w2: word sz) b, WS b (w1 ^+ w2) = w1~0 ^+ WS b w2.
Proof.
  word_lia_Z.
Qed.

Lemma wpow2_pow2:
  forall sz, wordToNat (wpow2 sz) = pow2 sz.
Proof.
  word_lia_Z.
Qed.

Lemma wpow2_Npow2:
  forall sz, wordToN (wpow2 sz) = Npow2 sz.
Proof.
  word_lia_Z.
Qed.

Lemma wpow2_wneg:
  forall sz, wneg (wpow2 sz) = wpow2 sz.
Proof.
  word_lia_Z.
Qed.

Lemma wpow2_wmsb:
  forall sz, wmsb (wpow2 sz) false = true.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wnot:
  forall sz (w: word (S sz)) b1 b2,
    wmsb (wnot w) b1 = negb (wmsb w b2).
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wneg_true:
  forall sz (w: word (S sz)),
    w <> wpow2 sz ->
    forall b1 b2,
      wmsb w b1 = true ->
      wmsb (wneg w) b2 = false.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wneg_false:
  forall sz (w: word (S sz)),
    wordToNat w <> 0 ->
    forall b1 b2,
      wmsb w b1 = false ->
      wmsb (wneg w) b2 = true.
Proof.
  word_lia_Z.
Qed.

Lemma zext_WO_wzero:
  forall n, zext WO n = wzero n.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_wneg_zext:
  forall sz (w: word sz) b n,
    n <> 0 -> wordToNat w <> 0 ->
    wmsb (wneg (zext w n)) b = true.
Proof.
  word_to_Z; word_mod_simpl; try reflexivity; try lia; exfalso; nia.
Qed.

Lemma wminus_WS_pos:
  forall sz (w1 w2: word (S sz)),
    wordToZ (WS true w1 ^- WS false w2) =
    (2 * wordToZ (w1 ^- w2) + 1)%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z_lt_le_dec (z0 - z)%Z 0) as [Hs|Hs];
     [ rewrite (@Zmod_small_neg (z0 - z)%Z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia;
       rewrite (@Zmod_small_neg (1 + 2 * z0 - 2 * z)%Z
                                (2 * (2 * 2 ^ Z.of_nat sz))%Z) in * by lia
     | rewrite (Z.mod_small (z0 - z)%Z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia;
       rewrite (Z.mod_small (1 + 2 * z0 - 2 * z)%Z
                            (2 * (2 * 2 ^ Z.of_nat sz))%Z) in * by lia ]);
    lia.
Qed.

Lemma wminus_WS_pos':
  forall sz (w1 w2: word (sz + 1)),
    wordToZ (WS true w1 ^- WS false w2) =
    (2 * wordToZ (w1 ^- w2) + 1)%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z_lt_le_dec (z0 - z)%Z 0) as [Hs|Hs];
     [ rewrite (@Zmod_small_neg (z0 - z)%Z (2 ^ Z.of_nat sz * 2)%Z) in * by lia;
       rewrite (@Zmod_small_neg (1 + 2 * z0 - 2 * z)%Z
                                (2 * (2 ^ Z.of_nat sz * 2))%Z) in * by lia
     | rewrite (Z.mod_small (z0 - z)%Z (2 ^ Z.of_nat sz * 2)%Z) in * by lia;
       rewrite (Z.mod_small (1 + 2 * z0 - 2 * z)%Z
                            (2 * (2 ^ Z.of_nat sz * 2))%Z) in * by lia ]);
    lia.
Qed.

Lemma wtl_combine:
  forall (x: word 1) sz (y: word sz),
    wtl (combine x y) = y.
Proof.
  word_lia_Z.
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
  apply unsigned_inj. rewrite H0. clear H0 H.
  word_to_Z; pose proof (pow2_even_Z sz2 ltac:(lia)).
  all: try match goal with
           | H : (?p1 * ?p2 <= 2 * (?z0 + ?p1 * ?z))%Z, H' : (2 * ?z < ?p2)%Z |- _ =>
             exfalso; pose proof (@msb_combine_lt p1 p2 z0 z); lia
           | H : (2 * (?z0 + ?p1 * ?z) < ?p1 * ?p2)%Z, H' : (?p2 <= 2 * ?z)%Z |- _ =>
             exfalso; pose proof (@msb_combine_ge p1 p2 z0 z); lia
           end.
  all: word_mod_simpl; nia.
Qed.

Lemma wplus_wzero_1:
  forall sz (w: word sz), w ^+ (wzero _) = w.
Proof.
  word_lia_Z.
Qed.

Lemma wplus_wzero_2:
  forall sz (w: word sz), (wzero _) ^+ w = w.
Proof.
  word_lia_Z.
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
  intros; rewrite (wplus_comm w2 w3), combine_wplus_1, wplus_comm; reflexivity.
Qed.

Lemma existT_wplus:
  forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^+ w2) = existT word _ (w3 ^+ w4).
Proof.
  intros; apply existT_word_inv in H; apply existT_word_inv in H0; destruct H, H0; subst.
  apply unsigned_inj in H1; apply unsigned_inj in H2; subst; reflexivity.
Qed.

Lemma existT_wminus:
  forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^- w2) = existT word _ (w3 ^- w4).
Proof.
  intros; apply existT_word_inv in H; apply existT_word_inv in H0; destruct H, H0; subst.
  apply unsigned_inj in H1; apply unsigned_inj in H2; subst; reflexivity.
Qed.

Lemma existT_sext:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (sext w1 n) = existT word _ (sext w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_extz:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (extz w1 n) = existT word _ (extz w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_wrshifta:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wrshifta w1 n) = existT word _ (wrshifta w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma existT_wlshift:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wlshift w1 n) = existT word _ (wlshift w2 n).
Proof.
  intros; apply existT_word_inv in H; destruct H; subst.
  apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma eq_rect_wplus:
  forall sz (w1 w2: word sz) sz' Hsz,
    eq_rect sz word (w1 ^+ w2) sz' Hsz =
    (eq_rect sz word w1 sz' Hsz) ^+ (eq_rect sz word w2 sz' Hsz).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma eq_rect_2:
  forall sz (pa: word sz) sz' Heq1 Heq2,
    eq_rect sz' word (eq_rect sz word pa sz' Heq1) sz Heq2 = pa.
Proof.
  intros; subst; rewrite (UIP_dec Nat.eq_dec Heq2 eq_refl); reflexivity.
Qed.

Lemma wzero_eq_rect:
  forall sz1 sz2 Heq,
    eq_rect sz1 word (wzero sz1) sz2 Heq = wzero sz2.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wrshifta_0:
  forall sz (w: word sz), wrshifta w 0 = w.
Proof.
  word_lia_Z.
Qed.

Lemma wrshifta_WO:
  forall n, wrshifta WO n = WO.
Proof.
  intros; apply word0.
Qed.

Lemma split2_WO:
  forall n w, split2 n 0 w = WO.
Proof.
  intros; apply word0.
Qed.

Lemma sext_wzero:
  forall sz n, sext (wzero sz) n = wzero (sz + n).
Proof.
  word_lia_Z.
Qed.

Lemma wrshifta_wzero:
  forall sz n, wrshifta (wzero sz) n = wzero _.
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

Lemma sext_WS:
  forall sz (w: word (S sz)) b n,
    sext (WS b w) n = WS b (sext w n).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; lia).
  all: try (rewrite !Zmod_small_neg by lia); lia.
Qed.

Lemma sext_wordToZ:
  forall sz n (w: word sz),
    wordToZ (sext w n) = wordToZ w.
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); nia.
Qed.

Lemma sext_natToWord': forall sz1 sz2 n,
  (2 * n < pow2 sz1)%nat ->
  sext (natToWord sz1 n) sz2 = natToWord (sz1 + sz2) n.
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
Qed.

Lemma sext_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
  (2 * n < pow2 sz1)%nat ->
  eq_rect (sz1 + sz2) word (sext (natToWord sz1 n) sz2) sz e = natToWord sz n.
Proof.
  intros; subst; apply sext_natToWord'; assumption.
Qed.

Lemma sext_wneg_natToWord'': forall sz1 sz2 n,
  pow2 sz1 <= 2 * n < pow2 (S sz1) ->
  sext (natToWord sz1 n) sz2 = natToWord (sz1 + sz2) (pow2 (sz1+sz2) - (pow2 sz1 - n)).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); nia.
Qed.

Lemma sext_wneg_natToWord': forall sz1 sz2 n,
  (2 * n < pow2 sz1)%nat ->
  sext (wneg (natToWord sz1 n)) sz2 = wneg (natToWord (sz1 + sz2) n).
Proof.
  word_to_Z; pose proof (pow2_Z sz1); pose proof (pow2_pos_Z sz1); pose proof (pow2_pos_Z sz2);
    rewrite (Z.mod_small (Z.of_nat n) (2 ^ Z.of_nat sz1)%Z) in * by lia;
    (destruct (Z.eq_dec (Z.of_nat n) 0) as [E|E];
     [ rewrite E in *; rewrite ?Z.opp_0, ?Z.mod_0_l in * by lia
     | rewrite (@Zmod_small_neg (- Z.of_nat n)%Z (2 ^ Z.of_nat sz1)%Z) in * by lia ]);
    try lia.
  replace (- Z.of_nat n + 2 ^ Z.of_nat sz1 - 2 ^ Z.of_nat sz1)%Z with (- Z.of_nat n)%Z by ring.
  rewrite (Z.mod_small (Z.of_nat n) (2 ^ Z.of_nat sz1 * 2 ^ Z.of_nat sz2)%Z) by nia.
  reflexivity.
Qed.

Lemma sext_wneg_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
  (2 * n < pow2 sz1)%nat ->
  eq_rect (sz1 + sz2) word (sext (wneg (natToWord sz1 n)) sz2) sz e = wneg (natToWord sz n).
Proof.
  intros; subst; apply sext_wneg_natToWord'; assumption.
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

Lemma wordToNat_split2:
  forall sz1 sz2 (w: word (sz1 + sz2)),
    wordToNat (split2 _ _ w) =
    Nat.div (wordToNat w) (pow2 sz1).
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_wrshifta:
  forall sz (w: word sz) n,
    wordToNat (wrshifta w n) =
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

Lemma wordToNat_wlshift:
  forall sz (w: word sz) n,
    wordToNat (wlshift w n) =
    Nat.mul (Nat.modulo (wordToNat w) (pow2 (sz - n))) (pow2 n).
Proof.
  intros; destruct (le_lt_dec n sz).
  - word_to_Z; pose proof (pow2_pos_Z n); pose proof (pow2_pos_Z (sz - n)).
    replace sz with ((sz - n) + n) at 1 by lia. rewrite pow2_add_Z.
    rewrite Z.mul_mod_distr_r by lia.
    assert (0 <= z mod 2 ^ Z.of_nat (sz - n))%Z by (apply Z.mod_pos_bound; lia).
    rewrite Z2Nat.inj_mul, Z2Nat.inj_mod by lia.
    replace (Z.to_nat (2 ^ Z.of_nat (sz - n))) with (pow2 (sz - n)) by lia.
    replace (Z.to_nat (2 ^ Z.of_nat n)) with (pow2 n) by lia.
    reflexivity.
  - rewrite wlshift_gt by lia. replace (sz - n) with 0 by lia. word_lia_Z.
Qed.

Lemma wordToNat_extz:
  forall sz (w: word sz) n,
    wordToNat (extz w n) = pow2 n * wordToNat w.
Proof.
  word_lia_Z.
Qed.

Lemma extz_is_mult_pow2: forall sz n d,
  extz (natToWord sz n) d = natToWord (d + sz) (pow2 d * n).
Proof.
  word_lia_Z.
Qed.

Lemma extz_is_mult_pow2_neg: forall sz n d,
  extz (wneg (natToWord sz n)) d = wneg (natToWord (d + sz) (pow2 d * n)).
Proof.
  intros; word_to_Z.
  rewrite !Zopp_mod_idemp by lia.
  rewrite <- Z.mul_opp_r, Z.mul_mod_distr_l by lia.
  reflexivity.
Qed.

Lemma wordToNat_sext_bypass:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) (Hsz: sz1 = sz2) n,
    wordToNat w1 = wordToNat w2 ->
    wordToNat (sext w1 n) = wordToNat (sext w2 n).
Proof.
  intros; subst; apply wordToNat_inj in H; subst; reflexivity.
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
    existT word _ (wrshifta (extz w (n1 + n2)) n1) =
    existT word _ (sext (extz w n2) n1).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); try nia.
Qed.

Lemma wordToNat_sext_modulo:
  forall sz (w: word sz) n,
    Nat.modulo (wordToNat (sext w n)) (pow2 sz) = wordToNat w.
Proof.
  word_to_Z; pose proof (pow2_Z sz); pose proof (pow2_pos_Z sz); pose proof (pow2_pos_Z n).
  - rewrite (Z.mod_small z) by nia; apply Nat.mod_small; lia.
  - rewrite (@Zmod_small_neg (z - 2 ^ Z.of_nat sz)%Z) by nia.
    apply Nat2Z.inj; rewrite Nat2Z.inj_mod, pow2_Z, !Z2Nat.id by nia.
    replace (z - 2 ^ Z.of_nat sz + 2 ^ Z.of_nat sz * 2 ^ Z.of_nat n)%Z
       with (z + (2 ^ Z.of_nat n - 1) * 2 ^ Z.of_nat sz)%Z by ring.
    rewrite Z.mod_add by lia; apply Z.mod_small; lia.
Qed.

Lemma wlshift_sext_extz:
  forall sz (w: word sz) n,
    existT word _ (wlshift (sext w n) n) =
    existT word _ (extz w n).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); try nia.
Qed.

Lemma wlshift_combine_extz:
  forall sn sl (wl: word sl) ssu (wu: word (ssu + sn)),
    existT word (sl + (ssu + sn)) (wlshift (combine wl wu) sn) =
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

Lemma extz_sext_eq_rect:
  forall sz (w: word sz) n1 n2 nsz Hnsz1,
  exists Hnsz2,
    eq_rect (n2 + (sz + n1)) word (extz (sext w n1) n2) nsz Hnsz1 =
    eq_rect (n2 + sz + n1) word (sext (extz w n2) n1) nsz Hnsz2.
Proof.
  intros; assert (Hnsz2 : n2 + sz + n1 = nsz) by lia; exists Hnsz2.
  pose proof (extz_sext w n1 n2) as E; apply existT_word_inv in E; destruct E.
  word_to_Z; assumption.
Qed.

Lemma sext_zero:
  forall n m, sext (natToWord n 0) m = natToWord _ 0.
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

Lemma sext_sext:
  forall sz (w: word sz) n1 n2,
    existT word _ (sext w (n1 + n2)) = existT word _ (sext (sext w n1) n2).
Proof.
  word_to_Z; word_mod_simpl; try lia; try (exfalso; nia).
  all: try (rewrite !Zmod_small_neg by nia); try nia.
Qed.

Lemma wneg_wordToN:
  forall sz (w: word sz),
    wordToN w <> 0%N ->
    wordToN (wneg w) = (Npow2 sz - wordToN w)%N.
Proof.
  word_lia_Z.
Qed.

Lemma Nmul_two:
  forall n, (n + n = 2 * n)%N.
Proof.
  intros; lia.
Qed.

Lemma wmsb_false_bound:
  forall sz (w: word (S sz)),
    wmsb w false = false -> (wordToN w < Npow2 sz)%N.
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_true_bound:
  forall sz (w: word (S sz)),
    wmsb w false = true -> (Npow2 sz <= wordToN w)%N.
Proof.
  word_lia_Z.
Qed.

(** * [Z] round trips and signed arithmetic *)

Lemma ZToWord_wordToZ:
  forall sz (w: word sz), ZToWord sz (wordToZ w) = w.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_ZToWord:
  forall z sz,
    (- Z.of_nat (pow2 sz) <= z < Z.of_nat (pow2 sz))%Z ->
    wordToZ (ZToWord (S sz) z) = z.
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
      wordToZ (ZToWord sz n) = n.
Proof.
  intros; destruct sz; [lia|].
  replace (Z.of_nat (S sz) - 1)%Z with (Z.of_nat sz) in H0 by lia.
  apply wordToZ_ZToWord; rewrite pow2_Z; assumption.
Qed.

Lemma wordToZ_wordToN:
  forall sz (w: word sz),
    wordToZ w = (Z.of_N (wordToN w) - Z.of_N (if wmsb w false then Npow2 sz else 0))%Z.
Proof.
  word_lia_Z.
Qed.

Lemma ZToWord_Z_of_N:
  forall sz n,
    ZToWord sz (Z.of_N n) = NToWord sz n.
Proof.
  reflexivity.
Qed.

Lemma ZToWord_Z_of_nat: forall sz x, ZToWord sz (Z.of_nat x) = natToWord sz x.
Proof.
  reflexivity.
Qed.

Lemma natToWord_Z_to_nat: forall sz n,
    (0 <= n)%Z ->
    natToWord sz (Z.to_nat n) = ZToWord sz n.
Proof.
  word_lia_Z.
Qed.

Lemma ZToWord_sz0: forall z, ZToWord 0 z = $0.
Proof.
  intros; apply word0.
Qed.

Lemma ZToWord_0: forall sz, ZToWord sz 0 = wzero sz.
Proof.
  word_lia_Z.
Qed.

Lemma ZToWord_1{sz : nat}: ZToWord sz 1 = wone sz.
Proof.
  word_lia_Z.
Qed.

Lemma natToWord_pow2_add:
  forall sz n,
    natToWord sz (n + pow2 sz) = natToWord sz n.
Proof.
  intros; word_to_Z.
  replace (Z.of_nat n + 2 ^ Z.of_nat sz)%Z with (Z.of_nat n + 1 * 2 ^ Z.of_nat sz)%Z by lia.
  apply Z_mod_plus_full.
Qed.

Lemma nat_add_pow2_wzero:
  forall sz n1 n2,
    n1 + n2 = pow2 sz ->
    natToWord sz n1 ^+ natToWord sz n2 = wzero sz.
Proof.
  word_lia_Z.
Qed.

Lemma Npos_Npow2_wzero:
  forall sz p1 p2,
    N.pos (p1 + p2) = Npow2 sz ->
    posToWord sz p1 ^+ posToWord sz p2 = wzero sz.
Proof.
  word_lia_Z.
Qed.

Lemma ZToWord_Npow2_sub:
  forall sz z,
    ZToWord sz (z - Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  intros; word_to_Z.
  replace (z - 2 ^ Z.of_nat sz)%Z with (z + (-1) * 2 ^ Z.of_nat sz)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Lemma wplus_wplusZ:
  forall sz (w1 w2: word sz),
    w1 ^+ w2 = wplusZ w1 w2.
Proof.
  intros; cbv [wplusZ wordBinZ]; word_to_Z;
    [ reflexivity
    | replace (z0 + (z - 2 ^ Z.of_nat sz))%Z
         with (z0 + z + (-1) * 2 ^ Z.of_nat sz)%Z by ring
    | replace (z0 - 2 ^ Z.of_nat sz + z)%Z
         with (z0 + z + (-1) * 2 ^ Z.of_nat sz)%Z by ring
    | replace (z0 - 2 ^ Z.of_nat sz + (z - 2 ^ Z.of_nat sz))%Z
         with (z0 + z + (-2) * 2 ^ Z.of_nat sz)%Z by ring ];
    symmetry; apply Z_mod_plus_full.
Qed.

Lemma ZToWord_Npow2_sub_k : forall (sz : nat) (z : Z) (k: nat),
    ZToWord sz (z - Z.of_nat k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  intros; word_to_Z.
  replace (z - Z.of_nat k * 2 ^ Z.of_nat sz)%Z
     with (z + (- Z.of_nat k) * 2 ^ Z.of_nat sz)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Lemma ZToWord_Npow2_add_k : forall (sz : nat) (z : Z) (k: nat),
    ZToWord sz (z + Z.of_nat k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  word_lia_Z.
Qed.

Lemma ZToWord_Npow2_sub_z : forall (sz : nat) (z : Z) (k: Z),
    ZToWord sz (z - k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  intros; word_to_Z.
  replace (z - k * 2 ^ Z.of_nat sz)%Z with (z + (- k) * 2 ^ Z.of_nat sz)%Z by ring.
  apply Z_mod_plus_full.
Qed.

Lemma ZToWord_Npow2_add_k':  forall sz z k,
    ZToWord sz (z + k * Z.of_N (Npow2 sz)) = ZToWord sz z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_ZToWord': forall sz w,
    exists k, wordToZ (ZToWord sz w) = (w - k * Z.of_N (Npow2 sz))%Z.
Proof.
  intros; destruct sz.
  - exists w; word_lia_Z.
  - pose proof (pow2_pos_Z (S sz)).
    assert (E : wordToZ (ZToWord (S sz) w) =
                (if 2 * (w mod 2 ^ Z.of_nat (S sz)) <? 2 ^ Z.of_nat (S sz)
                 then w mod 2 ^ Z.of_nat (S sz)
                 else w mod 2 ^ Z.of_nat (S sz) - 2 ^ Z.of_nat (S sz))%Z)
      by (cbv [wordToZ ZToWord]; rewrite signed_eqn, unsigned_ofZ; reflexivity).
    rewrite Npow2_Z, E.
    destruct (Z.ltb_spec (2 * (w mod 2 ^ Z.of_nat (S sz)))%Z (2 ^ Z.of_nat (S sz))%Z).
    + exists (w / 2 ^ Z.of_nat (S sz))%Z; rewrite (Z.mod_eq w) by lia; lia.
    + exists (w / 2 ^ Z.of_nat (S sz) + 1)%Z; rewrite (Z.mod_eq w) by lia; lia.
Qed.

Lemma ZToWord_plus: forall sz a b, ZToWord sz (a + b) = ZToWord sz a ^+ ZToWord sz b.
Proof.
  word_lia_Z.
Qed.

Lemma wplus_Z:  forall sz (a b : word sz),
    a ^+ b = ZToWord sz (wordToZ a + wordToZ b).
Proof.
  word_to_Z;
    [ reflexivity
    | replace (z0 + (z - 2 ^ Z.of_nat sz))%Z
         with (z0 + z + (-1) * 2 ^ Z.of_nat sz)%Z by ring
    | replace (z0 - 2 ^ Z.of_nat sz + z)%Z
         with (z0 + z + (-1) * 2 ^ Z.of_nat sz)%Z by ring
    | replace (z0 - 2 ^ Z.of_nat sz + (z - 2 ^ Z.of_nat sz))%Z
         with (z0 + z + (-2) * 2 ^ Z.of_nat sz)%Z by ring ];
    symmetry; apply Z_mod_plus_full.
Qed.

Lemma else_0_to_ex_N: forall (b: bool) (a: N),
    exists k, (if b then a else 0%N) = (k * a)%N.
Proof.
  intros; destruct b; [exists 1%N | exists 0%N]; lia.
Qed.

Local Lemma wmultZ_helper: forall a b k1 k2 p,
    ((a - k1 * p) * (b - k2 * p) = a * b - (k1 * b + k2 * a - k1 * k2 * p) * p)%Z.
Proof.
  intros; ring.
Qed.

Lemma wmult_wmultZ: forall (sz : nat) (w1 w2 : word sz), w1 ^* w2 = wmultZ w1 w2.
Proof.
  intros; cbv [wmultZ wordBinZ]; word_to_Z;
    [ reflexivity
    | replace (z0 * (z - 2 ^ Z.of_nat sz))%Z
         with (z0 * z + (- z0) * 2 ^ Z.of_nat sz)%Z by ring
    | replace ((z0 - 2 ^ Z.of_nat sz) * z)%Z
         with (z0 * z + (- z) * 2 ^ Z.of_nat sz)%Z by ring
    | replace ((z0 - 2 ^ Z.of_nat sz) * (z - 2 ^ Z.of_nat sz))%Z
         with (z0 * z + (- z0 - z + 2 ^ Z.of_nat sz) * 2 ^ Z.of_nat sz)%Z by ring ];
    symmetry; apply Z_mod_plus_full.
Qed.

Lemma ZToWord_mult: forall sz a b, ZToWord sz (a * b) = ZToWord sz a ^* ZToWord sz b.
Proof.
  word_lia_Z.
Qed.

Lemma wmult_Z:  forall sz (a b : word sz),
    a ^* b = ZToWord sz (wordToZ a * wordToZ b).
Proof.
  word_to_Z;
    [ reflexivity
    | replace (z0 * (z - 2 ^ Z.of_nat sz))%Z
         with (z0 * z + (- z0) * 2 ^ Z.of_nat sz)%Z by ring
    | replace ((z0 - 2 ^ Z.of_nat sz) * z)%Z
         with (z0 * z + (- z) * 2 ^ Z.of_nat sz)%Z by ring
    | replace ((z0 - 2 ^ Z.of_nat sz) * (z - 2 ^ Z.of_nat sz))%Z
         with (z0 * z + (- z0 - z + 2 ^ Z.of_nat sz) * 2 ^ Z.of_nat sz)%Z by ring ];
    symmetry; apply Z_mod_plus_full.
Qed.

Lemma wordToZ_wplus_bound:
  forall sz (w1 w2: word (S sz)),
    (- Z.of_nat (pow2 sz) <= wordToZ w1 + wordToZ w2 < Z.of_nat (pow2 sz))%Z ->
    (wordToZ w1 + wordToZ w2 = wordToZ (w1 ^+ w2))%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z_lt_le_dec (z0 + z)%Z (2 * 2 ^ Z.of_nat sz)%Z) as [Hs|Hs];
     [ rewrite (Z.mod_small (z0 + z)%Z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia
     | rewrite (@Zmod_small_2 (z0 + z)%Z (2 * 2 ^ Z.of_nat sz)%Z) in * by lia ]);
    lia.
Qed.

Lemma wordToZ_wplus_bound':
  forall sz (w1 w2: word sz),
    sz <> 0 ->
    (- Z.of_nat (pow2 (pred sz)) <= wordToZ w1 + wordToZ w2 < Z.of_nat (pow2 (pred sz)))%Z ->
    (wordToZ w1 + wordToZ w2 = wordToZ (w1 ^+ w2))%Z.
Proof.
  intros; destruct sz; [lia|]; apply wordToZ_wplus_bound; assumption.
Qed.

Lemma wordToZ_size':
  forall sz (w: word (S sz)),
    (- Z.of_nat (pow2 sz) <= wordToZ w < Z.of_nat (pow2 sz))%Z.
Proof.
  word_lia_Z.
Qed.

Lemma wordToZ_size:
  forall sz (w: word (S sz)),
    (Z.abs (wordToZ w) <= Z.of_nat (pow2 sz))%Z.
Proof.
  intros; pose proof (wordToZ_size' w); lia.
Qed.

Lemma wordToZ_size'': forall (sz : nat),
    (0 < sz)%nat ->
    forall  w : word sz,
      (- 2 ^ (Z.of_nat sz - 1) <= wordToZ w < 2 ^ (Z.of_nat sz - 1))%Z.
Proof.
  intros; destruct sz; [lia|].
  replace (Z.of_nat (S sz) - 1)%Z with (Z.of_nat sz) by lia.
  pose proof (wordToZ_size' w); rewrite pow2_Z in H0; assumption.
Qed.

Lemma wneg_wzero:
  forall sz (w: word sz), wneg w = wzero sz -> w = wzero sz.
Proof.
  intros; apply wneg_zero; assumption.
Qed.

Lemma wmsb_false_pos:
  forall sz (w: word sz),
    wmsb w false = false <-> (wordToZ w >= 0)%Z.
Proof.
  split; word_lia_Z.
Qed.

Lemma wmsb_true_neg:
  forall sz (w: word sz),
    wmsb w false = true <-> (wordToZ w < 0)%Z.
Proof.
  split; word_lia_Z.
Qed.

Lemma wordToZ_distr_diff_wmsb:
  forall sz (w1 w2: word sz),
    wmsb w1 false = negb (wmsb w2 false) ->
    wordToZ (w1 ^+ w2) = (wordToZ w1 + wordToZ w2)%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z_lt_le_dec (z0 + z)%Z (2 ^ Z.of_nat sz)%Z) as [Hs|Hs];
     [ rewrite (Z.mod_small (z0 + z)%Z (2 ^ Z.of_nat sz)%Z) in * by lia
     | rewrite (@Zmod_small_2 (z0 + z)%Z (2 ^ Z.of_nat sz)%Z) in * by lia ]);
    lia.
Qed.

Lemma sext_wplus_wordToZ_distr:
  forall sz (w1 w2: word sz) n,
    n <> 0 -> wordToZ (sext w1 n ^+ sext w2 n) =
              (wordToZ (sext w1 n) + wordToZ (sext w2 n))%Z.
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

Lemma sext_wplus_wordToZ_distr_existT:
  forall sz (w1 w2: word sz) ssz (sw1 sw2: word ssz) n,
    existT word _ w1 = existT word _ (sext sw1 n) ->
    existT word _ w2 = existT word _ (sext sw2 n) ->
    n <> 0 -> wordToZ (w1 ^+ w2) = (wordToZ w1 + wordToZ w2)%Z.
Proof.
  intros; apply existT_word_inv in H; apply existT_word_inv in H0; destruct H, H0; subst.
  apply unsigned_inj in H2; apply unsigned_inj in H3; subst.
  apply sext_wplus_wordToZ_distr; assumption.
Qed.

Lemma split1_existT:
  forall n sz1 (w1: word (n + sz1)) sz2 (w2: word (n + sz2)),
    existT word _ w1 = existT word _ w2 ->
    split1 n _ w1 = split1 n _ w2.
Proof.
  intros; apply existT_word_inv in H; destruct H.
  assert (sz1 = sz2) by lia; subst; apply unsigned_inj in H0; subst; reflexivity.
Qed.

Lemma word_combinable:
  forall sz1 sz2 (w: word (sz1 + sz2)),
  exists w1 w2, w = combine w1 w2.
Proof.
  intros; exists (split1 sz1 sz2 w), (split2 sz1 sz2 w); symmetry; apply combine_split.
Qed.

Lemma split1_combine_existT:
  forall sz n (w: word (n + sz)) sl (wl: word (n + sl)) su (wu: word su),
    existT word _ w = existT word _ (combine wl wu) ->
    split1 n _ w = split1 n _ wl.
Proof.
  intros; apply existT_word_inv in H; destruct H.
  apply unsigned_inj; rewrite !unsigned_split1, H0, unsigned_combine.
  rewrite <- (Z.mod_add (unsigned wl) (2 ^ Z.of_nat sl * unsigned wu) (2 ^ Z.of_nat n))
    by (pose proof (pow2_pos_Z n); lia).
  f_equal; f_equal; rewrite (pow2_add_Z n sl); ring.
Qed.

Lemma extz_pow2_wordToZ:
  forall sz (w: word sz) n,
    wordToZ (extz w n) = (wordToZ w * Z.of_nat (pow2 n))%Z.
Proof.
  word_to_Z; try lia; try (exfalso; nia); nia.
Qed.

Lemma extz_wneg:
  forall sz (w: word sz) n,
    extz (wneg w) n = wneg (extz w n).
Proof.
  word_lia_Z.
Qed.

Lemma wneg_wordToZ:
  forall sz (w: word (S sz)),
    w <> wpow2 sz ->
    wordToZ (wneg w) = (- wordToZ w)%Z.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz);
    (destruct (Z.eq_dec z 0) as [->|];
     [ rewrite Z.opp_0, Z.mod_0_l in * by lia
     | rewrite (@Zmod_small_neg (- z)%Z) in * by lia ]);
    lia.
Qed.

Lemma wneg_wordToZ':
  forall sz (w: word (S sz)) z,
    w <> wpow2 sz ->
    (z + wordToZ (wneg w))%Z = (z - wordToZ w)%Z.
Proof.
  intros; rewrite wneg_wordToZ by assumption; lia.
Qed.

Lemma wneg_wplus_distr:
  forall sz (w1 w2: word sz),
    wneg (w1 ^+ w2) = wneg w1 ^+ wneg w2.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz).
  rewrite Zopp_mod_idemp by lia.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  f_equal; ring.
Qed.

Lemma wminus_wneg:
  forall sz (w1 w2: word sz),
    wneg (w1 ^- w2) = w2 ^- w1.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz).
  rewrite Zopp_mod_idemp by lia; f_equal; ring.
Qed.

Lemma wminus_wordToZ:
  forall sz (w1 w2: word (S sz)),
    w2 ^- w1 <> wpow2 sz ->
    wordToZ (w1 ^- w2) = (- wordToZ (w2 ^- w1))%Z.
Proof.
  intros; rewrite <- wminus_wneg; apply wneg_wordToZ; assumption.
Qed.

Lemma wminus_wordToZ':
  forall sz (w1 w2: word (sz + 1)),
    existT word _ (w2 ^- w1) <> existT word _ (wpow2 sz) ->
    wordToZ (w1 ^- w2) = (- wordToZ (w2 ^- w1))%Z.
Proof.
  intros; rewrite <- wminus_wneg.
  assert (w2 ^- w1 <> eq_rect _ word (wpow2 sz) _ (Nat.add_comm 1 sz)).
  { intro E; apply H; rewrite E; clear.
    apply existT_word_eq; [lia | rewrite unsigned_eq_rect; reflexivity]. }
  clear H. word_to_Z; pose proof (pow2_pos_Z sz);
    assert (Hd : (0 <= (z0 - z) mod (2 ^ Z.of_nat sz * 2) < 2 ^ Z.of_nat sz * 2)%Z)
      by (apply Z.mod_pos_bound; lia);
    (destruct (Z.eq_dec ((z0 - z) mod (2 ^ Z.of_nat sz * 2))%Z 0) as [E|E];
     [ rewrite E in *; rewrite ?Z.opp_0, ?Z.mod_0_l in * by lia
     | rewrite (@Zmod_small_neg (- ((z0 - z) mod (2 ^ Z.of_nat sz * 2)))%Z
                                (2 ^ Z.of_nat sz * 2)%Z) in * by lia ]);
    lia.
Qed.

Lemma wminus_wminusZ: forall (sz : nat) (w1 w2 : word sz), w1 ^- w2 = wminusZ w1 w2.
Proof.
  intros; cbv [wminusZ wordBinZ]; word_lia_Z.
Qed.

Local Lemma wminusZ_helper: forall a b k1 k2 p,
    ((a - k1 * p) - (b - k2 * p) = a - b - (k1 - k2) * p)%Z.
Proof.
  intros; ring.
Qed.

Lemma ZToWord_minus: forall sz a b, ZToWord sz (a - b) = ZToWord sz a ^- ZToWord sz b.
Proof.
  word_lia_Z.
Qed.

Lemma wminus_Z: forall sz (a b : word sz),
    a ^- b = ZToWord sz (wordToZ a - wordToZ b).
Proof.
  word_lia_Z.
Qed.

Lemma ZToWord_opp_wneg{sz: nat}: forall (x: Z),
    ZToWord sz (- x) = ^~ (ZToWord sz x).
Proof.
  word_lia_Z.
Qed.

Lemma Zeqb_true_ZToWord: forall {sz: nat} (x y: Z),
    (x =? y)%Z = true ->
    ZToWord sz x = ZToWord sz y.
Proof.
  intros; apply Z.eqb_eq in H; subst; reflexivity.
Qed.

Lemma word_ring_theory_Z: forall (sz: nat),
    ring_theory (ZToWord sz 0) (ZToWord sz 1)
                (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) eq.
Proof.
  intros; rewrite ZToWord_0, ZToWord_1; apply wring.
Qed.

Lemma word_ring_morph_Z: forall (sz: nat),
    ring_morph (ZToWord sz 0) (ZToWord sz 1) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz)
               eq 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb
               (ZToWord sz).
Proof.
  intros; constructor; intros.
  - reflexivity.
  - reflexivity.
  - apply ZToWord_plus.
  - apply ZToWord_minus.
  - apply ZToWord_mult.
  - apply ZToWord_opp_wneg.
  - apply Zeqb_true_ZToWord; assumption.
Qed.

Lemma extz_zero:
  forall sz n, extz (natToWord sz 0) n = wzero _.
Proof.
  word_lia_Z.
Qed.

Lemma sext_eq_rect:
  forall sz (w: word sz) n nsz Hsz1,
  exists Hsz2,
    eq_rect (sz + n) word (sext w n) (nsz + n) Hsz1 =
    sext (eq_rect sz word w nsz Hsz2) n.
Proof.
  intros; assert (Hsz2 : sz = nsz) by lia; exists Hsz2; subst.
  rewrite (Eqdep_dec.UIP_dec Nat.eq_dec Hsz1 eq_refl); reflexivity.
Qed.

Lemma wmsb_sext:
  forall sz (w: word sz) n,
    wmsb (sext w n) false = wmsb w false.
Proof.
  intros.
  pose proof (pow2_pos_Z sz); pose proof (pow2_pos_Z n); pose proof (unsigned_range w).
  rewrite !wmsb_eqn_gen, unsigned_sext, signed_eqn, pow2_add_Z.
  destruct (Z.eqb_spec (Z.of_nat sz) 0) as [E|E].
  - assert (Es : sz = 0) by lia; subst sz.
    assert (Eu : unsigned w = 0%Z) by (cbn in *; lia).
    rewrite Eu; cbn [Z.mul Z.ltb Z.compare].
    rewrite Z.mul_1_l, Z.mod_0_l by lia.
    destruct (Z.eqb_spec (Z.of_nat (0 + n)) 0); [reflexivity|].
    destruct (Z.leb_spec (2 ^ Z.of_nat n) 0); [lia|reflexivity].
  - destruct (Z.eqb_spec (Z.of_nat (sz + n)) 0); [rewrite Nat2Z.inj_add in *; lia|].
    destruct (Z.ltb_spec (2 * unsigned w) (2 ^ Z.of_nat sz)).
    + rewrite Z.mod_small by nia.
      destruct (Z.leb_spec (2 ^ Z.of_nat sz * 2 ^ Z.of_nat n) (2 * unsigned w));
        destruct (Z.leb_spec (2 ^ Z.of_nat sz) (2 * unsigned w));
        try reflexivity; nia.
    + rewrite (@Zmod_small_neg (unsigned w - 2 ^ Z.of_nat sz)%Z) by nia.
      destruct (Z.leb_spec (2 ^ Z.of_nat sz * 2 ^ Z.of_nat n)
                  (2 * (unsigned w - 2 ^ Z.of_nat sz +
                        2 ^ Z.of_nat sz * 2 ^ Z.of_nat n))%Z);
        destruct (Z.leb_spec (2 ^ Z.of_nat sz) (2 * unsigned w));
        try reflexivity; nia.
Qed.

Lemma wmsb_testbit : forall sz (w : word sz) b,
    sz <> 0 -> wmsb w b = Z.testbit (unsigned w) (Z.of_nat sz - 1).
Proof.
  intros; destruct sz; [lia|]; cbv [wmsb]; f_equal; lia.
Qed.

Lemma wmsb_wlshift_sext:
  forall sz (w: word sz) n,
    wmsb (sext w n) false = wmsb (wlshift (sext w n) n) false.
Proof.
  intros; destruct sz.
  { assert (Eu : unsigned w = 0%Z) by (pose proof (unsigned_range w); cbn in *; lia).
    pose proof (pow2_pos_Z (0 + n)).
    rewrite !wmsb_eqn_gen, unsigned_wlshift, !unsigned_sext, signed_eqn, Eu.
    replace (2 ^ Z.of_nat 0)%Z with 1%Z by reflexivity.
    cbn [Z.mul Z.ltb Z.compare].
    rewrite ?Z.mod_0_l, ?Z.mul_0_l, ?Z.mod_0_l by lia.
    reflexivity. }
  rewrite wmsb_sext, !wmsb_testbit by lia.
  rewrite unsigned_wlshift, Z.testbit_mod_pow2, Z.mul_pow2_bits by lia.
  replace (Z.of_nat (S sz + n) - 1 - Z.of_nat n)%Z with (Z.of_nat (S sz) - 1)%Z by lia.
  destruct (Z.ltb_spec (Z.of_nat (S sz + n) - 1) (Z.of_nat (S sz + n))); [|lia].
  rewrite Bool.andb_true_l.
  rewrite <- (Z.mod_pow2_bits_low (unsigned (sext w n)) (Z.of_nat (S sz)) (Z.of_nat (S sz) - 1)) by lia.
  rewrite <- unsigned_split1, sext_split1. reflexivity.
Qed.

Lemma wordToZ_wordToNat_pos:
  forall sz (w: word sz),
    wmsb w false = false ->
    Z.of_nat (wordToNat w) = wordToZ w.
Proof.
  word_lia_Z.
Qed.

Corollary wmsb_Zabs_pos:
  forall sz (w: word sz),
    wmsb w false = false -> Z.abs (wordToZ w) = wordToZ w.
Proof.
  intros; rewrite <- wordToZ_wordToNat_pos by assumption; lia.
Qed.

Corollary wmsb_Zabs_neg:
  forall sz (w: word sz),
    wmsb w false = true -> (Z.abs (wordToZ w) = - wordToZ w)%Z.
Proof.
  intros; apply wmsb_true_neg in H; lia.
Qed.

Lemma wordToN_combine:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2),
    wordToN (combine w1 w2) = (wordToN w1 + Npow2 sz1 * wordToN w2)%N.
Proof.
  word_lia_Z.
Qed.

Lemma word_exists_bound:
  forall sz z,
    (- Z.of_nat (pow2 sz) <= z < Z.of_nat (pow2 sz))%Z ->
    exists w: word (S sz), wordToZ w = z.
Proof.
  intros; exists (ZToWord (S sz) z); apply wordToZ_ZToWord; assumption.
Qed.

Lemma sext_size:
  forall sz n (w: word (sz + n)),
    sz <> 0 ->
    (- Z.of_nat (pow2 (sz - 1)) <= wordToZ w < Z.of_nat (pow2 (sz - 1)))%Z ->
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
    wordToZ (combine w WO) = wordToZ w.
Proof.
  word_lia_Z.
Qed.

Lemma combine_WO:
  forall sz (w: word sz),
    combine w WO = eq_rect _ word w _ (Nat.add_comm 0 sz).
Proof.
  word_lia_Z.
Qed.

Lemma zext_zero:
  forall sz (w: word sz),
    zext w 0 = eq_rect _ word w _ (Nat.add_comm 0 sz).
Proof.
  word_lia_Z.
Qed.

Lemma wmsb_false_wordToNat_eq:
  forall sz (w: word (S sz)),
    wmsb w false = false ->
    wordToNat w = wordToNat (split1 sz _ (eq_rect _ word w _ (Nat.add_comm 1 sz))).
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
    (- Z.of_nat (pow2 sz) <= wordToZ w < Z.of_nat (pow2 sz))%Z ->
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
  intros; exists (ZToWord (S sz) (wordToZ w1 + wordToZ w2)).
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

(* Making wlt_dec opaque is necessary to prevent the [exact H] in the
 * example below from blowing up..
 *)
Global Opaque wlt_dec.

Definition test_wlt_f (a : nat) (b : nat) : nat :=
  if wlt_dec (natToWord 64 a) $0 then 0 else 0.
Theorem test_wlt_f_example: forall x y z, test_wlt_f x y = 0 -> test_wlt_f x z = 0.
Proof.
  intros.
  exact H.
Qed.

(** * [wordToNat] transfer lemmas and [word_lia] *)

Lemma wordToNat_eq1: forall sz (a b: word sz), a = b -> wordToNat a = wordToNat b.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma wordToNat_eq2: forall sz (a b: word sz), wordToNat a = wordToNat b -> a = b.
Proof.
  intros; apply wordToNat_inj; assumption.
Qed.

Lemma wordToNat_lt1: forall sz (a b: word sz), a < b -> (wordToNat a < wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_lt2: forall sz (a b: word sz), (wordToNat a < wordToNat b)%nat -> a < b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_gt1: forall sz (a b: word sz), a > b -> (wordToNat a > wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_gt2: forall sz (a b: word sz), (wordToNat a > wordToNat b)%nat -> a > b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_le1: forall sz (a b: word sz), a <= b -> (wordToNat a <= wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_le2: forall sz (a b: word sz), (wordToNat a <= wordToNat b)%nat -> a <= b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_ge1: forall sz (a b: word sz), a >= b -> (wordToNat a >= wordToNat b)%nat.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_ge2: forall sz (a b: word sz), (wordToNat a >= wordToNat b)%nat -> a >= b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_neq1: forall sz (a b: word sz), a <> b -> wordToNat a <> wordToNat b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_neq2: forall sz (a b: word sz), wordToNat a <> wordToNat b -> a <> b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_wplus': forall sz (a b: word sz),
    (#a + #b < pow2 sz)%nat ->
    #(a ^+ b) = #a + #b.
Proof.
  word_to_Z; rewrite Z.mod_small by lia; lia.
Qed.

Lemma wordToNat_wplus'': forall sz (a: word sz) (b: nat),
    (#a + b < pow2 sz)%nat -> #(a ^+ $b) = #a + b.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_wmult': forall sz (a b: word sz),
    (#a * #b < pow2 sz)%nat ->
    #(a ^* b) = #a * #b.
Proof.
  word_lia_Z.
Qed.

Lemma wordNotNot: forall sz (a b: word sz), (a <> b -> False) -> a = b.
Proof.
  intros; destruct (weq a b); [assumption | exfalso; auto].
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
  word_lia_Z.
Qed.

Lemma word_le_zero sz (w: word sz): w <= wzero sz -> w = wzero sz.
Proof.
  word_lia_Z.
Qed.

Close Scope word_scope.

Open Scope word_scope.
Local Open Scope nat.

Lemma wzero_wones: forall sz, sz >= 1 ->
                              natToWord sz 0 <> wones sz.
Proof.
  intros; destruct sz; [lia|]; word_lia_Z.
Qed.

Lemma wzero_wplus: forall sz w, wzero sz ^+ w = w.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_nonZero sz (w: word sz):
  w <> wzero sz -> wordToNat w > 0.
Proof.
  word_lia_Z.
Qed.

Lemma split2_pow2: forall sz n,
    2 ^ sz <= n < 2 ^ S sz ->
    wordToNat (split2 sz 1 (natToWord (sz + 1) n)) = 1.
Proof.
  word_to_Z. word_mod_simpl. zify. Z.div_mod_to_equations. nia.
Qed.

Lemma combine_wones_WO sz:
  forall w, w <> wzero sz -> split2 sz 1 (combine (wones sz) ($ 0) ^+ combine w ($ 0)) = WO~1.
Proof.
  word_to_Z. word_mod_simpl. zify. Z.div_mod_to_equations. nia.
Qed.

Lemma wordToNat_plus sz (w1 w2: word sz):
  natToWord sz (wordToNat w1 + wordToNat w2) = w1 ^+ w2.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_natToWord_eqn sz:
  forall n,
    wordToNat (natToWord sz n) = n mod (pow2 sz).
Proof.
  word_lia_Z.
Qed.


Lemma mod_factor a b c:
  b <> 0 ->
  c <> 0 ->
  (a mod (b * c)) mod b = a mod b.
Proof.
  intros. apply Nat2Z.inj. rewrite !Nat2Z.inj_mod, Nat2Z.inj_mul.
  apply Z.mod_mod_divide. exists (Z.of_nat c). lia.
Qed.

Lemma split1_combine_wplus sz1 sz2 (w11 w21: word sz1) (w12 w22: word sz2):
  split1 _ _ (combine w11 w12 ^+ combine w21 w22) = w11 ^+ w21.
Proof.
  intros; word_to_Z.
  rewrite Zmod_mul_mod by (apply pow2_pos_Z).
  replace (z2 + 2 ^ Z.of_nat sz1 * z1 + (z0 + 2 ^ Z.of_nat sz1 * z))%Z
     with ((z2 + z0) + (z1 + z) * 2 ^ Z.of_nat sz1)%Z by ring.
  rewrite Z.mod_add by (pose proof (pow2_pos_Z sz1); lia); reflexivity.
Qed.

Lemma div_2 a b:
  b <> 0 ->
  a < b * 2 ->
  a >= b ->
  a / b = 1.
Proof.
  intros. zify. Z.div_mod_to_equations. nia.
Qed.

Lemma mod_sub a b:
  b <> 0 ->
  a < b * 2 ->
  a >= b ->
  a mod b = a - b.
Proof.
  intros; apply Nat2Z.inj; rewrite Nat2Z.inj_mod, Nat2Z.inj_sub by lia.
  apply (@Zmod_small_2); lia.
Qed.

Lemma wordToNat_wneg_non_0 sz: forall (a: word sz),
    a <> natToWord _ 0 ->
    # (wneg a) = pow2 sz - #a.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_wnot sz: forall (a: word sz),
    # (wnot a) = pow2 sz - #a - 1.
Proof.
  word_lia_Z.
Qed.

Lemma wzero_wor: forall sz w, w ^| wzero sz = w.
Proof.
  word_bits; word_bits_cases.
Qed.

Lemma bool_prop1: forall a b, a && negb (a && b) = a && negb b.
Proof.
  destruct a, b; reflexivity.
Qed.

Lemma wordToNat_wplus sz (w1 w2: word sz):
  #(w1 ^+ w2) = (#w1 + #w2) mod (pow2 sz).
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz).
  rewrite Z2Nat.inj_mod, Z2Nat.inj_add by lia.
  replace (Z.to_nat (2 ^ Z.of_nat sz)) with (pow2 sz) by lia.
  reflexivity.
Qed.

Lemma wordToNat_wmult : forall (sz : nat) (w1 w2 : word sz),
  #(w1 ^* w2) = (#w1 * #w2) mod pow2 sz.
Proof.
  word_to_Z; pose proof (pow2_pos_Z sz).
  rewrite Z2Nat.inj_mod, Z2Nat.inj_mul by nia.
  replace (Z.to_nat (2 ^ Z.of_nat sz)) with (pow2 sz) by lia.
  reflexivity.
Qed.

Local Arguments natToWord : simpl never.
Local Arguments weq : simpl never.

Lemma wor_r_wzero_1 sz:
  forall w1 w2,
    w1 ^| w2 = natToWord sz 0 ->
    w2 = natToWord sz 0.
Proof.
  intros; word_to_Z.
  match goal with H : Z.lor _ _ = 0%Z |- _ => apply Z.lor_eq_0_iff in H; lia end.
Qed.

Lemma wor_r_wzero_2 sz:
  forall w1 w2,
    w1 ^| w2 = natToWord sz 0 ->
    w1 = natToWord sz 0.
Proof.
  intros; word_to_Z.
  match goal with H : Z.lor _ _ = 0%Z |- _ => apply Z.lor_eq_0_iff in H; lia end.
Qed.

Lemma wordToNat_zero sz: forall (w: word sz), #w = 0 -> w = natToWord _ 0.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_notZero sz: forall (w: word sz), #w <> 0 -> w <> natToWord _ 0.
Proof.
  word_lia_Z.
Qed.

Lemma natToWord_nzero sz x:
  0 < x ->
  x < pow2 sz ->
  natToWord sz x <> natToWord sz 0.
Proof.
  word_lia_Z.
Qed.

Lemma pow2_lt_pow2_S:
  forall n, pow2 n < pow2 (n+1).
Proof.
  intros; rewrite pow2_add_mul; simpl (pow2 1); pose proof (pow2_zero n); lia.
Qed.

Lemma combine_shiftl_plus_n n x:
  x < pow2 n ->
  (combine (natToWord n x) WO~1) = (natToWord (n + 1) (pow2 n)) ^+ natToWord (n + 1) x.
Proof.
  word_lia_Z.
Qed.

Lemma combine_natToWord_wzero n:
  forall x,
    x < pow2 n ->
    combine (natToWord n x) (natToWord 1 0) = natToWord (n+1) x.
Proof.
  word_lia_Z.
Qed.

Lemma word_cancel_l sz (a b c: word sz):
  a = b -> c ^+ a = c ^+ b.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma word_cancel_r sz (a b c: word sz):
  a = b -> a ^+ c = b ^+ c.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma word_cancel_m sz (a b c a' b': word sz):
  a ^+ a' = b ^+ b'-> a ^+ c ^+ a' = b ^+ c ^+ b'.
Proof.
  intros; word_to_Z; word_mod_simpl.
  match goal with
  | H : (?x mod ?p)%Z = (?y mod ?p)%Z |- (?u mod ?p)%Z = (?v mod ?p)%Z =>
    replace u with (x + (u - x))%Z by lia; replace v with (y + (v - y))%Z by lia;
    rewrite (Zplus_mod x), (Zplus_mod y), H; f_equal; f_equal; f_equal; lia
  end.
Qed.

Lemma move_wplus_wminus sz (a b c: word sz):
  a ^+ b = c <-> a = c ^- b.
Proof.
  split; word_lia_Z.
Qed.

Lemma move_wplus_pow2 sz (w1 w2: word (S sz)):
  w1 = w2 ^+ $(pow2 sz) <->
  w1 ^+ $(pow2 sz) = w2.
Proof.
  split; word_lia_Z.
Qed.

Lemma move_wminus_pow2 sz (w1 w2: word (S sz)):
  w1 = w2 ^- $(pow2 sz) <->
  w1 ^- $(pow2 sz) = w2.
Proof.
  split; word_lia_Z.
Qed.

Lemma pow2_wzero sz :
  $(pow2 sz) = wzero sz.
Proof.
  word_lia_Z.
Qed.

Lemma pow2_wplus_wzero sz:
  $(pow2 sz) ^+ $(pow2 sz) = wzero (sz + 1).
Proof.
  word_lia_Z.
Qed.

Lemma wplus_wplus_pow2 sz (x1 x2 y1 y2: word (sz + 1)):
  x1 = y1 ^+ $(pow2 sz) ->
  x2 = y2 ^+ $(pow2 sz) ->
  x1 ^+ x2 = y1 ^+ y2.
Proof.
  intros; word_to_Z.
  rewrite (Z.mod_small (2 ^ Z.of_nat sz)) in * by (pose proof (pow2_pos_Z sz); lia).
  subst.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  replace (z1 + 2 ^ Z.of_nat sz + (z + 2 ^ Z.of_nat sz))%Z
     with ((z1 + z) + 1 * (2 ^ Z.of_nat sz * 2))%Z by ring.
  rewrite Z.mod_add by (pose proof (pow2_pos_Z sz); lia); reflexivity.
Qed.

Lemma wlt_meaning sz (w1 w2: word sz):
  (w1 < w2)%word <-> #w1 < #w2.
Proof.
  split; word_lia_Z.
Qed.

Lemma word1_neq (w: word 1):
  w <> WO~0 ->
  w <> WO~1 ->
  False.
Proof.
  word_lia_Z.
Qed.

Lemma combine_1 sz:
  sz > 1 ->
  natToWord (sz + 1) 1 = combine ($ 1) WO~0.
Proof.
  word_lia_Z.
Qed.

Lemma wordToNat_cast ni no (pf: ni = no):
  forall w,
    #w = #(match pf in _ = Y return _ Y with
           | eq_refl => w
           end).
Proof.
  intros; destruct pf; reflexivity.
Qed.

Lemma wordToN_mod: forall sz (a b: word sz),
    wordToN (a ^% b) = (wordToN a mod wordToN b)%N.
Proof.
  word_to_Z; apply Z2N.inj_mod; lia.
Qed.

Lemma wordToNat_mod: forall sz (a b: word sz),
    b <> $0 ->
    #(a ^% b) = #a mod #b.
Proof.
  word_to_Z; apply Z2Nat.inj_mod; lia.
Qed.

Lemma wlshift_mul_pow2: forall sz n (a: word sz),
    wlshift a n = a ^* $ (pow2 n).
Proof.
  word_lia_Z.
Qed.

Lemma wlshift_mul_Zpow2: forall sz n (a: word sz),
    (0 <= n)%Z ->
    wlshift a (Z.to_nat n) = a ^* ZToWord sz (2 ^ n).
Proof.
  word_lia_Z.
Qed.

Lemma wlshift_distr_plus: forall sz n (a b: word sz),
    wlshift (a ^+ b) n = wlshift a n ^+ wlshift b n.
Proof.
  word_lia_Z.
Qed.

Lemma wlshift_iter: forall sz n1 n2 (a: word sz),
    wlshift (wlshift a n1) n2 = wlshift a (n1 + n2).
Proof.
  word_lia_Z.
Qed.

Lemma wlshift_zero: forall sz n, wlshift $0 n = natToWord sz 0.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_wordToZ: forall (sz : nat) (w : word sz),
    wordToN w = Z.to_N (wordToZ w + Z.of_N (if wmsb w false then Npow2 sz else 0%N)).
Proof.
  word_lia_Z.
Qed.

Lemma uwordToZ_ZToWord_0: forall (sz : nat) (z : Z),
    (0 <= z < Z.of_N (Npow2 sz))%Z ->
    uwordToZ (ZToWord sz z) = z.
Proof.
  word_lia_Z.
Qed.

Lemma uwordToZ_ZToWord: forall (sz : nat) (z : Z),
    (0 <= z < 2 ^ (Z.of_nat sz))%Z ->
    uwordToZ (ZToWord sz z) = z.
Proof.
  word_lia_Z.
Qed.

Lemma NToWord_Z_to_N: forall sz n,
    (0 <= n)%Z ->
    NToWord sz (Z.to_N n) = ZToWord sz n.
Proof.
  word_lia_Z.
Qed.

Lemma uwordToZ_ZToWord_k: forall (sz : nat) (n : Z),
    (0 <= n)%Z ->
    exists k, uwordToZ (ZToWord sz n) = (n - k * 2 ^ Z.of_nat sz)%Z /\ (k * 2 ^ Z.of_nat sz <= n)%Z.
Proof.
  intros; exists (n / 2 ^ Z.of_nat sz)%Z.
  word_to_Z. Z.div_mod_to_equations. nia.
Qed.

Lemma Zpow2_pos: forall n, (2 ^ Z.of_nat n > 0)%Z.
Proof.
  intros; pose proof (pow2_pos_Z n); lia.
Qed.

Lemma uwordToZ_bound: forall sz (a: word sz),
    (0 <= uwordToZ a < 2 ^ Z.of_nat sz)%Z.
Proof.
  word_lia_Z.
Qed.

Lemma uwordToZ_ZToWord_mod: forall (sz : nat) (z : Z),
    (0 <= z)%Z ->
    uwordToZ (ZToWord sz z) = (z mod 2 ^ (Z.of_nat sz))%Z.
Proof.
  word_lia_Z.
Qed.

Section ZScope.
Import Zdiv.

Lemma uwordToZ_ZToWord_full
    (sz : nat) (width_nonneg : (0 < sz)%nat) (z : Z)
  : uwordToZ (ZToWord sz z)
    = (z mod 2 ^ Z.of_nat sz)%Z.
Proof.
  word_lia_Z.
Qed.

Lemma pow2_times2: forall i,
    (0 < i ->
    2 ^ i = 2 * 2 ^ (i - 1))%Z.
Proof.
  intros. rewrite <- Z.pow_succ_r by lia. f_equal; lia.
Qed.

Lemma wordToZ_ZToWord_full sz (H: (0 < sz)%nat) (z:Z) :
  wordToZ (ZToWord sz z) =
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

Lemma wordToZ_ZToWord_full_post sz (H: (0 < sz)%nat) (z:Z) :
  wordToZ (ZToWord sz z) =
  (( wordToZ (ZToWord sz z)
    + 2 ^ (Z.of_nat sz - 1)
    ) mod (2 ^ Z.of_nat sz)
    - 2 ^ (Z.of_nat sz - 1))%Z.
Proof.
  destruct sz; [lia|].
  replace (Z.of_nat (S sz) - 1)%Z with (Z.of_nat sz) by lia.
  pose proof (wordToZ_size' (ZToWord (S sz) z)).
  rewrite pow2_Z in H0.
  rewrite Z.mod_small by (rewrite pow2_S_Z; lia). lia.
Qed.

End ZScope.

Lemma ZToWord_uwordToZ: forall sz (a: word sz),
    ZToWord sz (uwordToZ a) = a.
Proof.
  word_lia_Z.
Qed.

Lemma wordToN_neq_0: forall sz (b : word sz),
    b <> $0 ->
    wordToN b <> 0%N.
Proof.
  word_lia_Z.
Qed.

Lemma wmod_plus_distr_does_not_hold: ~ forall sz (a b m: word sz),
    m <> $0 ->
    (a ^+ b) ^% m = ((a ^% m) ^+ (b ^% m)) ^% m.
Proof.
  intro C.
  specialize (C 4 $9 $11 $7).
  match type of C with (?A -> _) =>
    assert A as H by (intro E; apply (f_equal (@Zmod.unsigned _)) in E; vm_compute in E; discriminate)
  end.
  specialize (C H). apply (f_equal (@Zmod.unsigned _)) in C. vm_compute in C. discriminate.
Qed.

Lemma wmul_mod_distr_does_not_hold: ~ forall sz (a b n: word sz),
    n <> $0 ->
    (a ^* b) ^% n = ((a ^% n) ^* (b ^% n)) ^% n.
Proof.
  intro C.
  specialize (C 4 $9 $11 $7).
  match type of C with (?A -> _) =>
    assert A as H by (intro E; apply (f_equal (@Zmod.unsigned _)) in E; vm_compute in E; discriminate)
  end.
  specialize (C H). apply (f_equal (@Zmod.unsigned _)) in C. vm_compute in C. discriminate.
Qed.

Lemma Nmod_0_r: forall a : N, (a mod 0)%N = a.
Proof.
  intros; destruct a; reflexivity.
Qed.

Lemma wordToN_0: forall sz,
    wordToN (natToWord sz 0) = 0%N.
Proof.
  word_lia_Z.
Qed.

Lemma NToWord_0: forall sz,
    NToWord sz 0 = $ (0).
Proof.
  word_lia_Z.
Qed.

Lemma wmod_0_r: forall sz (a: word sz), a ^% $0 = a.
Proof.
  word_to_Z; word_mod_simpl; rewrite Z.mod_0_r; lia.
Qed.

Lemma wordToN_NToWord_eqn: forall sz (n : N),
    wordToN (NToWord sz n) = (n mod Npow2 sz)%N.
Proof.
  word_lia_Z.
Qed.

Lemma Nminus_mod_idemp_r: forall a b n : N,
    (n <> 0)%N ->
    (b <= a)%N ->
    ((a - b mod n) mod n)%N = ((a - b) mod n)%N.
Proof.
  intros. apply N2Z.inj. rewrite !N2Z.inj_mod, !N2Z.inj_sub, N2Z.inj_mod.
  - apply Zminus_mod_idemp_r.
  - lia.
  - pose proof (N.mod_le b n H). lia.
Qed.

Lemma drop_sub_N: forall sz (n k : N),
    (k * Npow2 sz <= n)%N ->
    NToWord sz (n - k * Npow2 sz) = NToWord sz n.
Proof.
  intros; word_to_Z. rewrite N2Z.inj_sub by lia. word_mod_simpl. rewrite N2Z.inj_mul, Npow2_Z.
  rewrite Zminus_mul_mod by lia. reflexivity.
Qed.


Lemma wmod_divides: forall sz (a b: word sz),
    a ^% b = $0 ->
    exists k, a = b ^* k.
Proof.
  intros; exists (wdiv a b).
  word_to_Z.
  match goal with H : (?a mod ?b)%Z = 0%Z |- _ =>
    destruct (Z.eq_dec b 0) as [E|E];
    [ rewrite E, Z.mod_0_r in H; rewrite E, Z.mul_0_l, Z.mod_0_l; lia
    | apply (Z.div_exact a b E) in H; rewrite <- H; symmetry; apply Z.mod_small; lia ]
  end.
Qed.

Lemma wmod_divides_other_direction_does_not_hold: ~ forall sz (a b: word sz),
    b <> $0 ->
    (exists k, a = b ^* k) ->
    a ^% b = $0.
Proof.
  intro C. specialize (C 4 $14 $5).
  match type of C with (?A -> _) =>
    assert A as H by (intro E; apply (f_equal (@Zmod.unsigned _)) in E; vm_compute in E; discriminate)
  end.
  specialize (C H).
  match type of C with (?A -> _) => assert A as B end.
  - exists (natToWord 4 6). apply unsigned_inj. vm_compute. reflexivity.
  - specialize (C B). apply (f_equal (@Zmod.unsigned _)) in C. vm_compute in C. discriminate.
Qed.

Lemma wmod_mul_does_not_hold: ~ forall sz (a b: word sz),
    b <> $0 ->
    (a ^* b) ^% b = $0.
Proof.
  intro C.
  specialize (C 4 $6 $5).
  match type of C with (?A -> _) =>
    assert A as H by (intro E; apply (f_equal (@Zmod.unsigned _)) in E; vm_compute in E; discriminate)
  end.
  specialize (C H).
  apply (f_equal (@Zmod.unsigned _)) in C. vm_compute in C. discriminate.
Qed.

Lemma wmult_plus_distr_l: forall (sz : nat) (x y z : word sz),
    z ^* (x ^+ y) = z ^* x ^+ z ^* y.
Proof.
  word_lia_Z.
Qed.

Lemma wmod_same: forall sz (a: word sz), a ^% a = $0.
Proof.
  word_to_Z.
  match goal with |- (?a mod ?a)%Z = _ =>
    destruct (Z.eq_dec a 0) as [E|E]; [rewrite E; reflexivity | rewrite Z.mod_same; lia]
  end.
Qed.

Lemma wmod_0_l: forall sz (m: word sz),
    $0 ^% m = $0.
Proof.
  word_to_Z.
  match goal with |- (0 mod ?a)%Z = _ =>
    destruct (Z.eq_dec a 0) as [E|E]; [rewrite E; reflexivity | rewrite Z.mod_0_l; lia]
  end.
Qed.

Lemma wmod_plus_distr: forall sz (a b m: word sz),
    (exists k, (wordToN m * k)%N = Npow2 sz) ->
    (a ^+ b) ^% m = ((a ^% m) ^+ (b ^% m)) ^% m.
Proof.
  intros sz a b m [k Hk]. word_to_Z.
  match goal with Hk : (Z.to_N ?um * ?k)%N = Npow2 ?sz |- _ =>
    assert (D : Z.divide um (2 ^ Z.of_nat sz)) by (exists (Z.of_N k); nia)
  end.
  rewrite !(Z.mod_mod_divide _ _ _ D). rewrite (Zplus_mod _ _). reflexivity.
Qed.

Lemma wmod_mul: forall sz (a b: word sz),
    (exists k, (wordToN b * k)%N = Npow2 sz) ->
    (a ^* b) ^% b = $0.
Proof.
  intros sz a b [k Hk]. word_to_Z.
  match goal with Hk : (Z.to_N ?ub * ?k)%N = Npow2 ?sz |- _ =>
    assert (D : Z.divide ub (2 ^ Z.of_nat sz)) by (exists (Z.of_N k); nia);
    assert (ub <> 0%Z) by (intro E; rewrite E in Hk; cbn in Hk; pose proof (Npow2_not_zero sz); lia)
  end.
  rewrite (Z.mod_mod_divide _ _ _ D). rewrite Z.mod_mul by assumption. reflexivity.
Qed.

Lemma combine_zero_general sz1 sz2:
  forall (w: word sz1) (b: word sz2), (combine w b = $ 0 -> w = $ 0 /\ b = $ 0)%word.
Proof.
  intros; split; word_to_Z; nia.
Qed.

Lemma combine_lt sz1 sz2:
  forall (w1 w2: word sz1) (b1 b2: word sz2), (combine w1 b1 < combine w2 b2 ->
                                               b1 <= b2)%word.
Proof.
  word_to_Z; nia.
Qed.

Lemma split2_le sz1 sz2:
  forall (w1 w2: word (sz1 + sz2)), (w1 <= w2 ->
                                     split2 _ _ w1 <= split2 _ _ w2)%word.
Proof.
  intros; apply le_wle; rewrite !wordToNat_split2; apply Nat.div_le_mono;
    [pose proof (pow2_zero sz1); lia | apply wle_le; assumption].
Qed.

Lemma word1_neq': forall w : word 1, w <> WO~1 -> w = WO~0.
Proof.
  word_lia_Z.
Qed.

Lemma combine_ge sz1 sz2 (x1 y1: word sz1) (x2 y2: word sz2):
  (combine x1 x2 <= combine y1 y2 ->
   x2 < y2 \/ (x2 = y2 /\ x1 <= y1))%word.
Proof.
  intros; destruct (weq x2 y2); subst.
  - right; split; [reflexivity|]; word_to_Z; nia.
  - left; word_to_Z; nia.
Qed.
