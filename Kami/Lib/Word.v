(** Fixed precision machine words *)

Require Import Arith Div2 NArith Bool Omega.
Require Import Lib.Nomega Lib.NatLib.
Require Import Eqdep_dec.

Set Implicit Arguments.

(** * Basic definitions and conversion to and from [nat] *)

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall n, word n -> word (S n).

Fixpoint wordToNat sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => (wordToNat w') * 2
    | WS true w' => S (wordToNat w' * 2)
  end.

Fixpoint wordToNat' sz (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w' => 2 * wordToNat w'
    | WS true w' => S (2 * wordToNat w')
  end.

Theorem wordToNat_wordToNat' : forall sz (w : word sz),
  wordToNat w = wordToNat' w.
Proof.
  induction w. auto. simpl. rewrite mult_comm. reflexivity.
Qed.

Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.

Fixpoint wordToN sz (w : word sz) : N :=
  match w with
    | WO => 0
    | WS false w' => 2 * wordToN w'
    | WS true w' => Nsucc (2 * wordToN w')
  end%N.

Definition Nmod2 (n : N) : bool :=
  match n with
    | N0 => false
    | Npos (xO _) => false
    | _ => true
  end.

Definition wzero sz := natToWord sz 0.

Fixpoint wzero' (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS false (wzero' sz')
  end.

Fixpoint posToWord (sz : nat) (p : positive) {struct p} : word sz :=
  match sz with
    | O => WO
    | S sz' =>
      match p with
        | xI p' => WS true (posToWord sz' p')
        | xO p' => WS false (posToWord sz' p')
        | xH => WS true (wzero' sz')
      end
  end.

Definition NToWord (sz : nat) (n : N) : word sz :=
  match n with
    | N0 => wzero' sz
    | Npos p => posToWord sz p
  end.

Fixpoint Npow2 (n : nat) : N :=
  match n with
    | O => 1
    | S n' => 2 * Npow2 n'
  end%N.

Hint Rewrite div2_double div2_S_double : div2.
Local Hint Resolve mod2_S_double mod2_double.

Theorem natToWord_wordToNat : forall sz w, natToWord sz (wordToNat w) = w.
  induction w; rewrite wordToNat_wordToNat'; intuition; f_equal; unfold natToWord, wordToNat'; fold natToWord; fold wordToNat';
    destruct b; f_equal; autorewrite with div2; intuition.
Qed.

Theorem roundTrip_0 : forall sz, wordToNat (natToWord sz 0) = 0.
  induction sz; simpl; intuition.
Qed.

Hint Rewrite roundTrip_0 : wordToNat.

Local Hint Extern 1 (@eq nat _ _) => omega.

Lemma wordToNat_natToWord' : forall sz w, exists k, wordToNat (natToWord sz w) + k * pow2 sz = w.
  induction sz; simpl; intuition; repeat rewrite untimes2.

  exists w; intuition.

  case_eq (mod2 w); intro Hmw.

  specialize (IHsz (div2 w)); firstorder.
  rewrite wordToNat_wordToNat' in *. 
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite mult_comm. simpl mult at 1.
  rewrite (plus_Sn_m (2 * wordToNat' (natToWord sz (div2 w)))).
  rewrite <- mult_assoc.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_odd; auto.
  
  specialize (IHsz (div2 w)); firstorder.
  exists x; intuition.
  rewrite mult_assoc.
  rewrite (mult_comm x 2).
  rewrite <- mult_assoc.
  rewrite mult_comm.
  rewrite <- mult_plus_distr_l.
  rewrite H; clear H.
  symmetry; apply div2_even; auto.
Qed.

Theorem wordToNat_natToWord : forall sz w,
    exists k, wordToNat (natToWord sz w) = w - k * pow2 sz /\ k * pow2 sz <= w.
  intros; destruct (wordToNat_natToWord' sz w) as [k]; exists k; intuition.
Qed.

Lemma wordToNat_natToWord_2: forall sz w : nat,
    (w < pow2 sz)%nat -> wordToNat (natToWord sz w) = w.
Proof.
  intros.
  pose proof (wordToNat_natToWord sz w).
  destruct H0; destruct H0.
  rewrite H0 in *; clear H0.
  destruct x; try omega.
  exfalso; simpl in H1.

  pose proof (Lt.le_lt_trans _ _ _ H1 H).
  pose proof (Plus.le_plus_l (pow2 sz) (x * pow2 sz)).
  pose proof (Lt.le_lt_trans _ _ _ H2 H0).
  omega.
Qed.

Definition wone sz := natToWord sz 1.

Fixpoint wones (sz : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS true (wones sz')
  end.


(** Comparisons *)

Fixpoint wmsb sz (w : word sz) (a : bool) : bool :=
  match w with
    | WO => a
    | WS b x => wmsb x b
  end.

(* head of a word with at least 1 bit *)
Definition whd sz (w : word (S sz)) : bool :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S _ => bool
                             end with
    | WO => tt
    | WS b _ => b
  end.

(* tail of a word with at least 1 bit *)
Definition wtl sz (w : word (S sz)) : word sz :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S sz'' => word sz''
                             end with
    | WO => tt
    | WS _ w' => w'
  end.

Theorem WS_neq : forall b1 b2 sz (w1 w2 : word sz),
  (b1 <> b2 \/ w1 <> w2)
  -> WS b1 w1 <> WS b2 w2.
  intuition.
  apply (f_equal (@whd _)) in H0; tauto.
  apply (f_equal (@wtl _)) in H0; tauto.
Qed.

Fixpoint rep_bit (n : nat) (b : word 1) : word n :=
  match n as n0 return (word n0) with
  | 0 => WO
  | S n0 => WS (whd b) (rep_bit n0 b)
  end.


(** Shattering **)

Lemma shatter_word : forall n (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.
  destruct a; eauto.
Qed.

Lemma shatter_word_S : forall n (a : word (S n)),
  exists b, exists c, a = WS b c.
Proof.
  intros; repeat eexists; apply (shatter_word a).
Qed.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.
Proof.
  intros; apply (shatter_word a).
Qed.

Hint Resolve shatter_word_0.

Theorem word0: forall (w : word 0), w = WO.
Proof.
  firstorder.
Qed.

Definition weq : forall sz (x y : word sz), {x = y} + {x <> y}.
  refine (fix weq sz (x : word sz) : forall y : word sz, {x = y} + {x <> y} :=
    match x in word sz return forall y : word sz, {x = y} + {x <> y} with
      | WO => fun _ => left _ _
      | WS b x' => fun y => if bool_dec b (whd y)
        then if weq _ x' (wtl y) then left _ _ else right _ _
        else right _ _
    end); clear weq.

  abstract (symmetry; apply shatter_word_0).

  abstract (subst; symmetry; apply (shatter_word y)).

  abstract (rewrite (shatter_word y); intro; injection H; intros; apply inj_pair2_eq_dec in H0; [ auto | apply eq_nat_dec]).

  abstract (rewrite (shatter_word y); simpl; intro; injection H; auto).
Defined.

Fixpoint weqb sz (x : word sz) : word sz -> bool :=
  match x in word sz return word sz -> bool with
    | WO => fun _ => true
    | WS b x' => fun y => 
      if eqb b (whd y)
      then if @weqb _ x' (wtl y) then true else false
      else false
  end.

Theorem weqb_true_iff : forall sz x y,
  @weqb sz x y = true <-> x = y.
Proof.
  induction x; simpl; intros.
  { split; auto. }
  { rewrite (shatter_word y) in *. simpl in *.
    case_eq (eqb b (whd y)); intros.
    case_eq (weqb x (wtl y)); intros.
    split; auto; intros. rewrite eqb_true_iff in H. f_equal; eauto. eapply IHx; eauto.
    split; intros; try congruence. inversion H1; clear H1; subst.
    eapply inj_pair2_eq_dec in H4. eapply IHx in H4. congruence.
    eapply Peano_dec.eq_nat_dec.
    split; intros; try congruence.
    inversion H0. apply eqb_false_iff in H. congruence. }
Qed.

(** * Dependent type helpers *)

Theorem eq_rect_nat_double : forall T (a b c : nat) x ab bc,
  eq_rect b T (eq_rect a T x b ab) c bc = eq_rect a T x c (eq_trans ab bc).
Proof.
  intros.
  destruct ab.
  destruct bc.
  rewrite (UIP_dec eq_nat_dec (eq_trans eq_refl eq_refl) eq_refl).
  simpl.
  auto.
Qed.

Hint Rewrite eq_rect_nat_double.
Hint Rewrite <- (eq_rect_eq_dec eq_nat_dec).

Ltac generalize_proof :=
    match goal with
    | [ |- context[eq_rect _ _ _ _ ?H ] ] => generalize H
    end.

Ltac eq_rect_simpl :=
  unfold eq_rec_r, eq_rec;
  repeat rewrite eq_rect_nat_double;
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).

Lemma eq_rect_word_offset_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; congruence.
Qed.

Theorem eq_rect_word_offset : forall n n' offset w Heq,
  eq_rect n (fun n => word (offset + n)) w n' Heq =
  eq_rect (offset + n) (fun n => word n) w (offset + n') (eq_rect_word_offset_helper _ Heq).
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_offset_helper offset eq_refl) eq_refl).
  reflexivity.
Qed.

Lemma eq_rect_word_mult_helper : forall a b c,
  a = b -> a * c = b * c.
Proof.
  intros; congruence.
Qed.

Theorem eq_rect_word_mult : forall n n' scale w Heq,
  eq_rect n (fun n => word (n * scale)) w n' Heq =
  eq_rect (n * scale) (fun n => word n) w (n' * scale) (eq_rect_word_mult_helper _ Heq).
Proof.
  intros.
  destruct Heq.
  rewrite (UIP_dec eq_nat_dec (eq_rect_word_mult_helper scale eq_refl) eq_refl).
  reflexivity.
Qed.

Theorem eq_rect_word_match : forall n n' (w : word n) (H : n = n'),
  match H in (_ = N) return (word N) with
  | eq_refl => w
  end = eq_rect n (fun n => word n) w n' H.
Proof.
  intros.
  destruct H.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem whd_match : forall n n' (w : word (S n)) (Heq : S n = S n'),
  whd w = whd (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
  intros.
  rewrite eq_rect_word_match.
  generalize dependent w.
  remember Heq as Heq'. clear HeqHeq'.
  generalize dependent Heq'.
  replace (n') with (n) by omega.
  intros. rewrite <- (eq_rect_eq_dec eq_nat_dec). reflexivity.
Qed.

Theorem wtl_match : forall n n' (w : word (S n)) (Heq : S n = S n') (Heq' : n = n'),
  (match Heq' in (_ = N) return (word N) with
   | eq_refl => wtl w
   end) = wtl (match Heq in (_ = N) return (word N) with
               | eq_refl => w
               end).
Proof.
  intros.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  generalize dependent w; clear.
  intros.
  generalize Heq Heq'.
  subst.
  intros.
  rewrite (UIP_dec eq_nat_dec Heq' (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Lemma whd_eq_rect : forall n w Heq,
  whd (eq_rect (S n) word w (S (n + 0)) Heq) =
  whd w.
Proof.
  intros.
  generalize Heq.
  replace (n + 0) with n by omega.
  intros.
  f_equal.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma wtl_eq_rect : forall n w Heq Heq',
  wtl (eq_rect (S n) word w (S (n + 0)) Heq) =
  eq_rect n word (wtl w) (n + 0) Heq'.
Proof.
  intros.
  generalize dependent Heq.
  rewrite <- Heq'; simpl; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma whd_eq_rect_mul : forall n w Heq,
  whd (eq_rect (S n) word w (S (n * 1)) Heq) =
  whd w.
Proof.
  intros.
  generalize Heq.
  replace (n * 1) with n by auto.
  intros.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma wtl_eq_rect_mul : forall n w b Heq Heq',
  wtl (eq_rect (S n) word (WS b w) (S (n * 1)) Heq) =
  eq_rect _ word w _ Heq'.
Proof.
  intros.
  generalize Heq.
  rewrite <- Heq'.
  intros. eq_rect_simpl.
  reflexivity.
Qed.

(** * Combining and splitting *)

Fixpoint combine (sz1 : nat) (w : word sz1) : forall sz2, word sz2 -> word (sz1 + sz2) :=
  match w in word sz1 return forall sz2, word sz2 -> word (sz1 + sz2) with
    | WO => fun _ w' => w'
    | WS b w' => fun _ w'' => WS b (combine w' w'')
  end.

Fixpoint split1 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz1 :=
  match sz1 with
    | O => fun _ => WO
    | S sz1' => fun w => WS (whd w) (split1 sz1' sz2 (wtl w))
  end.

Fixpoint split2 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz2 :=
  match sz1 with
    | O => fun w => w
    | S sz1' => fun w => split2 sz1' sz2 (wtl w)
  end.

Ltac shatterer := simpl; intuition;
  match goal with
    | [ w : _ |- _ ] => rewrite (shatter_word w); simpl
  end; f_equal; auto.

Theorem split1_0 : forall n w Heq,
  split1 n 0 (eq_rect _ word w _ Heq) = w.
Proof.
  intros.
  induction n; intros.
  shatterer.
  simpl.
  erewrite wtl_eq_rect.
  rewrite IHn.
  rewrite whd_eq_rect.
  simpl.
  shatterer.

  Grab Existential Variables.
  omega.
Qed.

Theorem split2_0 : forall n w Heq,
  split2 0 n (eq_rect _ word w _ Heq) = w.
Proof.
  intros.
  simpl.
  eq_rect_simpl.
  reflexivity.
Qed.

Theorem combine_split : forall sz1 sz2 (w : word (sz1 + sz2)),
  combine (split1 sz1 sz2 w) (split2 sz1 sz2 w) = w.
Proof.
  induction sz1; shatterer.
Qed.

Theorem split1_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split1 sz1 sz2 (combine w z) = w.
Proof.
  induction sz1; shatterer.
Qed.

Theorem split2_combine : forall sz1 sz2 (w : word sz1) (z : word sz2),
  split2 sz1 sz2 (combine w z) = z.
Proof.
  induction sz1; shatterer.
Qed.

Theorem combine_assoc : forall n1 (w1 : word n1) n2 n3 (w2 : word n2) (w3 : word n3) Heq,
  combine (combine w1 w2) w3
  = match Heq in _ = N return word N with
      | refl_equal => combine w1 (combine w2 w3)
    end.
Proof.
  induction w1; simpl; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHw1 _ _ _ _ (plus_assoc _ _ _)); clear IHw1.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.  
  generalize dependent (combine w1 (combine w2 w3)).
  rewrite plus_assoc; intros.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem split2_iter : forall n1 n2 n3 Heq w,
  split2 n2 n3 (split2 n1 (n2 + n3) w)
  = split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                           | refl_equal => w
                         end).
Proof.
  induction n1; simpl; intuition.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)); reflexivity.

  rewrite (IHn1 _ _ (plus_assoc _ _ _)).
  f_equal.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  generalize dependent w.
  simpl.
  fold plus.
  generalize (n1 + (n2 + n3)); clear.
  intros.
  generalize Heq e.
  subst.
  intros.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem combine_end : forall n1 n2 n3 Heq w,
  combine (split1 n2 n3 (split2 n1 (n2 + n3) w))
  (split2 (n1 + n2) n3 (match Heq in _ = N return word N with
                          | refl_equal => w
                        end))
  = split2 n1 (n2 + n3) w.
Proof.
  induction n1; simpl; intros.

  rewrite (UIP_dec eq_nat_dec Heq (refl_equal _)).
  apply combine_split.

  rewrite (shatter_word w) in *.
  simpl.
  eapply trans_eq; [ | apply IHn1 with (Heq := plus_assoc _ _ _) ]; clear IHn1.
  repeat f_equal.
  repeat match goal with
           | [ |- context[match ?pf with refl_equal => _ end] ] => generalize pf
         end.
  simpl.
  generalize dependent w.
  rewrite plus_assoc.
  intros.
  rewrite (UIP_dec eq_nat_dec e (refl_equal _)).
  rewrite (UIP_dec eq_nat_dec Heq0 (refl_equal _)).
  reflexivity.
Qed.

Theorem combine_0_n : forall sz2 (w: word 0) (v: word sz2),
  combine w v = v.
Proof.
  intros.
  replace w with WO.
  auto.
  rewrite word0; auto.
Qed.

Lemma WS_eq_rect : forall b n (w: word n) n' H H',
  eq_rect _ word (@WS b n w) _ H = @WS b n' (eq_rect _ word w _ H').
Proof.
  destruct n; intros; subst;
    eq_rect_simpl; auto.
Qed.

Theorem combine_n_0 : forall sz1 (w : word sz1) (v : word 0),
  combine w v = eq_rect _ word w _ (plus_n_O sz1).
Proof.
  induction w; intros.
  - replace v with WO; auto.
  - simpl; rewrite IHw.
    erewrite WS_eq_rect.
    reflexivity.
Qed.

Theorem combine_wzero : forall sz1 sz2, combine (wzero sz1) (wzero sz2) = wzero (sz1 + sz2).
Proof.
  induction sz1; auto.
  unfold wzero in *.
  intros; simpl; f_equal; auto.
Qed.

Theorem combine_wones : forall sz1 sz2, combine (wones sz1) (wones sz2) = wones (sz1 + sz2).
Proof.
  induction sz1; auto.
  intros; simpl; f_equal; auto.
Qed.

Theorem eq_rect_combine : forall n1 n2 n2' (w1 : word n1) (w2 : word n2') Heq,
  eq_rect (n1 + n2') (fun n => word n)
    (combine w1 w2) (n1 + n2) Heq =
  combine w1 (eq_rect n2' (fun n => word n) w2 n2 (plus_reg_l _ _ _ Heq)).
Proof.
  intros.
  generalize (plus_reg_l n2' n2 n1 Heq); intros.
  generalize dependent Heq.
  generalize dependent w2.
  rewrite e; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.


Lemma eq_rect_combine_assoc' : forall a b c H wa wb wc,
  eq_rect (a + (b + c)) word (combine wa (combine wb wc)) _ H = combine (combine wa wb) wc.
Proof.
  intros.
  erewrite combine_assoc, eq_rect_word_match.
  reflexivity.
Qed.

Lemma eq_rect_split2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; omega.
Qed.

Theorem eq_rect_split2 : forall n1 n2 n2' (w : word (n1 + n2')) Heq,
  eq_rect n2' (fun n => word n)
    (split2 n1 n2' w) n2 Heq =
  split2 n1 n2 (eq_rect (n1+n2') (fun n => word n) w (n1+n2) (eq_rect_split2_helper _ Heq)).
Proof.
  intros.
  generalize (eq_rect_split2_helper n1 Heq); intros.
  generalize dependent Heq.
  generalize dependent w.
  assert (n2' = n2) as H' by omega.
  generalize dependent e.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem eq_rect_split2_eq2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq Heq2,
  eq_rect n2 (fun n => word n)
    (split2 n1 n2 w) n2' Heq =
  split2 n1 n2' (eq_rect (n1+n2) (fun n => word n) w (n1+n2') Heq2).
Proof.
  intros.
  assert (H' := Heq).
  generalize dependent w.
  generalize dependent Heq.
  generalize dependent Heq2.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem eq_rect_split2_eq1 : forall n1 n1' n2 (w: word (n1 + n2)) Heq,
     split2 n1 n2 w = split2 n1' n2
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1' + n2) Heq).
Proof.
  intros.
  assert (n1 = n1') as H' by omega.
  generalize dependent w.
  generalize dependent Heq.
  rewrite H'; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem combine_split_eq_rect2 : forall n1 n2 n2' (w : word (n1 + n2)) Heq,
  combine (split1 n1 n2 w)
          (eq_rect n2 (fun n => word n) (split2 n1 n2 w)
                   n2' Heq) =
  eq_rect (n1 + n2) (fun n => word n) w
          (n1 + n2') (eq_rect_split2_helper _ Heq).
Proof.
  intros.
  assert (n2 = n2') by omega.
  generalize dependent Heq.
  generalize dependent w.
  rewrite <- H; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  apply combine_split.
Qed.

Lemma eq_rect_split1_helper : forall a b c,
  a = b -> a + c = b + c.
Proof.
  intros; omega.
Qed.

Lemma eq_rect_split1_eq2_helper : forall a b c,
  a = b -> c + a = c + b.
Proof.
  intros; omega.
Qed.

Theorem eq_rect_split1 : forall n1 n1' n2 (w : word (n1' + n2)) Heq,
  eq_rect n1' (fun n => word n)
    (split1 n1' n2 w) n1 Heq =
  split1 n1 n2 (eq_rect (n1'+n2) (fun n => word n) w (n1+n2) (eq_rect_split1_helper _ Heq)).
Proof.
  intros.
  generalize (eq_rect_split1_helper n2 Heq); intros.
  generalize dependent Heq.
  generalize dependent w.
  assert (n1' = n1) as H' by omega.
  generalize dependent e.
  rewrite H'; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem eq_rect_split1_eq1 : forall n1 n1' n2 (w : word (n1 + n2)) Heq Heq1,
  eq_rect n1 (fun n => word n)
    (split1 n1 n2 w) n1' Heq =
  split1 n1' n2 (eq_rect (n1+n2) (fun n => word n) w (n1'+n2) Heq1).
Proof.
  intros.
  generalize dependent w.
  generalize dependent Heq1.
  rewrite Heq; intros.
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma split1_eq_rect_eq1_helper : forall a b c, b = a -> a + c = b + c.
Proof. intros. subst. reflexivity. Qed.

Theorem split1_eq_rect_eq1 : forall a a' b H w,
  split1 a b w = eq_rect _ word (split1 a' b
    (eq_rect _ word w _ (split1_eq_rect_eq1_helper b H))) _ H.
Proof.
  intros a a' b H.
  subst a'; intros; eq_rect_simpl; auto.
Qed.

Theorem eq_rect_split1_eq2 : forall n1 n2 n2' (w: word (n1 + n2)) Heq,
     split1 n1 n2 w = split1 n1 n2'
        (eq_rect (n1 + n2) (fun y : nat => word y) w
     (n1 + n2') Heq).
Proof.
  intros.
  assert (n2 = n2') as H' by omega.
  generalize dependent w.
  generalize dependent Heq.
  rewrite H'; intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Fact eq_rect_combine_dist_helper1 : forall a b c d, b * c = d -> (a + b) * c = a * c + d.
Proof. intros; subst. apply Nat.mul_add_distr_r. Qed.

Fact eq_rect_combine_dist_helper2 : forall a b c d, b * c = d -> a * c + d = (a + b) * c.
Proof. intros; subst. symmetry; apply Nat.mul_add_distr_r. Qed.

Theorem eq_rect_combine_dist : forall a b c d (w : word ((a + b) * c)) (H : b * c = d),
  b * c = d ->
  let H1 := (eq_rect_combine_dist_helper1 a b c H) in
  let H2 := (eq_rect_combine_dist_helper2 a b c H) in
  let w' := eq_rec ((a + b) * c) word w _ H1 in
  w = eq_rec _ word (combine (split1 (a * c) d w') (split2 (a * c) d w')) _ H2.
Proof.
  intros.
  subst d.
  rewrite combine_split.
  eq_rect_simpl.
  generalize dependent w.
  generalize dependent H2.
  rewrite H1.
  intros.
  eq_rect_simpl; auto.
Qed.

Lemma wzero_dist : forall a b c H,
  wzero ((a + b) * c) = eq_rect _ word (wzero (a * c + b * c)) _ H.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Lemma wzero_rev : forall (a b : nat) H,
   wzero (a + b) = eq_rect _ word (wzero (b + a)) _ H.
Proof. intros a b H. rewrite H. auto. Qed.

Lemma split1_zero : forall sz1 sz2, split1 sz1 sz2 (natToWord _ O) = natToWord _ O.
Proof.
  induction sz1; auto; simpl; intros.
  f_equal. eauto.
Qed.

Lemma split2_zero : forall sz1 sz2, split2 sz1 sz2 (natToWord _ O) = natToWord _ O.
Proof.
  induction sz1; auto.
Qed.

Theorem combine_inj : forall sz1 sz2 a b c d,
  @combine sz1 a sz2 b = @combine sz1 c sz2 d -> a = c /\ b = d.
Proof.
  induction sz1; simpl; intros.
  - rewrite (word0 a) in *.
    rewrite (word0 c) in *.
    simpl in *.
    intuition.
  - rewrite (shatter_word a) in *.
    rewrite (shatter_word c) in *.
    simpl in *.
    inversion H.
    apply (inj_pair2_eq_dec _ eq_nat_dec) in H2.
    destruct (IHsz1 _ _ _ _ _ H2).
    intuition.
    f_equal; auto.
Qed.


(** * Extension operators *)

Definition sext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  if wmsb w false then
    combine w (wones sz')
  else 
    combine w (wzero sz').

Definition zext (sz : nat) (w : word sz) (sz' : nat) : word (sz + sz') :=
  combine w (wzero sz').


(** * Shift operators *)

Lemma sz_minus_nshift : forall sz nshift, (nshift < sz)%nat -> sz = sz - nshift + nshift.
Proof.
  intros; omega.
Qed.

Lemma nshift_plus_nkeep : forall sz nshift, (nshift < sz)%nat -> nshift + (sz - nshift) = sz.
Proof.
  intros; omega.
Qed.

Definition wlshift (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split1 sz n _).
  rewrite plus_comm.
  exact (combine (wzero n) w).
Defined.

Definition wrshift (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split2 n sz _).
  rewrite plus_comm.
  exact (combine w (wzero n)).
Defined.

Definition wrshifta (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split2 n sz _).
  rewrite plus_comm.
  exact (sext w _).
Defined.

Theorem wlshift_0 : forall sz (w : word sz), @wlshift sz w 0 = w.
Proof.
  intros.
  unfold wlshift.
  eapply split1_0.
Qed.

Theorem wrshift_0 : forall sz (w : word sz), @wrshift sz w 0 = w.
Proof.
  intros.
  unfold wrshift.
  simpl.
  rewrite combine_n_0.
  eq_rect_simpl. reflexivity.
Qed.

Theorem wlshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wlshift w n = wzero sz.
Proof.
  intros sz n w H.
  generalize dependent w.
  remember (n - sz) as e.
  assert (n = sz + e) by omega; subst n.
  intros w.
  unfold wlshift.
  rewrite <- combine_wzero.
  erewrite combine_assoc, eq_rect_word_match.
  eq_rect_simpl.
  rewrite eq_rect_combine.
  apply split1_combine.
  Grab Existential Variables. omega.
Qed.

Theorem wrshift_gt : forall sz n (w : word sz), (n > sz)%nat ->
  wrshift w n = wzero sz.
Proof.
  intros sz n w H.
  generalize dependent w.
  remember (n - sz) as e.
  assert (n = sz + e) by omega; subst n.
  intros w.
  unfold wrshift.
  erewrite wzero_rev, <- combine_wzero.
  eq_rect_simpl.
  rewrite <- eq_rect_word_match, <- eq_rect_combine, eq_rect_word_match.
  eq_rect_simpl.
  rewrite eq_rect_combine_assoc', split2_combine.
  reflexivity.
  Grab Existential Variables. omega.
Qed.

(** * Arithmetic (unsigned) *)

Definition wneg sz (x : word sz) : word sz :=
  NToWord sz (Npow2 sz - wordToN x).
Definition wordBin (f : N -> N -> N) sz (x y : word sz) : word sz :=
  NToWord sz (f (wordToN x) (wordToN y)).
Definition wplus := wordBin Nplus.
Definition wminus sz (x y : word sz) : word sz := wplus x (wneg y).
Definition wmult := wordBin Nmult.
Definition wmult' sz (x y : word sz) : word sz := 
  split2 sz sz (NToWord (sz + sz) (Nmult (wordToN x) (wordToN y))).
Definition wdiv := wordBin Ndiv.
Definition wrem := wordBin Nmod.

Definition wnegN sz (x : word sz) : word sz :=
  natToWord sz (pow2 sz - wordToNat x).
Definition wordBinN (f : nat -> nat -> nat) sz (x y : word sz) : word sz :=
  natToWord sz (f (wordToNat x) (wordToNat y)).
Definition wplusN := wordBinN plus.
Definition wminusN sz (x y : word sz) : word sz := wplusN x (wnegN y).
Definition wmultN := wordBinN mult.
Definition wmultN' sz (x y : word sz) : word sz := 
  split2 sz sz (natToWord (sz + sz) (mult (wordToNat x) (wordToNat y))).
Definition wdivN := wordBinN Nat.div.
Definition wremN := wordBinN Nat.modulo.

(** * Arithmetic (signed) *)
Definition wordToZ sz (w : word sz) : Z :=
  if wmsb w false then
    (** Negative **)
    match wordToN (wneg w) with
    | N0 => 0%Z
    | Npos x => Zneg x
    end
  else 
    (** Positive **)
    match wordToN w with
    | N0 => 0%Z
    | Npos x => Zpos x
    end.

Definition ZToWord (sz : nat) (z : Z) : word sz :=
  match z with
  | Z0 => wzero' sz
  | Zpos x => posToWord sz x
  | Zneg x => wneg (posToWord sz x)
  end.

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

(** * Notations *)

Delimit Scope word_scope with word.
Bind Scope word_scope with word.

Notation "w ~ 1" :=
  (WS true w) (at level 7, left associativity, format "w '~' '1'") : word_scope.
Notation "w ~ 0" :=
  (WS false w) (at level 7, left associativity, format "w '~' '0'") : word_scope.

Notation "^~" := wneg.
Notation "l ^+ r" := (@wplus _ l%word r%word) (at level 50, left associativity).
Notation "l ^* r" := (@wmult _ l%word r%word) (at level 40, left associativity).
Notation "l ^- r" := (@wminus _ l%word r%word) (at level 50, left associativity).
Notation "l ^<< r" := (@wlshift _ _ l%word r%word) (at level 35).
Notation "l ^>> r" := (@wrshift _ _ l%word r%word) (at level 35).
Notation "l ^~>> r" := (@wrshifta _ _ l%word r%word) (at level 35).

Theorem wordToN_nat : forall sz (w : word sz), wordToN w = N_of_nat (wordToNat w).
  induction w; intuition.
  destruct b; unfold wordToN, wordToNat; fold wordToN; fold wordToNat.

  rewrite N_of_S.
  rewrite N_of_mult.
  rewrite <- IHw. 
  rewrite Nmult_comm.
  reflexivity.

  rewrite N_of_mult.
  rewrite <- IHw.
  rewrite Nmult_comm.
  reflexivity.
Qed.

Theorem mod2_S : forall n k,
  2 * k = S n
  -> mod2 n = true.
  induction n using strong; intros.
  destruct n; simpl in *.
  elimtype False; omega.
  destruct n; simpl in *; auto.
  destruct k; simpl in *.
  discriminate.
  apply H with k; auto.
Qed.

Theorem wzero'_def : forall sz, wzero' sz = wzero sz.
  unfold wzero; induction sz; simpl; intuition.
  congruence.
Qed.

Theorem posToWord_nat : forall p sz, posToWord sz p = natToWord sz (nat_of_P p).
  induction p; destruct sz; simpl; intuition; f_equal; try rewrite wzero'_def in *.
  
  rewrite ZL6.
  destruct (ZL4 p) as [? Heq]; rewrite Heq; simpl.
  replace (x + S x) with (S (2 * x)) by omega.
  symmetry; apply mod2_S_double.

  rewrite IHp.
  rewrite ZL6.
  destruct (nat_of_P p); simpl; intuition.
  replace (n + S n) with (S (2 * n)) by omega.
  rewrite div2_S_double; auto.

  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  symmetry; apply mod2_double.

  rewrite IHp.
  unfold nat_of_P; simpl.
  rewrite ZL6.
  replace (nat_of_P p + nat_of_P p) with (2 * nat_of_P p) by omega.
  rewrite div2_double.
  auto.
  auto.
Qed.

Theorem NToWord_nat : forall sz n, NToWord sz n = natToWord sz (nat_of_N n).
  destruct n; simpl; intuition; try rewrite wzero'_def in *.
  auto.
  apply posToWord_nat.
Qed.

Theorem wplus_alt : forall sz (x y : word sz), wplus x y = wplusN x y.
  unfold wplusN, wplus, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.

Theorem wmult_alt : forall sz (x y : word sz), wmult x y = wmultN x y.
  unfold wmultN, wmult, wordBinN, wordBin; intros.

  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nmult.
  repeat rewrite nat_of_N_of_nat.
  reflexivity.
Qed.

Lemma pow2_zero: forall sz, (pow2 sz > 0)%nat.
Proof.
  induction sz; simpl; auto; omega.
Qed.

Theorem Npow2_nat : forall n, nat_of_N (Npow2 n) = pow2 n.
  induction n; simpl; intuition.
  rewrite <- IHn; clear IHn.
  case_eq (Npow2 n); intuition.
  rewrite untimes2.
  replace (Npos p~0) with (Ndouble (Npos p)) by reflexivity.
  apply nat_of_Ndouble.
Qed.

Theorem wneg_alt : forall sz (x : word sz), wneg x = wnegN x.
  unfold wnegN, wneg; intros.
  repeat rewrite wordToN_nat; repeat rewrite NToWord_nat.
  rewrite nat_of_Nminus.
  do 2 f_equal.
  apply Npow2_nat.
  apply nat_of_N_of_nat.
Qed.

Theorem wminus_Alt : forall sz (x y : word sz), wminus x y = wminusN x y.
  intros; unfold wminusN, wminus; rewrite wneg_alt; apply wplus_alt.
Qed.

Theorem wplus_unit : forall sz (x : word sz), natToWord sz 0 ^+ x = x.
  intros; rewrite wplus_alt; unfold wplusN, wordBinN; intros.
  rewrite roundTrip_0; apply natToWord_wordToNat.
Qed.

Theorem wplus_comm : forall sz (x y : word sz), x ^+ y = y ^+ x.
  intros; repeat rewrite wplus_alt; unfold wplusN, wordBinN; f_equal; auto.
Qed.

Theorem drop_sub : forall sz n k,
  k * pow2 sz <= n
  -> natToWord sz (n - k * pow2 sz) = natToWord sz n.
  induction sz; simpl; intuition; repeat rewrite untimes2 in *; f_equal.

  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  apply drop_mod2.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.

  rewrite <- (IHsz (div2 n) k).
  rewrite mult_assoc.
  rewrite (mult_comm k).
  rewrite <- mult_assoc.
  rewrite div2_minus_2.
  reflexivity.  
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.
  
  apply div2_bound.
  rewrite mult_assoc.
  rewrite (mult_comm 2).
  rewrite <- mult_assoc.
  auto.
Qed.

Local Hint Extern 1 (_ <= _) => omega.

Theorem wplus_assoc : forall sz (x y z : word sz), x ^+ (y ^+ z) = x ^+ y ^+ z.
  intros; repeat rewrite wplus_alt; unfold wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  replace (wordToNat x + wordToNat y - x1 * pow2 sz + wordToNat z)
    with (wordToNat x + wordToNat y + wordToNat z - x1 * pow2 sz) by auto.
  replace (wordToNat x + (wordToNat y + wordToNat z - x0 * pow2 sz))
    with (wordToNat x + wordToNat y + wordToNat z - x0 * pow2 sz) by auto.
  repeat rewrite drop_sub; auto.
Qed.

Theorem roundTrip_1 : forall sz, wordToNat (natToWord (S sz) 1) = 1.
  induction sz; simpl in *; intuition.
Qed.

Theorem mod2_WS : forall sz (x : word sz) b, mod2 (wordToNat (WS b x)) = b.
  intros. rewrite wordToNat_wordToNat'.
  destruct b; simpl.

  rewrite untimes2.
  case_eq (2 * wordToNat x); intuition.
  eapply mod2_S; eauto.
  rewrite <- (mod2_double (wordToNat x)); f_equal; omega.
Qed.

Theorem div2_WS : forall sz (x : word sz) b, div2 (wordToNat (WS b x)) = wordToNat x.
  destruct b; rewrite wordToNat_wordToNat'; unfold wordToNat'; fold wordToNat'.
  apply div2_S_double.
  apply div2_double.
Qed.

Theorem wmult_unit : forall sz (x : word sz), natToWord sz 1 ^* x = x.
  intros; rewrite wmult_alt; unfold wmultN, wordBinN; intros.
  destruct sz; simpl.
  rewrite (shatter_word x); reflexivity.
  rewrite roundTrip_0; simpl.
  rewrite plus_0_r.
  rewrite (shatter_word x).
  f_equal.

  apply mod2_WS.

  rewrite div2_WS.
  apply natToWord_wordToNat.
Qed.

Theorem wmult_comm : forall sz (x y : word sz), x ^* y = y ^* x.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; auto with arith.
Qed.

Theorem wmult_assoc : forall sz (x y z : word sz), x ^* (y ^* z) = x ^* y ^* z.
  intros; repeat rewrite wmult_alt; unfold wmultN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_l.
  rewrite mult_minus_distr_r.
  rewrite (mult_assoc (wordToNat x) x0).
  rewrite <- (mult_assoc x1).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x1).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x1).
  rewrite <- (mult_assoc (wordToNat x)).
  rewrite (mult_comm (wordToNat y)).
  rewrite mult_assoc.
  rewrite (mult_comm (wordToNat x)).
  repeat rewrite <- mult_assoc.
  auto with arith.
  repeat rewrite <- mult_assoc.
  auto with arith.
Qed.

Theorem wmult_plus_distr : forall sz (x y z : word sz), (x ^+ y) ^* z = (x ^* z) ^+ (y ^* z).
  intros; repeat rewrite wmult_alt; repeat rewrite wplus_alt; unfold wmultN, wplusN, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.

  rewrite mult_minus_distr_r.
  rewrite <- (mult_assoc x0).
  rewrite (mult_comm (pow2 sz)).
  rewrite (mult_assoc x0).

  replace (wordToNat x * wordToNat z - x1 * pow2 sz +
    (wordToNat y * wordToNat z - x2 * pow2 sz))
    with (wordToNat x * wordToNat z + wordToNat y * wordToNat z - x1 * pow2 sz - x2 * pow2 sz).
  repeat rewrite drop_sub; auto with arith.
  rewrite (mult_comm x0).
  rewrite (mult_comm (wordToNat x + wordToNat y)).
  rewrite <- (mult_assoc (wordToNat z)).
  auto with arith.
  generalize dependent (wordToNat x * wordToNat z).
  generalize dependent (wordToNat y * wordToNat z).
  intros.
  omega.
Qed.

Theorem wminus_def : forall sz (x y : word sz), x ^- y = x ^+ ^~ y.
  reflexivity.
Qed.

Theorem wordToNat_bound : forall sz (w : word sz), wordToNat w < pow2 sz.
  induction w; simpl; intuition.
  destruct b; simpl; omega.
Qed.

Theorem natToWord_pow2 : forall sz, natToWord sz (pow2 sz) = natToWord sz 0.
  induction sz; simpl; intuition.

  generalize (div2_double (pow2 sz)); simpl; intro Hr; rewrite Hr; clear Hr.
  f_equal.
  generalize (mod2_double (pow2 sz)); auto.
  auto.
Qed.

Theorem wminus_inv : forall sz (x : word sz), x ^+ ^~ x = wzero sz.
  intros; rewrite wneg_alt; rewrite wplus_alt; unfold wnegN, wplusN, wzero, wordBinN; intros.

  repeat match goal with
           | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
             let Heq := fresh "Heq" in
               destruct (wordToNat_natToWord sz w) as [? [Heq ?]]; rewrite Heq
         end.
  
  replace (wordToNat x + (pow2 sz - wordToNat x - x0 * pow2 sz))
    with (pow2 sz - x0 * pow2 sz).
  rewrite drop_sub; auto with arith.
  apply natToWord_pow2.
  generalize (wordToNat_bound x).
  omega.
Qed.

Definition wring (sz : nat) : ring_theory (wzero sz) (wone sz) (@wplus sz) (@wmult sz) (@wminus sz) (@wneg sz) (@eq _) :=
  mk_rt _ _ _ _ _ _ _
  (@wplus_unit _) (@wplus_comm _) (@wplus_assoc _)
  (@wmult_unit _) (@wmult_comm _) (@wmult_assoc _)
  (@wmult_plus_distr _) (@wminus_def _) (@wminus_inv _).

Theorem weqb_sound : forall sz (x y : word sz), weqb x y = true -> x = y.
Proof.
  eapply weqb_true_iff.
Qed.

(* Arguments weqb_sound []. *)

(* Ltac isWcst w := *)
(*   match eval hnf in w with *)
(*     | WO => constr:true *)
(*     | WS ?b ?w' => *)
(*       match eval hnf in b with *)
(*         | true => isWcst w' *)
(*         | false => isWcst w' *)
(*         | _ => constr:false *)
(*       end *)
(*     | _ => constr:false *)
(*   end. *)

(* Ltac wcst w := *)
(*   let b := isWcst w in *)
(*     match b with *)
(*       | true => w *)
(*       | _ => constr:NotConstant *)
(*     end. *)

(* Here's how you can add a ring for a specific bit-width.
   There doesn't seem to be a polymorphic method, so this code really does need to be copied. *)

(*
Definition wring8 := wring 8.
Add Ring wring8 : wring8 (decidable (weqb_sound 8), constants [wcst]).
*)


(** * Bitwise operators *)

Fixpoint rev (sz : nat) (w : word sz) : word sz :=
  match w in (word n) return (word n) with
  | WO => WO
  | @WS b sz' w' =>
    eq_rec (sz' + 1) (fun n => word n) (combine (rev w') (WS b WO)) 
           (S sz') (Nat.add_1_r sz')
  end.

Fixpoint wnot sz (w : word sz) : word sz :=
  match w with
    | WO => WO
    | WS b w' => WS (negb b) (wnot w')
  end.

Fixpoint bitwp (f : bool -> bool -> bool) sz (w1 : word sz) : word sz -> word sz :=
  match w1 with
    | WO => fun _ => WO
    | WS b w1' => fun w2 => WS (f b (whd w2)) (bitwp f w1' (wtl w2))
  end.

Definition wor := bitwp orb.
Definition wand := bitwp andb.
Definition wxor := bitwp xorb.

Notation "l ^| r" := (@wor _ l%word r%word) (at level 50, left associativity).
Notation "l ^& r" := (@wand _ l%word r%word) (at level 40, left associativity).

Theorem wor_unit : forall sz (x : word sz), wzero sz ^| x = x.
  unfold wzero, wor; induction x; simpl; intuition congruence.
Qed.

Theorem wor_comm : forall sz (x y : word sz), x ^| y = y ^| x.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wor_assoc : forall sz (x y z : word sz), x ^| (y ^| z) = x ^| y ^| z.
  unfold wor; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_unit : forall sz (x : word sz), wones sz ^& x = x.
  unfold wand; induction x; simpl; intuition congruence.
Qed.

Theorem wand_kill : forall sz (x : word sz), wzero sz ^& x = wzero sz.
  unfold wzero, wand; induction x; simpl; intuition congruence.
Qed.

Theorem wand_comm : forall sz (x y : word sz), x ^& y = y ^& x.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_assoc : forall sz (x y z : word sz), x ^& (y ^& z) = x ^& y ^& z.
  unfold wand; induction x; intro y; rewrite (shatter_word y); simpl; intuition; f_equal; auto with bool.
Qed.

Theorem wand_or_distr : forall sz (x y z : word sz), (x ^| y) ^& z = (x ^& z) ^| (y ^& z).
  unfold wand, wor; induction x; intro y; rewrite (shatter_word y); intro z; rewrite (shatter_word z); simpl; intuition; f_equal; auto with bool.
  destruct (whd y); destruct (whd z); destruct b; reflexivity.
Qed.

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
  intros; intro; subst.
  unfold wminus in H.
  rewrite wminus_inv in H.
  tauto.
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

Open Scope word_scope.

(** * Comparison Predicates and Deciders **)
Definition wlt sz (l r : word sz) : Prop :=
  Nlt (wordToN l) (wordToN r).
Definition wslt sz (l r : word sz) : Prop :=
  Zlt (wordToZ l) (wordToZ r).

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
    match Ncompare (wordToN l) (wordToN r) as k return Ncompare (wordToN l) (wordToN r) = k -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

Definition wslt_dec : forall sz (l r : word sz), {l <s r} + {l >s= r}.
  refine (fun sz l r => 
    match Zcompare (wordToZ l) (wordToZ r) as c return Zcompare (wordToZ l) (wordToZ r) = c -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.

(* Ordering Lemmas **)
Lemma lt_le : forall sz (a b : word sz),
  a < b -> a <= b.
Proof.
  unfold wlt, Nlt. intros. intro. rewrite <- Ncompare_antisym in H0. rewrite H in H0. simpl in *. congruence.
Qed.
Lemma eq_le : forall sz (a b : word sz),
  a = b -> a <= b.
Proof.
  intros; subst. unfold wlt, Nlt. rewrite Ncompare_refl. congruence.
Qed.
Lemma wordToN_inj : forall sz (a b : word sz),
  wordToN a = wordToN b -> a = b.
Proof.
  induction a; intro b0; rewrite (shatter_word b0); intuition.
  simpl in H.
  destruct b; destruct (whd b0); intros.
  f_equal. eapply IHa. eapply Nsucc_inj in H.
  destruct (wordToN a); destruct (wordToN (wtl b0)); try congruence.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  destruct (wordToN (wtl b0)); destruct (wordToN a); inversion H.
  f_equal. eapply IHa. 
  destruct (wordToN a); destruct (wordToN (wtl b0)); try congruence.
Qed.
Lemma unique_inverse : forall sz (a b1 b2 : word sz),
  a ^+ b1 = wzero _ ->
  a ^+ b2 = wzero _ ->
  b1 = b2.
Proof.
  intros.
  transitivity (b1 ^+ wzero _).
  rewrite wplus_comm. rewrite wplus_unit. auto.
  transitivity (b1 ^+ (a ^+ b2)). congruence.
  rewrite wplus_assoc.
  rewrite (wplus_comm b1). rewrite H. rewrite wplus_unit. auto.
Qed.
Lemma sub_0_eq : forall sz (a b : word sz),
  a ^- b = wzero _ -> a = b.
Proof.
  intros. destruct (weq (wneg b) (wneg a)).
  transitivity (a ^+ (^~ b ^+ b)).
  rewrite (wplus_comm (^~ b)). rewrite wminus_inv. 
  rewrite wplus_comm. rewrite wplus_unit. auto.
  rewrite e. rewrite wplus_assoc. rewrite wminus_inv. rewrite wplus_unit. auto.
  unfold wminus in H.
  generalize (unique_inverse a (wneg a) (^~ b)).
  intros. elimtype False. apply n. symmetry; apply H0.
  apply wminus_inv.
  auto.
Qed.

Lemma le_neq_lt : forall sz (a b : word sz),
  b <= a -> a <> b -> b < a.
Proof.
  intros; destruct (wlt_dec b a); auto.
  elimtype False. apply H0. unfold wlt, Nlt in *.
  eapply wordToN_inj. eapply Ncompare_eq_correct.
  case_eq ((wordToN a ?= wordToN b)%N); auto; try congruence.
  intros. rewrite <- Ncompare_antisym in n. rewrite H1 in n. simpl in *. congruence.
Qed.


Hint Resolve word_neq lt_le eq_le sub_0_eq le_neq_lt : worder.

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
  intros; destruct (weq a b); try solve [ elimtype False; auto ].
  f_equal. 
  eapply UIP_dec. eapply weq.
Qed.


(** * Some more useful derived facts *)

Lemma natToWord_plus : forall sz n m, natToWord sz (n + m) = natToWord _ n ^+ natToWord _ m.
  destruct sz; intuition.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  destruct (wordToNat_natToWord (S sz) n); intuition.
  destruct (wordToNat_natToWord (S sz) m); intuition.
  rewrite H0; rewrite H2; clear H0 H2.
  replace (n - x * pow2 (S sz) + (m - x0 * pow2 (S sz))) with (n + m - x * pow2 (S sz) - x0 * pow2 (S sz))
    by omega.
  repeat rewrite drop_sub; auto; omega.
Qed.

Lemma natToWord_S : forall sz n, natToWord sz (S n) = natToWord _ 1 ^+ natToWord _ n.
  intros; change (S n) with (1 + n); apply natToWord_plus.
Qed.

Theorem natToWord_inj : forall sz n m, natToWord sz n = natToWord sz m
  -> (n < pow2 sz)%nat
  -> (m < pow2 sz)%nat
  -> n = m.
  intros.
  apply (f_equal (@wordToNat _)) in H.
  destruct (wordToNat_natToWord sz n).
  destruct (wordToNat_natToWord sz m).
  intuition.
  rewrite H4 in H; rewrite H2 in H; clear H4 H2.
  assert (x = 0).
  destruct x; auto.
  simpl in *.
  generalize dependent (x * pow2 sz).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; auto.
  simpl in *.
  generalize dependent (x0 * pow2 sz).
  intros.
  omega.
  subst; simpl in *; omega.
Qed.

Lemma wordToNat_inj: forall {sz} (w1 w2: word sz),
    wordToNat w1 = wordToNat w2 -> w1 = w2.
Proof.
  intros; apply wordToN_inj; rewrite ! wordToN_nat; auto.
Qed.

Lemma wordToNat_natToWord_idempotent : forall sz n,
  (N.of_nat n < Npow2 sz)%N
  -> wordToNat (natToWord sz n) = n.
  intros.
  destruct (wordToNat_natToWord sz n); intuition.
  destruct x.
  simpl in *; omega.
  simpl in *.
  apply Nlt_out in H.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (x * pow2 sz).
  intros; omega.
Qed.

Lemma wplus_cancel : forall sz (a b c : word sz),
  a ^+ c = b ^+ c
  -> a = b.
  intros.
  apply (f_equal (fun x => x ^+ ^~ c)) in H.
  repeat rewrite <- wplus_assoc in H.
  rewrite wminus_inv in H.
  repeat rewrite (wplus_comm _ (wzero sz)) in H.
  repeat rewrite wplus_unit in H.
  assumption.
Qed.

Lemma wminus_plus_distr:
  forall {sz} (x y z: word sz), x ^- (y ^+ z) = x ^- y ^- z.
Proof.
  intros.
  apply wplus_cancel with (c:= y ^+ z).
  rewrite wminus_def, <-wplus_assoc.
  rewrite wplus_comm with (y:= y ^+ z), wminus_inv.
  rewrite wplus_comm with (x:= x), wplus_unit.
  rewrite !wminus_def, <-wplus_assoc.
  rewrite wplus_assoc with (x:= ^~ z).
  rewrite wplus_comm with (x:= ^~ z).
  rewrite <-wplus_assoc with (x:= y).
  rewrite wplus_comm with (x:= ^~ z), wminus_inv.
  rewrite wplus_comm with (x:= y), wplus_unit.
  rewrite <-wplus_assoc.
  rewrite wplus_comm with (x:= ^~ y), wminus_inv.
  rewrite wplus_comm, wplus_unit.
  reflexivity.
Qed.

Lemma wneg_zero:
  forall {sz} (w: word sz), ^~ w = (natToWord sz 0) -> w = natToWord sz 0.
Proof.
  intros.
  apply wplus_cancel with (c:= ^~ w).
  rewrite wminus_inv, wplus_unit; auto.
Qed.

Lemma wneg_idempotent:
  forall {sz} (w: word sz), ^~ (^~ w) = w.
Proof.
  intros.
  apply sub_0_eq.
  rewrite wminus_def.
  rewrite wplus_comm.
  apply wminus_inv.
Qed.

Lemma wplus_one_neq: forall {sz} (w: word (S sz)), w ^+ (natToWord (S sz) 1) <> w.
Proof.
  intros; intro Hx.
  rewrite wplus_comm in Hx.
  assert ((natToWord (S sz) 1) ^+ w ^- w = w ^- w) by (rewrite Hx; reflexivity).
  clear Hx.
  do 2 rewrite wminus_def in H.
  rewrite <-wplus_assoc in H.
  rewrite wminus_inv in H.
  rewrite wplus_comm, wplus_unit in H.
  inversion H.
Qed.

Lemma wneg_one_pow2_minus_one: forall {sz}, wordToNat (^~ (natToWord sz 1)) = pow2 sz - 1.
Proof.
  destruct sz; auto.
  unfold wneg; intros.
  rewrite wordToN_nat, roundTrip_1.
  simpl BinNat.N.of_nat.
  rewrite NToWord_nat, Nnat.N2Nat.inj_sub, Npow2_nat.
  apply wordToNat_natToWord_2.
  pose (pow2_zero (S sz)).
  omega.
Qed.

Lemma wones_pow2_minus_one: forall {sz}, wordToNat (wones sz) = pow2 sz - 1.
Proof.
  induction sz; simpl; auto.
  rewrite IHsz; pose (pow2_zero sz).
  omega.
Qed.

Lemma pow2_minus_one_wones: forall {sz} (w: word sz),
    wordToNat w = pow2 sz - 1 -> w = wones sz.
Proof.
  intros; rewrite <-wones_pow2_minus_one in H.
  apply wordToNat_inj; auto.
Qed.

Lemma wones_wneg_one: forall {sz}, wones sz = ^~ (natToWord sz 1).
Proof.
  intros; apply wordToNat_inj.
  rewrite wneg_one_pow2_minus_one.
  rewrite wones_pow2_minus_one.
  reflexivity.
Qed.

Lemma wordToNat_natToWord_pred:
  forall {sz} (w: word sz), w <> wzero sz ->
                            pred (wordToNat w) =
                            wordToNat (w ^- (natToWord sz 1)).
Proof.
  intros; remember (wordToNat w) as wn; destruct wn; simpl in *.
  - elim H.
    apply wordToNat_inj.
    rewrite roundTrip_0; auto.
  - apply natToWord_inj with (sz:= sz).
    + rewrite natToWord_wordToNat.
      apply wplus_cancel with (c:= (natToWord sz 1)).
      rewrite wminus_def, <-wplus_assoc.
      rewrite wplus_comm with (x:= ^~ (natToWord sz 1)).
      rewrite wminus_inv.
      rewrite wplus_comm with (x:= w).
      rewrite wplus_unit.
      rewrite wplus_comm, <-natToWord_S.
      apply wordToNat_inj.
      rewrite wordToNat_natToWord_2; auto.
      rewrite Heqwn.
      apply wordToNat_bound.
    + pose proof (wordToNat_bound w); omega.
    + apply wordToNat_bound.
Qed.

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
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_lt2: forall sz (a b: word sz), (wordToNat a < wordToNat b)%nat -> a < b.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_gt1: forall sz (a b: word sz), a > b -> (wordToNat a > wordToNat b)%nat.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_gt2: forall sz (a b: word sz), (wordToNat a > wordToNat b)%nat -> a > b.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_le1: forall sz (a b: word sz), a <= b -> (wordToNat a <= wordToNat b)%nat.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_le2: forall sz (a b: word sz), (wordToNat a <= wordToNat b)%nat -> a <= b.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat.
  assumption.
Qed.

Lemma wordToNat_ge1: forall sz (a b: word sz), a >= b -> (wordToNat a >= wordToNat b)%nat.
Proof.
  intros.
  pre_nomega.
  repeat rewrite wordToN_to_nat in H.
  assumption.
Qed.

Lemma wordToNat_ge2: forall sz (a b: word sz), (wordToNat a >= wordToNat b)%nat -> a >= b.
Proof.
  intros.
  pre_nomega.
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

Ltac pre_word_omega :=
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


Ltac word_omega := pre_word_omega; omega.

Lemma word_le_ge_eq sz (w1 w2: word sz): w1 <= w2 -> w1 >= w2 -> w1 = w2.
Proof.
  intros; word_omega.
Qed.

Lemma word_le_zero sz (w: word sz): w <= wzero sz -> w = wzero sz.
Proof.
  intros;
  word_omega.
Qed.

