Require Import Arith NatLib Ring ArithRing Omega Vector.
Require Import Kami.


(** * Warm-up: words (bitvectors) *)

Definition B := word 8.
Definition multibyte := Vector.t B.

Fixpoint mbToNat {len} (mb : multibyte len) : nat :=
  match mb with
  | Vector.nil _ => 0
  | Vector.cons _ b _ mb' => wordToNat b + mbToNat mb' * 256
  end.

Fixpoint mbAdd' {len} (carry : word 1) : multibyte len -> multibyte len -> multibyte (S len) :=
  match len with
  | O => fun _ _ => Vector.cons _ (combine carry (wzero 7)) _ (Vector.nil _)
  | S len' => fun mb1 mb2 =>
    let carry_9 := combine carry (wzero 8) in
    let b1_9 := combine (Vector.hd mb1) (wzero 1) in
    let b2_9 := combine (Vector.hd mb2) (wzero 1) in
    let sum_9 := carry_9 ^+ b1_9 ^+ b2_9 in
    let sum_8 := split1 8 1 sum_9 in
    let carry' := split2 8 1 sum_9 in
    Vector.cons _ sum_8 _ (mbAdd' carry' (Vector.tl mb1) (Vector.tl mb2))
  end.

Definition mbAdd {len} := mbAdd' (len := len) (wzero 1).

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

Lemma shatter_vector : forall {A n} (v : Vector.t A n),
    match n return Vector.t A n -> Prop with
    | O => fun v => v = Vector.nil _
    | S n' => fun v => exists h t, v = Vector.cons _ h _ t
    end v.
Proof.
  destruct v; eauto.
Qed.

Lemma mbAdd'_ok : forall len (mb1 mb2 : multibyte len) carry,
    mbToNat (mbAdd' carry mb1 mb2)
    = wordToNat carry + mbToNat mb1 + mbToNat mb2.
Proof.
  induction len; simpl; intuition.

  {
    pose proof (shatter_vector mb1).
    pose proof (shatter_vector mb2).
    simpl in *; subst; simpl.
    pose proof (shatter_word_S carry).
    destruct H as [b [c Heq]]; subst.
    simpl.
    pose proof (shatter_word_0 c); subst.
    destruct b; simpl.
    reflexivity.
    reflexivity.
  }
  
  {
    pose proof (shatter_vector mb1).
    pose proof (shatter_vector mb2).
    simpl in *; subst; simpl.
    destruct H as [a [mb1' ?]]; subst.
    destruct H0 as [b [mb2' ?]]; subst.
    rewrite IHlen; simpl.
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
      replace (256 * mbToNat mb1' + 256 * mbToNat mb2' + # (carry) + # (a) + # (b))
              with (256 * mbToNat mb1' + 256 * mbToNat mb2' + (# (carry) + # (a) + # (b))) by omega.
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

Theorem mbAdd_ok : forall len (mb1 mb2 : multibyte len),
    mbToNat (mbAdd mb1 mb2)
    = mbToNat mb1 + mbToNat mb2.
Proof.
  intros; unfold mbAdd.
  rewrite mbAdd'_ok.
  reflexivity.
Qed.


(** * Introducing a deeply embedded language *)

Notation "[ x1 ; .. ; xN ]" := (Vector.cons _ x1 _ (.. (Vector.cons _ xN _ (Vector.nil _)) ..)).

Lemma hd_map : forall {A B len} (f : A -> B) (v : Vector.t A (S len)),
    Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
  intros.
  pose proof (shatter_vector v); simpl in *.
  destruct H as [a [v' ?]]; subst.
  reflexivity.
Qed.

Lemma tl_map : forall {A B len} (f : A -> B) (v : Vector.t A (S len)),
    Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
Proof.
  intros.
  pose proof (shatter_vector v); simpl in *.
  destruct H as [a [v' ?]]; subst.
  reflexivity.
Qed.

Module DeeplyEmbedded.
  Inductive expr : nat -> Type :=
  | Const : forall {n}, word n -> expr n
  | Combine : forall {n1 n2}, expr n1 -> expr n2 -> expr (n1 + n2)
  | Split1 : forall {n1 n2}, expr (n1 + n2) -> expr n1
  | Split2 : forall {n1 n2}, expr (n1 + n2) -> expr n2
  | Add : forall {n}, expr n -> expr n -> expr n.

  Definition Multibyte := Vector.t (expr 8).

  Fixpoint MbAdd' {len} (carry : expr 1) : Multibyte len -> Multibyte len -> Multibyte (S len) :=
    match len with
    | 0 => fun _ _ => Vector.cons _ (Combine carry (Const (wzero 7))) _ (Vector.nil _)
    | S len' => fun mb1 mb2 =>
      let carry_9 := Combine carry (Const (wzero 8)) in
      let b1_9 := Combine (Vector.hd mb1) (Const (wzero 1)) in
      let b2_9 := Combine (Vector.hd mb2) (Const (wzero 1)) in
      let sum_9 := Add (Add carry_9 b1_9) b2_9 in
      let sum_8 := Split1 (n1 := 8) (n2 := 1) sum_9 in
      let carry' := Split2 (n1 := 8) (n2 := 1) sum_9 in
      Vector.cons _ sum_8 _ (MbAdd' carry' (Vector.tl mb1) (Vector.tl mb2))
    end.

  Definition MbAdd {len} := MbAdd' (len := len) (Const (wzero 1)).

  (** ** Semantics *)

  Fixpoint interp {n} (e : expr n) : word n :=
    match e with
    | Const k => k
    | Combine e1 e2 => combine (interp e1) (interp e2)
    | Split1 e1 => split1 _ _ (interp e1)
    | Split2 e2 => split2 _ _ (interp e2)
    | Add e1 e2 => interp e1 ^+ interp e2
    end.

  Lemma MbAdd'_encoded_properly : forall len (mb1 mb2 : Multibyte len) carry,
      Vector.map interp (MbAdd' carry mb1 mb2)
      = mbAdd' (interp carry) (Vector.map interp mb1) (Vector.map interp mb2).
  Proof.
    induction len; simpl; intuition.

    rewrite IHlen.
    simpl.
    repeat rewrite hd_map, tl_map.
    reflexivity.
  Qed.

  Lemma MbAdd_encoded_properly : forall len (mb1 mb2 : Multibyte len),
      Vector.map interp (MbAdd mb1 mb2)
      = mbAdd (Vector.map interp mb1) (Vector.map interp mb2).
  Proof.
    unfold MbAdd, mbAdd; intros.
    rewrite MbAdd'_encoded_properly.
    reflexivity.
  Qed.

  Theorem MbAdd_ok : forall len (mb1 mb2 : Multibyte len),
      mbToNat (Vector.map interp (MbAdd mb1 mb2))
      = mbToNat (Vector.map interp mb1) + mbToNat (Vector.map interp mb2).
  Proof.
    intros.
    rewrite MbAdd_encoded_properly.
    apply mbAdd_ok.
  Qed.

  (** ** Trouble in paradise *)

  Definition add2 a1 a2 b1 b2 := MbAdd [a1; a2] [b1; b2].
  Compute add2.

  Definition add3 a1 a2 a3 b1 b2 b3 := MbAdd [a1; a2; a3] [b1; b2; b3].
  Compute add3.
End DeeplyEmbedded.


(** * Parametric Higher-Order Abstract Syntax *)

Module Phoas.
  Section var.
    Context {var : nat -> Type}.

    Inductive expr : nat -> Type :=
    | Const : forall {n}, word n -> expr n
    | Combine : forall {n1 n2}, expr n1 -> expr n2 -> expr (n1 + n2)
    | Split1 : forall {n1 n2}, expr (n1 + n2) -> expr n1
    | Split2 : forall {n1 n2}, expr (n1 + n2) -> expr n2
    | Add : forall {n}, expr n -> expr n -> expr n

    | Var : forall {n}, var n -> expr n
    | LetIn : forall {n1 n2}, expr n1 -> (var n1 -> expr n2) -> expr n2.
  End var.

  Arguments expr : clear implicits.

  Definition Expr n := forall var, expr var n.

  Section var'.
    Context {var : nat -> Type}.

    Definition Multibyte' := Vector.t (expr var 8).

    Fixpoint MbAdd' {len} (carry : expr var 1) : Multibyte' len -> Multibyte' len -> expr var (len * 8 + 8) :=
      match len with
      | 0 => fun _ _ => Combine carry (Const (wzero 7))
      | S len' => fun mb1 mb2 =>
        LetIn (Combine carry (Const (wzero 8))) (fun carry_9 =>
        LetIn (Combine (Vector.hd mb1) (Const (wzero 1))) (fun b1_9 =>
        LetIn (Combine (Vector.hd mb2) (Const (wzero 1))) (fun b2_9 =>
        LetIn (Add (Add (Var carry_9) (Var b1_9)) (Var b2_9)) (fun sum_9 =>
        LetIn (Split1 (n1 := 8) (n2 := 1) (Var sum_9)) (fun sum_8 =>
        LetIn (Split2 (n1 := 8) (n2 := 1) (Var sum_9)) (fun carry' =>
        Combine (Var sum_8) (MbAdd' (Var carry') (Vector.tl mb1) (Vector.tl mb2))))))))
      end.
  End var'.

  Arguments Multibyte' : clear implicits.  

  Definition Multibyte len := forall var, Multibyte' var len.
  Definition MbAdd {len} (mb1 mb2 : Multibyte len) : Expr (len * 8 + 8) := 
    fun var => MbAdd' (Const (wzero 1)) (mb1 var) (mb2 var).

  (** ** Semantics *)

  Fixpoint interp {n} (e : expr word n) : word n :=
    match e with
    | Const k => k
    | Combine e1 e2 => combine (interp e1) (interp e2)
    | Split1 e1 => split1 _ _ (interp e1)
    | Split2 e2 => split2 _ _ (interp e2)
    | Add e1 e2 => interp e1 ^+ interp e2

    | Var k => k
    | LetIn e1 e2 => interp (e2 (interp e1))
    end.

  Definition Interp {n} (E : Expr n) : word n := interp (E word).

  Fixpoint flatten {len} : multibyte (S len) -> word (len * 8 + 8) :=
    match len with
    | O => fun w => Vector.hd w
    | S len' => fun w => combine (Vector.hd w) (flatten (Vector.tl w))
    end.

  Lemma MbAdd'_encoded_properly : forall len (mb1 mb2 : Multibyte' word len) carry,
      interp (MbAdd' carry mb1 mb2)
      = flatten (mbAdd' (interp carry) (Vector.map interp mb1) (Vector.map interp mb2)).
  Proof.
    induction len; simpl; intuition.

    rewrite IHlen.
    simpl.
    repeat rewrite hd_map, tl_map.
    reflexivity.
  Qed.

  Lemma MbAdd_encoded_properly : forall len (mb1 mb2 : Multibyte len),
      Interp (MbAdd mb1 mb2)
      = flatten (mbAdd (Vector.map interp (mb1 word)) (Vector.map interp (mb2 word))).
  Proof.
    unfold MbAdd, mbAdd, Interp; intros.
    rewrite MbAdd'_encoded_properly.
    reflexivity.
  Qed.

  Opaque wordToNat split1 split2 combine pow2.

  Lemma flatten_ok : forall len (mb : multibyte (S len)),
      wordToNat (flatten mb) = mbToNat mb.
  Proof.
    induction len; simpl; intuition.

    {
      pose proof (shatter_vector mb); simpl in *.
      destruct H as [a [mb']]; subst.
      simpl.
      pose proof (shatter_vector mb'); simpl in *; subst.
      simpl.
      omega.
    }

    {
      pose proof (wordToNat_combine (Vector.hd mb) (flatten (Vector.tl mb))).
      simpl in *.
      rewrite H.
      pose proof (shatter_vector mb); simpl in *.      
      destruct H0 as [a [mb']]; subst.
      simpl.
      rewrite IHlen.
      change (pow2 8) with 256.
      omega.
    }
  Qed.

  Theorem MbAdd_ok : forall len (mb1 mb2 : Multibyte len),
      wordToNat (Interp (MbAdd mb1 mb2))
      = mbToNat (Vector.map interp (mb1 word)) + mbToNat (Vector.map interp (mb2 word)).
  Proof.
    intros.
    rewrite MbAdd_encoded_properly.
    rewrite flatten_ok.
    apply mbAdd_ok.
  Qed.

  (** ** Less trouble in paradise *)

  Definition add2 {var : nat -> Type} (a1 a2 b1 b2 : var 8) :=
    MbAdd' (Const (wzero 1)) [Var a1; Var a2] [Var b1; Var b2].
  Compute add2.

  Definition add3 {var : nat -> Type} (a1 a2 a3 b1 b2 b3 : var 8) :=
    MbAdd' (Const (wzero 1)) [Var a1; Var a2; Var a3] [Var b1; Var b2; Var b3].
  Set Printing Depth 100.
  Compute add3.
End Phoas.
