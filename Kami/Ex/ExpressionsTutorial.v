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

Fixpoint flatten {len} : multibyte (S len) -> word (len * 8 + 8) :=
  match len with
  | O => fun w => Vector.hd w
  | S len' => fun w => combine (Vector.hd w) (flatten (Vector.tl w))
  end.

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


  (** ** A simple example of a traversal of expression syntax *)

  Fixpoint numLets {n} (e : expr (fun _ => unit) n) : nat :=
    match e with
    | Const _ => 0
    | Combine e1 e2 => numLets e1 + numLets e2
    | Split1 e1 => numLets e1
    | Split2 e1 => numLets e1
    | Add e1 e2 => numLets e1 + numLets e2
    | Var _ => 0
    | LetIn e1 e2 => 1 + numLets e1 + numLets (e2 tt)
    end.

  Definition add2_lets := numLets (add2 tt tt tt tt).
  Compute add2_lets.

  Definition add3_lets := numLets (add3 tt tt tt tt tt tt).
  Compute add3_lets.


  (** ** A simple optimization, constant folding *)

  Fixpoint cfold {var len} (e : expr (expr var) len) : expr var len :=
    match e in expr _ len return expr var len with
    | Const k => Const k
    | Combine e1 e2 =>
      match cfold e1, cfold e2 with
      | Const k1, Const k2 => Const (combine k1 k2)
      | e1', e2' => Combine e1' e2'
      end
    | @Split1 _ n1 n2 e1 =>
      match cfold e1 in expr _ len' return (word len' -> expr _ _) -> expr _ _ with
      | Const k => fun f => f k
      | e1' => fun _ => Split1 e1'
      end (fun k => Const (split1 n1 n2 k))
    | @Split2 _ n1 n2 e1 =>
      match cfold e1 in expr _ len' return (word len' -> expr _ _) -> expr _ _ with
      | Const k => fun f => f k
      | e1' => fun _ => Split2 e1'
      end (fun k => Const (split2 n1 n2 k))
    | Add e1 e2 =>
      match cfold e1 in expr _ len' return expr _ len' -> expr _ len' with
      | Const k1 => fun cfold_e2 =>
        if weq k1 (wzero _) then cfold_e2
        else match cfold_e2 in expr _ len' return word len' -> expr _ len' with
             | Const k2 => fun k1 => Const (k1 ^+ k2)
             | e2' => fun k1 => Add (Const k1) e2'
             end k1
      | e1' => fun cfold_e2 => Add e1' cfold_e2
      end (cfold e2)
    | Var x => x
    | LetIn e1 e2 =>
      match cfold e1 in expr _ len' return (expr _ len' -> expr _ _) -> expr _ _ with
      | Const k => fun f => f (Const k)
      | e1' => fun f => LetIn e1' (fun x => f (Var x))
      end (fun x => cfold (e2 x))
    end.

  Definition add2' {var : nat -> Type} (a1 a2 b1 b2 : var 8) :=
    cfold (MbAdd' (Const (wzero 1))
                  [Var (Var a1); Var (Var a2)]
                  [Var (Var b1); Var (Var b2)]).
  Compute add2'.

  Definition add3' {var : nat -> Type} (a1 a2 a3 b1 b2 b3 : var 8) :=
    cfold (MbAdd' (Const (wzero 1))
                  [Var (Var a1); Var (Var a2); Var (Var a3)]
                  [Var (Var b1); Var (Var b2); Var (Var b3)]).
  Compute add3'.


  (** ** How would we prove that optimization? *)
  Section equiv.
    Context {var1 var2 : nat -> Type}.
    Record bound := {
      width : nat;
      val1 : var1 width;
      val2 : var2 width
    }.

    Inductive equiv (b : list bound) : forall {n}, expr var1 n -> expr var2 n -> Prop :=
    | EquivConst : forall n (w : word n),
        equiv b (Const w) (Const w)
    | EquivCombine : forall n1 n2 (a1 : expr var1 n1) (a2 : expr var1 n2)
                            (b1 : expr var2 n1) (b2 : expr var2 n2),
        equiv b a1 b1
        -> equiv b a2 b2
        -> equiv b (Combine a1 a2) (Combine b1 b2)
    | EquivSplit1 : forall n1 n2 (a1 : expr var1 (n1 + n2)) (b1 : expr var2 (n1 + n2)),
        equiv b a1 b1
        -> equiv b (Split1 a1) (Split1 b1)
    | EquivSplit2 : forall n1 n2 (a1 : expr var1 (n1 + n2)) (b1 : expr var2 (n1 + n2)),
        equiv b a1 b1
        -> equiv b (Split2 a1) (Split2 b1)
    | EquivAdd : forall n (a1 a2 : expr var1 n) (b1 b2 : expr var2 n),
        equiv b a1 b1
        -> equiv b a2 b2
        -> equiv b (Add a1 a2) (Add b1 b2)

    | EquivVar : forall width (val1 : var1 width) (val2 : var2 width),
        In {| val1 := val1; val2 := val2 |} b
        -> equiv b (Var val1) (Var val2)
    | EquivLet : forall n1 n2 (a1 : expr var1 n1) (a2 : var1 n1 -> expr var1 n2)
                        (b1 : expr var2 n1) (b2 : var2 n1 -> expr var2 n2),
        equiv b a1 b1
        -> (forall val1 val2, equiv ({| val1 := val1; val2 := val2 |} :: b) (a2 val1) (b2 val2))
        -> equiv b (LetIn a1 a2) (LetIn b1 b2).

    Hint Constructors equiv.

    Lemma equiv_weaken : forall n (e1 : expr _ n) e2 b1,
        equiv b1 e1 e2
        -> forall b2, (forall x, In x b1 -> In x b2)
        -> equiv b2 e1 e2.
    Proof.
      induction 1; intuition eauto.
      constructor; intuition.
      apply H1.
      simpl; intuition.
    Qed.
  End equiv.

  Ltac equiv1 :=
    match goal with
    | [ |- equiv ?b (Combine (n1 := ?A) (n2 := ?B) _ _) _ ] => apply (EquivCombine b A B)
    | _ => constructor; intros;
           match goal with
           | [ |- In _ _ ] => simpl; tauto
           | [ |- equiv _ _ _ ] => idtac
           end
    | [ |- equiv _ _ _ ] => eapply equiv_weaken; [ eassumption | simpl; solve [ intuition ] ]
    | _ => auto
    end.
  Ltac equiv := repeat equiv1.

  Definition Wf {n} (E : Expr n) := forall var1 var2, equiv nil (E var1) (E var2).
  Definition MultibyteWf {n} (mb : Multibyte n) :=
    forall var1 var2, Vector.Forall2 (equiv nil) (mb var1) (mb var2).

  Require Import Eqdep.

  Lemma MbAdd'_Wf : forall var1 var2 len
                           b (mb11 : Multibyte' var1 len) (mb21 : Multibyte' var2 len),
      Vector.Forall2 (equiv b) mb11 mb21
      -> forall mb12 mb22, Vector.Forall2 (equiv b) mb12 mb22
      -> forall b', (forall x, In x b -> In x b')
      -> forall carry1 carry2, equiv b' carry1 carry2
      -> equiv b' (MbAdd' carry1 mb11 mb12) (MbAdd' carry2 mb21 mb22).
  Proof.
    induction 1; inversion 1; simpl; intros;
      repeat match goal with
             | [ H : existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; subst
             end; equiv; simpl.
    eapply IHForall2; eauto.
    simpl; intuition.
    constructor; simpl; tauto.
  Qed.

  Theorem MbAdd_Wf : forall len (mb1 mb2 : Multibyte len),
      MultibyteWf mb1
      -> MultibyteWf mb2
      -> Wf (MbAdd mb1 mb2).
  Proof.
    unfold MultibyteWf, Wf, MbAdd; intros.
    apply MbAdd'_Wf with (b := nil); equiv.
  Qed.
End Phoas.


(** * Now let's redo that code using Kami proper. *)

Section var.
  Context {var : Kind -> Type}.

  Definition Multibyte' := Vector.t (Expr var (SyntaxKind (Bit 8))).

  Fixpoint MbAdd' {res len} (carry : Expr var (SyntaxKind (Bit 1)))
    : Multibyte' len -> Multibyte' len
      -> (Expr var (SyntaxKind (Bit (len * 8 + 8))) -> ActionT var res)
      -> ActionT var res :=
    match len with
    | 0 => fun _ _ f => f (BinBit (Concat _ _) (Const var (ConstBit (wzero 7))) carry)
    | S len' => fun mb1 mb2 f =>
      Let_ (BinBit (Concat _ _) (Const var (ConstBit (wzero 8))) carry) (fun carry_9 =>
      Let_ (BinBit (Concat _ _) (Const var (ConstBit (wzero 1))) (Vector.hd mb1)) (fun b1_9 =>
      Let_ (BinBit (Concat _ _) (Const var (ConstBit (wzero 1))) (Vector.hd mb2)) (fun b2_9 =>
      Let_ (BinBit (Add _) (BinBit (Add _) (Var _ _ carry_9) (Var _ _ b1_9)) (Var _ _ b2_9)) (fun sum_9 =>
      Let_ (UniBit (Trunc 8 1) (Var _ _ sum_9)) (fun sum_8 =>
      Let_ (BinBit (Srl 9 8) (Var _ _ sum_9) (Const var (ConstBit (natToWord 8 8)))) (fun carry'' =>
      Let_ (UniBit (Trunc 1 8) (Var _ _ carry'')) (fun carry' =>
        MbAdd' (Var _ _ carry') (Vector.tl mb1) (Vector.tl mb2)
               (fun e => f (BinBit (Concat _ _) e (Var _ _ sum_8))))))))))
    end.

  Definition MbAdd {res len} := MbAdd' (res := res) (len := len) (Const var (ConstBit (wzero _))).
End var.

Lemma msb_by_shifting : forall (w : word 9),
    split1 1 8 (wrshift w 8) = split2 8 1 w.
Proof.
  intros.
  repeat match goal with
         | [ w : word _ |- _ ] =>
           let H := fresh "H" in
           specialize (shatter_word w) as H; simpl in H; rewrite H; clear H;
             try (generalize (whd w); generalize (wtl w)); clear w; intros
         end.

  vm_compute.
  Require Import Eqdep.
  match goal with
  | [ |- context[match ?PF with eq_refl => _ end] ] => rewrite (UIP_refl _ _ PF)
  end.
  reflexivity.
Qed.

Lemma MbAdd'_ok : forall r res len carry (mb1 mb2 : Multibyte' len)
                         (f : Expr type (SyntaxKind (Bit (len * 8 + 8)))
                              -> ActionT type res)
                         (f_gives : word (len * 8 + 8) -> type res),
    (forall e, SemAction r (f e) (M.empty _) (M.empty _) (f_gives (evalExpr e)))
    -> SemAction r (MbAdd' carry mb1 mb2 f) (M.empty _) (M.empty _)
                 (f_gives (flatten (mbAdd' (evalExpr carry)
                                           (Vector.map (@evalExpr _) mb1)
                                           (Vector.map (@evalExpr _) mb2)))).
Proof.
  induction len; simpl; intuition.

  apply H.

  repeat apply SemLet.
  match goal with
  | [ |- context[MbAdd' ?carry ?mb1 ?mb2 ?f] ] => specialize (IHlen carry mb1 mb2 f)
  end.
  simpl in IHlen.
  repeat rewrite hd_map, tl_map.
  specialize (IHlen (fun ans => f_gives (combine
          (split1 8 1
             (combine (evalExpr carry) (wzero 8)
              ^+ combine (evalExpr (Vector.hd mb1)) (wzero 1)
              ^+ combine (evalExpr (Vector.hd mb2)) (wzero 1))) ans))).
  simpl in *.

  match goal with
  | [ |- context[mbAdd' ?carry' _ _] ] =>
    replace carry'
      with (split1 1 8
                   (wrshift
                      (combine (evalExpr carry) (wzero 8)
                               ^+ combine (evalExpr (Vector.hd mb1)) (wzero 1)
                               ^+ combine (evalExpr (Vector.hd mb2)) (wzero 1)) 8))
  end.
  apply IHlen.
  intros.
  apply H.
  apply msb_by_shifting.
Qed.

Lemma mbToNat_bound : forall {len} (mb : multibyte len),
    (mbToNat mb < pow2 (len * 8))%nat.
Proof.
  induction mb; simpl.

  change (pow2 0) with 1.
  omega.

  pose proof (wordToNat_bound h).
  replace (pow2 (S (S (S (S (S (S (S (S (n * 8))))))))))
    with (256 * pow2 (n * 8)).
  change (pow2 8) with 256 in *.
  omega.

  change (pow2 (S (S (S (S (S (S (S (S (n * 8))))))))))
    with (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * pow2 (n * 8))))))))).
  clear.
  generalize (pow2 (n * 8 + 8)).
  intros.
  omega.
Qed.

Theorem MbAdd_ok : forall r len (mb1 mb2 : Multibyte' len),
    SemAction r (MbAdd mb1 mb2 (fun e => Return e)) (M.empty _) (M.empty _)
              (natToWord _ (mbToNat (Vector.map (@evalExpr _) mb1)
                            + mbToNat (Vector.map (@evalExpr _) mb2))).
Proof.
  unfold MbAdd; intros.
  match goal with
  | [ |- context[MbAdd' ?carry ?mb1 ?mb2 ?f] ] => pose proof (MbAdd'_ok r _ _ carry mb1 mb2 f (fun x => x))
  end.
  simpl in H.
  match type of H with
  | ?P -> _ => assert P; intuition
  end.
  constructor; reflexivity.
  match goal with
  | [ _ : SemAction _ _ _ _ ?X |- SemAction _ _ _ _ ?Y ] => replace Y with X; auto
  end.
  apply wordToNat_inj.
  rewrite flatten_ok.
  rewrite mbAdd'_ok.
  change (# (wzero 1)) with 0; simpl.
  symmetry; apply wordToNat_natToWord_idempotent'.
  match goal with
  | [ |- (mbToNat ?X + mbToNat ?Y < _)%nat ] =>
    pose proof (mbToNat_bound X);
      pose proof (mbToNat_bound Y)
  end.
  rewrite pow2_add_mul.
  change (pow2 8) with 256.
  omega.
Qed.

Definition AddInputs :=
  STRUCT { "a1" :: Bit 8;
           "a2" :: Bit 8;
           "a3" :: Bit 8;
           "b1" :: Bit 8;
           "b2" :: Bit 8;
           "b3" :: Bit 8 }.

Definition kamiModule :=
  MODULE {
    Register "data" : Bit 8 <- Default

    with Method "add3" (arg: Struct AddInputs) : Bit 32 :=
      (MbAdd
        [#arg!AddInputs@."a1"; #arg!AddInputs@."a2"; #arg!AddInputs@."a3"]
        [#arg!AddInputs@."b1"; #arg!AddInputs@."b2"; #arg!AddInputs@."b3"]
        (fun e => Return e))%kami_expr
  }.

Transparent arg.
Compute kamiModule.

Require Import Kami.Synthesize Ext.BSyntax.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Definition targetProcB := ModulesSToBModules (getModuleS kamiModule).

Extraction "../Ext/Ocaml/Target.ml" targetProcB.
