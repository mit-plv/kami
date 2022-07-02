Require Import Bool Peano_dec Vector List String.
Require Import Lib.CommonTactics Lib.StringEq Lib.Word Lib.FMap Lib.StringEq Lib.ilist Lib.Struct Lib.Indexer.

Require Import FunctionalExtensionality. (* for appendAction_assoc *)
Require Import Eqdep. (* for signature_eq *)

Set Implicit Arguments.
Set Asymmetric Patterns.

(* `Vec n` is effectively a map from bit vectors of length
   `n` to elements of `A` *)
Inductive Vec (A: Type): nat -> Type :=
| Vec0: A -> Vec A 0
| VecNext n: Vec A n -> Vec A n -> Vec A (S n).

Fixpoint replicate (A: Type) (v: A) n :=
  match n with
  | 0 => Vec0 v
  | S m => VecNext (replicate v m) (replicate v m)
  end.

Inductive Kind :=
| Bool    : Kind
| Bit     : nat -> Kind
| Vector  : Kind -> nat -> Kind
| Struct  : forall n, Vector.t (Attribute Kind) n -> Kind
| Array   : Kind -> nat -> Kind.

Fixpoint type (t: Kind): Type :=
  match t with
  | Bool => bool
  | Bit n => word n
  | Vector nt n => word n -> type nt
  | Struct n ks =>
    forall i: Fin.t n,
      Vector.nth (Vector.map (fun p => type (attrType p)) ks) i
  | Array nt n => Fin.t n -> type nt
  end.

Inductive FullKind: Type :=
| SyntaxKind: Kind -> FullKind
| NativeKind (t: Type) (c: t) : FullKind.

Section Vector_dec.
  Variables (A: Type) (n: nat).
  Variable decA: forall a1 a2: A, {a1 = a2} + {a1 <> a2}.

  Lemma decA_true_iff_sumbool:
    forall a1 a2,
      (if decA a1 a2 then true else false) = true <-> a1 = a2.
  Proof.
    intros; destruct (decA a1 a2); intuition congruence.
  Qed.

  Definition Vector_dec:
    forall v1 v2: Vector.t A n, {v1 = v2} + {v1 <> v2} :=
    Vector.eq_dec _ _ decA_true_iff_sumbool _.

End Vector_dec.

Lemma vector_0_nil A: forall ls: Vector.t A 0, Vector.nil A = ls.
Proof.
  intros; apply Vector.case0; reflexivity.
Defined.

Definition structHd (k: Kind): Attribute Kind :=
  match k with
  | Struct _ Vector.nil => Build_Attribute "FAIL" (Bit 0)
  | Struct _ (Vector.cons attr _ _) => attr
  | _ => Build_Attribute "FAIL" (Bit 0)
  end.

Definition structTl (k: Kind): Kind :=
  match k with
  | Struct _ Vector.nil => Bit 0
  | Struct _ (Vector.cons _ _ tl) => Struct tl
  | _ => Bit 0
  end.

Lemma structHd_ok: forall k1 k2, k1 = k2 -> structHd k1 = structHd k2.
Proof.
  intros; destruct k1, k2; try (inversion H || simpl; reflexivity).
Defined.

Lemma struct_eq_hd:
  forall n (t1 t2: Vector.t _ n),
    Struct t1 = Struct t2 -> structHd (Struct t1) = structHd (Struct t2).
Proof. intros; exact (structHd_ok H). Defined.

Lemma structTl_ok: forall k1 k2, k1 = k2 -> structTl k1 = structTl k2.
Proof.
  intros; destruct k1, k2; try (inversion H || simpl; reflexivity).
Defined.

Lemma struct_eq_tl:
  forall n (t1 t2: Vector.t _ n),
    Struct t1 = Struct t2 -> structTl (Struct t1) = structTl (Struct t2).
Proof. intros; exact (structTl_ok H). Defined.

Lemma struct_eq_inv:
  forall n (t t1: Vector.t _ n), Struct t1 = Struct t -> t1 = t.
Proof.
  induction t; intros.
  - symmetry; apply vector_0_nil.
  - rewrite (VectorSpec.eta t1) in *.
    pose proof (struct_eq_hd H).
    pose proof (struct_eq_tl H).
    simpl in *.
    apply IHt in H1; subst.
    reflexivity.
Defined.

Fixpoint decKind (k1 k2: Kind) : {k1 = k2} + {k1 <> k2}.
  refine match k1, k2 return {k1 = k2} + {k1 <> k2} with
         | Bool, Bool => left eq_refl
         | Bit n, Bit m =>
           match PeanoNat.Nat.eq_dec n m with
           | left l => left match l in _ = Y return Bit n = Bit Y with
                            | eq_refl => eq_refl
                            end
           | right r => right _
           end
         | Vector k1 n1, Vector k2 n2 =>
           match PeanoNat.Nat.eq_dec n1 n2 with
           | left l => match decKind k1 k2 with
                       | left kl => left match l in _ = Y, kl in _ = kY
                                               return Vector k1 n1 = Vector kY Y with
                                         | eq_refl, eq_refl => eq_refl
                                         end
                       | right kr => right _
                       end
           | right r => right _
           end
         | Struct n1 l1, Struct n2 l2 =>
           match PeanoNat.Nat.eq_dec n1 n2 with
           | left l =>
             match l in _ = Y return
                   forall l2: Vector.t _ Y,
                     {Struct l1 = Struct l2} + {Struct l1 <> Struct l2} with
             | eq_refl =>
               fun l2 =>
                 (fix help n l1 :=
                    match l1 in Vector.t _ n'
                          return forall l2: Vector.t _ n',
                        {Struct l1 = Struct l2} + {Struct l1 <> Struct l2} with
                    | Vector.nil => fun l2 => left (f_equal (@Struct 0) (vector_0_nil l2))
                    | Vector.cons h n'' t =>
                      fun l2 => _
                    end) n1 l1 l2
             end l2
           | right r => right _
           end
         | Array k1 n1, Array k2 n2 =>
           match PeanoNat.Nat.eq_dec n1 n2 with
           | left l => match decKind k1 k2 with
                       | left kl => left match l in _ = Y, kl in _ = kY
                                               return Array k1 n1 = Array kY Y with
                                         | eq_refl, eq_refl => eq_refl
                                         end
                       | right kr => right _
                       end
           | right r => right _
           end
         | _, _ => right _
         end;
    try (clear decKind;
         abstract (intro; try inversion H; try inversion H0; destruct_existT; congruence)).

  generalize t (help _ t); clear help t.
  apply (Vector.caseS
           (fun n (l2: Vector.t (Attribute Kind) (S n)) =>
              forall t1, (forall t2: Vector.t (Attribute Kind) n,
                             {Struct t1 = Struct t2} + {Struct t1 <> Struct t2}) ->
                         {Struct (Vector.cons _ h n t1) = Struct l2}
                         + {Struct (Vector.cons _ h n t1) <> Struct l2})).
  intros.
  destruct h, h0.
  destruct (decKind attrType attrType0).
  - destruct (string_dec attrName attrName0).
    + destruct (H t).
      * left; do 2 f_equal.
        { congruence. }
        { exact (struct_eq_inv e1). }
      * clear decKind; right; abstract (intro; inversion H0; destruct_existT; congruence).
    + clear decKind; right; abstract (intro; injection H0; intros; destruct_existT; congruence).
  - clear decKind; right; abstract (intro; injection H0; intros; destruct_existT; congruence).
Defined.

Lemma kind_eq: forall k, decKind k k = left eq_refl.
Proof.
  intros; destruct (decKind k k).
  - rewrite UIP_refl with (p:= e); auto.
  - elim n; auto.
Qed.

Inductive ConstT: Kind -> Type :=
| ConstBool: bool -> ConstT Bool
| ConstBit n: word n -> ConstT (Bit n)
| ConstVector k n: Vec (ConstT k) n -> ConstT (Vector k n)
| ConstStruct n (ls: Vector.t _ n): ilist (fun a => ConstT (attrType a)) ls -> ConstT (Struct ls)
| ConstArray k n: Vector.t (ConstT k) n -> ConstT (Array k n).

Inductive ConstFullT: FullKind -> Type :=
| SyntaxConst k: ConstT k -> ConstFullT (SyntaxKind k)
| NativeConst t (c c': t): ConstFullT (NativeKind c).

Coercion ConstBool : bool >-> ConstT.
Coercion ConstBit : word >-> ConstT.

Fixpoint vector_repeat A n (a: A) :=
  match n return Vector.t A n with
  | 0 => Vector.nil A
  | S m => Vector.cons A a m (@vector_repeat A m a)
  end.

Fixpoint getDefaultConst (k: Kind): ConstT k :=
  match k with
    | Bool => ConstBool false
    | Bit n => ConstBit (wzero _)
    | Vector k n => ConstVector (replicate (getDefaultConst k) n)
    | Struct n ls =>
      ConstStruct ((fix help n (ls: Vector.t _ n) :=
                      match ls return ilist (fun a => ConstT (attrType a)) ls with
                        | Vector.nil => inil _
                        | Vector.cons x m xs => icons x (getDefaultConst (attrType x)) (help m xs)
                      end) n ls)
    | Array k n => ConstArray (vector_repeat n (getDefaultConst k))
  end.

Fixpoint evalConstStruct n (vs: Vector.t _ n) (ils: ilist (fun a => type (attrType a)) vs) {struct ils}: type (Struct vs) :=
  match vs in Vector.t _ k return ilist (fun a => type (attrType a)) vs -> type (Struct vs) with
  | Vector.nil => fun ils0 i0 => Fin.case0 _ i0
  | Vector.cons a1 n1 vs1 =>
    fun ils1 i1 =>
      match ils1 in ilist _ (Vector.cons a n2 vs2)
            return forall i2: Fin.t (S n2),
          Vector.nth
            (Vector.map (fun p => type (attrType p)) (Vector.cons _ a n2 vs2)) i2 with
      | inil => idProp
      | icons t3 n3 vs3 b ils3 =>
        fun k =>
          match k as k4 in Fin.t (S n4) return
                forall (vs4: Vector.t _ n4),
                  type (Struct vs4) ->
                  (Vector.nth (Vector.map (fun p => type (attrType p))
                                          (Vector.cons _ t3 n4 vs4)) k4)
          with
          | Fin.F1 s5 => fun _ _ => b
          | Fin.FS s5 f5 => fun vs5 f => f f5
          end vs3 (@evalConstStruct _ _ ils3)
      end i1
  end ils.

Fixpoint getDefaultConstNative (k: Kind): type k :=
  match k return type k with
  | Bool => false
  | Bit n => wzero _
  | Vector k n => fun _ => getDefaultConstNative k
  | Struct n attrs =>
    fun i =>
      ilist_to_fun _ ((fix help n (ls: Vector.t _ n) :=
                         match ls return ilist (fun a => type (attrType a)) ls with
                         | Vector.nil => inil _
                         | Vector.cons x _ xs =>
                           icons x (getDefaultConstNative (attrType x)) (help _ xs)
                         end) n attrs) i
  | Array k n => fun _ => getDefaultConstNative k
  end.

Definition getDefaultConstFull (k: FullKind): ConstFullT k :=
  match k with
    | SyntaxKind k' => SyntaxConst (getDefaultConst k')
    | NativeKind t c => NativeConst c c
  end.

Record SignatureT :=
  { arg: Kind;
    ret: Kind
  }.

Definition SignatureT_dec: forall (s1 s2: SignatureT), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
  apply decKind.
  apply decKind.
Defined.

Lemma signature_eq: forall sig, SignatureT_dec sig sig = left eq_refl.
Proof.
  intros; destruct (SignatureT_dec sig sig).
  - rewrite UIP_refl with (p:= e); auto.
  - elim n; auto.
Qed.

Inductive UniBoolOp: Set :=
| NegB: UniBoolOp.

Inductive BinBoolOp: Set :=
| AndB: BinBoolOp
| OrB: BinBoolOp.

Inductive UniBitOp: nat -> nat -> Set :=
| Inv n: UniBitOp n n
| Neg n: UniBitOp n n
| ConstExtract n1 n2 n3: UniBitOp (n1 + n2 + n3) n2 (* LSB : n1, MSB : n3 *)
| Trunc n1 n2: UniBitOp (n1 + n2) n1 (* LSB : n1 *)
| ZeroExtendTrunc n1 n2: UniBitOp n1 n2
| SignExtendTrunc n1 n2: UniBitOp n1 n2
| TruncLsb n1 n2 : UniBitOp (n1 + n2) n2. (* MSB : n2 *)

Inductive BinSign := SignSS | SignSU | SignUU.

Inductive BinBitOp: nat -> nat -> nat -> Set :=
| Add n: BinBitOp n n n
| Sub n: BinBitOp n n n
| Mul n: BinSign -> BinBitOp n n n
| Div n: bool -> BinBitOp n n n
| Rem n: bool -> BinBitOp n n n
| Band n: BinBitOp n n n
| Bor n: BinBitOp n n n
| Bxor n: BinBitOp n n n
| Sll n m: BinBitOp n m n
| Srl n m: BinBitOp n m n
| Sra n m: BinBitOp n m n
| Concat n1 n2: BinBitOp n1 n2 (n2 + n1). (* MSB : n1, LSB : n2 *)

Inductive BinBitBoolOp: nat -> nat -> Set :=
| Lt n: BinBitBoolOp n n
| Slt n: BinBitBoolOp n n.

Section Phoas.
  Variable ty: Kind -> Type.
  Definition fullType k := match k with
                           | SyntaxKind k' => ty k'
                           | NativeKind k' _ => k'
                           end.

  Definition FieldKind {n} (ls: Vector.t (Attribute Kind) n)
             (i: Fin.t n) :=
    Vector.nth (Vector.map (@attrType _) ls) i.

  Inductive Expr: FullKind -> Type :=
  | Var k: fullType k -> Expr k
  | Const k: ConstT k -> Expr (SyntaxKind k)
  | UniBool: UniBoolOp -> Expr (SyntaxKind Bool) -> Expr (SyntaxKind Bool)
  | BinBool: BinBoolOp -> Expr (SyntaxKind Bool) -> Expr (SyntaxKind Bool) -> Expr (SyntaxKind Bool)
  | UniBit n1 n2: UniBitOp n1 n2 -> Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2))
  | BinBit n1 n2 n3: BinBitOp n1 n2 n3 ->
                     Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2)) ->
                     Expr (SyntaxKind (Bit n3))
  | BinBitBool n1 n2: BinBitBoolOp n1 n2 ->
                      Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2)) ->
                      Expr (SyntaxKind Bool)
  | ITE k: Expr (SyntaxKind Bool) -> Expr k -> Expr k -> Expr k
  | Eq k: Expr (SyntaxKind k) -> Expr (SyntaxKind k) -> Expr (SyntaxKind Bool)
  | ReadIndex i k: Expr (SyntaxKind (Bit i)) ->
                   Expr (SyntaxKind (Vector k i)) -> Expr (SyntaxKind k)
  | ReadField n (ls: Vector.t _ n) (i: Fin.t n):
      Expr (SyntaxKind (Struct ls)) -> Expr (SyntaxKind (FieldKind ls i))
  | BuildVector n k: Vec (Expr (SyntaxKind n)) k -> Expr (SyntaxKind (Vector n k))
  | BuildStruct n (attrs: Vector.t _ n):
      ilist (fun a => Expr (SyntaxKind (attrType a))) attrs -> Expr (SyntaxKind (Struct attrs))
  | UpdateVector i k: Expr (SyntaxKind (Vector k i)) ->
                      Expr (SyntaxKind (Bit i)) -> Expr (SyntaxKind k) ->
                      Expr (SyntaxKind (Vector k i))
  | ReadArrayIndex i k sz: Expr (SyntaxKind (Bit i)) ->
                           Expr (SyntaxKind (Array k (S sz))) ->
                           Expr (SyntaxKind k)
  | BuildArray n k:
      Vector.t (Expr (SyntaxKind n)) k -> Expr (SyntaxKind (Array n k))
  | UpdateArray k sz i: Expr (SyntaxKind (Array k (S sz))) ->
                        Expr (SyntaxKind (Bit i)) ->
                        Expr (SyntaxKind k) ->
                        Expr (SyntaxKind (Array k (S sz))).

  Inductive BitFormat :=
  | Binary
  | Decimal
  | Hex.

  Definition FullBitFormat := (nat * BitFormat)%type.

  Inductive Disp: Type :=
  | DispBool: FullBitFormat -> Expr (SyntaxKind Bool) -> Disp
  | DispBit: FullBitFormat -> forall n, Expr (SyntaxKind (Bit n)) -> Disp
  | DispStruct n: (Vector.t FullBitFormat n) ->
                  forall ls, Expr (SyntaxKind (@Struct n ls)) -> Disp
  | DispArray: FullBitFormat -> forall n k, Expr (SyntaxKind (Array n k)) -> Disp.

  Inductive ActionT (lretT: Kind) : Type :=
  | MCall (meth: string) s:
      Expr (SyntaxKind (arg s)) ->
      (ty (ret s) -> ActionT lretT) ->
      ActionT lretT
  | Let_ lretT': Expr lretT' -> (fullType lretT' -> ActionT lretT) -> ActionT lretT
  | ReadNondet:
      forall k, (fullType k -> ActionT lretT) -> ActionT lretT
  | ReadReg (r: string):
      forall k, (fullType k -> ActionT lretT) -> ActionT lretT
  | WriteReg (r: string) k:
      Expr k -> ActionT lretT -> ActionT lretT
  | IfElse: Expr (SyntaxKind Bool) -> forall k,
                                        ActionT k ->
                                        ActionT k ->
                                        (ty k -> ActionT lretT) ->
                                        ActionT lretT
  | Assert_: Expr (SyntaxKind Bool) -> ActionT lretT -> ActionT lretT
  | Displ: list Disp -> ActionT lretT -> ActionT lretT
  | Return: Expr (SyntaxKind lretT) -> ActionT lretT.

  Section StructUpdate.
    
    Lemma nth_map_transparent {A B} (f: A -> B) {n} v (p1 p2: Fin.t n) (eq: p1 = p2):
      Vector.nth (Vector.map f v) p1 = f (Vector.nth v p2).
    Proof.
      subst p2; induction p1.
      - revert n v; refine (@caseS _ _ _); now simpl.
      - revert n v p1 IHp1; refine (@caseS _  _ _); now simpl.
    Defined.

    Fixpoint getFinList n: Vector.t (Fin.t n) n :=
      match n with
      | 0 => Vector.nil _
      | S m => Vector.cons _ Fin.F1 _ (Vector.map (fun x => Fin.FS x) (getFinList m))
      end.

    Fixpoint zipVector (A: Type) B n (va: Vector.t A n): Vector.t B n -> Vector.t (A * B) n :=
      match va in Vector.t _ n return Vector.t B n -> Vector.t (A * B) n
      with
      | Vector.nil => fun _ => Vector.nil _
      | Vector.cons a n' va' =>
        fun vb => match vb in Vector.t _ n2 return Vector.t A (pred n2) ->
                                                   Vector.t (A * B) n2 with
                  | Vector.nil => fun _ => Vector.nil _
                  | Vector.cons b n3 vb' =>
                    fun va' => Vector.cons _ (a, b) _ (zipVector va' vb')
                  end va'
      end.

    Definition getVectorFin (A: Type) n (ls: Vector.t A n) :=
      zipVector ls (getFinList n).

    Definition getIlistExpr' n (ls: Vector.t (Attribute Kind) n)
               (e: Expr (SyntaxKind (Struct ls))):
      ilist@{Set Type}
           (fun i : Attribute Kind * Fin.t n =>
              Expr (SyntaxKind (attrType (Vector.nth ls (snd i)))))
           (zipVector ls (getFinList n)) :=
      imap_list _ (fun i => match @nth_map_transparent _ _ (@attrType _) _
                                                       ls (snd i) (snd i) eq_refl
                                  in _ = Y
                                  return Expr (SyntaxKind Y)
                            with
                            | eq_refl => ReadField (snd i) e
                            end) (zipVector ls (getFinList n)).
    
    Lemma Vector_in_cons (A: Type) (P: A -> Prop) (h: A) n (ls: Vector.t A n):
      (forall a, Vector.In a (Vector.cons A h n ls) -> P a) ->
      forall x, Vector.In x ls -> P x.
    Proof.
      intros pf x in_pf; apply pf.
      apply Vector.In_cons_tl; assumption.
    Defined.

    Section Vec.
      Section VIn.
        Variable A: Type.
        Inductive vIn : A -> forall (n : nat), Vector.t A n -> Prop :=
          In_cons_hd : forall a (m : nat) (v : Vector.t A m), vIn a (Vector.cons A a m v)
        | In_cons_tl : forall a (m : nat) (x : A) (v : Vector.t A m),
            vIn a v -> vIn a (Vector.cons A x m v).

        Lemma vIn_In: forall (a: A) n vs, @vIn a n vs <-> @Vector.In _ a n vs.
        Proof.
          intros.
          split; intros.
          - induction H.
            + apply Vector.In_cons_hd.
            + apply Vector.In_cons_tl; auto.
          - induction H.
            + constructor.
            + constructor; auto.
        Defined.

        Fixpoint VIn (a: A) n (l: Vector.t A n) : Prop :=
          match l with
          | Vector.nil => False
          | Vector.cons b n' ls' => a = b \/ VIn a ls'
          end.

        Lemma VIn_In: forall (a: A) n vs, @VIn a n vs <-> @Vector.In _ a n vs.
        Proof.
          intros.
          split; intros.
          - induction vs.
            + simpl in *.
              exfalso; auto.
            + simpl in H.
              destruct H; subst; constructor; auto.
          - induction H; simpl; auto.
        Defined.

        Lemma in_cons: forall n (ls: Vector.t A n) a b,
            Vector.In a (Vector.cons _ b _ ls) -> a = b \/ Vector.In a ls.
        Proof.
          intros.
          apply VIn_In in H.
          destruct H.
          left; assumption.
          right; apply VIn_In; assumption.
        Defined.

        Lemma Vector_In_nil : forall a, ~ Vector.In a (Vector.nil A).
        Proof.
          unfold not; intros.
          apply VIn_In in H.
          simpl in H.
          assumption.
        Defined.
      End VIn.

      Variables A B: Type.

      Lemma in_zip2: forall n a b (la: Vector.t A n) (lb: Vector.t B n),
          Vector.In (a, b) (zipVector la lb) -> Vector.In b lb.
      Proof.
        induction la; intros.
        - rewrite <- vector_0_nil with (ls := lb) in H.
          simpl in H.
          apply Vector_In_nil in H.
          exfalso; auto.
        - specialize (IHla (Vector.tl lb)).
          rewrite Vector.eta with (v := lb) in H.
          simpl in H.
          apply in_cons in H.
          destruct H.
          + rewrite Vector.eta with (v := lb).
            inv H.
            apply Vector.In_cons_hd.
          + specialize (IHla H).
            rewrite Vector.eta with (v := lb).
            econstructor; eauto.
      Defined.
    End Vec.

    Section Overall.
      Section Imap_change_vec.
        Variable A: Set.
        Variable B: Set.
        Variable f: A -> Type.
        Variable g: B -> Type.
        Variable h: A -> B.
        Fixpoint imap_change_vec n (ls: Vector.t A n):
          ilist f ls -> (forall a, Vector.In a ls -> f a = g (h a)) -> ilist g (Vector.map h ls)
          := match ls in Vector.t _ n
                   return ilist f ls -> (forall a, Vector.In a ls -> f a = g (h a)) ->
                          ilist g (Vector.map h ls)
             with
             | Vector.nil => fun _ _ => inil _
             | Vector.cons h0 n0 ls0 =>
               fun ila pf =>
                 icons (h h0) match pf _ (Vector.In_cons_hd _ _) in _ = Y return Y with
                              | eq_refl => ilist_hd' ila
                              end (imap_change_vec (ilist_tl' ila) (Vector_in_cons _ pf))
             end.
      End Imap_change_vec.

      Section Map.
        Variable A B C: Type.
        Variable f: B -> C.

        Lemma map_zip n (la: Vector.t A n):
          forall (lb: Vector.t B n),
            Vector.map fst (zipVector la lb) = la.
        Proof.
          induction la; intros; auto.
          specialize (IHla (Vector.tl lb)).
          rewrite Vector.eta with (v := lb).
          simpl.
          f_equal; auto.
        Defined.

        Lemma in_zip_map n (la: Vector.t A n):
          forall (lb: Vector.t B n) a c,
            Vector.In (a, c) (zipVector la (Vector.map f lb)) ->
            exists b, c = f b /\ Vector.In (a, b) (zipVector la lb).
        Proof.
          induction la; intros; auto.
          - apply Vector_In_nil in H; exfalso; auto.
          - rewrite Vector.eta with (v := lb) in H.
            simpl in H.
            apply in_cons in H.
            destruct H.
            + inversion H; subst.
              exists (Vector.hd lb).
              split.
              * reflexivity.
              * rewrite Vector.eta with (v := lb).
                simpl.
                apply Vector.In_cons_hd.
            + rewrite Vector.eta with (v := lb).
              specialize (IHla _ _ _ H).
              destruct IHla as [b [ceq vin]].
              simpl.
              exists b.
              split; auto.
              apply Vector.In_cons_tl; auto.
        Defined.
      End Map.

      Variable A: Set.
      Variable f: A -> Type.

      Lemma in_eq n ls:
        (forall a : A * Fin.t n,
            Vector.In a (zipVector ls (getFinList n)) ->
            (fun i : A * Fin.t n => f (Vector.nth ls (snd i))) a = f (fst a)).
      Proof.
        induction ls; intros; destruct a.
        - apply Fin.case0; assumption.
        - simpl in H.
          cbv [fst snd].
          apply in_cons in H.
          destruct H.
          + inversion H; subst.
            reflexivity.
          + apply in_zip_map in H.
            dest; subst.
            apply IHls in H0.
            apply H0.
      Defined.

      Definition elim_fin n (ls: Vector.t A n)
                 (il: ilist@{Set Type} (fun i: (A * Fin.t n) => f (Vector.nth ls (snd i)))
                           (zipVector ls (getFinList n))): ilist@{Set Type} f ls :=
        match map_zip ls (getFinList n) in _ = Y return _ Y with
        | eq_refl => imap_change_vec f (@fst A (Fin.t n)) il (in_eq ls)
        end.
    End Overall.

    Definition getIlistExpr n (ls: Vector.t (Attribute Kind) n)
               (e: Expr (SyntaxKind (Struct ls))):
      ilist@{Set Type} (fun a => Expr (SyntaxKind (attrType a))) ls :=
      elim_fin _ _ (getIlistExpr' e).

    Definition updStruct n (ls: Vector.t (Attribute Kind) n) (e: Expr (SyntaxKind (Struct ls)))
               (i: Fin.t n)
               (v: Expr (SyntaxKind (Vector.nth (Vector.map (@attrType _) ls) i))):
      Expr (SyntaxKind (Struct ls)) :=
      BuildStruct
        (replace_Index (getIlistExpr e) i
                       (match @nth_map_transparent _ _ (@attrType _) _ ls i i eq_refl
                              in _ = Y return Expr (SyntaxKind Y) with
                        | eq_refl => v
                        end)).
  End StructUpdate.

End Phoas.

Definition Action (retTy : Kind) := forall ty, ActionT ty retTy.
Definition MethodT (sig : SignatureT) := forall ty, ty (arg sig) -> ActionT ty (ret sig).

Inductive RegInitValue :=
| RegInitCustom: sigT ConstFullT -> RegInitValue
| RegInitDefault: FullKind -> RegInitValue.

Definition RegInitT := Attribute RegInitValue.
Definition DefMethT := Attribute (sigT MethodT).

Definition filterDm (dms: list DefMethT) (filt: string) :=
  filter (fun dm => if string_dec (attrName dm) filt then false else true) dms.

Definition filterDms (dms: list DefMethT) (filt: list string) :=
  filter (fun dm => if string_in (attrName dm) filt then false else true) dms.

Definition Void := Bit 0.

Record PrimitiveModule :=
  { pm_name: string;
    pm_regInits: list RegInitT;
    pm_rules: list (Attribute (Action Void));
    pm_methods: list DefMethT }.

Inductive Modules: Type :=
| PrimMod (prim: PrimitiveModule): Modules
| Mod (regs: list RegInitT)
      (rules: list (Attribute (Action Void)))
      (dms: list DefMethT): Modules
| ConcatMod (m1 m2: Modules): Modules.

Fixpoint getRules m :=
  match m with
  | PrimMod prim => prim.(pm_rules)
  | Mod _ rules _ => rules
  | ConcatMod m1 m2 => getRules m1 ++ getRules m2
  end.

Fixpoint getRegInits m :=
  match m with
  | PrimMod prim => prim.(pm_regInits)
  | Mod regs _ _ => regs
  | ConcatMod m1 m2 => getRegInits m1 ++ getRegInits m2
  end.

Fixpoint getDefsBodies (m: Modules): list DefMethT :=
  match m with
  | PrimMod prim => prim.(pm_methods)
  | Mod _ _ meths => meths
  | ConcatMod m1 m2 => (getDefsBodies m1) ++ (getDefsBodies m2)
  end.

Definition getDefs m: list string := namesOf (getDefsBodies m).

Lemma getDefs_in:
  forall ma mb k,
    In k (getDefs (ConcatMod ma mb)) ->
    In k (getDefs ma) \/ In k (getDefs mb).
Proof.
  unfold getDefs, namesOf; intros.
  simpl in *; rewrite map_app in H.
  apply in_app_or; auto.
Qed.

Lemma getDefs_in_1:
  forall ma mb k,
    In k (getDefs ma) -> In k (getDefs (ConcatMod ma mb)).
Proof.
  unfold getDefs, namesOf; intros.
  simpl in *; rewrite map_app.
  apply in_or_app; auto.
Qed.

Lemma getDefs_in_2:
  forall ma mb k,
    In k (getDefs mb) -> In k (getDefs (ConcatMod ma mb)).
Proof.
  unfold getDefs, namesOf; intros.
  simpl in *; rewrite map_app.
  apply in_or_app; auto.
Qed.

Lemma getDefs_app:
  forall ma mb,
    getDefs (ConcatMod ma mb) = getDefs ma ++ getDefs mb.
Proof.
  intros.
  unfold getDefs; simpl.
  unfold namesOf; rewrite map_app; reflexivity.
Qed.

Section AppendAction.
  Variable ty: Kind -> Type.

  Fixpoint appendAction {retT1 retT2} (a1: ActionT ty retT1)
           (a2: ty retT1 -> ActionT ty retT2): ActionT ty retT2 :=
    match a1 with
      | MCall name sig ar cont => MCall name sig ar (fun a => appendAction (cont a) a2)
      | Let_ _ ar cont => Let_ ar (fun a => appendAction (cont a) a2)
      | ReadNondet k cont => ReadNondet k (fun a => appendAction (cont a) a2)
      | ReadReg reg k cont => ReadReg reg k (fun a => appendAction (cont a) a2)
      | WriteReg reg _ e cont => WriteReg reg e (appendAction cont a2)
      | IfElse ce _ ta fa cont => IfElse ce ta fa (fun a => appendAction (cont a) a2)
      | Assert_ ae cont => Assert_ ae (appendAction cont a2)
      | Displ ls cont => Displ ls (appendAction cont a2)
      | Return e => Let_ e a2
    end.

  Lemma appendAction_assoc:
    forall {retT1 retT2 retT3}
           (a1: ActionT ty retT1) (a2: ty retT1 -> ActionT ty retT2)
           (a3: ty retT2 -> ActionT ty retT3),
      appendAction a1 (fun t => appendAction (a2 t) a3) = appendAction (appendAction a1 a2) a3.
  Proof.
    induction a1; simpl; intuition idtac; f_equal; try extensionality x; eauto.
  Qed.

End AppendAction.

Section GetCalls.
  Definition typeUT (k: Kind): Type := unit.
  Definition fullTypeUT := fullType typeUT.
  Definition getUT (k: FullKind): fullTypeUT k :=
    match k with
      | SyntaxKind _ => tt
      | NativeKind t c => c
    end.

  Fixpoint getCallsA_Sig {k} (a: ActionT typeUT k): list (string * SignatureT) :=
    match a with
      | MCall m s _ c => (m, s) :: (getCallsA_Sig (c tt))
      | Let_ fk e c => getCallsA_Sig
                         (c match fk as fk' return fullType typeUT fk' with
                              | SyntaxKind _ => tt
                              | NativeKind _ c' => c'
                            end)
      | ReadNondet fk c => getCallsA_Sig
                             (c match fk as fk' return fullType typeUT fk' with
                                | SyntaxKind _ => tt
                                | NativeKind _ c' => c'
                                end)
      | ReadReg _ fk c => getCallsA_Sig
                            (c match fk as fk' return fullType typeUT fk' with
                                 | SyntaxKind _ => tt
                                 | NativeKind _ c' => c'
                               end)
      | WriteReg _ _ _ c => getCallsA_Sig c
      | IfElse _ _ aT aF c =>
        (getCallsA_Sig aT) ++ (getCallsA_Sig aF)
                           ++ (getCallsA_Sig (c tt))
      | Assert_ _ c => getCallsA_Sig c
      | Displ ls c => getCallsA_Sig c
      | Return _ => nil
    end.

  Fixpoint getCallsA {k} (a: ActionT typeUT k): list string :=
    match a with
      | MCall m _ _ c => m :: (getCallsA (c tt))
      | Let_ fk e c => getCallsA
                         (c match fk as fk' return fullType typeUT fk' with
                              | SyntaxKind _ => tt
                              | NativeKind _ c' => c'
                            end)
      | ReadNondet fk c => getCallsA
                            (c match fk as fk' return fullType typeUT fk' with
                                 | SyntaxKind _ => tt
                                 | NativeKind _ c' => c'
                               end)
      | ReadReg _ fk c => getCallsA
                            (c match fk as fk' return fullType typeUT fk' with
                                 | SyntaxKind _ => tt
                                 | NativeKind _ c' => c'
                               end)
      | WriteReg _ _ _ c => getCallsA c
      | IfElse _ _ aT aF c =>
        (getCallsA aT) ++ (getCallsA aF)
                       ++ (getCallsA (c tt))
      | Assert_ _ c => getCallsA c
      | Displ ls c => getCallsA c
      | Return _ => nil
    end.

  Lemma getCallsA_Sig_getCallsA k (a: ActionT typeUT k):
    map fst (getCallsA_Sig a) = getCallsA a.
  Proof.
    induction a; auto; simpl; try f_equal; firstorder idtac.
    rewrite ?map_app; congruence.
  Qed.

  Lemma getCallsA_appendAction:
    forall {retK1} (a1: ActionT typeUT retK1)
           {retK2} (a2: typeUT retK1 -> ActionT typeUT retK2),
      getCallsA (appendAction a1 a2) =
      getCallsA a1 ++ getCallsA (a2 tt).
  Proof.
    induction a1; simpl; intros; auto.
    - f_equal; auto.
    - do 2 rewrite <-app_assoc.
      f_equal; f_equal; auto.
  Qed.

  Definition getCallsRule (r: Attribute (Action (Bit 0)))
  : list string :=
    getCallsA (attrType r typeUT).

  Definition getCallsRule_Sig (r: Attribute (Action (Bit 0))) :=
    getCallsA_Sig (attrType r typeUT).

  Lemma getCallsRule_Sig_getCallsRule r:
    map fst (getCallsRule_Sig r) = getCallsRule r.
  Proof.
    unfold getCallsRule_Sig, getCallsRule.
    rewrite getCallsA_Sig_getCallsA.
    auto.
  Qed.

  Fixpoint getCallsR (rl: list (Attribute (Action (Bit 0))))
  : list string :=
    match rl with
      | nil => nil
      | r :: rl' => (getCallsA (attrType r typeUT)) ++ (getCallsR rl')
    end.

  Fixpoint getCallsR_Sig (rl: list (Attribute (Action (Bit 0)))) :=
    match rl with
      | nil => nil
      | r :: rl' => (getCallsA_Sig (attrType r typeUT)) ++ (getCallsR_Sig rl')
    end.

  Lemma getCallsR_Sig_getCallsR r:
    map fst (getCallsR_Sig r) = getCallsR r.
  Proof.
    induction r; auto; simpl.
    rewrite map_app.
    rewrite IHr.
    rewrite getCallsA_Sig_getCallsA.
    auto.
  Qed.

  Definition getCallsDm (dm: DefMethT): list string :=
    getCallsA (projT2 (attrType dm) typeUT tt).

  Definition getCallsDm_Sig (dm: DefMethT) :=
    getCallsA_Sig (projT2 (attrType dm) typeUT tt).

  Lemma getCallsDm_Sig_getCallsDm r:
    map fst (getCallsDm_Sig r) = getCallsDm r.
  Proof.
    unfold getCallsDm_Sig, getCallsDm.
    rewrite getCallsA_Sig_getCallsA.
    auto.
  Qed.

  Fixpoint getCallsM (ms: list DefMethT): list string :=
    match ms with
      | nil => nil
      | m :: ms' => (getCallsA ((projT2 (attrType m)) typeUT tt))
                      ++ (getCallsM ms')
    end.

  Fixpoint getCallsM_Sig (ms: list DefMethT) :=
    match ms with
      | nil => nil
      | m :: ms' => (getCallsA_Sig ((projT2 (attrType m)) typeUT tt))
                      ++ (getCallsM_Sig ms')
    end.

  Lemma getCallsM_Sig_getCallsM r:
    map fst (getCallsM_Sig r) = getCallsM r.
  Proof.
    induction r; simpl; auto.
    rewrite map_app, IHr, getCallsA_Sig_getCallsA.
    auto.
  Qed.

  Lemma getCallsM_implies_getCallsDm s ms:
    In s (getCallsM ms) -> exists dm, In dm ms /\ In s (getCallsDm dm).
  Proof.
    induction ms; intros; simpl in *.
    - intuition.
    - apply in_app_or in H.
      destruct H.
      + exists a.
        intuition.
      + specialize (IHms H).
        destruct IHms.
        destruct H0.
        exists x.
        intuition.
  Qed.

  Lemma getCallsM_app: forall ms1 ms2, getCallsM (ms1 ++ ms2) = getCallsM ms1 ++ getCallsM ms2.
  Proof.
    induction ms1; intros; [reflexivity|].
    simpl; rewrite IHms1; apply app_assoc.
  Qed.

  Lemma getCallsR_app: forall ms1 ms2, getCallsR (ms1 ++ ms2) = getCallsR ms1 ++ getCallsR ms2.
  Proof.
    induction ms1; intros; [reflexivity|].
    simpl; rewrite IHms1; apply app_assoc.
  Qed.

  Definition getCalls m := getCallsR (getRules m) ++ getCallsM (getDefsBodies m).

  Definition getCalls_Sig m := getCallsR_Sig (getRules m) ++ getCallsM_Sig (getDefsBodies m).

  Lemma getCalls_Sig_getCalls m:
    map fst (getCalls_Sig m) = getCalls m.
  Proof.
    unfold getCalls_Sig, getCalls.
    rewrite map_app, getCallsR_Sig_getCallsR, getCallsM_Sig_getCallsM.
    auto.
  Qed.

  Lemma getCalls_in:
    forall ma mb k,
      In k (getCalls (ConcatMod ma mb)) ->
      In k (getCalls ma) \/ In k (getCalls mb).
  Proof.
    unfold getCalls; intros.
    apply in_app_or in H; destruct H.
    - simpl in H; rewrite getCallsR_app in H.
      apply in_app_or in H; destruct H.
      + left; apply in_or_app; auto.
      + right; apply in_or_app; auto.
    - simpl in H; rewrite getCallsM_app in H.
      apply in_app_or in H; destruct H.
      + left; apply in_or_app; auto.
      + right; apply in_or_app; auto.
  Qed.

  Lemma getCalls_in_1:
    forall ma mb k,
      In k (getCalls ma) -> In k (getCalls (ConcatMod ma mb)).
  Proof.
    unfold getCalls; intros.
    apply in_or_app; apply in_app_or in H; destruct H.
    - left; simpl; rewrite getCallsR_app.
      apply in_or_app; auto.
    - right; simpl; rewrite getCallsM_app.
      apply in_or_app; auto.
  Qed.

  Lemma getCalls_in_2:
    forall ma mb k,
      In k (getCalls mb) -> In k (getCalls (ConcatMod ma mb)).
  Proof.
    unfold getCalls; intros.
    apply in_or_app; apply in_app_or in H; destruct H.
    - left; simpl; rewrite getCallsR_app.
      apply in_or_app; auto.
    - right; simpl; rewrite getCallsM_app.
      apply in_or_app; auto.
  Qed.

  Lemma getCalls_subList_1:
    forall m1 m2, SubList (getCalls m1 ++ getCalls m2) (getCalls (ConcatMod m1 m2)).
  Proof.
    unfold SubList; intros.
    apply in_app_or in H; destruct H.
    - apply getCalls_in_1; auto.
    - apply getCalls_in_2; auto.
  Qed.

  Lemma getCalls_subList_2:
    forall m1 m2, SubList (getCalls (ConcatMod m1 m2)) (getCalls m1 ++ getCalls m2).
  Proof.
    unfold SubList; intros.
    apply getCalls_in in H; destruct H; apply in_or_app; auto.
  Qed.

  Lemma getCallsR_SubList:
    forall ra rb,
      SubList ra rb ->
      SubList (getCallsR ra) (getCallsR rb).
  Proof.
    induction ra; simpl; intros.
    - apply SubList_nil.
    - apply SubList_cons_inv in H; dest.
      apply SubList_app_3; auto.
      clear -H; induction rb; simpl; [inv H|].
      inv H.
      + apply SubList_app_1, SubList_refl.
      + apply SubList_app_2; auto.
  Qed.

  Lemma getCallsM_SubList:
    forall ra rb,
      SubList ra rb ->
      SubList (getCallsM ra) (getCallsM rb).
  Proof.
    induction ra; simpl; intros.
    - apply SubList_nil.
    - apply SubList_cons_inv in H; dest.
      apply SubList_app_3; auto.
      clear -H; induction rb; simpl; [inv H|].
      inv H.
      + apply SubList_app_1, SubList_refl.
      + apply SubList_app_2; auto.
  Qed.

  Lemma module_structure_indep_getCalls:
    forall ma mb,
      SubList (getRules ma) (getRules mb) ->
      SubList (getDefsBodies ma) (getDefsBodies mb) ->
      SubList (getCalls ma) (getCalls mb).
  Proof.
    intros.
    unfold getCalls.
    apply SubList_app_3.
    - apply SubList_app_1.
      apply getCallsR_SubList; auto.
    - apply SubList_app_2.
      apply getCallsM_SubList; auto.
  Qed.

  Definition DefCallSub (impl spec: Modules) :=
    SubList (getDefs spec) (getDefs impl) /\
    SubList (getCalls spec) (getCalls impl).

  Lemma DefCallSub_refl:
    forall m, DefCallSub m m.
  Proof.
    intros; split; apply SubList_refl.
  Qed.
  #[local] Hint Immediate DefCallSub_refl.

  Lemma DefCallSub_modular:
    forall m1 m2 m3 m4,
      DefCallSub m1 m3 ->
      DefCallSub m2 m4 ->
      DefCallSub (ConcatMod m1 m2) (ConcatMod m3 m4).
  Proof.
    unfold DefCallSub, SubList; intros; dest; split; intros.
    - specialize (H e); specialize (H0 e); specialize (H1 e); specialize (H2 e).
      apply getDefs_in in H3; destruct H3.
      + apply getDefs_in_1; auto.
      + apply getDefs_in_2; auto.
    - specialize (H e); specialize (H0 e); specialize (H1 e); specialize (H2 e).
      apply getCalls_in in H3; destruct H3.
      + apply getCalls_in_1; auto.
      + apply getCalls_in_2; auto.
  Qed.

End GetCalls.

Section NoInternalCalls.
  Fixpoint isLeaf {retT} (a: ActionT typeUT retT) (cs: list string) :=
    match a with
    | MCall name _ _ cont => (negb (string_in name cs)) && (isLeaf (cont tt) cs)
    | Let_ _ ar cont => isLeaf (cont (getUT _)) cs
    | ReadNondet k cont => isLeaf (cont (getUT _)) cs
    | ReadReg reg k cont => isLeaf (cont (getUT _)) cs
    | WriteReg reg _ e cont => isLeaf cont cs
    | IfElse ce _ ta fa cont => (isLeaf ta cs) && (isLeaf fa cs) && (isLeaf (cont tt) cs)
    | Assert_ ae cont => isLeaf cont cs
    | Displ ls cont => isLeaf cont cs
    | Return e => true
    end.

  Definition noCallDm (dm: DefMethT) (tgt: DefMethT) :=
    isLeaf (projT2 (attrType dm) typeUT tt) (attrName tgt :: nil).

  Fixpoint noCallsDms (dms: list DefMethT) (calls: list string) :=
    match dms with
    | nil => true
    | dm :: dms' =>
      if isLeaf (projT2 (attrType dm) typeUT tt) calls
      then noCallsDms dms' calls
      else false
    end.

  Fixpoint noCallsRules (rules: list (Attribute (Action Void)))
           (calls: list string) :=
    match rules with
    | nil => true
    | r :: rules' =>
      if isLeaf (attrType r typeUT) calls
      then noCallsRules rules' calls
      else false
    end.

  Definition noCalls (m: Modules) (calls: list string) :=
    (noCallsRules (getRules m) calls)
      && (noCallsDms (getDefsBodies m) calls).

  Definition noInternalCalls (m: Modules) :=
    noCalls m (getDefs m).

End NoInternalCalls.

Definition getExtDefsBodies (m: Modules) :=
  filter (fun dm => negb (string_in (attrName dm) (getCalls m))) (getDefsBodies m).

Definition getExtDefs (m: Modules) :=
  filter (fun d => negb (string_in d (getCalls m))) (getDefs m).

Definition getExtCalls (m: Modules) :=
  filter (fun c => negb (string_in c (getDefs m))) (getCalls m).

Definition getIntDefs (m: Modules) :=
  filter (fun d => string_in d (getCalls m)) (getDefs m).

Definition getIntCalls (m: Modules) :=
  filter (fun c => string_in c (getDefs m)) (getCalls m).

Definition getExtMeths (m: Modules) := getExtDefs m ++ getExtCalls m.
Definition getIntMeths (m: Modules) := getIntDefs m ++ getIntCalls m.

Lemma getExtDefs_getDefs:
  forall m, SubList (getExtDefs m) (getDefs m).
Proof.
  unfold SubList, getExtDefs; intros.
  apply filter_In in H; dest; auto.
Qed.

Lemma getExtCalls_getCalls:
  forall m, SubList (getExtCalls m) (getCalls m).
Proof.
  unfold SubList, getExtCalls; intros.
  apply filter_In in H; dest; auto.
Qed.

Lemma getExtMeths_meths:
  forall m, SubList (getExtMeths m) (getDefs m ++ getCalls m).
Proof.
  intros; apply SubList_app_3.
  - apply SubList_app_1, getExtDefs_getDefs.
  - apply SubList_app_2, getExtCalls_getCalls.
Qed.

Lemma getIntDefs_getDefs:
  forall m, SubList (getIntDefs m) (getDefs m).
Proof.
  unfold SubList, getIntDefs; intros.
  apply filter_In in H; dest; auto.
Qed.

Lemma getIntCalls_getCalls:
  forall m, SubList (getIntCalls m) (getCalls m).
Proof.
  unfold SubList, getIntCalls; intros.
  apply filter_In in H; dest; auto.
Qed.

Lemma getIntMeths_meths:
  forall m, SubList (getIntMeths m) (getDefs m ++ getCalls m).
Proof.
  intros; apply SubList_app_3.
  - apply SubList_app_1, getIntDefs_getDefs.
  - apply SubList_app_2, getIntCalls_getCalls.
Qed.

Lemma getIntCalls_getExtCalls_disj:
  forall m, DisjList (getIntCalls m) (getExtCalls m).
Proof.
  unfold getIntCalls, getExtCalls; intros.
  apply DisjList_logic; intros.
  apply filter_In in H; apply filter_In in H0; dest.
  rewrite H2 in H1; discriminate.
Qed.

Lemma getIntDefs_getExtDefs_disj:
  forall m, DisjList (getIntDefs m) (getExtDefs m).
Proof.
  unfold getIntDefs, getExtDefs; intros.
  apply DisjList_logic; intros.
  apply filter_In in H; apply filter_In in H0; dest.
  rewrite H2 in H1; discriminate.
Qed.

Lemma getCalls_flattened:
  forall m,
    getCalls (Mod (getRegInits m) (getRules m) (getDefsBodies m)) =
    getCalls m.
Proof. reflexivity. Qed.

Lemma getDefs_flattened:
  forall m,
    getDefs (Mod (getRegInits m) (getRules m) (getDefsBodies m)) =
    getDefs m.
Proof. reflexivity. Qed.

Lemma getExtDefs_in:
  forall m1 m2 s,
    In s (getExtDefs (ConcatMod m1 m2)) ->
    In s (getExtDefs m1) \/ In s (getExtDefs m2).
Proof.
  unfold getExtDefs; intros.
  apply filter_In in H; dest.
  apply negb_true_iff, eq_sym in H0.
  apply string_in_dec_not_in in H0.
  rewrite getDefs_app in H; apply in_app_or in H; destruct H.
  - left; apply filter_In; split; auto.
    apply negb_true_iff.
    remember (string_in _ _) as sin; destruct sin; auto.
    apply string_in_dec_in in Heqsin.
    elim H0; apply getCalls_in_1; auto.
  - right; apply filter_In; split; auto.
    apply negb_true_iff.
    remember (string_in _ _) as sin; destruct sin; auto.
    apply string_in_dec_in in Heqsin.
    elim H0; apply getCalls_in_2; auto.
Qed.

Lemma getExtCalls_in:
  forall m1 m2 s,
    In s (getExtCalls (ConcatMod m1 m2)) ->
    In s (getExtCalls m1) \/ In s (getExtCalls m2).
Proof.
  unfold getExtCalls; intros.
  apply filter_In in H; dest.
  apply negb_true_iff, eq_sym in H0.
  apply string_in_dec_not_in in H0.
  apply getCalls_in in H; destruct H.
  - left; apply filter_In; split; auto.
    apply negb_true_iff.
    remember (string_in _ _) as sin; destruct sin; auto.
    apply string_in_dec_in in Heqsin.
    elim H0; rewrite getDefs_app; apply in_or_app; auto.
  - right; apply filter_In; split; auto.
    apply negb_true_iff.
    remember (string_in _ _) as sin; destruct sin; auto.
    apply string_in_dec_in in Heqsin.
    elim H0; rewrite getDefs_app; apply in_or_app; auto.
Qed.

Lemma getExtMeths_in:
  forall m1 m2 s,
    In s (getExtMeths (ConcatMod m1 m2)) ->
    In s (getExtMeths m1) \/ In s (getExtMeths m2).
Proof.
  unfold getExtMeths; intros.
  apply in_app_or in H; destruct H.
  - apply getExtDefs_in in H; destruct H.
    + left; apply in_or_app; auto.
    + right; apply in_or_app; auto.
  - apply getExtCalls_in in H; destruct H.
    + left; apply in_or_app; auto.
    + right; apply in_or_app; auto.
Qed.

#[global] Hint Unfold pm_rules pm_regInits pm_methods
     getRules getRegInits getDefs getCalls getDefsBodies
     getExtDefsBodies getExtDefs getExtCalls getExtMeths
     getIntDefs getIntCalls getIntMeths.

(** Notations *)

Declare Scope kami_struct_scope.
Notation "name :: ty" := {| attrName := name; attrType := ty |} : kami_struct_scope.
Delimit Scope kami_struct_scope with struct.

Declare Scope kami_scope.
Notation "m1 ++ m2" := (ConcatMod m1 m2) : kami_scope.
Delimit Scope kami_scope with kami.
