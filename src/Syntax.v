Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word.

Set Implicit Arguments.

Fixpoint getDefaultConstBit n: word n :=
  match n with
    | 0 => WO
    | S m => WS false (getDefaultConstBit m)
  end.

Section Vec.
  Variable A: Type.

  (* `Vec n` is effectively a map from bit vectors of length
     `n` to elements of `A` *)
  Inductive Vec: nat -> Type :=
  | Vec0: A -> Vec 0
  | VecNext n: Vec n -> Vec n -> Vec (S n).

  Fixpoint replicate (v: A) n :=
    match n with
      | 0 => Vec0 v
      | S m => VecNext (replicate v m) (replicate v m)
    end.
End Vec.

(*
Record Universe :=
  { Univ     : Set    (* set of codes for the universe *)
  ; typeU    : Univ -> Set (* decoding function *)
  ; decUniv  : forall (t1 t2 : Univ), {t1 = t2} + {t1 <> t2}
               (* decidable equality on codes *)
  ; decEqU   : forall (t : Univ) (x y : typeU t), {x = y} + {x <> y}
               (* decidable equality on all Coq Sets in the universe *)
  ; defaultU : forall (u : Univ), typeU u 
               (* default values for each Coq Set in the universe *)
  }.
*)

(*
Section Kinds.

Context {U : Universe}.
*)

Inductive Kind: Type :=
| Bool    : Kind
| Bit     : nat -> Kind
| Vector  : Kind -> nat -> Kind
| Struct  : list (Attribute Kind) -> Kind.

Inductive FullKind: Type :=
| SyntaxKind: Kind -> FullKind
| NativeKind (t: Type) (c: t) : FullKind.

Fixpoint decKind (k1 k2: Kind) : {k1 = k2} + {k1 <> k2}.
Proof.
  decide equality.
  clear decKind; decide equality.
  clear decKind; decide equality.
  decide equality.
  decide equality.
  apply (string_dec).
Defined.

Inductive ConstT: Kind -> Type :=
| ConstBool: bool -> ConstT Bool
| ConstBit n: word n -> ConstT (Bit n)
| ConstVector k n: Vec (ConstT k) n -> ConstT (Vector k n)
| ConstStruct attrs: ilist (fun a => ConstT (attrType a)) attrs -> ConstT (Struct attrs).

Inductive ConstFullT: FullKind -> Type :=
| SyntaxConst k: ConstT k -> ConstFullT (SyntaxKind k)
| NativeConst t (c c': t): ConstFullT (NativeKind c).

Coercion ConstBool : bool >-> ConstT.
Coercion ConstBit : word >-> ConstT.

Fixpoint getDefaultConst (k: Kind): ConstT k :=
  match k with
    | Bool => ConstBool false
    | Bit n => ConstBit (getDefaultConstBit n)
    | Vector k n => ConstVector (replicate (getDefaultConst k) n)
    | Struct ls =>
      ConstStruct ((fix help ls :=
                      match ls return ilist (fun a => ConstT (attrType a)) ls with
                        | nil => inil _
                        | x :: xs => icons x (getDefaultConst (attrType x)) (help xs)
                      end) ls)
  end.

(*
Definition RegKey := Attribute Kind.

Definition RegKey_dec: forall (s1 s2: Attribute Kind), {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  decide equality.
  apply decKind.
  apply string_dec.
Qed.
*)

Record SignatureT :=
  { arg: Kind;
    ret: Kind
  }.

(*
Definition MethKey := Attribute SignatureT.
*)

Definition SignatureT_dec: forall (s1 s2: SignatureT), {s1 = s2} + {s1 <> s2}.
Proof.
  intros.
  decide equality.
  apply decKind.
  apply decKind.
Qed.

Inductive UniBoolOp: Set :=
| Neg: UniBoolOp.

Inductive BinBoolOp: Set :=
| And: BinBoolOp
| Or: BinBoolOp.

Inductive UniBitOp: nat -> nat -> Set :=
| Inv n: UniBitOp n n
| ConstExtract n1 n2 n3: UniBitOp (n1 + n2 + n3) n2
| ZeroExtendTrunc n1 n2: UniBitOp n1 n2
| SignExtendTrunc n1 n2: UniBitOp n1 n2
| TruncLsb n1 n2: UniBitOp (n1 + n2) n1.

Inductive BinBitOp: nat -> nat -> nat -> Set :=
| Add n: BinBitOp n n n
| Sub n: BinBitOp n n n.

Section Phoas.
  Variable type: Kind -> Type.
  Definition fullType k := match k with
                             | SyntaxKind k' => type k'
                             | NativeKind t c => t
                           end.
  
  Inductive Expr: FullKind -> Type :=
  | Var k: fullType k -> Expr k
  | Const k: ConstT k -> Expr (SyntaxKind k)
  | UniBool: UniBoolOp -> Expr (SyntaxKind Bool) -> Expr (SyntaxKind Bool)
  | BinBool: BinBoolOp -> Expr (SyntaxKind Bool) -> Expr (SyntaxKind Bool) -> Expr (SyntaxKind Bool)
  | UniBit n1 n2: UniBitOp n1 n2 -> Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2))
  | BinBit n1 n2 n3: BinBitOp n1 n2 n3 -> Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2)) ->
                     Expr (SyntaxKind (Bit n3))
  | ITE k: Expr (SyntaxKind Bool) -> Expr k -> Expr k -> Expr k
  | Eq k: Expr (SyntaxKind k) -> Expr (SyntaxKind k) -> Expr (SyntaxKind Bool)
  | ReadIndex i k: Expr (SyntaxKind (Bit i)) -> Expr (SyntaxKind (Vector k i)) -> Expr (SyntaxKind k)
  | ReadField attrs (attr: BoundedIndexFull attrs):
      Expr (SyntaxKind (Struct attrs)) -> Expr (SyntaxKind (GetAttrType attr))
  | BuildVector n k: Vec (Expr (SyntaxKind n)) k -> Expr (SyntaxKind (Vector n k))
  | BuildStruct attrs: ilist (fun a => Expr (SyntaxKind (attrType a))) attrs -> Expr (SyntaxKind (Struct attrs))
  | UpdateVector i k: Expr (SyntaxKind (Vector k i)) -> Expr (SyntaxKind (Bit i)) -> Expr (SyntaxKind k)
                      -> Expr (SyntaxKind (Vector k i)).

  Inductive Action (lretT: Kind) : Type :=
  | MCall (meth: string) s:
      Expr (SyntaxKind (arg s)) ->
      (type (ret s) -> Action lretT) ->
      Action lretT
  | Let_ lretT': Expr lretT' -> (fullType lretT' -> Action lretT) -> Action lretT
  | ReadReg (r: string):
      forall k, (fullType k -> Action lretT) -> Action lretT
  | WriteReg (r: string) k:
      Expr k -> Action lretT -> Action lretT
  | IfElse: Expr (SyntaxKind Bool) -> forall k,
                                        Action k ->
                                        Action k ->
                                        (type k -> Action lretT) ->
                                        Action lretT
  | Assert_: Expr (SyntaxKind Bool) -> Action lretT -> Action lretT
  | Return: Expr (SyntaxKind lretT) -> Action lretT.

  Definition RegInitT := Attribute (Typed ConstFullT).
  Definition DefMethT := Attribute (Typed (fun (a: SignatureT) =>
                                             type (arg a) ->
                                             Action (ret a))).

  Inductive Modules: Type :=
  | Mod (regs: list RegInitT)
        (rules: list (Attribute (Action (Bit 0))))
        (dms: list DefMethT):
      Modules
  | ConcatMod (m1 m2: Modules):
    Modules.

  Fixpoint getRules m := 
    match m with
      | Mod _ rules _ => rules
      | ConcatMod m1 m2 => getRules m1 ++ getRules m2
    end.

  Fixpoint getRegInits m :=
    match m with
      | Mod regs _ _ => regs
      | ConcatMod m1 m2 => getRegInits m1 ++ getRegInits m2
    end.

End Phoas.

Hint Unfold getRules getRegInits.


(* Notations: registers and methods declaration *)
Notation Default := (getDefaultConst _).
Definition Void := Bit 0.
Notation "'MethodSig' name () : retT" :=
  (Build_Attribute name {| arg := Void; ret := retT |})
  (at level 0, name at level 0, retT at level 200).
Notation "'MethodSig' name ( argT ) : retT" :=
  (Build_Attribute name {| arg := argT; ret := retT |})
  (at level 0, name at level 0, argT at level 200, retT at level 200).

(* Notations: expression *)
Notation "# v" := (Var _ _ v) (at level 0) : kami_scope.
Notation "!" := (UniBool Neg) : kami_scope.
Infix "&&" := (BinBool And) : kami_scope.
Infix "||" := (BinBool Or) : kami_scope.
Infix "+" := (BinBit (Add _)) : kami_scope.
Infix "==" := Eq (at level 30, no associativity) : kami_scope.
Notation "v @[ idx ] " := (ReadIndex idx v) (at level 0) : kami_scope.
Notation "s @. fd" := (ReadField ``(fd) s) (at level 0) : kami_scope.
Notation "'VEC' v" := (BuildVector v) (at level 10) : kami_scope.
Notation "v '@[' idx <- val ] " := (UpdateVector v idx val) (at level 0) : kami_scope.
Notation "$ n" := (Const _ (natToWord _ n)) (at level 0) : kami_scope.
Notation "$$ e" := (Const _ e) (at level 0) : kami_scope.
Notation "'IF' e1 'then' e2 'else' e3" := (ITE e1 e2 e3) : kami_scope.
Notation "[ x1 ; .. ; xN ]" := (cons x1 .. (cons xN nil) ..).
Notation "$ n" := (natToWord _ n) (at level 0).

Delimit Scope kami_scope with kami.

Notation "name :: ty" := (Build_Attribute name ty) : kami_struct_scope.

Ltac deattr := repeat match goal with
                      | [ H : Build_Attribute _ _ = Build_Attribute _ _ |- _ ] =>
                        injection H; clear H; intros; try subst
                      end.

Delimit Scope kami_struct_scope with struct.

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (Struct (cons s1%struct .. (cons sN%struct nil) ..)).
