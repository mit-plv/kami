Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word.

Set Implicit Arguments.

Inductive Kind: Type :=
| Bool: Kind
| Bit: nat -> Kind
| Vector: Kind -> nat -> Kind
| Struct: list (Attribute Kind) -> Kind.

Fixpoint decKind (k1 k2: Kind) : {k1 = k2} + {k1 <> k2}.
Proof.
  decide equality.
  clear decKind; decide equality.
  clear decKind; decide equality.
  decide equality.
  decide equality.
  apply (string_dec).
Defined.

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

Inductive ConstT: Kind -> Type :=
| ConstBool: bool -> ConstT Bool
| ConstBit n: word n -> ConstT (Bit n)
| ConstVector k n: Vec (ConstT k) n -> ConstT (Vector k n)
| ConstStruct attrs: ilist (fun a => ConstT (attrType a)) attrs -> ConstT (Struct attrs).

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

  Inductive Expr: Kind -> Type :=
  | Var k: type k -> Expr k
  | Const k: ConstT k -> Expr k
  | UniBool: UniBoolOp -> Expr Bool -> Expr Bool
  | BinBool: BinBoolOp -> Expr Bool -> Expr Bool -> Expr Bool
  | UniBit n1 n2: UniBitOp n1 n2 -> Expr (Bit n1) -> Expr (Bit n2)
  | BinBit n1 n2 n3: BinBitOp n1 n2 n3 -> Expr (Bit n1) -> Expr (Bit n2) ->
                     Expr (Bit n3)
  | ITE k: Expr Bool -> Expr k -> Expr k -> Expr k
  | Eq k: Expr k -> Expr k -> Expr Bool
  | ReadIndex i k: Expr (Bit i) -> Expr (Vector k i) -> Expr k
  | ReadField attrs (attr: BoundedIndexFull attrs):
      Expr (Struct attrs) -> Expr (GetAttrType attr)
  | BuildVector n k: Vec (Expr n) k -> Expr (Vector n k)
  | BuildStruct attrs: ilist (fun a => Expr (attrType a)) attrs -> Expr (Struct attrs)
  | UpdateVector i k: Expr (Vector k i) -> Expr (Bit i) -> Expr k -> Expr (Vector k i).

  Inductive Action (lretT: Kind) : Type :=
  | MCall (meth: string) s:
      Expr (arg s) ->
      (type (ret s) -> Action lretT) ->
      Action lretT
  | Let lretT': Expr lretT' -> (type lretT' -> Action lretT) -> Action lretT
  | ReadReg (r: string):
      forall k, (type k -> Action lretT) -> Action lretT
  | WriteReg (r: string) k:
      Expr k -> Action lretT -> Action lretT
  | IfElse: Expr Bool -> forall k,
                           Action k ->
                           Action k ->
                           (type k -> Action lretT) ->
                           Action lretT
  | Assert: Expr Bool -> Action lretT -> Action lretT
  | Return: Expr lretT -> Action lretT.

  Definition RegInitT := Attribute (Typed ConstT).
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
Notation "'Reg#(' type ) name <- 'mkReg(' init ) ;" :=
  (Build_Attribute name (Build_Typed _ type init))
    (format "'Reg#('  '/' type  '/' ')'  '/' name  '/' <-  'mkReg('  '/' init  '/' ) ;").
Notation "'Reg#(' type ) name <- 'mkRegU' ;" :=
  (Build_Attribute name (Build_Typed _ type (getDefaultConst _)))
    (format "'Reg#('  '/' type  '/' ')'  '/' name  '/' <-  'mkRegU' ;").
Notation "'Method' 'Value#(' retT ) name '#(' argT ) ;" :=
  (Build_Attribute name {| arg := argT; ret := retT |})
    (format "'Method'  'Value#('  '/' retT  '/' )  '/' name  '/' '#('  '/' argT  '/' ) ;").

(* Notations: action *)
Notation "'vcall' meth :@: sign '#(' arg ) '#;' cont " :=
  (MCall meth sign arg (fun _ => cont))
    (at level 12, right associativity,
     format "'vcall'  '/' meth  '/' :@:  '/' sign  '/' '#('  '/' arg  '/' )  '#;' '//' cont").
Notation "'vcall' name <- meth :@: sign '#(' arg ) '#;' cont " :=
  (MCall meth sign arg (fun name => cont))
    (at level 12, right associativity,
     format "'vcall'  '/' name  <-  '/' meth  '/' :@:  '/' sign  '/' '#('  '/' arg  '/' )  '#;' '//' cont ").
Notation "'vlet' name <- expr '#;' cont " :=
  (Let expr (fun name => cont))
    (at level 12, right associativity,
     format "'vlet'  '/' name  '/' <-  '/' expr  '#;' '//' cont ").
Notation "'vread' name <- reg '#;' cont " :=
  (ReadReg reg _ (fun name => cont))
    (at level 12, right associativity,
     format "'vread'  name  '/' <-  '/' reg  '#;' '//' cont").
Notation "'vread' name :@: kind <- reg '#;' cont " :=
  (ReadReg reg kind (fun name => cont))
    (at level 12, right associativity,
     format "'vread'  name  '/' :@:  '/' kind  '/' <-  '/' reg  '#;' '//' cont"). 
Notation "reg <= expr '#;' cont " :=
  (WriteReg reg expr cont)
    (at level 12, right associativity,
     format "reg  '/' <=  '/' expr  '#;' '//' cont ").
Notation "reg <= expr :@: kind '#;' cont " :=
  (@WriteReg _ _ reg kind expr cont)
    (at level 12, right associativity,
     format "reg  '/' <=  '/' expr  '/' :@:  '/' kind  '/' '#;' '//' cont ").
Notation "'vif' cexpr 'vthen' tact 'velse' fact '#;' cont " :=
  (IfElse cexpr tact fact cont)
    (at level 12, right associativity,
     format "'vif'  cexpr  '/' 'vthen'  tact  '/' 'velse'  fact  '#;' '//' cont ").
Notation "'vassert' expr '#;' cont " :=
  (Assert expr cont)
    (at level 12, right associativity,
     format "'vassert'  expr  '#;' '//' cont ").
Notation "'vret' expr '#;' " :=
  (Return expr) (at level 12, format "'vret'  expr  '#;'").

(* Notations: expression *)
Notation "'V' v" := (Var _ _ v) (at level 10).
Notation "'C' c" := (Const _ c) (at level 10).
Notation "'Cd' t" := (Const _ (getDefaultConst t)) (at level 10).
Notation "'Not' e" := (UniBool Neg e) (at level 10).
Infix "AND" := (BinBool And) (at level 10).
Infix "OR" := (BinBool Or) (at level 10).
Infix "==" := Eq (at level 10).
Notation "v '@[' idx ] " := (ReadIndex idx v) (at level 10).
Notation "s '@>' fd #[] " := (ReadField ``(fd) s) (at level 10).
Notation "s '@>' fd '#[' attrs ] " :=
  (ReadField (attrs:=attrs) ``(fd) s) (at level 10).
Notation "'VEC' v" := (BuildVector v) (at level 10).
Notation "'ST' il" := (BuildStruct il) (at level 10).
Notation "v '@[' idx <- val ] " := (UpdateVector v idx val) (at level 10).

