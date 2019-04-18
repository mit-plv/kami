Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.ilist Lib.Indexer Lib.StringAsList.
Require Import Kami.Syntax.
Require Import Kami.ParametricSyntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Common notations for normal modules and meta-modules *)

(** Notations for registers and methods declaration *)

Notation Default := (getDefaultConst _).

Notation "'MethodSig' name () : retT" :=
  (Build_Attribute name {| arg := Void; ret := retT |})
  (at level 0, name at level 0, retT at level 200).
Notation "'MethodSig' name ( argT ) : retT" :=
  (Build_Attribute name {| arg := argT; ret := retT |})
  (at level 0, name at level 0, argT at level 200, retT at level 200).

(** Notations for Struct **) 
Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (Vector.cons _ s1%struct _ .. (Vector.cons _ sN%struct _ (Vector.nil _)) ..).

(** Notations for expressions *)

Notation "nkind #< def" := (@NativeKind nkind def) (at level 0): kami_expr_scope.

Notation "# v" := (Var _ (SyntaxKind _) v) (at level 0) : kami_expr_scope.
(* Notation "## v : kind" := (Var _ kind v) (at level 0) : kami_expr_scope. *)
Notation "!" := (UniBool NegB) : kami_expr_scope.
Infix "&&" := (BinBool AndB) : kami_expr_scope.
Infix "||" := (BinBool OrB) : kami_expr_scope.
Infix "+" := (BinBit (Add _)) : kami_expr_scope.
Infix "-" := (BinBit (Sub _)) : kami_expr_scope.
Infix "*" := (BinBit (Mul _ SignUU)) : kami_expr_scope.
Infix "*s" := (BinBit (Mul _ SignSS)) (at level 0) : kami_expr_scope.
Infix "*su" := (BinBit (Mul _ SignSU)) (at level 0) : kami_expr_scope.
Infix "/" := (BinBit (Div _ false)) : kami_expr_scope.
Infix "/s" := (BinBit (Div _ true)) (at level 0) : kami_expr_scope.
(* Infix "/su" := (BinBit (Div _ SignSU)) (at level 0) : kami_expr_scope. *)
Infix "~&" := (BinBit (Band _)) (at level 0) : kami_expr_scope.
Infix "~|" := (BinBit (Bor _)) (at level 0) : kami_expr_scope.
Infix "~+" := (BinBit (Bxor _)) (at level 0) : kami_expr_scope.
Infix "<<" := (BinBit (Sll _ _)) (at level 0) : kami_expr_scope.
Infix ">>" := (BinBit (Srl _ _)) (at level 0) : kami_expr_scope.
Infix "~>>" := (BinBit (Sra _ _)) (at level 0) : kami_expr_scope.
Infix "<" := (BinBitBool (Lt _)) : kami_expr_scope.
Notation "x > y" := (BinBitBool (Lt _) y x) : kami_expr_scope.
Notation "x >= y" := (UniBool NegB (BinBitBool (Lt _) x y)) : kami_expr_scope.
Notation "x <= y" := (UniBool NegB (BinBitBool (Lt _) y x)) : kami_expr_scope.
Infix "==" := Eq (at level 30, no associativity) : kami_expr_scope.
Infix "!=" := (fun e1 e2 => UniBool NegB (Eq e1 e2))
                (at level 30, no associativity) : kami_expr_scope.
Notation "v @[ idx ] " := (ReadIndex idx v) (at level 0) : kami_expr_scope.

Notation "a $[ i : j ]@ w":=
  (UniBit
     (ConstExtract
        j
        (i + 1 - j)%nat
        (w - 1 - i)%nat
     ) a) (at level 100, i at level 99) : kami_expr_scope.

Notation "'_zeroExtend_' x" :=
  (UniBit (ZeroExtendTrunc _ _) x) (at level 0) : kami_expr_scope.
Notation "'_signExtend_' x" :=
  (UniBit (SignExtendTrunc _ _) x) (at level 0) : kami_expr_scope.
Notation "{ a , b }" := (BinBit (Concat _ _) a b) (at level 0, a at level 99) : kami_expr_scope.
Notation "{ a ::( al ) , b }" := (BinBit (Concat al _) a b) (at level 0, a at level 99) : kami_expr_scope.
Notation "{ a , b ::( bl ) }" := (BinBit (Concat _ bl) a b) (at level 0, a at level 99) : kami_expr_scope.

Delimit Scope kami_expr_scope with kami_expr.

Definition getStructVector {n} {ls: Vector.t (Attribute Kind) n} {e: Kind} (isEq: e = Struct ls) := ls.

Notation "s !! f" := (Lib.VectorFacts.Vector_find
                        (fun x => Lib.StringEq.string_eq f%string (attrName x)) s)
                       (at level 0).
Notation "e ! s @. f" := (@ReadField _ _ s (s !! f) e%kami_expr) (at level 0): kami_expr_scope.
Notation "'VEC' v" := (BuildVector v) (at level 10) : kami_expr_scope.
Notation "v '@[' idx <- val ] " := (UpdateVector v idx val) (at level 0) : kami_expr_scope.
Notation "$ n" := (Const _ (natToWord _ n)) (at level 0) : kami_expr_scope.
Notation "$$ e" := (Const _ e) (at level 0) : kami_expr_scope.
Notation "'IF' e1 'then' e2 'else' e3" := (ITE e1 e2 e3) : kami_expr_scope.
Notation "$ n" := (natToWord _ n) (at level 0).

Definition icons' {ty} (na : {a : Attribute Kind & Expr ty (SyntaxKind (attrType a))})
           {n} {attrs: Vector.t _ n}
           (tl : ilist (fun a : Attribute Kind => Expr ty (SyntaxKind (attrType a))) attrs)
  : ilist (fun a : Attribute Kind => Expr ty (SyntaxKind (attrType a))) (Vector.cons _ (projT1 na) _ attrs) :=
  icons (projT1 na) (projT2 na) tl.

Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => Expr _ (SyntaxKind (attrType a)))
          (Build_Attribute name _) value) (at level 50) : init_scope.
Delimit Scope init_scope with init.

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (BuildStruct (icons' s1%init .. (icons' sN%init (inil _)) ..)) : kami_expr_scope.
Notation "e :: t" := (e : Expr _ (SyntaxKind t)) : kami_expr_scope.

Definition isValid := "isValid"%string.
Definition value := "value"%string.

Definition Maybe (t: Kind) := STRUCT {
                                  isValid :: Bool;
                                  value :: t
                                }.

Notation "k @ var" := (Expr var (SyntaxKind k)) (at level 0).

(** Notations for action *)

Notation "'Call' meth ( arg ) ; cont " :=
  (MCall (attrName meth) (attrType meth) arg%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_action_scope.
Notation "'Call' name <- meth ( arg ) ; cont " :=
  (MCall (attrName meth) (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_action_scope.
Notation "'Call' name : t <- meth ( arg ) ; cont " :=
  (MCall (lretT := t) (attrName meth) (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_action_scope.
Notation "'Call' meth () ; cont " :=
  (MCall (attrName meth) (attrType meth) (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_action_scope.
Notation "'Call' name <- meth () ; cont " :=
  (MCall (attrName meth) (attrType meth) (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_action_scope.
Notation "'Call' name : t <- meth () ; cont " :=
  (MCall (lretT := t) (attrName meth) (attrType meth) (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_action_scope.

Notation "'CallM' meth ( a : argT ) ; cont " :=
  (MCall meth%string {| arg := argT; ret := Void |} a%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0, a at level 99) : kami_action_scope.
Notation "'CallM' name : retT <- meth ( a : argT ) ; cont " :=
  (MCall meth%string {| arg := argT; ret := retT |} a%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0, a at level 99) : kami_action_scope.
Notation "'CallM' meth () ; cont " :=
  (MCall meth%string {| arg := Void; ret := Void |} (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_action_scope.
Notation "'CallM' name : retT <- meth () ; cont " :=
  (MCall meth%string {| arg := Void; ret := retT |} (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_action_scope.

Notation "'LETN' name : kind <- expr ; cont " :=
  (Let_ (lretT' := kind) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_action_scope.
Notation "'LET' name <- expr ; cont " :=
  (Let_ expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_action_scope.
Notation "'LET' name : t <- expr ; cont " :=
  (Let_ (lretT' := SyntaxKind t) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_action_scope.
Notation "'Nondet' name : kind ; cont" :=
  (ReadNondet kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_action_scope.
Notation "'ReadN' name : kind <- reg ; cont " :=
  (ReadReg reg kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_action_scope.
Notation "'Read' name <- reg ; cont" :=
  (ReadReg reg _ (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_action_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (ReadReg reg (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_action_scope.
Notation "'WriteN' reg : kind <- expr ; cont " :=
  (@WriteReg _ _ reg kind expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_action_scope.
Notation "'Write' reg <- expr ; cont " :=
  (WriteReg reg expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_action_scope.
Notation "'Write' reg : kind <- expr ; cont " :=
  (@WriteReg _ _ reg (SyntaxKind kind) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun name => cont))
    (at level 13, right associativity, name at level 0, cexpr at level 0, tact at next level, fact at next level) : kami_action_scope.
Notation "'If' cexpr 'then' tact 'else' fact ; cont " :=
  (IfElse cexpr%kami_expr tact fact (fun _ => cont))
    (at level 13, right associativity, cexpr at level 0, tact at next level, fact at next level) : kami_action_scope.
Notation "'If' cexpr 'then' tact ; cont" :=
  (IfElse cexpr%kami_expr tact (Return (Const _ (k := Void) Default)) (fun _ => cont))
    (at level 13, right associativity, cexpr at level 0, tact at next level) : kami_action_scope.
Notation "'Assert' expr ; cont " :=
  (Assert_ expr%kami_expr cont)
    (at level 12, right associativity) : kami_action_scope.
Notation "'Ret' expr" :=
  (Return expr%kami_expr) (at level 12) : kami_action_scope.
Notation "'Retv'" := (Return (Const _ (k := Void) Default)) : kami_action_scope.

Delimit Scope kami_action_scope with kami_action.


(** * Notation for normal modules *)

Inductive ModuleElt :=
| MERegister (_ : RegInitT)
| MERule (_ : Attribute (Action Void))
| MEMeth (_ : DefMethT).

Inductive InModule :=
| NilInModule
| ConsInModule (_ : ModuleElt) (_ : InModule).

Fixpoint makeModule' (im : InModule) :=
  match im with
  | NilInModule => (nil, nil, nil)
  | ConsInModule e i =>
    let '(iregs, irules, imeths) := makeModule' i in
    match e with
    | MERegister mreg => (mreg :: iregs, irules, imeths)
    | MERule mrule => (iregs, mrule :: irules, imeths)
    | MEMeth mmeth => (iregs, irules, mmeth :: imeths)
    end
  end.

Definition makeModule (im : InModule) :=
  let '(regs, rules, meths) := makeModule' im in
  Mod regs rules meths.

Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.

Notation "'RegisterN' name : type <- 'Default'" :=
  (MERegister (Build_Attribute name (RegInitDefault type)))
    (at level 0, name at level 0, type at level 0) : kami_scope.

Notation "'RegisterN' name : type <- init" :=
  (MERegister (Build_Attribute name (RegInitCustom (existT ConstFullT type init))))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_scope.

Notation "'Register' name : type <- 'Default'" :=
  (MERegister (Build_Attribute name (RegInitDefault (SyntaxKind type))))
    (at level 0, name at level 0, type at level 0) : kami_scope.

Notation "'Register' name : type <- init" :=
  (MERegister (Build_Attribute name (RegInitCustom (existT ConstFullT (SyntaxKind type) (makeConst init)))))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_scope.

Notation "'Method' name () : retT := c" :=
  (MEMeth (Build_Attribute name
                           (existT MethodT {| arg := Void; ret := retT |}
                                   (fun ty => fun _ : ty Void =>
                                                (c)%kami_action : ActionT ty retT))))
    (at level 0, name at level 0) : kami_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (MEMeth (Build_Attribute name
                           (existT MethodT {| arg := dom; ret := retT |}
                                   (fun ty => fun param : ty dom =>
                                                (c)%kami_action : ActionT ty retT))))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_scope.

Notation "'Rule' name := c" :=
  (MERule (Build_Attribute name (fun ty => c%kami_action : ActionT ty Void)))
    (at level 0, name at level 0) : kami_scope.

Notation "'MODULE' { m1 'with' .. 'with' mN }" :=
  (makeModule (ConsInModule m1%kami .. (ConsInModule mN%kami NilInModule) ..))
    (at level 0, only parsing).


(** * Notations for meta-modules *)

(** Notations for SinAction *)

Notation "'Call' meth ( arg ) ; cont " :=
  (SMCall (Build_NameRec (attrName meth) eq_refl) (attrType meth) arg%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_sin_scope.
Notation "'Call' name <- meth ( arg ) ; cont " :=
  (SMCall (Build_NameRec (attrName meth) eq_refl) (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.
Notation "'Call' name : t <- meth ( arg ) ; cont " :=
  (SMCall (lretT := t) (Build_NameRec (attrName meth) eq_refl) (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.
Notation "'Call' meth () ; cont " :=
  (SMCall (Build_NameRec (attrName meth) eq_refl) (attrType meth)
          (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_sin_scope.
Notation "'Call' name <- meth () ; cont " :=
  (SMCall (Build_NameRec (attrName meth) eq_refl) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.
Notation "'Call' name : t <- meth () ; cont " :=
  (SMCall (lretT := t) (Build_NameRec (attrName meth) eq_refl) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.

Notation "'CallM' meth ( a : argT ) ; cont " :=
  (SMCall (Build_NameRec meth%string eq_refl) {| arg := argT; ret := Void |} a%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0, a at level 99) : kami_sin_scope.
Notation "'CallM' name : retT <- meth ( a : argT ) ; cont " :=
  (SMCall (Build_NameRec meth%string eq_refl) {| arg := argT; ret := retT |} a%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0, a at level 99) : kami_sin_scope.
Notation "'CallM' meth () ; cont " :=
  (SMCall (Build_NameRec meth%string eq_refl) {| arg := Void; ret := Void |} (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_sin_scope.
Notation "'CallM' name : retT <- meth () ; cont " :=
  (SMCall (Build_NameRec meth%string eq_refl) {| arg := Void; ret := retT |} (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.

Notation "'Call' { meth | pf } ( arg ) ; cont " :=
  (SMCall (Build_NameRec (attrName meth) pf) (attrType meth) arg%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_sin_scope.
Notation "'Call' name <- { meth | pf } ( arg ) ; cont " :=
  (SMCall (Build_NameRec (attrName meth) pf) (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.
Notation "'Call' name : t <- { meth | pf } ( arg ) ; cont " :=
  (SMCall (lretT := t) (Build_NameRec (attrName meth) pf) (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.
Notation "'Call' { meth | pf } () ; cont " :=
  (SMCall (Build_NameRec (attrName meth) pf) (attrType meth)
          (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_sin_scope.
Notation "'Call' name <- { meth | pf } () ; cont " :=
  (SMCall (Build_NameRec (attrName meth) pf) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.
Notation "'Call' name : t <- { meth | pf } () ; cont " :=
  (SMCall (lretT := t) (Build_NameRec (attrName meth) pf) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.

Notation "'CallM' { meth | pf } ( a : argT ) ; cont " :=
  (SMCall (Build_NameRec meth%string pf) {| arg := argT; ret := Void |} a%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0, a at level 99) : kami_sin_scope.
Notation "'CallM' name : retT <- { meth | pf } ( a : argT ) ; cont " :=
  (SMCall (Build_NameRec meth%string pf) {| arg := argT; ret := retT |} a%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0, a at level 99) : kami_sin_scope.
Notation "'CallM' { meth | pf } () ; cont " :=
  (SMCall (Build_NameRec meth%string pf) {| arg := Void; ret := Void |} (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_sin_scope.
Notation "'CallM' name : retT <- { meth | pf } () ; cont " :=
  (SMCall (Build_NameRec meth%string pf) {| arg := Void; ret := retT |} (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_sin_scope.



Notation "'LETN' name : kind <- expr ; cont " :=
  (SLet_ (lretT' := kind) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'LET' name <- expr ; cont " :=
  (SLet_ expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'LET' name : t <- expr ; cont " :=
  (SLet_ (lretT' := SyntaxKind t) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'Nondet' name : kind ; cont " :=
  (SReadNondet kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'ReadN' name : kind <- reg ; cont " :=
  (SReadReg (Build_NameRec reg eq_refl) kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'Read' name <- reg ; cont" :=
  (SReadReg (Build_NameRec reg eq_refl) _ (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (SReadReg (Build_NameRec reg eq_refl) (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'Read' name <- { reg | pf } ; cont" :=
  (SReadReg (Build_NameRec reg pf) _ (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'Read' name : kind <- { reg | pf } ; cont " :=
  (SReadReg (Build_NameRec reg pf) (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'ReadN' name : kind <- { reg | pf } ; cont " :=
  (SReadReg (Build_NameRec reg pf) kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_sin_scope.
Notation "'WriteN' reg : kind <- expr ; cont " :=
  (@SWriteReg _ _ (Build_NameRec reg eq_refl) kind expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_sin_scope.
Notation "'WriteN' { reg | pf } : kind <- expr ; cont " :=
  (@SWriteReg _ _ (Build_NameRec reg pf) kind expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_sin_scope.
Notation "'Write' reg <- expr ; cont " :=
  (SWriteReg (Build_NameRec reg eq_refl) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_sin_scope.
Notation "'Write' reg : kind <- expr ; cont " :=
  (@SWriteReg _ _ (Build_NameRec reg eq_refl) (SyntaxKind kind) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_sin_scope.
Notation "'Write' { reg | pf } <- expr ; cont " :=
  (SWriteReg (Build_NameRec reg pf) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_sin_scope.
Notation "'Write' { reg | pf } : kind <- expr ; cont " :=
  (@SWriteReg _ _ (Build_NameRec reg pf) (SyntaxKind kind) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_sin_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (SIfElse cexpr%kami_expr tact fact (fun name => cont))
    (at level 13, right associativity, name at level 0,
     cexpr at level 0, tact at next level, fact at next level) : kami_sin_scope.
Notation "'If' cexpr 'then' tact 'else' fact ; cont " :=
  (SIfElse cexpr%kami_expr tact fact (fun _ => cont))
    (at level 13, right associativity, cexpr at level 0, tact at next level, fact at next level) : kami_sin_scope.
Notation "'If' cexpr 'then' tact ; cont " :=
  (SIfElse cexpr%kami_expr tact (SReturn (Const _ (k := Void) Default)) (fun _ => cont))
    (at level 13, right associativity, cexpr at level 0, tact at next level) : kami_sin_scope.
Notation "'Assert' expr ; cont " :=
  (SAssert_ expr%kami_expr cont)
    (at level 12, right associativity) : kami_sin_scope.
Notation "'Ret' expr" :=
  (SReturn expr%kami_expr) (at level 12) : kami_sin_scope.
Notation "'Retv'" := (SReturn (Const _ (k := Void) Default)) : kami_sin_scope.

Delimit Scope kami_sin_scope with kami_sin.

(** Notations for GenAction *)

Notation "'Call' meth ( arg ) ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec (attrName meth) eq_refl))
          (attrType meth) arg%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'Call' name <- meth ( arg ) ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec (attrName meth) eq_refl))
          (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Call' name : t <- meth ( arg ) ; cont " :=
  (GMCall (lretT := t) (Build_NameRecIdx false (Build_NameRec (attrName meth) eq_refl))
          (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Call' meth () ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec (attrName meth) eq_refl)) (attrType meth)
          (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'Call' name <- meth () ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec (attrName meth) eq_refl)) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Call' name : t <- meth () ; cont " :=
  (GMCall (lretT := t) (Build_NameRecIdx false (Build_NameRec (attrName meth) eq_refl)) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.

Notation "'CallM' meth ( a : argT ) ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec meth%string eq_refl)) {| arg := argT; ret := Void |} a%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0, a at level 99) : kami_gen_scope.
Notation "'CallM' name : retT <- meth ( a : argT ) ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec meth%string eq_refl)) {| arg := argT; ret := retT |} a%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0, a at level 99) : kami_gen_scope.
Notation "'CallM' meth () ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec meth%string eq_refl)) {| arg := Void; ret := Void |} (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'CallM' name : retT <- meth () ; cont " :=
  (GMCall (Build_NameRecIdx false (Build_NameRec meth%string eq_refl)) {| arg := Void; ret := retT |} (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.

Notation "'Calli' meth ( arg ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) eq_refl))
          (attrType meth) arg%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'Calli' name <- meth ( arg ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) eq_refl))
          (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Calli' name : t <- meth ( arg ) ; cont " :=
  (GMCall (lretT := t) (Build_NameRecIdx true (Build_NameRec (attrName meth) eq_refl))
          (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Calli' meth () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) eq_refl)) (attrType meth)
          (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'Calli' name <- meth () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) eq_refl)) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Calli' name : t <- meth () ; cont " :=
  (GMCall (lretT := t) (Build_NameRecIdx true (Build_NameRec (attrName meth) eq_refl)) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.

Notation "'CalliM' meth ( a : argT ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth eq_refl)) {| arg := argT; ret := Void |} a%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'CalliM' name : retT <- meth ( a : argT ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth eq_refl)) {| arg := argT; ret := retT |} a%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'CalliM' meth () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth eq_refl)) {| arg := Void; ret := Void |} (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'CalliM' name : retT <- meth () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth eq_refl)) {| arg := Void; ret := retT |} (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.

Notation "'Calli' { meth | pf } ( arg ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) pf))
          (attrType meth) arg%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'Calli' name <- { meth | pf } ( arg ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) pf))
          (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Calli' name : t <- { meth | pf } ( arg ) ; cont " :=
  (GMCall (lretT := t) (Build_NameRecIdx true (Build_NameRec (attrName meth) pf))
          (attrType meth) arg%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Calli' { meth | pf } () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) pf)) (attrType meth)
          (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'Calli' name <- { meth | pf } () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec (attrName meth) pf)) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'Calli' name : t <- { meth | pf } () ; cont " :=
  (GMCall (lretT := t) (Build_NameRecIdx true (Build_NameRec (attrName meth) pf)) (attrType meth)
          (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.

Notation "'CalliM' { meth | pf } ( a : argT ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth pf)) {| arg := argT; ret := Void |} a%kami_expr (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'CalliM' name : retT <- { meth | pf } ( a : argT ) ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth pf)) {| arg := argT; ret := retT |} a%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.
Notation "'CalliM' { meth | pf } () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth pf)) {| arg := Void; ret := Void |} (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_gen_scope.
Notation "'CalliM' name : retT <- { meth | pf } () ; cont " :=
  (GMCall (Build_NameRecIdx true (Build_NameRec meth pf)) {| arg := Void; ret := retT |} (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_gen_scope.



Notation "'ILET' name ; cont " :=
  (GIndex (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'LETN' name : kind <- expr ; cont " :=
  (GLet_ (lretT' := kind) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'LET' name <- expr ; cont " :=
  (GLet_ expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'LET' name : t <- expr ; cont " :=
  (GLet_ (lretT' := SyntaxKind t) expr%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'Nondet' name : kind ; cont " :=
  (GReadNondet kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'ReadN' name : kind <- reg ; cont " :=
  (GReadReg (Build_NameRecIdx false (Build_NameRec reg eq_refl)) kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'ReadN' name : kind <- { reg | pf } ; cont " :=
  (GReadReg (Build_NameRecIdx false (Build_NameRec reg pf)) kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'ReadNi' name : kind <- reg ; cont " :=
  (GReadReg (Build_NameRecIdx true (Build_NameRec reg eq_refl)) kind (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'Read' name <- reg ; cont" :=
  (GReadReg (Build_NameRecIdx false (Build_NameRec reg eq_refl)) _ (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (GReadReg (Build_NameRecIdx false (Build_NameRec reg eq_refl))
            (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'Readi' name <- reg ; cont" :=
  (GReadReg (Build_NameRecIdx true (Build_NameRec reg eq_refl)) _ (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'Readi' name : kind <- reg ; cont " :=
  (GReadReg (Build_NameRecIdx true (Build_NameRec reg eq_refl))
            (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_gen_scope.
Notation "'WriteN' reg : kind <- expr ; cont " :=
  (@GWriteReg _ _ _ (Build_NameRecIdx false (Build_NameRec reg eq_refl)) kind expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'WriteNi' reg : kind <- expr ; cont " :=
  (@GWriteReg _ _ _ (Build_NameRecIdx true (Build_NameRec reg eq_refl)) kind expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'Write' reg <- expr ; cont " :=
  (GWriteReg (Build_NameRecIdx false (Build_NameRec reg eq_refl)) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'Write' reg : kind <- expr ; cont " :=
  (@GWriteReg _ _ _ (Build_NameRecIdx false (Build_NameRec reg eq_refl))
              (SyntaxKind kind) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'Write' { reg | pf } <- expr ; cont " :=
  (GWriteReg (Build_NameRecIdx false (Build_NameRec reg pf)) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'Write' { reg | pf } : kind <- expr ; cont " :=
  (@GWriteReg _ _ _ (Build_NameRecIdx false (Build_NameRec reg pf))
              (SyntaxKind kind) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'Writei' reg <- expr ; cont " :=
  (GWriteReg (Build_NameRecIdx true (Build_NameRec reg eq_refl)) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'Writei' reg : kind <- expr ; cont " :=
  (@GWriteReg _ _ _ (Build_NameRecIdx true (Build_NameRec reg eq_refl))
              (SyntaxKind kind) expr%kami_expr cont)
    (at level 12, right associativity, reg at level 0) : kami_gen_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (GIfElse cexpr%kami_expr tact fact (fun name => cont))
    (at level 13, right associativity, name at level 0,
     cexpr at level 0, tact at next level, fact at next level) : kami_gen_scope.
Notation "'If' cexpr 'then' tact 'else' fact ; cont " :=
  (GIfElse cexpr%kami_expr tact fact (fun _ => cont))
    (at level 13, right associativity, cexpr at level 0, tact at next level, fact at next level) : kami_gen_scope.
Notation "'If' cexpr 'then' tact ; cont " :=
  (GIfElse cexpr%kami_expr tact (GReturn _ (Const _ (k := Void) Default)) (fun _ => cont))
    (at level 13, right associativity, cexpr at level 0, tact at next level) : kami_gen_scope.
Notation "'Assert' expr ; cont " :=
  (GAssert_ expr%kami_expr cont)
    (at level 12, right associativity) : kami_gen_scope.
Notation "'Ret' expr" :=
  (GReturn _ expr%kami_expr) (at level 12) : kami_gen_scope.
Notation "'Retv'" := (GReturn _ (Const _ (k := Void) Default)) : kami_gen_scope.

Delimit Scope kami_gen_scope with kami_gen.

(** Notation for meta-modules *)

Fixpoint multiMetaRule (f: nat -> MetaRule) n :=
  match n with
  | 0 => nil
  | S m => f (S m) :: multiMetaRule f m
  end.

Lemma string_of_nat_no_indexSymbol: forall s, index 0 indexSymbol (string_of_nat s) = None.
Proof.
  induction s; auto; simpl.
  rewrite IHs.
  reflexivity.
Qed.

Section AddIndex.
  Variable name: string.
  Local Notation "^ s" := (name -- (string_of_nat s)) (at level 0).
  Hypothesis Hname: index 0 indexSymbol name = None.
  Lemma noIndexSymbol:
    forall s, index 0 indexSymbol (^s) = None.
  Proof.
    unfold withPrefix; intros.
    pose proof (string_of_nat_no_indexSymbol s) as H.
    apply index_not_in; apply index_not_in in H; apply index_not_in in Hname.
    intro Hx; elim H; clear H.
    apply S_in_app_or in Hx; destruct Hx; auto.
    apply S_in_app_or in H; destruct H.
    - unfold prefixSymbol in *; simpl in *.
      inversion H; inversion H0.
    - elim Hname; auto.
  Qed.
End AddIndex.

Inductive MetaModuleElt :=
| MMERegister (_ : MetaReg)
| MMERule (_ : MetaRule)
| MMEMultiRule (_: list MetaRule)
| MMEMeth (_ : MetaMeth).

Inductive InMetaModule :=
| NilInMetaModule
| ConsInMetaModule (_ : MetaModuleElt) (_ : InMetaModule).

Fixpoint makeMetaModule (im : InMetaModule) :=
  match im with
  | NilInMetaModule => {| metaRegs:= nil;
                          metaRules:= nil;
                          metaMeths:= nil |}
  | ConsInMetaModule e i =>
    let '(Build_MetaModule iregs irules imeths) := makeMetaModule i in
    match e with
    | MMERegister mreg => Build_MetaModule (mreg :: iregs) irules imeths
    | MMERule mrule => Build_MetaModule iregs (mrule :: irules) imeths
    | MMEMultiRule mrules => Build_MetaModule iregs (mrules ++ irules) imeths 
    | MMEMeth mmeth => Build_MetaModule iregs irules (mmeth :: imeths)
    end
  end.

Notation "'RegisterN' name : type <- 'Default'" :=
  (MMERegister (OneReg (RegInitDefault type)
                       {| nameVal := name;
                          goodName := eq_refl |} ))
    (at level 0, name at level 0, type at level 0) : kami_meta_scope.
Notation "'RegisterN' { name | pf } : type <- 'Default'" :=
  (MMERegister (OneReg (RegInitDefault type)
                       {| nameVal := name;
                          goodName := pf |} ))
    (at level 0, name at level 0, type at level 0) : kami_meta_scope.

Notation "'RegisterN' name : type <- init" :=
  (MMERegister (OneReg (RegInitCustom (existT ConstFullT (type) (init)))
                       {| nameVal := name;
                          goodName := eq_refl |} ))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_meta_scope.
Notation "'RegisterN' { name | pf } : type <- init" :=
  (MMERegister (OneReg (RegInitCustom (existT ConstFullT (type) (init)))
                       {| nameVal := name;
                          goodName := pf |} ))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_meta_scope.

Notation "'Register' name : type <- 'Default'" :=
  (MMERegister (OneReg (RegInitDefault (SyntaxKind type))
                       {| nameVal := name;
                          goodName := eq_refl |} ))
    (at level 0, name at level 0, type at level 0) : kami_meta_scope.
Notation "'Register' { name | pf } : type <- 'Default'" :=
  (MMERegister (OneReg (RegInitDefault (SyntaxKind type))
                       {| nameVal := name;
                          goodName := pf |} ))
    (at level 0, name at level 0, type at level 0) : kami_meta_scope.

Notation "'Register' name : type <- init" :=
  (MMERegister (OneReg (RegInitCustom (existT ConstFullT (SyntaxKind type) (makeConst init)))
                       {| nameVal := name;
                          goodName := eq_refl |}))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_meta_scope.
Notation "'Register' { name | pf } : type <- init" :=
  (MMERegister (OneReg (RegInitCustom ((existT ConstFullT (SyntaxKind type) (makeConst init))))
                       {| nameVal := name;
                          goodName := pf |} ))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_meta_scope.

Notation "'Repeat' 'Register' 'as' i 'till' n 'by' name : type <- 'Default'" :=
  (MMERegister (RepReg string_of_nat
                       string_of_nat_into
                       withIndex_index_eq
                       (fun i => RegInitDefault (SyntaxKind type))
                       {| nameVal := name; goodName := eq_refl |}
                       (getNatListToN_NoDup n)))
    (at level 0, name at level 0, type at level 0) : kami_meta_scope.

Notation "'Repeat' 'Register' 'as' i 'till' n 'by' name : type <- init" :=
  (MMERegister (RepReg string_of_nat
                       string_of_nat_into
                       withIndex_index_eq
                       (fun i => RegInitCustom
                                   (existT ConstFullT (SyntaxKind type) (makeConst init)))
                       {| nameVal := name; goodName := eq_refl |}
                       (getNatListToN_NoDup n)))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_meta_scope.

Notation "'Method' name () : retT := c" :=
  (MMEMeth (OneMeth (existT SinMethodT {| arg := Void; ret := retT |}
                            (fun ty => fun _ : ty Void => (c)%kami_sin : SinActionT ty retT))
                    {| nameVal := name;
                       goodName := eq_refl |} ))
    (at level 0, name at level 0) : kami_meta_scope.
Notation "'Method' { name | pf } () : retT := c" :=
  (MMEMeth (OneMeth (existT SinMethodT {| arg := Void; ret := retT |}
                            (fun ty => fun _ : ty Void => (c)%kami_sin : SinActionT ty retT))
                    {| nameVal := name;
                       goodName := pf |} ))
    (at level 0, name at level 0) : kami_meta_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (MMEMeth (OneMeth (existT SinMethodT {| arg := dom; ret := retT |}
                            (fun ty => fun param : ty dom => (c)%kami_sin : SinActionT ty retT))
                    {| nameVal := name;
                       goodName := eq_refl |} ))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_meta_scope.
Notation "'Method' { name | pf } ( param : dom ) : retT := c" :=
  (MMEMeth (OneMeth (existT SinMethodT {| arg := dom; ret := retT |}
                            (fun ty => fun param : ty dom => (c)%kami_sin : SinActionT ty retT))
                    {| nameVal := name;
                       goodName := pf |} ))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_meta_scope.

Notation "'Repeat' 'Method' 'till' n 'by' name () : retT := c" :=
  (MMEMeth (RepMeth string_of_nat
                    string_of_nat_into
                    natToVoid
                    withIndex_index_eq
                    (existT (GenMethodT Void) {| arg:= Void; ret:= retT |}
                            (fun ty (_: ty Void) => c%kami_gen))
                    {| nameVal := name; goodName := eq_refl |}
                    (getNatListToN_NoDup n)))
    (at level 0, name at level 0) : kami_meta_scope.

Notation "'Repeat' 'Method' 'till' n 'by' name ( param : dom ) : retT := c" :=
  (MMEMeth (RepMeth string_of_nat
                    string_of_nat_into
                    natToVoid
                    withIndex_index_eq
                    (existT (GenMethodT Void) {| arg:= dom; ret:= retT |}
                            (fun ty (param: ty dom) => c%kami_gen))
                    {| nameVal := name; goodName := eq_refl |}
                    (getNatListToN_NoDup n)))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_meta_scope.

Notation "'Repeat' 'Method' 'till' n 'with' sz 'by' name () : retT := c" :=
  (MMEMeth (RepMeth string_of_nat
                    string_of_nat_into
                    (natToWordConst sz)
                    withIndex_index_eq
                    (existT (GenMethodT Void) {| arg:= Void; ret:= retT |}
                            (fun ty (_: ty Void) => c%kami_gen))
                    name
                    (getNatListToN n)))
    (at level 0, name at level 0) : kami_meta_scope.

Notation "'Repeat' 'Method' 'till' n 'with' sz 'by' name ( param : dom ) : retT := c" :=
  (MMEMeth (RepMeth string_of_nat
                    string_of_nat_into
                    (natToWordConst sz)
                    withIndex_index_eq
                    (existT (GenMethodT Void) {| arg:= dom; ret:= retT |}
                            (fun ty (param: ty dom) => c%kami_gen))
                    name
                    (getNatListToN n)))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_meta_scope.

Notation "'Rule' name := c" :=
  (MMERule (OneRule (fun ty => c%kami_sin : SinActionT ty Void)
                    {| nameVal := name;
                       goodName := eq_refl |} ))
    (at level 0, name at level 0) : kami_meta_scope.
Notation "'Rule' { name | pf } := c" :=
  (MMERule (OneRule (fun ty => c%kami_sin : SinActionT ty Void)
                    {| nameVal := name;
                       goodName := pf |} ))
    (at level 0, name at level 0) : kami_meta_scope.

Notation "'Repeat' 'Rule' 'till' n 'by' name := c" :=
  (MMERule (RepRule string_of_nat
                    string_of_nat_into
                    natToVoid
                    withIndex_index_eq
                    (fun ty => c%kami_gen : GenActionT Void ty Void)
                    {| nameVal := name; goodName := eq_refl |}
                    (getNatListToN_NoDup n)))
    (at level 0, name at level 0) : kami_meta_scope.

Notation "'Repeat' 'Rule' 'till' n 'with' sz 'by' name := c" :=
  (MMERule (RepRule string_of_nat
                    string_of_nat_into
                    (natToWordConst sz)
                    withIndex_index_eq
                    (fun ty => c%kami_gen : GenActionT (Bit sz) ty Void)
                    {| nameVal := name; goodName := eq_refl |}
                    (getNatListToN_NoDup n)))
     (at level 0, name at level 0) : kami_meta_scope.

Notation "'MultiRule' 'until' x 'as' i 'by' name := c" :=
  (MMEMultiRule (multiMetaRule (fun i => OneRule (fun ty => c%kami_sin : SinActionT ty Void)
                                                 {| nameVal := name -- (string_of_nat i);
                                                    goodName := noIndexSymbol name eq_refl i |})
                               x))
    (at level 0, name at level 0) : kami_meta_scope.

Notation "'Repeat' 'MultiRule' 'until' x 'as' i 'till' n 'by' name := c" :=
  (MMEMultiRule (multiMetaRule (fun i => (RepRule string_of_nat
                                                  string_of_nat_into
                                                  natToVoid
                                                  withIndex_index_eq
                                                  (fun ty => c%kami_gen : GenActionT Void ty Void)
                                                  {| nameVal := name -- (string_of_nat i);
                                                     goodName := noIndexSymbol name eq_refl i |}
                                                  (getNatListToN_NoDup n))) x))
    (at level 0, name at level 0) : kami_meta_scope.

Notation "'Repeat' 'MultiRule' 'until' x 'as' i 'till' n 'with' sz 'by' name := c" :=
  (MMEMultiRule (multiMetaRule (fun i => (RepRule string_of_nat
                                                  string_of_nat_into
                                                  (natToWordConst sz)
                                                  withIndex_index_eq
                                                  (fun ty => c%kami_gen : GenActionT (Bit sz) ty Void)
                                                  {| nameVal := name -- (string_of_nat i);
                                                     goodName := noIndexSymbol name eq_refl i |}
                                                  (getNatListToN_NoDup n))) x))
    (at level 0, name at level 0) : kami_meta_scope.


Delimit Scope kami_meta_scope with kami_meta.

Notation "'MODULEMETA' { m1 'with' .. 'with' mN }" :=
  (modFromMeta
     (makeMetaModule
        (ConsInMetaModule m1%kami_meta .. (ConsInMetaModule mN%kami_meta NilInMetaModule) ..)))
    (at level 0, only parsing).

Notation "'META' { m1 'with' .. 'with' mN }" :=
  (makeMetaModule
     (ConsInMetaModule m1%kami_meta .. (ConsInMetaModule mN%kami_meta NilInMetaModule) ..))
    (at level 0, only parsing).

Notation "'META_MOD' { m1 'with' .. 'with' mN }" :=
  (MetaMod
     (makeMetaModule
        (ConsInMetaModule m1%kami_meta .. (ConsInMetaModule mN%kami_meta NilInMetaModule) ..)))
    (at level 0, only parsing).


(** Notation for sin-modules *)

Inductive SinModuleElt :=
| SMERegister (_ : SinReg nat)
| SMERule (_ : SinRule)
| SMEMeth (_ : SinMeth).

Inductive InSinModule :=
| NilInSinModule
| ConsInSinModule (_ : SinModuleElt) (_ : InSinModule).

Fixpoint makeSinModule (im : InSinModule) :=
  match im with
  | NilInSinModule => {| sinRegs:= nil;
                         sinRules:= nil;
                         sinMeths:= nil |}
  | ConsInSinModule e i =>
    let '(Build_SinModule iregs irules imeths) := makeSinModule i in
    match e with
    | SMERegister mreg => Build_SinModule (mreg :: iregs) irules imeths
    | SMERule mrule => Build_SinModule iregs (mrule :: irules) imeths
    | SMEMeth mmeth => Build_SinModule iregs irules (mmeth :: imeths)
    end
  end.

Notation "'RegisterN' name : type <- 'Default'" :=
  (SMERegister {| regGen := fun _ => RegInitDefault type;
                  regName := {| nameVal := name;
                                goodName := eq_refl |} |})
    (at level 0, name at level 0, type at level 0) : kami_sin_scope.
Notation "'RegisterN' { name | pf } : type <- 'Default'" :=
  (SMERegister {| regGen := fun _ => RegInitDefault type;
                  regName := {| nameVal := name;
                                goodName := pf |} |})
    (at level 0, name at level 0, type at level 0) : kami_sin_scope.

Notation "'RegisterN' name : type <- init" :=
  (SMERegister {| regGen := fun _ => RegInitCustom (existT ConstFullT (type) (init));
                  regName := {| nameVal := name;
                                goodName := eq_refl |} |})
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_sin_scope.
Notation "'RegisterN' { name | pf } : type <- init" :=
  (SMERegister {| regGen := fun _ => RegInitCustom (existT ConstFullT (type) (init));
                  regName := {| nameVal := name;
                                goodName := pf |} |})
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_sin_scope.

Notation "'Register' name : type <- 'Default'" :=
  (SMERegister {| regGen := fun _ => RegInitDefault (SyntaxKind type);
                  regName := {| nameVal := name;
                                goodName := eq_refl |} |})
    (at level 0, name at level 0, type at level 0) : kami_sin_scope.
Notation "'Register' { name | pf } : type <- 'Default'" :=
  (SMERegister {| regGen := fun _ => RegInitDefault (SyntaxKind type);
                  regName := {| nameVal := name;
                                goodName := pf |} |})
    (at level 0, name at level 0, type at level 0) : kami_sin_scope.

Notation "'Register' name : type <- init" :=
  (SMERegister {| regGen := fun _ => RegInitCustom (existT ConstFullT (SyntaxKind type)
                                                           (makeConst init));
                  regName := {| nameVal := name;
                                goodName := eq_refl |} |})
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_sin_scope.
Notation "'Register' { name | pf } : type <- init" :=
  (SMERegister {| regGen := fun _ => RegInitCustom (existT ConstFullT (SyntaxKind type)
                                                           (makeConst init));
                  regName := {| nameVal := name;
                                goodName := pf |} |})
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_sin_scope.

Notation "'Method' name () : retT := c" :=
  (SMEMeth {| methGen :=
                (existT SinMethodT {| arg := Void; ret := retT |}
                        (fun ty => fun _ : ty Void => (c)%kami_sin : SinActionT ty retT));
              methName := {| nameVal := name;
                             goodName := eq_refl |} |})
    (at level 0, name at level 0) : kami_sin_scope.
Notation "'Method' { name | pf } () : retT := c" :=
  (SMEMeth {| methGen :=
                (existT SinMethodT {| arg := Void; ret := retT |}
                        (fun ty => fun _ : ty Void => (c)%kami_sin : SinActionT ty retT));
              methName := {| nameVal := name;
                             goodName := pf |} |})
    (at level 0, name at level 0) : kami_sin_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (SMEMeth {| methGen :=
                (existT SinMethodT {| arg := dom; ret := retT |}
                        (fun ty => fun param : ty dom => (c)%kami_sin : SinActionT ty retT));
              methName := {| nameVal := name;
                             goodName := eq_refl |} |})
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_sin_scope.
Notation "'Method' { name | pf } ( param : dom ) : retT := c" :=
  (SMEMeth {| methGen :=
                (existT SinMethodT {| arg := dom; ret := retT |}
                        (fun ty => fun param : ty dom => (c)%kami_sin : SinActionT ty retT));
              methName := {| nameVal := name;
                             goodName := pf |} |})
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_sin_scope.

Notation "'Rule' name := c" :=
  (SMERule {| ruleGen := (fun ty => c%kami_sin : SinActionT ty Void);
              ruleName := {| nameVal := name;
                             goodName := eq_refl |} |})
    (at level 0, name at level 0) : kami_sin_scope.
Notation "'Rule' { name | pf } := c" :=
  (SMERule {| ruleGen := (fun ty => c%kami_sin : SinActionT ty Void);
              ruleName := {| nameVal := name;
                             goodName := pf |} |})
    (at level 0, name at level 0) : kami_sin_scope.

Delimit Scope kami_sin_scope with kami_sin.

Notation "'MODULESIN' n 'where' { m1 'with' .. 'with' mN }" :=
  (modFromMeta
     (getMetaFromSin
        string_of_nat string_of_nat_into natToVoid withIndex_index_eq
        (getNatListToN_NoDup n)
        (makeSinModule 
           (ConsInSinModule
              m1%kami_sin .. (ConsInSinModule mN%kami_sin NilInSinModule) ..))))
    (at level 0, only parsing).

Notation "'METASIN' n 'where' { m1 'with' .. 'with' mN }" :=
  (getMetaFromSin
     string_of_nat string_of_nat_into natToVoid withIndex_index_eq
     (getNatListToN_NoDup n)
     (makeSinModule 
        (ConsInSinModule
           m1%kami_sin .. (ConsInSinModule mN%kami_sin NilInSinModule) ..)))
    (at level 0, only parsing).

Notation "'SIN' { m1 'with' .. 'with' mN }" :=
  (makeSinModule 
     (ConsInSinModule
        m1%kami_sin .. (ConsInSinModule mN%kami_sin NilInSinModule) ..))
    (at level 0, only parsing).

