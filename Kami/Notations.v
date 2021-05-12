Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.ilist Lib.Indexer Lib.StringAsList.
Require Import Kami.Syntax.

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
  (Vector.cons _ s1%struct _ .. (Vector.cons _ sN%struct _ (Vector.nil _)) ..)
    (at level 80).

(** Notations for expressions *)
Declare Scope kami_expr_scope.

Notation "nkind #< def" := (@NativeKind nkind def) (at level 0): kami_expr_scope.
Notation "e :: t" :=  (e : Expr _ (SyntaxKind t)) : kami_expr_scope.

Notation "# v" := (Var _ (SyntaxKind _) v) (at level 5, format "# v") : kami_expr_scope.
Notation "!" := (UniBool NegB) (at level 15) : kami_expr_scope.

Infix "&&" := (BinBool AndB) : kami_expr_scope.
Infix "||" := (BinBool OrB) : kami_expr_scope.

Infix "+" := (BinBit (Add _)) : kami_expr_scope.
Infix "-" := (BinBit (Sub _)) : kami_expr_scope.
Infix "*" := (BinBit (Mul _ SignUU)) : kami_expr_scope.
Infix "*s" := (BinBit (Mul _ SignSS)) (at level 40) : kami_expr_scope.
Infix "*su" := (BinBit (Mul _ SignSU)) (at level 40) : kami_expr_scope.
Infix "/" := (BinBit (Div _ false)) : kami_expr_scope.
Infix "/s" := (BinBit (Div _ true)) (at level 40) : kami_expr_scope.

Infix "~&" := (BinBit (Band _)) (at level 40) : kami_expr_scope.
Infix "~|" := (BinBit (Bor _)) (at level 50) : kami_expr_scope.
Infix "~+" := (BinBit (Bxor _)) (at level 30) : kami_expr_scope.

Infix "<<" := (BinBit (Sll _ _)) (at level 20) : kami_expr_scope.
Infix ">>" := (BinBit (Srl _ _)) (at level 20) : kami_expr_scope.
Infix "~>>" := (BinBit (Sra _ _)) (at level 20) : kami_expr_scope.

Infix "<" := (BinBitBool (Lt _)) : kami_expr_scope.
Notation "x > y" := (BinBitBool (Lt _) y x) : kami_expr_scope.
Notation "x >= y" := (UniBool NegB (BinBitBool (Lt _) x y)) : kami_expr_scope.
Notation "x <= y" := (UniBool NegB (BinBitBool (Lt _) y x)) : kami_expr_scope.

Infix "<s" := (BinBitBool (Slt _)) : kami_expr_scope.
Notation "x >s y" := (BinBitBool (Slt _) y x) : kami_expr_scope.
Notation "x >s= y" := (UniBool NegB (BinBitBool (Slt _) x y)) : kami_expr_scope.
Notation "x <s= y" := (UniBool NegB (BinBitBool (Slt _) y x)) : kami_expr_scope.

Infix "==" := Eq (at level 30, no associativity) : kami_expr_scope.
Infix "!=" := (fun e1 e2 => UniBool NegB (Eq e1 e2))
                (at level 30, no associativity) : kami_expr_scope.

Notation "v @[ idx ] " := (ReadIndex idx v) (at level 10) : kami_expr_scope.
Notation "v #[ idx ] " := (ReadArrayIndex idx v) (at level 10) : kami_expr_scope.

Notation "'_zeroExtend_' x" :=
  (UniBit (ZeroExtendTrunc _ _) x) (at level 10) : kami_expr_scope.
Notation "'_signExtend_' x" :=
  (UniBit (SignExtendTrunc _ _) x) (at level 10) : kami_expr_scope.
Notation "'_truncate_' x" :=
  (UniBit (Trunc _ _) x) (at level 10) : kami_expr_scope.
Notation "'_truncLsb_' x" :=
  (UniBit (TruncLsb _ _) x) (at level 10) : kami_expr_scope.

Notation "{ a , b }" := (BinBit (Concat _ _) a b) (a at level 99) : kami_expr_scope.
Notation "{ a ::( al ) , b }" := (BinBit (Concat al _) a b) (a at level 99) : kami_expr_scope.
Notation "{ a , b ::( bl ) }" := (BinBit (Concat _ bl) a b) (a at level 99) : kami_expr_scope.

Delimit Scope kami_expr_scope with kami_expr.

Definition fieldAccessor {A} (fn: string) (x: Attribute A) :=
  Lib.StringEq.string_eq fn (attrName x).
Notation "s !! f" := (Lib.VectorFacts.Vector_find (fieldAccessor f%string) s) (at level 10).
Notation "e ! s @. f" :=
  (@ReadField
     _ _ s
     (Lib.VectorFacts.Vector_find (fieldAccessor f%string) s)
     e%kami_expr) (at level 10): kami_expr_scope.

Notation "'VEC' v" := (BuildVector v) (at level 10) : kami_expr_scope.
Notation "v '@[' idx <- val ] " := (UpdateVector v idx val) (at level 10) : kami_expr_scope.
Notation "v '#[' idx <- val ] " := (UpdateArray v idx val) (at level 10) : kami_expr_scope.
Notation "$ n" := (Const _ (natToWord _ n)) (at level 5) : kami_expr_scope.
Notation "$$ e" := (Const _ e) (at level 5) : kami_expr_scope.
Notation "'IF' e1 'then' e2 'else' e3" := (ITE e1 e2 e3) (at level 200, right associativity) : kami_expr_scope.

Definition icons' {ty} (na : {a : Attribute Kind & Expr ty (SyntaxKind (attrType a))})
           {n} {attrs: Vector.t _ n}
           (tl : ilist (fun a : Attribute Kind => Expr ty (SyntaxKind (attrType a))) attrs)
  : ilist (fun a : Attribute Kind => Expr ty (SyntaxKind (attrType a))) (Vector.cons _ (projT1 na) _ attrs) :=
  icons (projT1 na) (projT2 na) tl.

Declare Scope init_scope.
Notation "name ::= value" :=
  (* (existT (fun a : Attribute Kind => Expr _ (SyntaxKind (attrType a))) *)
  (existT (fun a : Attribute Kind => _)
          (Build_Attribute name _) value) (at level 80) : init_scope.
Delimit Scope init_scope with init.

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (BuildStruct (icons' s1%init .. (icons' sN%init (inil _)) ..))
    (at level 80): kami_expr_scope.
Notation "e '!' s '@{' f '<-' val '}' " :=
  (updStruct e (Lib.VectorFacts.Vector_find (fieldAccessor f%string) s) val) (at level 10) : kami_expr_scope.

Notation "k @ var" := (Expr var (SyntaxKind k)) (at level 0).

(** Notations for action *)
Declare Scope kami_action_scope.

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

