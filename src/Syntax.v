Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word.

Require Import FunctionalExtensionality. (* for appendAction_assoc *)

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

Section VecFunc.
  Variable A: Type.
  Fixpoint evalVec n (vec: Vec A n): word n -> A.
  Proof.
    refine match vec in Vec _ n return word n -> A with
             | Vec0 e => fun _ => e
             | VecNext n' v1 v2 =>
               fun w =>
                 match w in word m0 return m0 = S n' -> A with
                   | WO => _
                   | WS b m w' =>
                     if b
                     then fun _ => evalVec _ v2 (_ w')
                     else fun _ => evalVec _ v2 (_ w')
                 end eq_refl
           end;
    clear evalVec.
    abstract (intros; discriminate).
    abstract (injection _H; intros; subst; intuition).
    abstract (injection _H; intros; subst; intuition).
  Defined.

  Variable B: Type.
  Variable map: A -> B.
  Fixpoint mapVec n (vec: Vec A n): Vec B n :=
    match vec in Vec _ n return Vec B n with
      | Vec0 e => Vec0 (map e)
      | VecNext n' v1 v2 => VecNext (mapVec v1) (mapVec v2)
    end.
End VecFunc.

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

Definition getDefaultConstFull (k: FullKind): ConstFullT k :=
  match k with
    | SyntaxKind k' => SyntaxConst (getDefaultConst k')
    | NativeKind t c => NativeConst c c
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
                             | NativeKind k' _ => k'
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

  Inductive ActionT (lretT: Kind) : Type :=
  | MCall (meth: string) s:
      Expr (SyntaxKind (arg s)) ->
      (type (ret s) -> ActionT lretT) ->
      ActionT lretT
  | Let_ lretT': Expr lretT' -> (fullType lretT' -> ActionT lretT) -> ActionT lretT
  | ReadReg (r: string):
      forall k, (fullType k -> ActionT lretT) -> ActionT lretT
  | WriteReg (r: string) k:
      Expr k -> ActionT lretT -> ActionT lretT
  | IfElse: Expr (SyntaxKind Bool) -> forall k,
                                        ActionT k ->
                                        ActionT k ->
                                        (type k -> ActionT lretT) ->
                                        ActionT lretT
  | Assert_: Expr (SyntaxKind Bool) -> ActionT lretT -> ActionT lretT
  | Return: Expr (SyntaxKind lretT) -> ActionT lretT.
End Phoas.

Definition Action (retTy : Kind) := forall ty, ActionT ty retTy.
Definition MethodT (sig : SignatureT) := forall ty,
                                           ty (arg sig) -> ActionT ty (ret sig).

Definition RegInitT := Attribute (sigT ConstFullT).
Definition DefMethT := Attribute (sigT MethodT).

Definition Void := Bit 0.
Inductive Modules: Type :=
| Mod (regs: list RegInitT)
      (rules: list (Attribute (Action Void)))
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

Fixpoint getDefsBodies (m: Modules): list DefMethT :=
  match m with
    | Mod _ _ meths => meths
    | ConcatMod m1 m2 => (getDefsBodies m1) ++ (getDefsBodies m2)
  end.

Definition getDefs m: list string := namesOf (getDefsBodies m).

Section AppendAction.
  Variable type: Kind -> Type.
  
  Fixpoint appendAction {retT1 retT2} (a1: ActionT type retT1)
           (a2: type retT1 -> ActionT type retT2): ActionT type retT2 :=
    match a1 with
      | MCall name sig ar cont => MCall name sig ar (fun a => appendAction (cont a) a2)
      | Let_ _ ar cont => Let_ ar (fun a => appendAction (cont a) a2)
      | ReadReg reg k cont => ReadReg reg k (fun a => appendAction (cont a) a2)
      | WriteReg reg _ e cont => WriteReg reg e (appendAction cont a2)
      | IfElse ce _ ta fa cont => IfElse ce ta fa (fun a => appendAction (cont a) a2)
      | Assert_ ae cont => Assert_ ae (appendAction cont a2)
      | Return e => Let_ e a2
    end.

  Lemma appendAction_assoc:
    forall {retT1 retT2 retT3}
           (a1: ActionT type retT1) (a2: type retT1 -> ActionT type retT2)
           (a3: type retT2 -> ActionT type retT3),
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
  
  Fixpoint getCallsA {k} (a: ActionT typeUT k): list string :=
    match a with
      | MCall m _ _ c => m :: (getCallsA (c tt))
      | Let_ fk e c => getCallsA
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
      | Return _ => nil
    end.

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

  Fixpoint getCallsR (rl: list (Attribute (Action (Bit 0))))
  : list string :=
    match rl with
      | nil => nil
      | r :: rl' => (getCallsA (attrType r typeUT)) ++ (getCallsR rl')
    end.

  Fixpoint getCallsM (ms: list DefMethT): list string :=
    match ms with
      | nil => nil
      | m :: ms' => (getCallsA ((projT2 (attrType m)) typeUT tt))
                      ++ (getCallsM ms')
    end.

  Lemma getCallsM_app: forall ms1 ms2, getCallsM (ms1 ++ ms2) = getCallsM ms1 ++ getCallsM ms2.
  Proof.
    induction ms1; intros; [reflexivity|].
    simpl; rewrite IHms1; apply app_assoc.
  Qed.

  Definition getCalls m := getCallsR (getRules m) ++ getCallsM (getDefsBodies m).
End GetCalls.

Hint Unfold getRules getRegInits getDefs getCalls getDefsBodies.

(* Notations: registers and methods declaration *)
Notation Default := (getDefaultConst _).
Notation "'MethodSig' name () : retT" :=
  (Build_Attribute name {| arg := Void; ret := retT |})
  (at level 0, name at level 0, retT at level 200).
Notation "'MethodSig' name ( argT ) : retT" :=
  (Build_Attribute name {| arg := argT; ret := retT |})
  (at level 0, name at level 0, argT at level 200, retT at level 200).

(* Notations: expression *)
Notation "# v" := (Var _ (SyntaxKind _) v) (at level 0) : kami_scope.
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


(** * Notation corner! *)

(* Notations: action *)

Coercion attrName : Attribute >-> string.

Notation "'Call' meth ( arg ) ; cont " :=
  (MCall (attrName meth) (attrType meth) arg (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_scope.
Notation "'Call' name <- meth ( arg ) ; cont " :=
  (MCall (attrName meth) (attrType meth) arg (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_scope.
Notation "'Call' meth () ; cont " :=
  (MCall (attrName meth) (attrType meth) (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_scope.
Notation "'Call' name <- meth () ; cont " :=
  (MCall (attrName meth) (attrType meth) (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_scope.
Notation "'LET' name <- expr ; cont " :=
  (Let_ expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'LET' name : t <- expr ; cont " :=
  (Let_ (lretT' := t) expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'Read' name <- reg ; cont" :=
  (ReadReg reg _ (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (ReadReg reg (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'Write' reg <- expr ; cont " :=
  (WriteReg reg expr cont)
    (at level 12, right associativity, reg at level 0) : kami_scope.
Notation "'Write' reg <- expr : kind ; cont " :=
  (@WriteReg _ _ reg (SyntaxKind kind) expr cont)
    (at level 12, right associativity, reg at level 0) : kami_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElse cexpr tact fact (fun name => cont))
    (at level 13, right associativity, name at level 0, cexpr at level 0, tact at next level, fact at next level) : kami_scope.
Notation "'Assert' expr ; cont " :=
  (Assert_ expr cont)
    (at level 12, right associativity) : kami_scope.
Notation "'Ret' expr" :=
  (Return expr) (at level 12) : kami_scope.
Notation Retv := (Return (Const _ (k := Void) Default)).


(* * Modules *)

Inductive InModule :=
| NilInModule
| RegisterInModule (_ : RegInitT)
| RuleInModule (_ : Attribute (Action Void))
| MethodInModule (_ : DefMethT)
| ConcatInModule (_ _ : InModule)
| NumberedInModule (f : nat -> InModule) (n : nat).

Section numbered.
  Variable makeModule' : InModule
                         -> list RegInitT
                            * list (Attribute (Action Void))
                            * list DefMethT.

  Variable f : nat -> InModule.

  Fixpoint numbered (n : nat) :=
    match n with
      | O => (nil, nil, nil)
      | S n' =>
        let '(a, b, c) := makeModule' (f n') in
        let '(a', b', c') := numbered n' in
        (a ++ a', b ++ b', c ++ c')
    end.
End numbered.

Fixpoint makeModule' (im : InModule) := 
  match im with
    | NilInModule => (nil, nil, nil)
    | RegisterInModule r => (r :: nil, nil, nil)
    | RuleInModule r => (nil, r :: nil, nil)
    | MethodInModule r => (nil, nil, r :: nil)
    | ConcatInModule im1 im2 =>
      let '(a1, b1, c1) := makeModule' im1 in
      let '(a2, b2, c2) := makeModule' im2 in
      (a1 ++ a2, b1 ++ b2, c1 ++ c2)
    | NumberedInModule f n => numbered makeModule' f n
  end.

Fixpoint makeModule (im : InModule) :=
  let '(a, b, c) := makeModule' im in
  Mod a b c.

Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.

Notation DefaultFull := (makeConst Default).

Definition firstAction {T} (ls : list (Action T)) : Action T :=
  match ls with
  | a :: _ => a
  | _ => fun _ => Return (Const _ Default)
  end.

(*
Notation "'ACTION' { a1 'with' .. 'with' aN }" := (firstAction (cons (fun _ => a1%kami) .. (cons (fun _ => aN%kami) nil) ..))
  (at level 0, only parsing, a at level 200). *)

Notation "'ACTION' { a }" := (fun ty => a%kami : ActionT ty _)
  (at level 0, only parsing, a at level 0).

Notation "'Register' name : type <- init" :=
  (RegisterInModule (Build_Attribute name (existT ConstFullT (SyntaxKind type) (makeConst init))))
  (at level 0, name at level 0, type at level 0, init at level 0) : kami_method_scope.

Notation "'RegisterN' name : type <- init" :=
  (RegisterInModule (Build_Attribute name (existT ConstFullT (type) (init))))
  (at level 0, name at level 0, type at level 0, init at level 0) : kami_method_scope.

Notation "'Method' name () : retT := c" :=
  (MethodInModule (Build_Attribute name (existT MethodT {| arg := Void; ret := retT |}
     (fun ty => fun _ : ty Void => (c)%kami : ActionT ty retT))))
  (at level 0, name at level 0) : kami_method_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (MethodInModule (Build_Attribute name (existT MethodT {| arg := dom; ret := retT |}
     (fun ty => fun param : ty dom => (c)%kami : ActionT ty retT))))
  (at level 0, name at level 0, param at level 0, dom at level 0) : kami_method_scope.

Notation "'Rule' name := c" :=
  (RuleInModule (Build_Attribute name (fun ty => c%kami : ActionT ty Void)))
  (at level 0, name at level 0) : kami_method_scope.

Delimit Scope kami_method_scope with method.

Notation "'Repeat' count 'as' n { m1 'with' .. 'with' mN }" :=
  (NumberedInModule (fun n => ConcatInModule m1%method .. (ConcatInModule mN%method NilInModule) ..) count)
  (at level 0, count at level 0, n at level 0) : kami_method_scope.

Notation "'MODULE' { m1 'with' .. 'with' mN }" := (makeModule (ConcatInModule m1%method .. (ConcatInModule mN%method NilInModule) ..)) (at level 0, only parsing).

Definition icons' {ty} (na : {a : Attribute Kind & Expr ty (SyntaxKind (attrType a))})
           {attrs}
           (tl : ilist (fun a : Attribute Kind => Expr ty (SyntaxKind (attrType a))) attrs)
  : ilist (fun a : Attribute Kind => Expr ty (SyntaxKind (attrType a))) (projT1 na :: attrs) :=
  icons (projT1 na) (projT2 na) tl.

Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => Expr _ (SyntaxKind (attrType a)))
          (Build_Attribute name _) value) (at level 50) : init_scope.
Delimit Scope init_scope with init.

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (BuildStruct (icons' s1%init .. (icons' sN%init (inil _)) ..))
  : kami_scope.

Notation "e :: t" := (e : Expr _ (SyntaxKind t)) : kami_scope.
