Require Import Bool List String.
Require Import Lib.CommonTactics Lib.StringEq Lib.Word Lib.FMap Lib.StringEq Lib.ilist Lib.Struct Lib.Indexer.

Require Import FunctionalExtensionality. (* for appendAction_assoc *)
Require Import Eqdep. (* for signature_eq *)
Require Import Program.Equality.

Require Vector.

Set Implicit Arguments.
Set Asymmetric Patterns.

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
                     else fun _ => evalVec _ v1 (_ w')
                 end eq_refl
           end;
    clear evalVec.
    abstract (intros; discriminate).
    abstract (injection e; intros; subst; intuition).
    abstract (injection e; intros; subst; intuition).
  Defined.

  Variable B: Type.
  Variable map: A -> B.
  Fixpoint mapVec n (vec: Vec A n): Vec B n :=
    match vec in Vec _ n return Vec B n with
      | Vec0 e => Vec0 (map e)
      | VecNext n' v1 v2 => VecNext (mapVec v1) (mapVec v2)
    end.
End VecFunc.

Inductive Kind :=
| Bool    : Kind
| Bit     : nat -> Kind
| Vector  : Kind -> nat -> Kind
| Struct  : forall n, Vector.t (Attribute Kind) n -> Kind.

Fixpoint type (t: Kind): Type :=
  match t with
    | Bool => bool
    | Bit n => word n
    | Vector nt n => word n -> type nt
    | Struct n ks => forall i: Fin.t n, Vector.nth (Vector.map (fun p => type (attrType p)) ks) i
  end.

Inductive FullKind: Type :=
| SyntaxKind: Kind -> FullKind
| NativeKind (t: Type) (c: t) : FullKind.

Section VectorT_dec.
  Variable A: Type.
  Variable n: nat.
  Variable decA: forall (a1 a2: A), {a1 = a2} + {a1 <> a2}.

  Lemma decA_true_iff_sumbool a1 a2:
    (if decA a1 a2 then true else false) = true <-> a1 = a2.
  Proof.
    destruct (decA a1 a2); try intuition congruence.
  Qed.

  Definition
    VectorT_dec (v1 v2: Vector.t A n): {v1 = v2} + {v1 <> v2} :=
    Vector.eq_dec _ (fun a1 a2 => if decA a1 a2 then true else false) decA_true_iff_sumbool n v1 v2.
End VectorT_dec.

Section Pair_dec.
  Variable A B: Type.
  Variable decA: forall (a1 a2: A), {a1 = a2} + {a1 <> a2}.
  Variable decB: forall (b1 b2: B), {b1 = b2} + {b1 <> b2}.
  Lemma prod_dec: forall (ab1 ab2: (A*B)%type), {ab1 = ab2} + {ab1 <> ab2}.
  Proof.
    intros.
    destruct ab1, ab2.
    destruct (decA a a0), (decB b b0); clear decA decB.
    - abstract (subst; left; reflexivity).
    - abstract (subst; right; intro H; inversion H; tauto).
    - abstract (subst; right; intro H; inversion H; tauto).
    - abstract (subst; right; intro H; inversion H; tauto).
  Defined.
End Pair_dec.

Fixpoint decKind (k1 k2: Kind) : {k1 = k2} + {k1 <> k2}.
  refine match k1, k2 return {k1 = k2} + {k1 <> k2} with
           | Bool, Bool => left eq_refl
           | Bit n, Bit m => match PeanoNat.Nat.eq_dec n m with
                               | left l => left match l in _ = Y return Bit n = Bit Y with
                                                  | eq_refl => eq_refl
                                                end
                               | right r => right _
                             end
           | Vector k1 n1, Vector k2 n2 => match PeanoNat.Nat.eq_dec n1 n2 with
                                             | left l => match decKind k1 k2 with
                                                           | left kl => left match l in _ = Y, kl in _ = kY
                                                                                   return Vector k1 n1 = Vector kY Y with
                                                                               | eq_refl, eq_refl => eq_refl
                                                                             end
                                                           | right kr => right _
                                                         end
                                             | right r => right _
                                           end
           | Struct n1 l1, Struct n2 l2 => _
           | _, _ => right _
         end; try (clear decKind; abstract (intro; try inversion H; congruence)).
  - dependent induction l1; dependent destruction l2.
    + clear decKind; left; abstract reflexivity.
    + clear decKind; right; abstract (intro H; inversion H).
    + clear decKind; right; abstract (intro H; inversion H).
    + destruct h0, h.
      destruct (string_dec attrName0 attrName); [| clear decKind; abstract (right; intro H; inversion H; subst; tauto)].
      destruct (decKind attrType0 attrType); clear decKind;
      [| right; abstract (intro H; inversion H; try apply inj_pair2 in H; subst; tauto)].
      destruct (IHl1 _ l2); clear IHl1.
      * left; abstract (subst; inversion e1; try apply inj_pair2 in H1; subst; tauto).
      * right; abstract (subst; intros H; inversion H; subst; apply inj_pair2 in H3; subst; tauto).
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
| ConstStruct n (ls: Vector.t _ n): ilist (fun a => ConstT (attrType a)) ls -> ConstT (Struct ls).

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
    | Struct n ls =>
      ConstStruct ((fix help n (ls: Vector.t _ n) :=
                      match ls return ilist (fun a => ConstT (attrType a)) ls with
                        | Vector.nil => inil _
                        | Vector.cons x m xs => icons x (getDefaultConst (attrType x)) (help m xs)
                      end) n ls)
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
                    forall (vs4: Vector.t _ n4), type (Struct vs4) ->
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
    | Bit n => getDefaultConstBit n
    | Vector k n => fun _ => getDefaultConstNative k
    | Struct n attrs =>
      fun i =>
        ilist_to_fun _ ((fix help n (ls: Vector.t _ n) :=
                           match ls return ilist (fun a => type (attrType a)) ls with
                             | Vector.nil => inil _
                             | Vector.cons x _ xs =>
                               icons x (getDefaultConstNative (attrType x)) (help _ xs)
                           end) n attrs) i
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
  intros.
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
| Neg: UniBoolOp.

Inductive BinBoolOp: Set :=
| And: BinBoolOp
| Or: BinBoolOp.

Inductive UniBitOp: nat -> nat -> Set :=
| Inv n: UniBitOp n n
| ConstExtract n1 n2 n3: UniBitOp (n1 + n2 + n3) n2 (* LSB : n1, MSB : n3 *)
| Trunc n1 n2: UniBitOp (n1 + n2) n1 (* LSB : n1 *)
| ZeroExtendTrunc n1 n2: UniBitOp n1 n2
| SignExtendTrunc n1 n2: UniBitOp n1 n2
| TruncLsb n1 n2: UniBitOp (n1 + n2) n2. (* MSB : n2 *)

Inductive BinBitOp: nat -> nat -> nat -> Set :=
| Add n: BinBitOp n n n
| Sub n: BinBitOp n n n
| Mul n: BinBitOp n n n
| Band n: BinBitOp n n n
| Bor n: BinBitOp n n n
| Bxor n: BinBitOp n n n
| Sll n m: BinBitOp n m n
| Srl n m: BinBitOp n m n
| Sra n m: BinBitOp n m n
| Concat n1 n2: BinBitOp n1 n2 (n2 + n1). (* MSB : n1, LSB : n2 *)

Inductive BinBitBoolOp: nat -> nat -> Set :=
| Lt n: BinBitBoolOp n n.

Section Phoas.
  Variable ty: Kind -> Type.
  Definition fullType k := match k with
                             | SyntaxKind k' => ty k'
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
  | BinBitBool n1 n2: BinBitBoolOp n1 n2 -> Expr (SyntaxKind (Bit n1)) -> Expr (SyntaxKind (Bit n2)) ->
                      Expr (SyntaxKind Bool)
  | ITE k: Expr (SyntaxKind Bool) -> Expr k -> Expr k -> Expr k
  | Eq k: Expr (SyntaxKind k) -> Expr (SyntaxKind k) -> Expr (SyntaxKind Bool)
  | ReadIndex i k: Expr (SyntaxKind (Bit i)) -> Expr (SyntaxKind (Vector k i)) -> Expr (SyntaxKind k)
  | ReadField n (ls: Vector.t _ n) (i: Fin.t n):
      Expr (SyntaxKind (Struct ls)) -> Expr (SyntaxKind (Vector.nth (Vector.map (@attrType _) ls) i))
  | BuildVector n k: Vec (Expr (SyntaxKind n)) k -> Expr (SyntaxKind (Vector n k))
  | BuildStruct n (attrs: Vector.t _ n):
      ilist (fun a => Expr (SyntaxKind (attrType a))) attrs -> Expr (SyntaxKind (Struct attrs))
  | UpdateVector i k: Expr (SyntaxKind (Vector k i)) -> Expr (SyntaxKind (Bit i)) -> Expr (SyntaxKind k)
                      -> Expr (SyntaxKind (Vector k i)).

  Inductive ActionT (lretT: Kind) : Type :=
  | MCall (meth: string) s:
      Expr (SyntaxKind (arg s)) ->
      (ty (ret s) -> ActionT lretT) ->
      ActionT lretT
  | Let_ lretT': Expr lretT' -> (fullType lretT' -> ActionT lretT) -> ActionT lretT
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
  | Return: Expr (SyntaxKind lretT) -> ActionT lretT.
End Phoas.

Definition Action (retTy : Kind) := forall ty, ActionT ty retTy.
Definition MethodT (sig : SignatureT) := forall ty, ty (arg sig) -> ActionT ty (ret sig).

Inductive RegInitValue :=
| RegInitCustom: sigT ConstFullT -> RegInitValue
| RegInitDefault: FullKind -> RegInitValue.

Require Import Lib.Struct.

Definition RegInitT := Attribute RegInitValue.
Definition DefMethT := Attribute (sigT MethodT).

Definition filterDm (dms: list DefMethT) (filt: string) :=
  filter (fun dm => if string_dec (attrName dm) filt then false else true) dms.

Definition filterDms (dms: list DefMethT) (filt: list string) :=
  filter (fun dm => if string_in (attrName dm) filt then false else true) dms.

Definition Void := Bit 0.
Inductive Modules: Type :=
| RegFile (dataArray read write: string) (IdxBits: nat) (Data: Kind) (init: ConstT (Vector Data IdxBits)): Modules
| Mod (regs: list RegInitT)
      (rules: list (Attribute (Action Void)))
      (dms: list DefMethT):
    Modules
| ConcatMod (m1 m2: Modules):
    Modules.

Fixpoint getRules m := 
  match m with
    | RegFile _ _ _ _ _ _ => nil
    | Mod _ rules _ => rules
    | ConcatMod m1 m2 => getRules m1 ++ getRules m2
  end.

Fixpoint getRegInits m :=
  match m with
    | RegFile dataArray read write IdxBits Data init =>
      {| attrName := dataArray;
         attrType := RegInitCustom (existT ConstFullT (SyntaxKind (Vector Data IdxBits)) (SyntaxConst init)) |}
        :: nil
    | Mod regs _ _ => regs
    | ConcatMod m1 m2 => getRegInits m1 ++ getRegInits m2
  end.

Fixpoint getDefsBodies (m: Modules): list DefMethT :=
  match m with
    | RegFile dataArray read write IdxBits Data init =>
      {| attrName := read;
         attrType :=
           existT MethodT {| arg := Bit IdxBits; ret := Data |}
                  (fun ty (ar: ty (Bit IdxBits)) =>
                     (ReadReg dataArray%string
                              (SyntaxKind (Vector Data IdxBits))
                              (fun x: ty (Vector Data IdxBits) =>
                                 Return
                                   (ReadIndex
                                      (Var ty (SyntaxKind (Bit IdxBits)) ar)
                                      (Var ty (SyntaxKind (Vector Data IdxBits)) x)))))
      |} ::
         {| attrName := write%string;
            attrType :=
              existT MethodT {| arg := Struct
                                         (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                                      (Vector.cons _ {| attrName := "data"%string; attrType := Data |} _ (Vector.nil _)));
                                ret := Void |}
                     (fun ty (ar: ty (Struct
                                        (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                                     (Vector.cons _ {| attrName := "data"%string; attrType := Data |} _ (Vector.nil _)))))
                          =>
                            (ReadReg dataArray%string
                                     (SyntaxKind (Vector Data IdxBits))
                                     (fun x: ty (Vector Data IdxBits) =>
                                        WriteReg dataArray%string
                                                 (UpdateVector (Var ty (SyntaxKind (Vector Data IdxBits)) x)
                                                               (ReadField Fin.F1 (Var ty (SyntaxKind _) ar))
                                                               (ReadField (Fin.FS Fin.F1) (Var ty (SyntaxKind _) ar)))
                                                 (Return (Const _ (k := Void) WO)))))
         |} :: nil
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
      | ReadReg reg k cont => ReadReg reg k (fun a => appendAction (cont a) a2)
      | WriteReg reg _ e cont => WriteReg reg e (appendAction cont a2)
      | IfElse ce _ ta fa cont => IfElse ce ta fa (fun a => appendAction (cont a) a2)
      | Assert_ ae cont => Assert_ ae (appendAction cont a2)
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

  Fixpoint getCallsRule (r: Attribute (Action (Bit 0)))
  : list string :=
    getCallsA (attrType r typeUT).

  Fixpoint getCallsR (rl: list (Attribute (Action (Bit 0))))
  : list string :=
    match rl with
      | nil => nil
      | r :: rl' => (getCallsA (attrType r typeUT)) ++ (getCallsR rl')
    end.

  Definition getCallsDm (dm: DefMethT): list string :=
    getCallsA (projT2 (attrType dm) typeUT tt).
               
  Fixpoint getCallsM (ms: list DefMethT): list string :=
    match ms with
      | nil => nil
      | m :: ms' => (getCallsA ((projT2 (attrType m)) typeUT tt))
                      ++ (getCallsM ms')
    end.

  Lemma getCallsM_implies_getCallsDm s ms: In s (getCallsM ms) ->
                                           exists dm, In dm ms /\ In s (getCallsDm dm).
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
  Hint Immediate DefCallSub_refl.

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
    | ReadReg reg k cont => isLeaf (cont (getUT _)) cs
    | WriteReg reg _ e cont => isLeaf cont cs
    | IfElse ce _ ta fa cont => (isLeaf ta cs) && (isLeaf fa cs) && (isLeaf (cont tt) cs)
    | Assert_ ae cont => isLeaf cont cs
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

Definition getExtMeths (m: Modules) := getExtDefs m ++ getExtCalls m.

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

Hint Unfold getRules getRegInits getDefs getCalls getDefsBodies
     getExtDefsBodies getExtDefs getExtCalls getExtMeths.

(** Notations *)

Notation "[ x1 ; .. ; xN ]" := (cons x1 .. (cons xN nil) ..) : list_scope.
Notation "name :: ty" := {| attrName := name; attrType := ty |} : kami_struct_scope.
Delimit Scope kami_struct_scope with struct.
Notation "m1 ++ m2" := (ConcatMod m1 m2) : kami_scope.
Delimit Scope kami_scope with kami.

