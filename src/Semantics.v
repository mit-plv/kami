Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FnMap Syntax.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* concrete representations of data kinds *)
Fixpoint type (t: Kind): Type :=
  match t with
    | Bool => bool
    | Bit n => word n
    | Vector nt n => word n -> type nt
    | Struct attrs => forall i, @GetAttrType _ (map (mapAttr type) attrs) i
  end.

Section WordFunc.

  Definition wordZero (w: word 0): w = WO :=
    shatter_word w.

  Variable A: Type.

  (* a lemma for wordVecDec *)
  Definition wordVecDec':
    forall n (f g: word n -> A), (forall x: word n, {f x = g x} + {f x <> g x}) ->
                                 {forall x, f x = g x} + {exists x, f x <> g x}.
  Proof.
    intro n.
    induction n; intros f g H.
    - destruct (H WO).
      + left; intros x.
        rewrite (wordZero x) in *; intuition.
      + right; eauto.
    - assert (Hn: forall b (x: word n),
                    {f (WS b x) = g (WS b x)} + {f (WS b x) <> g (WS b x)}) by
             (intros; specialize (H (WS b x)); intuition).
      destruct (IHn _ _ (Hn false)) as [ef | nf].
      + destruct (IHn _ _ (Hn true)) as [et | nt].
        * left; intros x.
          specialize (ef (wtl x)).
          specialize (et (wtl x)).
          pose proof (shatter_word x) as use; simpl in *.
          destruct (whd x); rewrite <- use in *; intuition.
        * right; destruct_ex; eauto.
      + right; destruct_ex; eauto.
  Qed.

  Definition wordVecDec:
    forall n (f g: word n -> A), (forall x: word n, {f x = g x} + {f x <> g x}) ->
                                 {f = g} + {f <> g}.
  Proof.
    intros.
    pose proof (wordVecDec' _ _ H) as [lt | rt].
    left; apply functional_extensionality; intuition.
    right; unfold not; intros eq; rewrite eq in *.
    destruct rt; intuition.
  Qed.
End WordFunc.

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

(* for any kind, we have decidable equality on its representation *)
Definition isEq : forall k (e1: type k) (e2: type k),
                    {e1 = e2} + {e1 <> e2}.
Proof.
  refine (fix isEq k : forall (e1: type k) (e2: type k), {e1 = e2} + {e1 <> e2} :=
            match k return forall (e1: type k) (e2: type k),
                             {e1 = e2} + {e1 <> e2} with
              | Bool => bool_dec
              | Bit n => fun e1 e2 => weq e1 e2
              | Vector n nt =>
                  fun e1 e2 =>
                    wordVecDec e1 e2 (fun x => isEq _ (e1 x) (e2 x))
              | Struct h =>
                (fix isEqs atts : forall (vs1 vs2 : forall i, @GetAttrType _ (map (mapAttr type) atts) i),
                                    {vs1 = vs2} + {vs1 <> vs2} :=
                   match atts return forall (vs1 vs2 : forall i, @GetAttrType _ (map (mapAttr type) atts) i),
                                       {vs1 = vs2} + {vs1 <> vs2} with
                     | nil => fun _ _ => Yes
                     | att :: atts' => fun vs1 vs2 =>
                       isEq _
                            (vs1 {| bindex := attrName att; indexb := {| ibound := 0;
                                      boundi := eq_refl :
                                                  nth_error
                                                    (map (attrName (Kind:=Type))
                                                         (map (mapAttr type) (att :: atts'))) 0
                                                    = Some (attrName att) |} |})
                            (vs2 {| bindex := attrName att; indexb := {| ibound := 0;
                                      boundi := eq_refl :
                                                  nth_error
                                                    (map (attrName (Kind:=Type))
                                                         (map (mapAttr type) (att :: atts'))) 0
                                                    = Some (attrName att) |} |});;
                       isEqs atts'
                       (fun i => vs1 {| indexb := {| ibound := S (ibound (indexb i)) |} |})
                       (fun i => vs2 {| indexb := {| ibound := S (ibound (indexb i)) |} |});;
                       Yes
                   end) h
            end); clear isEq; try clear isEqs;
  abstract (unfold BoundedIndexFull in *; simpl in *; try (intro; subst; tauto);
  repeat match goal with
           | [ |- _ = _ ] => extensionality i
           | [ x : BoundedIndex _ |- _ ] => destruct x
           | [ x : IndexBound _ _ |- _ ] => destruct x
           | [ H : nth_error nil ?n = Some _ |- _ ] => destruct n; discriminate
           | [ |- _ {| indexb := {| ibound := ?b |} |} = _ ] =>
             match goal with
               | [ x : _ |- _ ] =>
                 match x with
                   | b => destruct b; simpl in *
                 end
             end
           | [ H : Specif.value _ = Some _ |- _ ] => progress (injection H; intro; subst)
           | [ H : _ = _ |- _ ] => progress rewrite (UIP_refl _ _ H)
           | [ H : _ = _ |- _ {| bindex := ?bi; indexb := {| ibound := S ?ib; boundi := ?pf |} |} = _ ] =>
             apply (f_equal (fun f => f {| bindex := bi; indexb := {| ibound := ib; boundi := pf |} |})) in H
         end; auto).
Defined.

Definition evalUniBool (op: UniBoolOp) : bool -> bool :=
  match op with
    | Neg => negb
  end.

Definition evalBinBool (op: BinBoolOp) : bool -> bool -> bool :=
  match op with
    | And => andb
    | Or => orb
  end.

(* the head of a word, or false if the word has 0 bits *)
Definition whd' sz (w: word sz) :=
  match sz as s return word s -> bool with
    | 0 => fun _ => false
    | S n => fun w => whd w
  end w.

Definition evalUniBit n1 n2 (op: UniBitOp n1 n2): word n1 -> word n2.
refine match op with
         | Inv n => @wneg n
         | ConstExtract n1 n2 n3 => fun w => split2 n1 n2 (split1 (n1 + n2) n3 w)
         | ZeroExtendTrunc n1 n2 => fun w => split2 n1 n2 (_ (combine (wzero n2) w))
         | SignExtendTrunc n1 n2 => fun w => split2 n1 n2 (_ (combine (if whd' w
                                                                       then wones n2
                                                                       else wzero n2) w))
         | TruncLsb n1 n2 => fun w => split1 n1 n2 w
       end;
  assert (H: n3 + n0 = n0 + n3) by omega;
  rewrite H in *; intuition.
Defined.

Definition evalBinBit n1 n2 n3 (op: BinBitOp n1 n2 n3)
  : word n1 -> word n2 -> word n3 :=
  match op with
    | Add n => @wplus n
    | Sub n => @wminus n
  end.

Definition evalConstStruct attrs (ils : ilist (fun a => type (attrType a)) attrs) : type (Struct attrs) :=
  fun (i: BoundedIndex (map (@attrName _) (map (mapAttr type) attrs))) =>
    mapAttrEq1 type attrs i
               (ith_Bounded _ ils (getNewIdx1 type attrs i)).

(* evaluate any constant operation *)
Fixpoint evalConstT k (e: ConstT k): type k :=
  match e in ConstT k return type k with
    | ConstBool b => b
    | ConstBit n w => w
    | ConstVector k' n v => evalVec (mapVec (@evalConstT k') v)
    | ConstStruct attrs ils => evalConstStruct (imap _ (fun _ ba => evalConstT ba) ils)
  end.

Definition evalConstFullT k (e: ConstFullT k) :=
  match e in ConstFullT k return fullType type k with
    | SyntaxConst k' c' => evalConstT c'
    | NativeConst t c c' => c'
  end.

Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.

Definition defaultConstFullT k: fullType type k :=
  match k as k' return fullType type k' with
    | SyntaxKind k => evalConstT (getDefaultConst _)
    | NativeKind t c => c
  end.

Section GetCms.
  Fixpoint getCmsA {k} (a: Action type k): list string :=
    match a with
      | MCall m _ _ c => m :: (getCmsA (c (evalConstT (getDefaultConst _))))
      | Let_ fk e c => getCmsA (c (defaultConstFullT fk))
      | ReadReg _ fk c => getCmsA (c (defaultConstFullT fk))
      | WriteReg _ _ _ c => getCmsA c
      | IfElse _ _ aT aF c =>
        (getCmsA aT) ++ (getCmsA aF)
                     ++ (getCmsA (c (evalConstT (getDefaultConst _))))
      | Assert_ _ c => getCmsA c
      | Return _ => nil
    end.

  Fixpoint getCmsR (rl: list (Attribute (Action type (Bit 0))))
  : list string :=
    match rl with
      | nil => nil
      | r :: rl' => (getCmsA (attrType r)) ++ (getCmsR rl')
    end.

  Fixpoint getCmsM (ms: list (DefMethT type)): list string :=
    match ms with
      | nil => nil
      | m :: ms' => (getCmsA ((objVal (attrType m))
                                (evalConstT (getDefaultConst _))))
                      ++ (getCmsM ms')
    end.

  Fixpoint getCmsMod (m: Modules type): list string :=
    match m with
      | Mod _ rules meths => getCmsR rules ++ getCmsM meths
      | ConcatMod m1 m2 => (listSub (getCmsMod m1) (getDmsMod m2))
                             ++ (listSub (getCmsMod m2) (getDmsMod m1))
    end
  with getDmsMod (m: Modules type): list string :=
         match m with
           | Mod _ _ meths => map (@attrName _) meths
           | ConcatMod m1 m2 => (listSub (getDmsMod m1) (getCmsMod m2))
                                  ++ (listSub (getDmsMod m2) (getCmsMod m1))
         end.

End GetCms.

Hint Unfold getCmsMod getDmsMod.

(* maps register names to the values which they currently hold *)
Definition RegsT := @Map (Typed (fullType type)).

(* a pair of the value sent to a method call and the value it returned *)
Definition SignT k := (type (arg k) * type (ret k))%type.

(* a list of simulatenous method call actions made during a single step *)
Definition CallsT := @Map (Typed SignT).

Section Semantics.
  Definition mkStruct attrs (ils : ilist (fun a => type (attrType a)) attrs) : type (Struct attrs) :=
    fun (i: BoundedIndex (map (@attrName _) (map (mapAttr type) attrs))) =>
      mapAttrEq1 type attrs i (ith_Bounded _ ils (getNewIdx1 type attrs i)).

  Fixpoint evalExpr exprT (e: Expr type exprT): fullType type exprT :=
    match e in Expr _ exprT return fullType type exprT with
      | Var _ v => v
      | Const _ v => evalConstT v
      | UniBool op e1 => (evalUniBool op) (evalExpr e1)
      | BinBool op e1 e2 => (evalBinBool op) (evalExpr e1) (evalExpr e2)
      | UniBit n1 n2 op e1 => (evalUniBit op) (evalExpr e1)
      | BinBit n1 n2 n3 op e1 e2 => (evalBinBit op) (evalExpr e1) (evalExpr e2)
      | ITE _ p e1 e2 => if evalExpr p
                         then evalExpr e1
                         else evalExpr e2
      | Eq _ e1 e2 => if isEq _ (evalExpr e1) (evalExpr e2)
                      then true
                      else false
      | ReadIndex _ _ i f => (evalExpr f) (evalExpr i)
      | ReadField heading fld val =>
          mapAttrEq2 type fld
            ((evalExpr val) (getNewIdx2 type fld))
      | BuildVector _ k vec => evalVec (mapVec (@evalExpr _) vec)
      | BuildStruct attrs ils => mkStruct (imap _ (fun _ ba => evalExpr ba) ils)
      | UpdateVector _ _ fn i v =>
          fun w => if weq w (evalExpr i) then evalExpr v else (evalExpr fn) w
    end.

  (*register names and constant expressions for their initial values *)
  Variable regInit: list RegInitT.

  Variable rules: list (Attribute (Action type (Bit 0))).

  (* register values just before the current cycle *)
  Variable oldRegs: RegsT.

  Inductive SemAction:
    forall k, Action type k -> RegsT -> CallsT -> type k -> Prop :=
  | SemMCall
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> Action type retK)
      newRegs (calls: CallsT) acalls
      (HAcalls: acalls = add meth {| objVal := (evalExpr marg, mret) |} calls)
      (HSemAction: SemAction (cont mret) newRegs calls fret):
      SemAction (MCall meth s marg cont) newRegs acalls fret
  | SemLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> Action type retK) newRegs calls
      (HSemAction: SemAction (cont (evalExpr e)) newRegs calls fret):
      SemAction (Let_ e cont) newRegs calls fret
  | SemReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> Action type retK)
      newRegs calls
      (HRegVal: find r oldRegs = Some {| objType := regT; objVal := regV |})
      (HSemAction: SemAction (cont regV) newRegs calls fret):
      SemAction (ReadReg r _ cont) newRegs calls fret
  | SemWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: Action type retK) newRegs calls anewRegs
      (HANewRegs: anewRegs = add r {| objVal := (evalExpr e) |} newRegs)
      (HSemAction: SemAction cont newRegs calls fret):
      SemAction (WriteReg r e cont) anewRegs calls fret
  | SemIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a: Action type k1)
      (a': Action type k1)
      (r1: type k1)
      k2 (cont: type k1 -> Action type k2)
      newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HAction: SemAction a newRegs1 calls1 r1)
      (HSemAction: SemAction (cont r1) newRegs2 calls2 r2)
      unewRegs ucalls
      (HUNewRegs: unewRegs = union newRegs1 newRegs2)
      (HUCalls: ucalls = union calls1 calls2):
      SemAction (IfElse p a a' cont) unewRegs ucalls r2
  | SemIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a: Action type k1)
      (a': Action type k1)
      (r1: type k1)
      k2 (cont: type k1 -> Action type k2)
      newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HFalse: evalExpr p = false)
      (HAction: SemAction a' newRegs1 calls1 r1)
      (HSemAction: SemAction (cont r1) newRegs2 calls2 r2)
      unewRegs ucalls
      (HUNewRegs: unewRegs = union newRegs1 newRegs2)
      (HUCalls: ucalls = union calls1 calls2):
      SemAction (IfElse p a a' cont) unewRegs ucalls r2
  | SemAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: Action type k2) newRegs2 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HSemAction: SemAction cont newRegs2 calls2 r2):
      SemAction (Assert_ p cont) newRegs2 calls2 r2
  | SemReturn
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e):
      SemAction (Return e) empty empty evale.

  Theorem inversionSemAction
          k a news calls retC
          (evalA: @SemAction k a news calls retC):
    match a with
      | MCall m s e c =>
        exists mret pcalls,
          SemAction (c mret) news pcalls retC /\
          calls = add m {| objVal := (evalExpr e, mret) |} pcalls
      | Let_ _ e cont =>
        SemAction (cont (evalExpr e)) news calls retC
      | ReadReg r k c =>
        exists rv,
          find r oldRegs = Some {| objType := k; objVal := rv |} /\
          SemAction (c rv) news calls retC
      | WriteReg r _ e a =>
        exists pnews,
          SemAction a pnews calls retC /\
          news = add r {| objVal := evalExpr e |} pnews
      | IfElse p _ aT aF c =>
        exists news1 calls1 news2 calls2 r1,
          match evalExpr p with
            | true =>
              SemAction aT news1 calls1 r1 /\
              SemAction (c r1) news2 calls2 retC /\
              news = union news1 news2 /\
              calls = union calls1 calls2
            | false =>
              SemAction aF news1 calls1 r1 /\
              SemAction (c r1) news2 calls2 retC /\
              news = union news1 news2 /\
              calls = union calls1 calls2
          end
      | Assert_ e c =>
        SemAction c news calls retC /\
        evalExpr e = true
      | Return e =>
        retC = evalExpr e /\
        news = empty /\
        calls = empty
    end.
  Proof.
    destruct evalA; eauto; repeat eexists; destruct (evalExpr p); eauto; try discriminate.
  Qed.

  Inductive SemMod: option string -> RegsT -> list (DefMethT type) -> CallsT -> CallsT -> Prop :=
  | SemEmpty news dm cm
             (HEmptyRegs: news = empty)
             (HEmptyDms: dm = empty)
             (HEmptyCms: cm = empty):
      SemMod None news nil dm cm
  | SemAddRule (ruleName: string)
               (ruleBody: Action type (Bit 0))
               (HInRule: In {| attrName := ruleName; attrType := ruleBody |} rules)
               news calls retV
               (HAction: SemAction ruleBody news calls retV)
               news2 meths dm2 cm2
               (HSemMod: SemMod None news2 meths dm2 cm2)
               (HNoDoubleWrites: Disj news news2)
               (HNoCallsBoth: Disj calls cm2)
               unews ucalls
               (HRegs: unews = union news news2)
               (HCalls: ucalls = union calls cm2):
      SemMod (Some ruleName) unews meths dm2 ucalls
  (* method `meth` was also called this clock cycle *)
  | SemAddMeth calls news (meth: DefMethT type) meths argV retV
               (HAction: SemAction ((objVal (attrType meth)) argV) news calls retV)
               news2 dm2 cm2
               (HSemMod: SemMod None news2 meths dm2 cm2)
               (HNoDoubleWrites: Disj news news2)
               (HNoCallsBoth: Disj calls cm2)
               unews ucalls udefs
               (HRegs: unews = union news news2)
               (HCalls: ucalls = union calls cm2)
               (HDefs: udefs = add (attrName meth) {| objVal := (argV, retV) |} dm2):
      SemMod None unews (meth :: meths) udefs ucalls
  (* method `meth` was not called in this clock cycle *)
  | SemSkipMeth news meth meths dm cm
                (HSemMod: SemMod None news meths dm cm):
      SemMod None news (meth :: meths) dm cm.

End Semantics.

Lemma SemMod_empty:
  forall rules or dms, SemMod rules or None empty dms empty empty.
Proof.
  induction dms; intros; [econstructor; auto|].
  eapply SemSkipMeth; eauto.
Qed.

Lemma SemMod_empty_inv:
  forall rules or nr dms cmMap,
    SemMod rules or None nr dms empty cmMap ->
    nr = empty /\ cmMap = empty.
Proof.
  induction dms; intros; [inv H; intuition|].
  inv H.
  - apply Equal_val with (k := attrName a) in HDefs.
    map_compute HDefs; discriminate.
  - apply IHdms; auto.
Qed.

Lemma SemMod_dmMap_InDomain:
  forall rules dms or rm nr dmMap cmMap,
    SemMod rules or rm nr dms dmMap cmMap ->
    InDomain dmMap (map (@attrName _) dms).
Proof.
  induction dms; intros.
  - simpl; inv H; [intuition|].
    inv HSemMod; intuition.
  - simpl; destruct rm.
    + inv H; inv HSemMod.
      * specialize (IHdms _ _ _ _ _ HSemMod0).
        unfold InDomain; intros.
        apply InMap_add in H; destruct H.
        { subst; left; reflexivity. }
        { right; specialize (IHdms _ H); assumption. }
      * specialize (IHdms _ _ _ _ _ HSemMod0).
        unfold InDomain; intros.
        right; specialize (IHdms _ H); assumption.
    + inv H.
      * specialize (IHdms _ _ _ _ _ HSemMod).
        unfold InDomain; intros.
        apply InMap_add in H; destruct H.
        { subst; left; reflexivity. }
        { right; specialize (IHdms _ H); assumption. }
      * specialize (IHdms _ _ _ _ _ HSemMod).
        unfold InDomain; intros.
        right; specialize (IHdms _ H); assumption.
Qed.      

Ltac cheap_firstorder :=
  repeat match goal with
         | [ H : ex _ |- _ ] => destruct H
         | [ H : _ /\ _ |- _ ] => destruct H
         end.

Ltac invertAction H := apply inversionSemAction in H; simpl in H; cheap_firstorder; try subst.
Ltac invertActionFirst :=
  match goal with
    | [H: SemAction _ _ _ _ _ |- _] => invertAction H
  end.
Ltac invertActionRep :=
  repeat
    match goal with
      | [H: SemAction _ _ _ _ _ |- _] => invertAction H
      | [H: if ?c
            then
              SemAction _ _ _ _ _ /\ _ /\ _ /\ _
            else
              SemAction _ _ _ _ _ /\ _ /\ _ /\ _ |- _] =>
        let ic := fresh "ic" in
        (remember c as ic; destruct ic; dest; subst)
    end.

Ltac invertSemMod H :=
  inv H;
  repeat match goal with
           | [H: Disj _ _ |- _] => clear H
         end.

Ltac invertSemModRep :=
  repeat
    match goal with
      | [H: SemMod _ _ _ _ _ _ _ |- _] => invertSemMod H
    end.

(* dm       : defined methods
   cm       : called methods
   ruleMeth : `None` if it is a method,
              `Some [rulename]` if it is a rule *)

Record RuleLabelT := { ruleMeth: option string;
                       dms: list string;
                       dmMap: CallsT;
                       cms: list string;
                       cmMap: CallsT }.

Hint Unfold ruleMeth dms dmMap cms cmMap.

Definition CombineRm (rm1 rm2 crm: option string) :=
  (rm1 = None \/ rm2 = None) /\
  crm = match rm1, rm2 with
          | Some rn1, None => Some rn1
          | None, Some rn2 => Some rn2
          | _, _ => None
        end.

Lemma combineRm_prop_1:
  forall r1 rm2 cr (Hcrm: CombineRm (Some r1) rm2 (Some cr)),
    r1 = cr.
Proof.
  intros; unfold CombineRm in Hcrm; dest.
  destruct rm2; inv H0; reflexivity.
Qed.

Lemma combineRm_prop_2:
  forall rm1 r2 cr (Hcrm: CombineRm rm1 (Some r2) (Some cr)),
    r2 = cr.
Proof.
  intros; unfold CombineRm in Hcrm; dest.
  destruct rm1; inv H0; reflexivity.
Qed.

Lemma combineRm_prop_3:
  forall rm1 crm (Hcrm: CombineRm rm1 None crm),
    rm1 = crm.
Proof.
  intros; unfold CombineRm in Hcrm; dest.
  destruct rm1; inv H0; reflexivity.
Qed.

Lemma combineRm_prop_4:
  forall rm2 crm (Hcrm: CombineRm None rm2 crm),
    rm2 = crm.
Proof.
  intros; unfold CombineRm in Hcrm; dest.
  destruct rm2; inv H0; reflexivity.
Qed.

Lemma combineRm_prop_5:
  forall rm1 rm2 (Hcrm: CombineRm rm1 rm2 None),
    rm1 = None /\ rm2 = None.
Proof.
  intros; unfold CombineRm in Hcrm; dest.
  destruct rm1, rm2; intuition; inv H1.
Qed.

Definition CallIffDef (l1 l2: RuleLabelT) :=
  (forall m, In m (cms l1) -> In m (dms l2) -> find m (cmMap l1) = find m (dmMap l2)) /\
  (forall m, In m (cms l2) -> In m (dms l1) -> find m (dmMap l1) = find m (cmMap l2)).

Definition FiltDm (l1 l2 l: RuleLabelT) :=
  dmMap l = disjUnion (complement (dmMap l1) (cms l2))
                      (complement (dmMap l2) (cms l1)) (listSub (dms l1) (cms l2)).

Definition FiltCm (l1 l2 l: RuleLabelT) :=
  cmMap l = disjUnion (complement (cmMap l1) (dms l2))
                      (complement (cmMap l2) (dms l1)) (listSub (cms l1) (dms l2)).

Definition ConcatLabel (l1 l2 l: RuleLabelT) :=
  CombineRm (ruleMeth l1) (ruleMeth l2) (ruleMeth l) /\
  CallIffDef l1 l2 /\ FiltDm l1 l2 l /\ FiltCm l1 l2 l.

Hint Unfold CombineRm CallIffDef FiltDm FiltCm ConcatLabel.

Ltac destConcatLabel :=
  repeat match goal with
           | [H: ConcatLabel _ _ _ |- _] =>
             let Hcrm := fresh "Hcrm" in
             let Hcid := fresh "Hcid" in
             let Hfd := fresh "Hfd" in
             let Hfc := fresh "Hfc" in
             destruct H as [Hcrm [Hcid [Hfd Hfc]]]; clear H; dest;
             unfold ruleMeth in Hcrm
         end.

(* rm = ruleMethod *)
Inductive LtsStep:
  Modules type -> option string -> RegsT -> RegsT -> CallsT -> CallsT -> Prop :=
| LtsStepMod regInits oRegs nRegs rules meths rm dmMap cmMap
             (HOldRegs: InDomain oRegs (map (@attrName _) regInits))
             (Hltsmod: SemMod rules oRegs rm nRegs meths dmMap cmMap):
    LtsStep (Mod regInits rules meths) rm oRegs nRegs dmMap cmMap
| LtsStepConcat m1 rm1 olds1 news1 dmMap1 cmMap1
                m2 rm2 olds2 news2 dmMap2 cmMap2
                (HOldRegs1: InDomain olds1 (map (@attrName _) (getRegInits m1)))
                (HOldRegs2: InDomain olds2 (map (@attrName _) (getRegInits m2)))
                (Hlts1: @LtsStep m1 rm1 olds1 news1 dmMap1 cmMap1)
                (Hlts2: @LtsStep m2 rm2 olds2 news2 dmMap2 cmMap2)
                crm colds cnews cdmMap ccmMap
                (Holds: colds = disjUnion olds1 olds2 (map (@attrName _) (getRegInits m1)))
                (Hnews: cnews = disjUnion news1 news2 (map (@attrName _) (getRegInits m1)))
                (HMerge: ConcatLabel
                           (Build_RuleLabelT rm1 (getDmsMod m1) dmMap1 (getCmsMod m1) cmMap1)
                           (Build_RuleLabelT rm2 (getDmsMod m2) dmMap2 (getCmsMod m2) cmMap2)
                           (Build_RuleLabelT crm (getDmsMod (ConcatMod m1 m2)) cdmMap
                                             (getCmsMod (ConcatMod m1 m2)) ccmMap)):
    LtsStep (ConcatMod m1 m2) crm colds cnews cdmMap ccmMap.

Lemma ltsStep_rule:
  forall m rm r or nr dmMap cmMap
         (Hstep: LtsStep m rm or nr dmMap cmMap)
         (Hrm: rm = Some r),
    In r (map (@attrName _) (getRules m)).
Proof.
  intros; subst.
  dependent induction Hstep.
  - invertSemMod Hltsmod.
    apply in_map_iff; simpl; eexists; split; [|eassumption]; reflexivity.
  - simpl; destConcatLabel.
    unfold CombineRm in Hcrm; dest.
    destruct rm1, rm2.
    + destruct H; discriminate.
    + inv H0; specialize (IHHstep1 s eq_refl).
      rewrite map_app; apply in_or_app; left; assumption.
    + inv H0; specialize (IHHstep2 s eq_refl).
      rewrite map_app; apply in_or_app; right; assumption.
    + inv H0.
Qed.

Ltac constr_concatMod :=
  repeat autounfold with ModuleDefs;
  match goal with
    | [ |- LtsStep (ConcatMod ?m1 ?m2) (Some ?r) ?or _ _ _ ] =>
      (let Hvoid := fresh "Hvoid" in
       assert (In r (map (@attrName _) (getRules m1))) as Hvoid by in_tac;
       clear Hvoid;
       eapply LtsStepConcat with
       (olds1 := restrict or (map (@attrName _) (getRegInits m1)))
         (olds2 := complement or (map (@attrName _) (getRegInits m1)))
         (rm1 := Some r) (rm2 := None); eauto)
        || (eapply LtsStepConcat with
            (olds1 := restrict or (map (@attrName _) (getRegInits m1)))
              (olds2 := complement or (map (@attrName _) (getRegInits m1)))
              (rm1 := None) (rm2 := Some r); eauto)
    | [ |- LtsStep (ConcatMod ?m1 ?m2) None _ _ _ _ ] =>
      eapply LtsStepConcat with
      (olds1 := restrict or (map (@attrName _) (getRegInits m1)))
        (olds2 := complement or (map (@attrName _) (getRegInits m1)))
        (rm1 := None) (rm2 := None); eauto
  end.

Hint Extern 1 (LtsStep (Mod _ _ _) _ _ _ _ _) => econstructor.
Hint Extern 1 (LtsStep (ConcatMod _ _) _ _ _ _ _) => constr_concatMod.
Hint Extern 1 (SemMod _ _ _ _ _ _ _) => econstructor.
(* Hint Extern 1 (SemAction _ _ _ _ _) => econstructor. *)
Hint Extern 1 (SemAction _ (Return _) _ _ _) =>
match goal with
  | [ |- SemAction _ _ _ _ ?ret ] =>
    match type of ret with
      | type (Bit 0) => eapply SemReturn with (evale := WO)
      | _ => econstructor
    end
end.

Definition initRegs (init: list RegInitT): RegsT := makeMap (fullType type) evalConstFullT init.
Hint Unfold initRegs.

(* m = module
   or = old registers
   nr = new registers *)
Inductive LtsStepClosure:
  Modules type ->
  RegsT -> list RuleLabelT ->
  Prop :=
| lcNil m inits
        (Hinits: inits = (initRegs (getRegInits m))):
    LtsStepClosure m inits nil
| lcLtsStep m rm or nr c cNew dNew or'
            (Hlc: LtsStepClosure m or c)
            (Hlts: LtsStep m rm or nr dNew cNew)
            (Hrs: or' = update or nr):
    LtsStepClosure m or' ((Build_RuleLabelT rm (getDmsMod m) dNew (getCmsMod m) cNew) :: c).

Inductive ConcatLabelSeq: list RuleLabelT -> list RuleLabelT -> list RuleLabelT -> Prop :=
| ConcatNil: ConcatLabelSeq nil nil nil
| ConcatJoin l1 l2 l:
    ConcatLabelSeq l1 l2 l ->
    forall a1 a2 a, ConcatLabel a1 a2 a -> ConcatLabelSeq (a1 :: l1) (a2 :: l2) (a :: l).

Definition RegsInDomain m :=
  forall rm or nr dm cm,
    LtsStep m rm or nr dm cm -> InDomain nr (map (@attrName _) (getRegInits m)).

Lemma concatMod_RegsInDomain:
  forall m1 m2 (Hin1: RegsInDomain m1) (Hin2: RegsInDomain m2),
    RegsInDomain (ConcatMod m1 m2).
Proof.
  unfold RegsInDomain; intros; inv H.
  specialize (Hin1 _ _ _ _ _ Hlts1).
  specialize (Hin2 _ _ _ _ _ Hlts2).
  clear -Hin1 Hin2.
  unfold getRegInits; rewrite map_app.
  unfold InDomain in *; intros.
  unfold InMap, find, disjUnion in H.
  destruct (in_dec string_dec k _).
  - specialize (Hin1 _ H); apply in_or_app; intuition.
  - specialize (Hin2 _ H); apply in_or_app; intuition.
Qed.

Section Domain.
  Variable m: Modules type.
  Variable newRegsDomain: RegsInDomain m.
  Theorem regsDomain r l
    (clos: LtsStepClosure m r l):
    InDomain r (map (@attrName _) (getRegInits m)).
  Proof.
    induction clos.
    - unfold InDomain, InMap, initRegs in *; intros.
      subst.
      clear -H.
      induction (getRegInits m); simpl in *.
      + unfold empty in *; intuition.
      + destruct a; destruct attrType; simpl in *.
        unfold add, unionL, find, string_eq in H.
        destruct (string_dec attrName k); intuition.
    - pose proof (@newRegsDomain _ _ _ _ _ Hlts).
      rewrite Hrs.
      apply InDomain_update; intuition.
  Qed.
End Domain.

Section WellFormed.
  Variable m1 m2: Modules type.

  Variable newRegsDomainM1: RegsInDomain m1.
  Variable newRegsDomainM2: RegsInDomain m2.

  Variable disjRegs:
    forall r, ~ (In r (map (@attrName _) (getRegInits (type := type) m1)) /\
                 In r (map (@attrName _) (getRegInits (type := type) m2))).
  Variable r: RegsT.
  Variable l: list RuleLabelT.

  Theorem ltsStepClosure_split:
    LtsStepClosure (ConcatMod m1 m2) r l ->
    exists r1 r2 l1 l2,
      LtsStepClosure m1 r1 l1 /\
      LtsStepClosure m2 r2 l2 /\
      disjUnion r1 r2 (map (@attrName _) (getRegInits m1)) = r /\
      ConcatLabelSeq l1 l2 l.
  Proof.
    intros clos.
    remember (ConcatMod m1 m2) as m.
    induction clos; rewrite Heqm in *; simpl in *.
    - exists (initRegs (getRegInits m1)).
             exists (initRegs (getRegInits m2)).
             unfold initRegs in *.
             rewrite (disjUnionProp (f1 := ConstFullT) (fullType type) evalConstFullT
                                    (getRegInits m1) (getRegInits m2)) in *.
             exists nil; exists nil.
             repeat (constructor || intuition).
    - destruct (IHclos eq_refl) as [r1 [r2 [l1 [l2 [step1 [step2 [regs labels]]]]]]];
      clear IHclos.
      inversion Hlts; subst.
      exists (update olds1 news1).
      exists (update olds2 news2).
      exists ((Build_RuleLabelT rm1 (getDmsMod m1) dmMap1 (getCmsMod m1) cmMap1) :: l1).
      exists ((Build_RuleLabelT rm2 (getDmsMod m2) dmMap2 (getCmsMod m2) cmMap2) :: l2).
      pose proof (regsDomain newRegsDomainM1 step1) as regs1.
      pose proof (regsDomain newRegsDomainM2 step2) as regs2.
      pose proof (disjUnion_div disjRegs regs1 regs2 HOldRegs1 HOldRegs2 Holds) as [H1 H2].
      subst.
      constructor.
      + apply (lcLtsStep (or' := update olds1 news1) step1 Hlts1 eq_refl).
      + constructor.
        * apply (lcLtsStep (or' := update olds2 news2) step2 Hlts2 eq_refl).
        * constructor.
          { pose proof newRegsDomainM1 Hlts1 as H1.
            pose proof newRegsDomainM2 Hlts2 as H2.
            apply disjUnion_update_comm.
          }
          { constructor; intuition. }
  Qed.
End WellFormed.

(** Tactics for dealing with semantics *)

Ltac invStep :=
  repeat
    match goal with
      | [Horig: LtsStep ?m None _ _ _ _ |- _] =>
        let Ha := fresh "Ha" in
        assert (Ha: exists lm rm, m = ConcatMod lm rm) by (repeat eexists);
          clear Ha; inv Horig; destConcatLabel;
          match goal with
            | [Hcrm: CombineRm _ _ None |- _] =>
              pose proof (combineRm_prop_5 Hcrm); dest; subst
          end
      | [Horig: LtsStep ?m (Some ?r) _ _ _ _ |- _] =>
        let Ha := fresh "Ha" in
        assert (Ha: exists lm rm, m = ConcatMod lm rm) by (repeat eexists);
          clear Ha; inv Horig; destConcatLabel;
          match goal with
            | [Hcrm: CombineRm _ _ _, H: LtsStep ?m ?rm _ _ _ _ |- _] =>
              let Hin := fresh "Hin" in
              assert (Hin: ~ In r (map (@attrName _) (getRules m))) by in_tac_ex;
                assert (rm = None) by
                  (destruct rm; [exfalso; elim Hin|reflexivity];
                   eapply ltsStep_rule; [eassumption|];
                   (rewrite (combineRm_prop_1 Hcrm) || rewrite (combineRm_prop_2 Hcrm));
                   reflexivity);
                clear Hin; subst;
                (rewrite (combineRm_prop_3 Hcrm) in * || rewrite (combineRm_prop_4 Hcrm) in *);
                clear Hcrm
          end
    end;
  repeat
    match goal with
      | [H: LtsStep ?m _ _ _ _ _ |- _] =>
        let Ha := fresh "Ha" in
        assert (Ha: exists m1 m2 m3, m = Mod m1 m2 m3) by (repeat eexists);
          clear Ha; inv H
    end.

Ltac destRule Hlts :=
  match type of Hlts with
    | (LtsStep _ ?rm _ _ _ _) =>
      inv Hlts;
        repeat match goal with
                 | [H: SemMod _ _ rm _ _ _ _ |- _] =>
                   destruct rm; [inv H; repeat match goal with
                                                 | [H: In _ _ |- _] => inv H
                                               end|]
                 | [H: {| attrName := _; attrType := _ |} =
                       {| attrName := _; attrType := _ |} |- _] => inv H
               end
  end.

Ltac destRuleRep :=
  repeat match goal with
           | [H: LtsStep _ _ _ _ _ _ |- _] => destRule H
         end.

Ltac combRule :=
  match goal with
    | [H: CombineRm (Some _) (Some _) _ |- _] =>
      unfold CombineRm in H; destruct H as [[H|H] _]; inversion H
    | [H: CombineRm None (Some _) _ |- _] =>
      unfold CombineRm in H; destruct H as [_]; subst
    | [H: CombineRm (Some _) None _ |- _] =>
      unfold CombineRm in H; destruct H as [_]; subst
    | [H: CombineRm None None _ |- _] =>
      unfold CombineRm in H; destruct H as [_]; subst
  end.

Ltac callIffDef_dest :=
  repeat
    match goal with
      | [H: CallIffDef _ _ |- _] => unfold CallIffDef in H; dest
    end;
  unfold dmMap, cmMap, dms, cms in *.

Ltac filt_dest :=
  repeat
    match goal with
      | [H: FiltDm _ _ _ |- _] =>
        unfold FiltDm in H;
          unfold dmMap, cmMap, dms, cms in H;
          subst
      | [H: FiltCm _ _ _ |- _] =>
        unfold FiltCm in H;
          unfold dmMap, cmMap, dms, cms in H;
          subst
    end.

Lemma opt_some_eq: forall {A} (v1 v2: A), Some v1 = Some v2 -> v1 = v2.
Proof. intros; inv H; reflexivity. Qed.

Lemma typed_type_eq:
  forall {A} (a1 a2: A) (B: A -> Type) (v1: B a1) (v2: B a2),
    {| objType := a1; objVal := v1 |} = {| objType := a2; objVal := v2 |} ->
    exists (Heq: a1 = a2), match Heq with eq_refl => v1 end = v2.
Proof. intros; inv H; exists eq_refl; reflexivity. Qed.

Lemma typed_eq:
  forall {A} (a: A) (B: A -> Type) (v1 v2: B a),
    {| objType := a; objVal := v1 |} = {| objType := a; objVal := v2 |} ->
    v1 = v2.
Proof. intros; inv H; apply Eqdep.EqdepTheory.inj_pair2 in H1; assumption. Qed.

Ltac basic_dest :=
  repeat
    match goal with
      | [H: Some _ = Some _ |- _] => try (apply opt_some_eq in H; subst)
      | [H: {| objType := _; objVal := _ |} = {| objType := _; objVal := _ |} |- _] =>
        try (apply typed_eq in H; subst)
      | [H: (_, _) = (_, _) |- _] => inv H; subst
      | [H: existT _ _ _ = existT _ _ _ |- _] =>
        try (apply Eqdep.EqdepTheory.inj_pair2 in H; subst)
      | [H: Some _ = None |- _] => inversion H
      | [H: None = Some _ |- _] => inversion H
      | [H: true = false |- _] => inversion H
      | [H: false = true |- _] => inversion H
    end.

Ltac pred_dest meth :=
  repeat
    match goal with
      | [H: forall m: string, In m nil -> _ |- _] =>
        clear H
    end;
  repeat
    match goal with
      | [H: forall m: string, In m _ -> _ |- _] =>
        let Hin := type of (H meth) in
        isNew Hin; let Hs := fresh "Hs" in pose proof (H meth) as Hs
    end;
  repeat
    match goal with
      | [H: In ?m ?l -> _ |- _] =>
        (let Hp := fresh "Hp" in
         assert (Hp: In m l)
           by (repeat autounfold; repeat autounfold with ModuleDefs; in_tac_ex);
         specialize (H Hp); clear Hp)
          || (clear H)
    end;
  repeat
    match goal with
      | [H: find _ _ = _ |- _] => repeat autounfold in H; repeat (map_compute H)
    end.

Ltac invariant_tac :=
  repeat
    match goal with
      | [H: find _ _ = Some _ |- _] => progress (map_simpl H)
      | [H1: ?lh = Some _, H2: ?lh = Some _ |- _] =>
        simpl in H1, H2; rewrite H1 in H2
      | [H1: ?lh = Some _, H2: Some _ = ?lh |- _] =>
        simpl in H1, H2; rewrite H1 in H2
      | [H1: ?lh = true, H2: ?lh = false |- _] =>
        simpl in H1, H2; rewrite H1 in H2
      | [H1: ?lh = true, H2: false = ?lh |- _] =>
        simpl in H1, H2; rewrite H1 in H2
      | [H1: ?lh = false, H2: true = ?lh |- _] =>
        simpl in H1, H2; rewrite H1 in H2
      | [H1: if weq ?w1 ?w2 then _ else _, H2: ?w1 = ?w3 |- _] =>
        rewrite H2 in H1; simpl in H1
      | [H: ?w1 = ?w3 |- context [if weq ?w1 ?w2 then _ else _] ] =>
        rewrite H; simpl
    end.

Ltac conn_tac meth :=
  callIffDef_dest; filt_dest; pred_dest meth; repeat (invariant_tac; basic_dest).
Ltac fconn_tac meth := exfalso; conn_tac meth.

Ltac regsInDomain_tac :=
  hnf; intros;
  repeat match goal with
         | [ H : LtsStep _ _ _ _ _ _ |- _ ] => inv H
         | [ H : SemMod _ _ _ _ _ _ _ |- _ ] => inv H
         end; in_tac_H; (deattr; simpl in *; repeat invertActionRep; inDomain_tac).


(** * Notation corner! *)

(* Notations: action *)

Coercion attrName : Attribute >-> string.

Notation "'Call' meth ( arg ) ; cont " :=
  (MCall (type := type) (attrName meth) (attrType meth) arg (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_scope.
Notation "'Call' name <- meth ( arg ) ; cont " :=
  (MCall (type := type) (attrName meth) (attrType meth) arg (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_scope.
Notation "'Call' meth () ; cont " :=
  (MCall (type := type) (attrName meth) (attrType meth) (Const _ Default) (fun _ => cont))
    (at level 12, right associativity, meth at level 0) : kami_scope.
Notation "'Call' name <- meth () ; cont " :=
  (MCall (type := type) (attrName meth) (attrType meth) (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_scope.
Notation "'Let' name <- expr ; cont " :=
  (Let_ (type := type) expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'Let' name : t <- expr ; cont " :=
  (Let_ (type := type) (lretT' := t) expr (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'Read' name <- reg ; cont" :=
  (ReadReg (type := type) reg _ (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'Read' name : kind <- reg ; cont " :=
  (ReadReg (type := type) reg (SyntaxKind kind) (fun name => cont))
    (at level 12, right associativity, name at level 0) : kami_scope.
Notation "'Write' reg <- expr ; cont " :=
  (WriteReg (type := type) reg expr cont)
    (at level 12, right associativity, reg at level 0) : kami_scope.
Notation "'Write' reg <- expr : kind ; cont " :=
  (@WriteReg type _ reg (SyntaxKind kind) expr cont)
    (at level 12, right associativity, reg at level 0) : kami_scope.
Notation "'If' cexpr 'then' tact 'else' fact 'as' name ; cont " :=
  (IfElse cexpr tact fact (fun name => cont))
    (at level 13, right associativity, name at level 0, cexpr at level 0, tact at next level, fact at next level) : kami_scope.
Notation "'Assert' expr ; cont " :=
  (Assert_ expr cont)
    (at level 12, right associativity) : kami_scope.
Notation "'Ret' expr" :=
  (Return expr) (at level 12) : kami_scope.
Notation Retv := (Return (Const _ (k := Bit 0) Default)).

(* * Modules *)

Inductive InModule :=
| NilInModule
| RegisterInModule (_ : RegInitT)
| RuleInModule (_ : Attribute (Action type (Bit 0)))
| MethodInModule (_ : DefMethT type)
| ConcatInModule (_ _ : InModule)
| NumberedInModule (f : nat -> InModule) (n : nat).

Section numbered.
  Variable makeModule' : InModule
                         -> list RegInitT
                            * list (Attribute (Action type (Bit 0)))
                            * list (DefMethT type).

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

Notation SyntaxType k := (fullType type (SyntaxKind k)).

Notation DefaultFull := (makeConst Default).

Notation "'Register' name : type <- init" :=
  (RegisterInModule (Build_Attribute name (Build_Typed ConstFullT (SyntaxKind type) (makeConst init))))
  (at level 0, name at level 0, type at level 0, init at level 0) : kami_method_scope.

Notation "'Method' name () : retT := c" :=
  (MethodInModule (Build_Attribute name (Build_Typed (fun a : SignatureT => type (arg a) -> Action type (ret a)) {| arg := Void; ret := retT |}
     (fun _ : type Void => c%kami : Action type retT))))
  (at level 0, name at level 0) : kami_method_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (MethodInModule (Build_Attribute name (Build_Typed (fun a : SignatureT => type (arg a) -> Action type (ret a)) {| arg := dom; ret := retT |}
     (fun param : type dom => c%kami : Action type retT))))
  (at level 0, name at level 0, param at level 0) : kami_method_scope.

Notation "'Rule' name := c" :=
  (RuleInModule (Build_Attribute name (c%kami : Action type Void)))
  (at level 0, name at level 0) : kami_method_scope.

Delimit Scope kami_method_scope with method.

Notation "'Repeat' count 'as' n { m1 'with' .. 'with' mN }" :=
  (NumberedInModule (fun n => ConcatInModule m1%method .. (ConcatInModule mN%method NilInModule) ..) count)
  (at level 0, count at level 0, n at level 0) : kami_method_scope.

Notation "'MODULE' { m1 'with' .. 'with' mN }" := (makeModule (ConcatInModule m1%method .. (ConcatInModule mN%method NilInModule) ..)) (at level 0, only parsing).

Definition icons' (na : {a : Attribute Kind & Expr type (SyntaxKind (attrType a))})
           {attrs}
           (tl : ilist (fun a : Attribute Kind => Expr type (SyntaxKind (attrType a))) attrs)
  : ilist (fun a : Attribute Kind => Expr type (SyntaxKind (attrType a))) (projT1 na :: attrs) :=
  icons (projT1 na) (projT2 na) tl.

Notation "name ::= value" :=
  (existT (fun a : Attribute Kind => Expr type (SyntaxKind (attrType a)))
          (Build_Attribute name _) value) (at level 50) : init_scope.
Delimit Scope init_scope with init.

Notation "'STRUCT' { s1 ; .. ; sN }" :=
  (BuildStruct (icons' s1%init .. (icons' sN%init (inil _)) ..))
  : kami_scope.

Notation "e :: t" := (e : Expr type (SyntaxKind t)) : kami_scope.

Definition firstAction {T} (ls : list (Action type T)) : Action type T :=
  match ls with
  | a :: _ => a
  | _ => Return (Const _ Default)
  end.

Notation "'ACTION' { a1 'with' .. 'with' aN }" := (firstAction (cons a1%kami .. (cons aN%kami nil) ..))
  (at level 0, only parsing, a at level 200).

Global Opaque mkStruct.
