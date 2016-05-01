Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap Syntax.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(*
Fixpoint fullType (k : FullKind) : Type := match k with
  | SyntaxKind t => type t
  | NativeKind t => t
  end.
 *)

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
    | Concat n1 n2 => fun x y => (combine x y)
  end.

Definition evalBinBitBool n1 n2 (op: BinBitBoolOp n1 n2)
  : word n1 -> word n2 -> bool :=
  match op with
    | Lt n => fun a b => if @wlt_dec n a b then true else false
  end.

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

(* maps register names to the values which they currently hold *)
Definition RegsT := M.t (sigT (fullType type)).

(* a pair of the value sent to a method call and the value it returned *)
Definition SignT k := (type (arg k) * type (ret k))%type.

(* a list of simulatenous method call actions made during a single step *)
Definition MethsT := M.t (sigT SignT).

Section Semantics.
  Definition mkStruct attrs (ils : ilist (fun a => type (attrType a)) attrs)
  : type (Struct attrs) :=
    fun (i: BoundedIndex (namesOf (map (mapAttr type) attrs))) =>
      mapAttrEq1 type attrs i (ith_Bounded _ ils (getNewIdx1 type attrs i)).

  Lemma nativeTypeEq k: fullType type (SyntaxKind k) = fullType type (@NativeKind (type k) (getDefaultConstNative k)).
  Proof.
    reflexivity.
  Qed.

  Lemma nativeTypeEq' k: fullType type (@NativeKind (type k) (getDefaultConstNative k)) = type k.
  Proof.
    reflexivity.
  Qed.

  Fixpoint typeToConst k: type k -> ConstT k.
  refine (fun v =>
            match k return type k -> ConstT k with
              | Bool => fun v => ConstBool v
              | Bit n => fun v => ConstBit v
              | Vector k' n => fun v => _
              | Struct attrs => fun v => _
            end v).
  induction n.
  exact (ConstVector (Vec0 (@typeToConst _ (v0 WO)))).
  pose proof (IHn (fun w => v0 (WS false w))) as v1.
  pose proof (IHn (fun w => v0 (WS false w))) as v2.
  dependent destruction v1; dependent destruction v2.
  exact (ConstVector (VecNext v1 v2)).
  induction attrs.
  exact (ConstStruct (inil _)).
  specialize (IHattrs (fun i => v0 (addFirstBoundedIndex _ i))).
  apply ConstStruct.
  dependent destruction IHattrs.
  constructor.
  specialize (v0 {| indexb := IndexBound_head (attrName (mapAttr type a)) (map (@attrName _) (map (mapAttr type) attrs)) |}).
  exact (@typeToConst _ v0).
  exact i.
  Defined.

  Definition typeToExpr k
    (v: fullType type (@NativeKind (type k) (getDefaultConstNative k))) ty: 
    Expr ty (SyntaxKind k) := Const ty (@typeToConst _ v).
  
  Fixpoint evalExpr exprT (e: Expr type exprT): fullType type exprT :=
    match e in Expr _ exprT return fullType type exprT with
      | Var _ v => v
(*    
      | Native k e =>
        match nativeTypeEq k in _ = t return fullType type (SyntaxKind k) -> t with
          | eq_refl => fun e => e
        end (evalExpr e)
*)
      | Const _ v => evalConstT v
      | UniBool op e1 => (evalUniBool op) (evalExpr e1)
      | BinBool op e1 e2 => (evalBinBool op) (evalExpr e1) (evalExpr e2)
      | UniBit n1 n2 op e1 => (evalUniBit op) (evalExpr e1)
      | BinBit n1 n2 n3 op e1 e2 => (evalBinBit op) (evalExpr e1) (evalExpr e2)
      | BinBitBool n1 n2 op e1 e2 => (evalBinBitBool op) (evalExpr e1) (evalExpr e2)
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

  (* register values just before the current cycle *)
  Variable oldRegs: RegsT.
  Definition UpdatesT := RegsT.

  Inductive SemAction:
    forall k, ActionT type k -> UpdatesT -> MethsT -> type k -> Prop :=
  | SemMCall
      meth s (marg: Expr type (SyntaxKind (arg s)))
      (mret: type (ret s))
      retK (fret: type retK)
      (cont: type (ret s) -> ActionT type retK)
      newRegs (calls: MethsT) acalls
      (HAcalls: acalls = M.add meth (existT _ _ (evalExpr marg, mret)) calls)
      (HSemAction: SemAction (cont mret) newRegs calls fret):
      SemAction (MCall meth s marg cont) newRegs acalls fret
  | SemLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) newRegs calls
      (HSemAction: SemAction (cont (evalExpr e)) newRegs calls fret):
      SemAction (Let_ e cont) newRegs calls fret
  | SemReadReg
      (r: string) regT (regV: fullType type regT)
      retK (fret: type retK) (cont: fullType type regT -> ActionT type retK)
      newRegs calls
      (HRegVal: M.find r oldRegs = Some (existT _ regT regV))
      (HSemAction: SemAction (cont regV) newRegs calls fret):
      SemAction (ReadReg r _ cont) newRegs calls fret
  | SemWriteReg
      (r: string) k
      (e: Expr type k)
      retK (fret: type retK)
      (cont: ActionT type retK) newRegs calls anewRegs
      (HANewRegs: anewRegs = M.add r (existT _ _ (evalExpr e)) newRegs)
      (HSemAction: SemAction cont newRegs calls fret):
      SemAction (WriteReg r e cont) anewRegs calls fret
  | SemIfElseTrue
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HAction: SemAction a newRegs1 calls1 r1)
      (HSemAction: SemAction (cont r1) newRegs2 calls2 r2)
      unewRegs ucalls
      (HUNewRegs: unewRegs = M.union newRegs1 newRegs2)
      (HUCalls: ucalls = M.union calls1 calls2):
      SemAction (IfElse p a a' cont) unewRegs ucalls r2
  | SemIfElseFalse
      (p: Expr type (SyntaxKind Bool)) k1
      (a: ActionT type k1)
      (a': ActionT type k1)
      (r1: type k1)
      k2 (cont: type k1 -> ActionT type k2)
      newRegs1 newRegs2 calls1 calls2 (r2: type k2)
      (HFalse: evalExpr p = false)
      (HAction: SemAction a' newRegs1 calls1 r1)
      (HSemAction: SemAction (cont r1) newRegs2 calls2 r2)
      unewRegs ucalls
      (HUNewRegs: unewRegs = M.union newRegs1 newRegs2)
      (HUCalls: ucalls = M.union calls1 calls2):
      SemAction (IfElse p a a' cont) unewRegs ucalls r2
  | SemAssertTrue
      (p: Expr type (SyntaxKind Bool)) k2
      (cont: ActionT type k2) newRegs2 calls2 (r2: type k2)
      (HTrue: evalExpr p = true)
      (HSemAction: SemAction cont newRegs2 calls2 r2):
      SemAction (Assert_ p cont) newRegs2 calls2 r2
  | SemReturn
      k (e: Expr type (SyntaxKind k)) evale
      (HEvalE: evale = evalExpr e):
      SemAction (Return e) (M.empty _) (M.empty _) evale.

  Theorem inversionSemAction
          k a news calls retC
          (evalA: @SemAction k a news calls retC):
    match a with
    | MCall m s e c =>
      exists mret pcalls,
      SemAction (c mret) news pcalls retC /\
      calls = M.add m (existT _ _ (evalExpr e, mret)) pcalls
    | Let_ _ e cont =>
      SemAction (cont (evalExpr e)) news calls retC
    | ReadReg r k c =>
      exists rv,
      M.find r oldRegs = Some (existT _ k rv) /\
      SemAction (c rv) news calls retC
    | WriteReg r _ e a =>
      exists pnews,
      SemAction a pnews calls retC /\
      news = M.add r (existT _ _ (evalExpr e)) pnews
    | IfElse p _ aT aF c =>
      exists news1 calls1 news2 calls2 r1,
      match evalExpr p with
      | true =>
        SemAction aT news1 calls1 r1 /\
        SemAction (c r1) news2 calls2 retC /\
        news = M.union news1 news2 /\
        calls = M.union calls1 calls2
      | false =>
        SemAction aF news1 calls1 r1 /\
        SemAction (c r1) news2 calls2 retC /\
        news = M.union news1 news2 /\
        calls = M.union calls1 calls2
      end
    | Assert_ e c =>
      SemAction c news calls retC /\
      evalExpr e = true
    | Return e =>
      retC = evalExpr e /\
      news = M.empty _ /\
      calls = M.empty _
    end.
  Proof.
    destruct evalA; eauto; repeat eexists; destruct (evalExpr p); eauto; try discriminate.
  Qed.
End Semantics.

Ltac invertAction H := apply inversionSemAction in H; simpl in H; dest; try subst.
Ltac invertActionFirst :=
  match goal with
  | [H: SemAction _ _ _ _ _ |- _] => invertAction H
  end.
Ltac invertActionRep :=
  repeat
    match goal with
    | [H: (_ :: _)%struct = (_ :: _)%struct |- _] => inv H
    | [H: SemAction _ _ _ _ _ |- _] => invertAction H
    | [H: if ?c
          then
            SemAction _ _ _ _ _ /\ _ /\ _ /\ _
          else
            SemAction _ _ _ _ _ /\ _ /\ _ /\ _ |- _] =>
      let ic := fresh "ic" in
      (remember c as ic; destruct ic; dest; subst)
    end.

Section AppendAction.
  Lemma appendAction_SemAction:
    forall retK1 retK2 a1 a2 olds news1 news2 calls1 calls2
           (retV1: type retK1) (retV2: type retK2),
      SemAction olds a1 news1 calls1 retV1 ->
      SemAction olds (a2 retV1) news2 calls2 retV2 ->
      SemAction olds (appendAction a1 a2) (M.union news1 news2) (M.union calls1 calls2) retV2.
  Proof.
    induction a1; intros.

    - invertAction H0; specialize (H _ _ _ _ _ _ _ _ _ H0 H1);
        econstructor; eauto.
      apply M.union_add.
    - invertAction H0; econstructor; eauto. 
    - invertAction H0; econstructor; eauto.
    - invertAction H; econstructor; eauto.
      apply M.union_add.
    - invertAction H0.
      simpl; remember (evalExpr e) as cv; destruct cv; dest; subst.
      + eapply SemIfElseTrue.
        * eauto.
        * eassumption.
        * eapply H; eauto.
        * rewrite M.union_assoc; reflexivity.
        * rewrite M.union_assoc; reflexivity.
      + eapply SemIfElseFalse.
        * eauto.
        * eassumption.
        * eapply H; eauto.
        * rewrite M.union_assoc; reflexivity.
        * rewrite M.union_assoc; reflexivity.

    - invertAction H; specialize (IHa1 _ _ _ _ _ _ _ _ H H0);
        econstructor; eauto.
    - invertAction H; econstructor; eauto.
  Qed.

End AppendAction.

Global Opaque mkStruct.

