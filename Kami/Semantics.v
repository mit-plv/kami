Require Import Bool List String Lia.
Require Import Structures.Equalities Program.Equality Eqdep Eqdep_dec.
Require Import FunctionalExtensionality.
Require Import Lib.Word Lib.CommonTactics Lib.ilist Lib.FMap Lib.StringEq Lib.VectorFacts Lib.Struct.
Require Import Kami.Syntax.

Set Implicit Arguments.

Set Asymmetric Patterns.

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
    - abstract (intros; discriminate).
    - injection e; intros; subst; exact x.
    - injection e; intros; subst; exact x.
  Defined.

  Variable B: Type.
  Variable map: A -> B.
  Fixpoint mapVec n (vec: Vec A n): Vec B n :=
    match vec in Vec _ n return Vec B n with
      | Vec0 e => Vec0 (map e)
      | VecNext n' v1 v2 => VecNext (mapVec v1) (mapVec v2)
    end.
End VecFunc.

(* Some definitions in Word.v are just opposite, we rename them to use correctly. *)
Definition spl1 := split2. (* to return _most_ significant bits *)
Definition spl2 := split1. (* to return _least_ significant bits *)
Definition cmb := fun sz1 (w1: word sz1) sz2 (w2: word sz2) => combine w2 w1.

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

Definition fin_tl' n (x: Fin.t (S n)) :=
match x return match x with
               | Fin.F1 _ => unit
               | Fin.FS m y => Fin.t m
               end with
| Fin.F1 _ => tt
| Fin.FS _ y => y
end.

Definition fin_tl n (x: Fin.t (S n)) (pf: x <> Fin.F1): Fin.t n :=
  Fin.caseS (fun n' x' => x' <> Fin.F1 -> Fin.t n')
            (fun n' pf' => match pf' eq_refl with
                           end)
            (fun n' p _ => p) x pf.

Theorem shatter_fin n (a: Fin.t (S n)):
  a = Fin.F1 \/ (exists pf: a <> Fin.F1, a = Fin.FS (fin_tl pf)).
refine
  match a with
  | Fin.F1 _ => or_introl eq_refl
  | Fin.FS _ y => or_intror _
  end.
assert (pf: Fin.FS y <> Fin.F1) by (intros; discriminate).
exists pf; f_equal.
Qed.

Section FinFunc.
  Variable A: Type.

  (* a lemma for wordVecDec *)
  Definition finVecDec':
    forall n (f g: Fin.t n -> A), (forall x: Fin.t n, {f x = g x} + {f x <> g x}) ->
                                  {forall x, f x = g x} + {exists x, f x <> g x}.
  Proof.
    intro n.
    induction n; intros f g H.
    - left; intros.
      eapply Fin.case0; eauto.
    - assert (Hn: forall (x: Fin.t n),
                    {f (Fin.FS x) = g (Fin.FS x)} + {f (Fin.FS x) <> g (Fin.FS x)}) by
             (intros; specialize (H (Fin.FS x)); intuition).
      destruct (IHn _ _ Hn) as [ef | nf].
      + destruct (IHn _ _ Hn) as [et | nt].
        * { destruct (H Fin.F1).
            - left; intros x.
              pose proof (shatter_fin x).
              destruct H0; subst; auto.
              destruct H0.
              specialize (ef (fin_tl x0)).
              specialize (et (fin_tl x0)).
              rewrite H0.
              auto.
            - right.
              eexists; eauto.
          }
        * right; destruct_ex; eauto.
      + right; destruct_ex; eauto.
  Qed.

  Definition finVecDec:
    forall n (f g: Fin.t n -> A), (forall x: Fin.t n, {f x = g x} + {f x <> g x}) ->
                                  {f = g} + {f <> g}.
  Proof.
    intros.
    pose proof (finVecDec' _ _ H) as [lt | rt].
    left; apply functional_extensionality; intuition.
    right; unfold not; intros eq; rewrite eq in *.
    destruct rt; intuition.
  Qed.
End FinFunc.

Fixpoint isEq k: forall (e1: type k) (e2: type k),
                   {e1 = e2} + {e1 <> e2}.
Proof.
  refine (match k return forall (e1: type k) (e2: type k),
                           {e1 = e2} + {e1 <> e2} with
            | Bool => bool_dec
            | Bit n => fun e1 e2 => weq e1 e2
            | Vector n nt =>
              fun e1 e2 =>
                wordVecDec e1 e2 (fun x => isEq _ (e1 x) (e2 x))
            | Struct n ls =>
              (fix help n ls1: forall (vs1 vs2: forall i, Vector.nth (Vector.map (fun p => type (attrType p)) ls1) i),
                                 {vs1 = vs2} + {vs1 <> vs2} :=
                 match ls1 return forall (vs1 vs2: forall i, Vector.nth (Vector.map (fun p => type (attrType p)) ls1) i),
                                    {vs1 = vs2} + {vs1 <> vs2} with
                   | Vector.nil => fun _ _ => Yes
                   | Vector.cons att n atts' =>
                     fun vs1 vs2 =>
                       isEq _ (vs1 Fin.F1) (vs2 Fin.F1);;
                            @help _ atts' (fun i => vs1 (Fin.FS i)) (fun i => vs2 (Fin.FS i));;
                            Yes
                 end) n ls
            | Array n nt =>
              fun e1 e2 =>
                finVecDec e1 e2 (fun x => isEq _ (e1 x) (e2 x))
          end); clear isEq; try clear help.
  - abstract (extensionality x;
              apply Fin.case0; assumption).
  - abstract (extensionality x;
              generalize atts' vs1 vs2 e e0 ; clear;
              pattern n, x;
              apply Fin.caseS with (n := n); simpl; intros; auto;
              apply (f_equal (fun i => i p) e0)).
  - abstract (intro; subst; tauto).
  - abstract (intro; subst; tauto).
Defined.

Definition evalUniBool (op: UniBoolOp) : bool -> bool :=
  match op with
    | NegB => negb
  end.

Definition evalBinBool (op: BinBoolOp) : bool -> bool -> bool :=
  match op with
    | AndB => andb
    | OrB => orb
  end.

(* the head of a word, or false if the word has 0 bits *)
Definition whd' sz (w: word sz) :=
  match sz as s return word s -> bool with
    | 0 => fun _ => false
    | S n => fun w => whd w
  end w.

Definition evalZeroExtendTrunc n1 n2 (w: word n1): word n2.
  refine (match Compare_dec.lt_dec n1 n2 with
          | left _ => _
          | right _ => _
          end).
  - replace n2 with (n1 + (n2 - n1)) by abstract lia.
    exact (zext w _).
  - replace n1 with (n2 + (n1 - n2)) in w by abstract lia.
    exact (split1 _ _ w).
Defined.

Definition evalSignExtendTrunc n1 n2 (w: word n1): word n2.
  refine (match Compare_dec.lt_dec n1 n2 with
          | left _ => _
          | right _ => _
          end).
  - replace n2 with (n1 + (n2 - n1)) by abstract lia.
    exact (sext w _).
  - replace n1 with (n2 + (n1 - n2)) in w by abstract lia.
    exact (split1 _ _ w).
Defined.

Definition evalUniBit n1 n2 (op: UniBitOp n1 n2): word n1 -> word n2.
  destruct op.
  - exact (@wnot n).
  - exact (@wneg n).
  - exact (fun w => split2 n1 n2 (split1 (n1 + n2) n3 w)).
  - exact (fun w => split1 n1 n2 w).
  - exact (fun w => evalZeroExtendTrunc _ w).
  - exact (fun w => evalSignExtendTrunc _ w).
  - exact (fun w => split2 n1 n2 w).
Defined.

Definition evalBinBit n1 n2 n3 (op: BinBitOp n1 n2 n3)
  : word n1 -> word n2 -> word n3 :=
  match op with
    | Add n => @wplus n
    | Sub n => @wminus n
    | Mul n SignSS => @wmultZ n
    | Mul n SignSU => @wmultZsu n
    | Mul n SignUU => @wmult n
    | Div n true => @wdivZ n
    (* | Div n SignSU => @wdivZsu n *)
    | Div n false => @wdivN n
    | Rem n true => @wremZ n
    (* | Rem n SignSU => @wremZsu n *)
    | Rem n false => @wremN n
    | Band n => @wand n
    | Bor n => @wor n
    | Bxor n => @wxor n
    | Sll n m => (fun x y => wlshift x (wordToNat y))
    | Srl n m => (fun x y => wrshift x (wordToNat y))
    | Sra n m => (fun x y => wrshifta x (wordToNat y))
    | Concat n1 n2 => fun x y => (combine y x)
  end.

Definition evalBinBitBool n1 n2 (op: BinBitBoolOp n1 n2)
  : word n1 -> word n2 -> bool :=
  match op with
    | Lt n => fun a b => if @wlt_dec n a b then true else false
    | Slt n => fun a b => if @wslt_dec n a b then true else false
  end.

Fixpoint evalArray A n (vs: Vector.t A n): Fin.t n -> A :=
  match vs in (Vector.t _ n0) return (Fin.t n0 -> A) with
  | Vector.nil => fun i => Fin.case0 _ i
  | Vector.cons a n' vs' => fun i => match i in Fin.t n'' return Vector.t A (pred n'') -> A with
                                     | Fin.F1 _ => fun _ => a
                                     | Fin.FS n1 j => fun vs' => evalArray vs' j
                                     end vs'
  end.

Fixpoint evalConstT k (e: ConstT k): type k :=
  match e in ConstT k return type k with
    | ConstBool b => b
    | ConstBit n w => w
    | ConstVector k' n v => evalVec (mapVec (@evalConstT k') v)
    | ConstStruct n vs ils =>
      (fix help n (vs: Vector.t _ n) (ils: ilist (fun a => ConstT (attrType a)) vs): type (Struct vs) :=
         match vs in Vector.t _ k return ilist (fun a => ConstT (attrType a)) vs -> type (Struct vs) with
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
                       | Fin.F1 s5 => fun _ _ => @evalConstT _ b
                       | Fin.FS s5 f5 => fun vs5 f => f f5
                     end vs3 (@help _ _ ils3)
               end i1
         end ils) n vs ils
    | ConstArray k' n v => evalArray (Vector.map (@evalConstT k') v)
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

  Fixpoint natToFin n (i: nat): Fin.t (S n) :=
    match i with
    | 0 => Fin.F1
    | S i' => match n with
              | 0 => Fin.F1
              | S n' => Fin.FS (natToFin n' i')
              end
    end.
  
  Fixpoint evalExpr exprT (e: Expr type exprT): fullType type exprT :=
    match e in Expr _ exprT return fullType type exprT with
      | Var _ v => v
      | Const _ v => evalConstT v
      | UniBool op e1 => (evalUniBool op) (@evalExpr _ e1)
      | BinBool op e1 e2 => (evalBinBool op) (@evalExpr _ e1) (@evalExpr _ e2)
      | UniBit n1 n2 op e1 => (evalUniBit op) (@evalExpr _ e1)
      | BinBit n1 n2 n3 op e1 e2 => (evalBinBit op) (@evalExpr _ e1) (@evalExpr _ e2)
      | BinBitBool n1 n2 op e1 e2 => (evalBinBitBool op) (@evalExpr _ e1) (@evalExpr _ e2)
      | ITE _ p e1 e2 => if @evalExpr _ p
                         then @evalExpr _ e1
                         else @evalExpr _ e2
      | Eq _ e1 e2 => if isEq _ (@evalExpr _ e1) (@evalExpr _ e2)
                      then true
                      else false
      | ReadIndex _ _ i f => (@evalExpr _ f) (@evalExpr _ i)
      | ReadField n ls i e =>
        Vector_nth_map (@attrType _) type ls (@evalExpr _ e) i
      | BuildVector _ k vec => evalVec (mapVec (@evalExpr _) vec)
      | BuildStruct n attrs ils =>
        ilist_to_fun_m _ _ (fun sk => SyntaxKind (attrType sk)) evalExpr ils
      | UpdateVector _ _ fn i v =>
        fun w => if weq w (@evalExpr _ i) then @evalExpr _ v else (@evalExpr _ fn) w
      | ReadArrayIndex _ k sz idx vec =>
        (@evalExpr _ vec) (natToFin sz (wordToNat (@evalExpr _ idx)))
      | BuildArray i k vecVal =>
        evalArray (Vector.map (@evalExpr _) vecVal)
      | UpdateArray k sz _ arr idx val =>
        fun fini => if Fin.eq_dec fini (natToFin sz (wordToNat (@evalExpr _ idx)))
                    then @evalExpr _ val
                    else @evalExpr _ arr fini
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
      (HDisjCalls: M.find meth calls = None)
      (HAcalls: acalls = M.add meth (existT _ _ (evalExpr marg, mret)) calls)
      (HSemAction: SemAction (cont mret) newRegs calls fret):
      SemAction (MCall meth s marg cont) newRegs acalls fret
  | SemLet
      k (e: Expr type k) retK (fret: type retK)
      (cont: fullType type k -> ActionT type retK) newRegs calls
      (HSemAction: SemAction (cont (evalExpr e)) newRegs calls fret):
      SemAction (Let_ e cont) newRegs calls fret
  | SemReadNondet
      valueT (valueV: fullType type valueT)
      retK (fret: type retK) (cont: fullType type valueT -> ActionT type retK)
      newRegs calls
      (HSemAction: SemAction (cont valueV) newRegs calls fret):
      SemAction (ReadNondet _ cont) newRegs calls fret
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
      (HDisjRegs: M.find r newRegs = None)
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
      (HDisjRegs: M.Disj newRegs1 newRegs2)
      (HDisjCalls: M.Disj calls1 calls2)
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
      (HDisjRegs: M.Disj newRegs1 newRegs2)
      (HDisjCalls: M.Disj calls1 calls2)
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
  | SemDispl ls k2 cont newRegs2 calls2 (r2: type k2)
             (HSemAction: SemAction cont newRegs2 calls2 r2):
      SemAction (Displ ls cont) newRegs2 calls2 r2
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
      M.find m pcalls = None /\
      SemAction (c mret) news pcalls retC /\
      calls = M.add m (existT _ _ (evalExpr e, mret)) pcalls
    | Let_ _ e cont =>
      SemAction (cont (evalExpr e)) news calls retC
    | ReadNondet k c =>
      exists rv,
      SemAction (c rv) news calls retC
    | ReadReg r k c =>
      exists rv,
      M.find r oldRegs = Some (existT _ k rv) /\
      SemAction (c rv) news calls retC
    | WriteReg r _ e a =>
      exists pnews,
      M.find r pnews = None /\
      SemAction a pnews calls retC /\
      news = M.add r (existT _ _ (evalExpr e)) pnews
    | IfElse p _ aT aF c =>
      exists news1 calls1 news2 calls2 r1,
      M.Disj news1 news2 /\
      M.Disj calls1 calls2 /\  
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
    | Displ ls c =>
      SemAction c news calls retC
    | Return e =>
      retC = evalExpr e /\
      news = M.empty _ /\
      calls = M.empty _
    end.
  Proof.
    destruct evalA; eauto; repeat eexists; destruct (evalExpr p); eauto; try discriminate.
  Qed.
End Semantics.

Global Arguments type: simpl never.
Global Arguments ilist_to_fun_m: simpl never.

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
      M.Disj news1 news2 ->
      M.Disj calls1 calls2 ->
      SemAction olds a1 news1 calls1 retV1 ->
      SemAction olds (a2 retV1) news2 calls2 retV2 ->
      SemAction olds (appendAction a1 a2) (M.union news1 news2) (M.union calls1 calls2) retV2.
  Proof.
    induction a1; intros.

    - invertAction H2.
      dest_disj.
      rewrite M.union_add.
      simpl in *.
      specialize (@H _ _ _ _ _ _ _ _ _ H0 H1 H4 H3); simpl in *.
      constructor 1 with (mret := x) (calls := M.union x0 calls2); auto.
      apply M.F.P.F.not_find_in_iff.
      apply M.F.P.F.not_find_in_iff in H2.
      unfold not; intros.
      apply M.union_In in H6; intuition.
    - invertAction H2; econstructor; eauto. 
    - invertAction H2; econstructor; eauto.
    - invertAction H2; econstructor; eauto.
    - invertAction H1.
      dest_disj.
      rewrite M.union_add.
      simpl in *.
      specialize (@IHa1 _ _ _ _ _ _ _ _ H H0 H3 H2); simpl in *.
      constructor 5 with (newRegs := M.union x news2); auto.
      apply M.F.P.F.not_find_in_iff.
      apply M.F.P.F.not_find_in_iff in H1.
      unfold not; intros.
      apply M.union_In in H5; intuition.
    - invertAction H2.
      simpl; remember (evalExpr e) as cv; destruct cv; dest; subst; simpl in *.
      + repeat rewrite <- M.union_assoc.
        eapply SemIfElseTrue with (newRegs1 := x) (newRegs2 := M.union x1 news2)
                                                  (calls1 := x0)
                                                  (calls2 := M.union x2 calls2); eauto.
      + repeat rewrite <- M.union_assoc.
        eapply SemIfElseFalse with (newRegs1 := x) (newRegs2 := M.union x1 news2)
                                                   (calls1 := x0)
                                                   (calls2 := M.union x2 calls2); eauto.
    - invertAction H1.
      specialize (@IHa1 _ _ _ _ _ _ _ _ H H0 H1 H2);
        econstructor; eauto.
    - invertAction H1; econstructor; eauto.
    - invertAction H1; econstructor; eauto.
  Qed.

End AppendAction.

Inductive UnitLabel :=
| Rle: option string -> UnitLabel
| Meth: option (Attribute (sigT SignT)) -> UnitLabel.

Record LabelT := { annot: option (option string);
                   defs: MethsT;
                   calls: MethsT }.

Definition emptyRuleLabel: LabelT :=
  {| annot := Some None; defs := M.empty _; calls := M.empty _ |}.
Definition emptyMethLabel: LabelT :=
  {| annot := None; defs := M.empty _; calls := M.empty _ |}.

Section GivenModule.
  Variable m: Modules.

  Section GivenOldregs.
    Variable o: RegsT.

    Inductive Substep: UpdatesT -> UnitLabel -> MethsT -> Prop :=
    | EmptyRule:
        Substep (M.empty _) (Rle None) (M.empty _)
    | EmptyMeth:
        Substep (M.empty _) (Meth None) (M.empty _)
    | SingleRule k (a: Action Void)
                 (HInRules: List.In {| attrName := k; attrType := a |} (getRules m))
                 u cs (HAction: SemAction o (a type) u cs WO):
        Substep u (Rle (Some k)) cs
    | SingleMeth (f: DefMethT)
                 (HIn: In f (getDefsBodies m))
                 u cs argV retV
                 (HAction: SemAction o ((projT2 (attrType f)) type argV) u cs retV)
                 sig (Hsig: sig = {| attrName := attrName f;
                                     attrType := (existT _ _ (argV, retV)) |}):
        Substep u (Meth (Some sig)) cs.

    Record SubstepRec :=
      { upd: UpdatesT;
        unitAnnot: UnitLabel;
        cms: MethsT;
        substep: Substep upd unitAnnot cms }.

    Definition Substeps := list SubstepRec.

    Definition canCombine (s1 s2: SubstepRec) :=
      M.Disj (upd s1) (upd s2) /\
      (forall x y, unitAnnot s1 = Meth (Some x) ->
                   unitAnnot s2 = Meth (Some y) -> attrName x <> attrName y) /\
      (exists x, unitAnnot s1 = Meth x \/ unitAnnot s2 = Meth x) /\
      M.Disj (cms s1) (cms s2).

    Inductive substepsComb: Substeps -> Prop :=
    | NilSubsteps: substepsComb nil
    | AddSubstep (s: SubstepRec) (ss: Substeps):
        substepsComb ss -> (forall s', In s' ss -> canCombine s s') ->
        substepsComb (s :: ss).

    Fixpoint foldSSUpds (ss: Substeps) :=
      match ss with
        | x :: xs => M.union (foldSSUpds xs) (upd x)
        | nil => M.empty _
      end.

    Definition getLabel (a: UnitLabel) (cs: MethsT) :=
      {| annot :=
           match a with
             | Rle x => Some x
             | Meth _ => None
           end;
         defs :=
           match a with
             | Meth (Some {| attrName := n; attrType := t |}) =>
               M.add n t (M.empty _)
             | _ => M.empty _
           end;
         calls := cs |}.

    Definition getSLabel (s: SubstepRec) := getLabel (unitAnnot s) (cms s).

    Definition mergeLabel lnew lold :=
      match lnew, lold with
        | {| annot := a'; defs := d'; calls := c' |},
          {| annot := a; defs := d; calls := c |} =>
          {| annot := match a', a with
                        | None, x => x
                        | x, None => x
                        | x, y => x
                      end; defs := M.union d' d; calls := M.union c' c |}
      end.
    
    Definition addLabelLeft lold s := mergeLabel (getSLabel s) lold.

    Fixpoint foldSSLabel (ss: Substeps) :=
      match ss with
        | x :: xs => addLabelLeft (foldSSLabel xs) x
        | nil => {| annot := None; defs := M.empty _; calls := M.empty _ |}
      end.

    
    Theorem foldSSLabelDist: forall s1 s2,
        foldSSLabel (s1 ++ s2) = mergeLabel (foldSSLabel s1) (foldSSLabel s2).
    Proof.
      induction s1; intros; simpl.
      - destruct (foldSSLabel s2).
        repeat rewrite M.union_empty_L.
        reflexivity.
      - specialize (IHs1 s2).
        rewrite IHs1; clear.
        unfold addLabelLeft.
        destruct a, (foldSSLabel s1), (foldSSLabel s2); clear; simpl.
        destruct unitAnnot0, annot0, annot1; repeat rewrite M.union_empty_L;
          repeat rewrite M.union_assoc; try reflexivity.
    Qed.

    Lemma sigT_eq:
      forall {A} (a: A) (B: A -> Type) (v1 v2: B a),
        existT _ a v1 = existT _ a v2 ->
        v1 = v2.
    Proof. intros; inv H; apply Eqdep.EqdepTheory.inj_pair2 in H1; assumption. Qed.

    Theorem signIsEq :
      forall (l1 l2 : sigT SignT), {l1 = l2} + {l1 <> l2}.
    Proof.
      intros. destruct l1, l2.
      destruct (SignatureT_dec x x0).
      - induction e. destruct x, s, s0.
        destruct (isEq arg t t1). induction e.
        destruct (isEq ret t0 t2). induction e. left. reflexivity.
        right. unfold not. intros. apply sigT_eq in H.
        inversion H. apply n in H1. assumption.
        right. unfold not. intros. apply sigT_eq in H.
        inversion H. apply n in H1. assumption.
      - right. unfold not. intros. inversion H. apply n in H1.
        assumption.
    Qed.

    Definition hide (l: LabelT) :=
      Build_LabelT (annot l) (M.subtractKV signIsEq (defs l) (calls l))
                   (M.subtractKV signIsEq (calls l) (defs l)).

    Definition wellHidden (l: LabelT) := M.KeysDisj (defs l) (getCalls m) /\
                                         M.KeysDisj (calls l) (getDefs m).

    Inductive Step: UpdatesT -> LabelT -> Prop :=
      StepIntro ss (HSubsteps: substepsComb ss)
                (HWellHidden: wellHidden (hide (foldSSLabel ss))) :
        Step (foldSSUpds ss) (hide (foldSSLabel ss)).

    (* Another step semantics based on inductive definitions for Substeps *)
    Definition CanCombineUUL u (l: LabelT) (su: UpdatesT) scs sul :=
      M.Disj su u /\
      M.Disj scs (calls l) /\
      match annot l, sul with
        | Some _, Rle _ => False
        | _, Meth (Some a) => ~ M.In (attrName a) (defs l)
        | _, _ => True
      end.

    Definition CanCombineLabel (l1 l2: LabelT) :=
      M.Disj (defs l1) (defs l2) /\
      M.Disj (calls l1) (calls l2) /\
      match annot l1, annot l2 with
      | Some _, Some _ => False
      | _, _ => True
      end.

    Definition CanCombineUL (u1 u2: UpdatesT) (l1 l2: LabelT) :=
      M.Disj u1 u2 /\ CanCombineLabel l1 l2.

    Inductive SubstepsInd: UpdatesT -> LabelT -> Prop :=
    | SubstepsNil: SubstepsInd (M.empty _)
                               {| annot:= None; defs:= M.empty _; calls:= M.empty _ |}
    | SubstepsCons:
        forall u l,
          SubstepsInd u l ->
          forall su scs sul,
            Substep su sul scs ->
            CanCombineUUL u l su scs sul ->
            forall uu ll,
              uu = M.union u su ->
              ll = mergeLabel (getLabel sul scs) l ->
              SubstepsInd uu ll.

    Inductive SubstepsIndAnnot: UpdatesT -> LabelT -> list SubstepRec -> Prop :=
    | SubstepsAnnotNil:
        SubstepsIndAnnot (M.empty _)
                         {| annot:= None; defs:= M.empty _; calls:= M.empty _ |} nil
    | SubstepsAnnotCons:
        forall u l ss,
          SubstepsIndAnnot u l ss ->
          forall su scs sul
                 (Hss: Substep su sul scs),
            CanCombineUUL u l su scs sul ->
            SubstepsIndAnnot (M.union u su)
                             (mergeLabel (getLabel sul scs) l)
                             ({| upd:= su; unitAnnot:= sul; cms:= scs; substep:= Hss |} :: ss).

    Lemma canCombine_consistent_1:
      forall su sul scs (Hss: Substep su sul scs) ss,
        (forall s', In s' ss -> canCombine {| substep := Hss |} s') ->
        CanCombineUUL (foldSSUpds ss) (foldSSLabel ss) su scs sul.
    Proof.
      induction ss; intros; simpl in *.
      - repeat (constructor; simpl in *; try apply M.Disj_empty_2).
        destruct sul; intuition; try destruct a0; try destruct o0; try intros X;
          try (apply M.F.P.F.empty_in_iff in X); intuition.
      - assert (ez: forall s', In s' ss -> canCombine {| substep := Hss |} s') by
            (intros s' ins'; apply H; intuition).
        specialize (IHss ez); clear ez.
        assert (ez: canCombine {| substep := Hss |} a) by
            (apply H; intuition).
        clear H.
        destruct IHss as [condss1 [condss2 condss3]].
        destruct ez as [conda1 [conda2 [conda3 conda4]]].
        simpl in *.
        constructor.
        + apply M.Disj_union; intuition.
        + constructor.
          * unfold addLabelLeft, mergeLabel in *;
            destruct (foldSSLabel ss); simpl in *.
            apply M.Disj_union; intuition.
          * unfold addLabelLeft, mergeLabel in *.
            destruct (foldSSLabel ss); simpl in *.
            destruct a; simpl in *.
            destruct annot0, unitAnnot0, sul; intuition.
            { destruct o2; intuition.
              destruct o1; intuition.
              destruct a0.
              rewrite M.union_add in H.
              rewrite M.union_empty_L in H.
              apply M.F.P.F.add_in_iff in H.
              destruct H; intuition.
              eapply conda2; eauto.
            }
            { destruct o1; intuition; 
              destruct conda3 as [x [y | z]]; discriminate.
            }
            { destruct o1; intuition.
              destruct o0; intuition.
              destruct a0.
              rewrite M.union_add in H.
              rewrite M.union_empty_L in H.
              apply M.F.P.F.add_in_iff in H.
              destruct H; intuition.
              eapply conda2; eauto.
            }
    Qed.

    Lemma unionCanCombineUUL u l su scs sul a:
      CanCombineUUL (M.union u (upd a))
                      (addLabelLeft l a) su scs sul ->
      CanCombineUUL u l su scs sul.
    Proof.
      intros [cond1 [cond2 cond3]].
      apply M.Disj_union_1 in cond1.
      unfold addLabelLeft, mergeLabel in cond2.
      destruct (getSLabel a).
      destruct l; simpl in *.
      apply M.Disj_union_2 in cond2.
      constructor; intuition; simpl in *.
      destruct (unitAnnot a), annot1, sul; intuition.
      destruct o2; intuition.
      destruct o0; intuition.
      destruct a1; intuition.
      rewrite M.union_add, M.union_empty_L, M.F.P.F.add_in_iff in cond3; intuition.
      destruct o1; intuition.
      destruct o0; intuition.
      destruct a1; intuition.
      rewrite M.union_add, M.union_empty_L, M.F.P.F.add_in_iff in cond3; intuition.
    Qed.

    Lemma canCombine_consistent_2:
      forall su sul scs (Hss: Substep su sul scs) ss,
        CanCombineUUL (foldSSUpds ss) (foldSSLabel ss) su scs sul ->
        (forall s', In s' ss -> canCombine {| substep := Hss |} s').
    Proof.
      induction ss; intros; simpl in *.
      - intuition.
      - destruct H0.
        + destruct H as [cond1 [cond2 cond3]].
          subst.
          unfold addLabelLeft, mergeLabel in *; case_eq (foldSSLabel ss); intros.
          rewrite H in *.
          case_eq (getSLabel s'); intros.
          simpl in *.
          apply M.Disj_union_2 in cond1.
          apply M.Disj_union_1 in cond2.
          constructor; intuition; simpl in *.
          * rewrite H1, H2, H3 in *; intuition.
            destruct annot0, y.
            rewrite M.union_add, M.union_empty_L, M.F.P.F.add_in_iff in cond3; intuition.
            rewrite M.union_add, M.union_empty_L, M.F.P.F.add_in_iff in cond3; intuition.
          * destruct annot0, (unitAnnot s'), sul; intuition;
            eexists; intuition.
        + apply (IHss (unionCanCombineUUL _ _ _ H)); intuition.
    Qed.

    Lemma canCombine_consistent:
      forall su sul scs (Hss: Substep su sul scs) ss,
        (forall s', In s' ss -> canCombine {| substep := Hss |} s') <->
        CanCombineUUL (foldSSUpds ss) (foldSSLabel ss) su scs sul.
    Proof.
      intros; constructor.
      apply canCombine_consistent_1; intuition.
      apply canCombine_consistent_2; intuition.
    Qed.

    Lemma substepsComb_substepsInd:
      forall ss,
        substepsComb ss ->
        SubstepsInd (foldSSUpds ss) (foldSSLabel ss).
    Proof.
      induction 1; simpl in *; [constructor|].

      destruct s as [su sul scs Hss]; simpl in *.
      econstructor; eauto.
      eapply canCombine_consistent; eauto.
    Qed.

    Lemma substepsInd_substepsComb:
      forall u l,
        SubstepsInd u l ->
        exists ss, SubstepsIndAnnot u l ss /\
                   substepsComb ss /\
                   u = foldSSUpds ss /\ l = foldSSLabel ss.
    Proof.
      induction 1.
      - eexists; repeat split; constructor.
      - destruct IHSubstepsInd as [ss [? [? [? ?]]]]; subst.
        exists ({| substep:= H0 |} :: ss); split.
        + constructor; auto.
        + repeat split.
          constructor; auto.
          apply canCombine_consistent; auto.
    Qed.

    Inductive StepInd: UpdatesT -> LabelT -> Prop :=
    | StepIndIntro: forall u l (HSubSteps: SubstepsInd u l)
                           (HWellHidden: wellHidden (hide l)),
                      StepInd u (hide l).

    Lemma step_consistent:
      forall u l, Step u l <-> StepInd u l.
    Proof.
      split; intros.
      - inv H; constructor; auto.
        apply substepsComb_substepsInd; auto.
      - inv H.
        apply substepsInd_substepsComb in HSubSteps.
        destruct HSubSteps as [ss [? [? [? ?]]]]; subst.
        econstructor; eauto.
    Qed.

  End GivenOldregs.

  Inductive Multistep: RegsT -> RegsT -> list LabelT -> Prop :=
  | NilMultistep o1 o2: o1 = o2 -> Multistep o1 o2 nil
  | Multi o a n (HMultistep: Multistep o n a)
          u l (HStep: Step n u l):
      Multistep o (M.union u n) (l :: a).

  Definition rawInitRegs (init: list RegInitT) :=
    map (fun r =>
           match r with
           | {| attrName := rn; attrType := ri |} =>
             {| attrName := rn;
                attrType := match ri with
                            | RegInitCustom ric => ric
                            | RegInitDefault rk => existT _ _ (getDefaultConstFull rk)
                            end
             |}
           end) init.

  Definition initRegs (init: list RegInitT): RegsT :=
    makeMap (fullType type) evalConstFullT (rawInitRegs init).
  #[local] Hint Unfold rawInitRegs initRegs.

  Lemma rawInitRegs_namesOf:
    forall r, namesOf r = namesOf (rawInitRegs r).
  Proof.
    induction r; simpl; intros; auto.
    destruct a; simpl; f_equal; auto.
  Qed.

  Lemma rawInitRegs_EquivList:
    forall r1 r2, EquivList r1 r2 -> EquivList (rawInitRegs r1) (rawInitRegs r2).
  Proof. intros; destruct H; split; apply SubList_map; auto. Qed.

  Lemma initRegs_eq':
    forall r1 r2,
      NoDup (namesOf r1) ->
      NoDup (namesOf r2) ->
      EquivList r1 r2 ->
      makeMap (fullType type) evalConstFullT r1 = 
      makeMap (fullType type) evalConstFullT r2.
  Proof.
    intros; M.ext y.
    do 2 (rewrite makeMap_find; auto).
    remember (getAttribute y r1) as yr1.
    remember (getAttribute y r2) as yr2.
    destruct yr1, yr2.
    - assert (a = a0).
      { pose proof (getAttribute_Some_name _ _ Heqyr1).
        apply getAttribute_Some_body in Heqyr1.
        pose proof (getAttribute_Some_name _ _ Heqyr2).
        apply getAttribute_Some_body in Heqyr2.
        inv H1; apply in_NoDup_attr with (attrs:= r2); auto.
      }
      subst; auto.
    - exfalso.
      apply getAttribute_Some in Heqyr1.
      apply getAttribute_None in Heqyr2.
      elim Heqyr2.
      inv H1; apply SubList_map with (f:= @attrName _) in H2; auto.
    - exfalso.
      apply getAttribute_None in Heqyr1.
      apply getAttribute_Some in Heqyr2.
      elim Heqyr1.
      inv H1; apply SubList_map with (f:= @attrName _) in H3; auto.
    - auto.
  Qed.
  
  Lemma initRegs_eq:
    forall r1 r2,
      NoDup (namesOf r1) ->
      NoDup (namesOf r2) ->
      EquivList r1 r2 ->
      initRegs r1 = initRegs r2.
  Proof.
    intros; apply initRegs_eq'.
    - rewrite <-rawInitRegs_namesOf; auto.
    - rewrite <-rawInitRegs_namesOf; auto.
    - apply rawInitRegs_EquivList; auto.
  Qed.

  Definition LabelSeqT := list LabelT.

  Inductive Behavior: RegsT -> LabelSeqT -> Prop :=
  | BehaviorIntro a n (HMultistepBeh: Multistep (initRegs (getRegInits m)) n a):
      Behavior n a.
End GivenModule.

Fixpoint CanCombineLabelSeq (ll1 ll2: list LabelT) :=
  match ll1, ll2 with
  | nil, nil => True
  | l1 :: ll1', l2 :: ll2' =>
    CanCombineLabel l1 l2 /\ CanCombineLabelSeq ll1' ll2'
  | _, _ => False (* forces the same length *)
  end.

Definition equivalentLabel p l1 l2 :=
  p (defs l1) = defs l2 /\
  p (calls l1) = calls l2 /\
  match annot l1, annot l2 with
    | Some _, Some _ => True
    | None, None => True
    | _, _ => False
  end.

Inductive equivalentLabelSeq p: LabelSeqT -> LabelSeqT -> Prop :=
| NilEquivalentSeq: equivalentLabelSeq p nil nil
| EquivalentSeq x xs y ys: equivalentLabel p x y -> equivalentLabelSeq p xs ys ->
                           equivalentLabelSeq p (x :: xs) (y :: ys).

Definition reachable o m := exists sigma, Behavior m o sigma.

Definition traceRefines p m1 m2 :=
  forall s1 sig1, Behavior m1 s1 sig1 ->
                  exists s2 sig2, Behavior m2 s2 sig2 /\
                             equivalentLabelSeq p sig1 sig2.

Section MapSet.
  Variable A: Type.
  Variable p: M.key -> A -> option A.

  Definition rmModify k v m := match p k v with
                                 | None => m
                                 | Some v' => M.add k v' m
                               end.
  Definition liftToMap1 s :=
    M.fold rmModify s (M.empty _).

End MapSet.

Definition idElementwise A (k: M.key) (v: A) := Some v.

Notation "ma '<<=[' p ']' mb" :=
  (traceRefines (liftToMap1 p) ma mb) (at level 100, format "ma  <<=[  p  ]  mb").
Notation "ma '<<==' mb" :=
  (ma <<=[@idElementwise _] mb) (at level 100, format "ma  <<==  mb").
Notation "ma '<<==>>' mb" :=
  (ma <<== mb /\ mb <<== ma)
    (at level 100, format "ma  <<==>>  mb").

