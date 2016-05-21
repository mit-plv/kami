Require Import Syntax String Lib.Struct List Inline InlineFacts_2 CommonTactics Program.Equality StringEq FunctionalExtensionality Bool Lib.Indexer.

Set Implicit Arguments.

Section AboutFold1.
  Variable A B: Type.
  Variable ls: list A.
  Variable b: B.
  Variable f: B -> A -> B.
  Variable a: A.
  Variable Hb: forall a', a <> a' -> f b a' = b.

  Variable HNotIn: ~ In a ls.

  Lemma fold_same: fold_left f ls b = b.
  Proof.
    generalize b Hb.
    clear b Hb.
    induction ls; simpl in *; intros.
    - intuition.
    - assert (s1: a0 <> a) by intuition.
      assert (s2: ~ In a l) by intuition.
      specialize (IHl s2 _ Hb).
      rewrite <- IHl at 2.
      f_equal.
      apply Hb; auto.
  Qed.
End AboutFold1.

Lemma badIndex:
  forall a c, index 0 indexSymbol (a ++ indexSymbol ++ c) <> None.
Proof.
  unfold not; intros.
  apply index_correct3 with (m := String.length a) in H; try omega; auto.
  rewrite substring_append_1 in H.
  assert (sth: prefix indexSymbol (indexSymbol ++ c) = true) by
      (clear; 
       induction c; intros; simpl in *; auto).
  apply prefix_correct in sth.
  intuition.
Qed.

Section AboutFold2.
  Variable A B: Type.
  Variable ls: list A.
  Variable b: B.
  Variable f: B -> A -> B.
  Variable a: A.
  Variable Hb: forall a', a <> a' -> f b a' = b.
  Variable Hfb: forall a', a <> a' -> f (f b a) a' = f b a.

  Variable HIn: In a ls.
  Variable HNoDups: NoDup ls.
  
  Lemma fold_single: fold_left f ls b = f b a.
  Proof.
    generalize b Hb Hfb HNoDups.
    clear b Hb Hfb HNoDups.
    induction ls; simpl in *; intros.
    - intuition.
    - inv HNoDups.
      inv HIn; subst.
      apply fold_same with (a := a); auto.
      rewrite Hb with (a' := a0) at 1; auto.
      unfold not; intros; subst; intuition.
  Qed.
End AboutFold2.

Section AboutFold3.
  Variable A B C: Type.
  Variable ls: list C.
  Variable f: B -> A -> B.
  Variable m: C -> A.
  
  Lemma fold_map: forall init,
                    fold_left f (map m ls) init = fold_left
                                                    (fun b c =>
                                                       f b (m c)) ls init.
  Proof.
    induction ls; simpl in *; intros.
    - reflexivity.
    - apply (IHl (f init (m a))).
  Qed.
End AboutFold3.

Section AboutFold4.
  Variable A B C: Type.
  Variable mab: A -> B.
  Variable mac: A -> C.
  Variable mcb: C -> B.
  

  Lemma map_in (ls: list A):
    (forall i, In i ls -> mab i = mcb (mac i)) ->
    map mab ls = map mcb (map mac ls).
  Proof.
    induction ls; simpl in *; intros.
    - reflexivity.
    - assert (mab a = mcb (mac a)) by (apply H; auto).
      assert (forall i, In i ls -> mab i = mcb (mac i)) by (intros; apply H; auto).
      pose proof (IHls H1).
      f_equal; auto.
  Qed.
End AboutFold4.

Record NameRec :=
  { nameVal: string;
    goodName: index 0 indexSymbol nameVal = None }.

Record NameRecIdx :=
  { isRep: bool;
    nameRec: NameRec }.

Definition convNameRec n := {| isRep := false;
                               nameRec := n |}.

Section Rep.
  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.

  Section Ty.
    Variable ty: Kind -> Type.

    Inductive GenActionT (lretT: Kind) : Type :=
    | GMCall (meth: NameRecIdx) s:
        Expr ty (SyntaxKind (arg s)) ->
        (ty (ret s) -> GenActionT lretT) ->
        GenActionT lretT
    | GLet_ lretT': Expr ty lretT' -> (fullType ty lretT' -> GenActionT lretT) ->
                    GenActionT lretT
    | GReadReg (r: NameRecIdx):
        forall k, (fullType ty k -> GenActionT lretT) -> GenActionT lretT
    | GWriteReg (r: NameRecIdx) k:
        Expr ty k -> GenActionT lretT -> GenActionT lretT
    | GIfElse: Expr ty (SyntaxKind Bool) -> forall k,
                                              GenActionT k ->
                                              GenActionT k ->
                                              (ty k -> GenActionT lretT) ->
                                              GenActionT lretT
    | GAssert_: Expr ty (SyntaxKind Bool) -> GenActionT lretT -> GenActionT lretT
    | GReturn: Expr ty (SyntaxKind lretT) -> GenActionT lretT.

    Fixpoint appendGenGenAction {retT1 retT2} (a1: GenActionT retT1)
           (a2: ty retT1 -> GenActionT retT2): GenActionT retT2 :=
    match a1 with
      | GMCall name sig ar cont => GMCall name sig ar (fun a => appendGenGenAction (cont a) a2)
      | GLet_ _ ar cont => GLet_ ar (fun a => appendGenGenAction (cont a) a2)
      | GReadReg reg k cont => GReadReg reg k (fun a => appendGenGenAction (cont a) a2)
      | GWriteReg reg _ e cont => GWriteReg reg e (appendGenGenAction cont a2)
      | GIfElse ce _ ta fa cont => GIfElse ce ta fa (fun a => appendGenGenAction (cont a) a2)
      | GAssert_ ae cont => GAssert_ ae (appendGenGenAction cont a2)
      | GReturn e => GLet_ e a2
    end.
    
    Section SpecificIdx.
      Variable i: A.
      Definition addIndexToStr s := append s (append indexSymbol (strA i)).
      Definition strFromName n := if isRep n
                                  then addIndexToStr (nameVal (nameRec n))
                                  else nameVal (nameRec n).
      
      Notation "^ n" := (strFromName n) (at level 0).
      
      Fixpoint getGenAction k (a: GenActionT k): ActionT ty k :=
        match a with
          | GMCall meth s e c => MCall ^meth s e (fun v => getGenAction (c v))
          | GLet_ k' e c => Let_ e (fun v => getGenAction (c v))
          | GReadReg r k c => ReadReg ^r k (fun v => getGenAction (c v))
          | GWriteReg r k e c => WriteReg ^r e (getGenAction c)
          | GIfElse e k aT aF c => IfElse e (getGenAction aT) (getGenAction aF)
                                          (fun v => getGenAction (c v))
          | GAssert_ e c => Assert_ e (getGenAction c)
          | GReturn e => Return e
        end.

      Lemma appendGenGenAction_matches k1 k2 (a1: GenActionT k1):
        forall a2, (getGenAction ((appendGenGenAction a1 a2): GenActionT k2)) =
                   (appendAction (getGenAction a1) (fun argv => getGenAction (a2 argv))).
      Proof.
        induction a1; simpl in *; intros; f_equal;
        repeat let x := fresh in extensionality x; apply H.
        apply IHa1.
        apply IHa1.
      Qed.
    End SpecificIdx.
  End Ty.

  Definition GenAction (retTy : Kind) := forall ty, GenActionT ty retTy.
  Definition GenMethodT (sig : SignatureT) := forall ty, ty (arg sig) -> GenActionT ty (ret sig).
  
  Definition getGenGenBody (n: NameRecIdx) dn (dm: sigT GenMethodT)
             (sig: SignatureT):
    option (sigT (fun x: sigT GenMethodT => projT1 x = sig)) :=
    if andb (string_eq (nameVal (nameRec n)) dn) (isRep n) then
      match SignatureT_dec (projT1 dm) sig with
        | left e => Some (existT _ dm e)
        | right _ => None
      end
    else None.

  Fixpoint inlineGenGenDm ty k (a: GenActionT ty k) dn (dm: sigT GenMethodT):
    GenActionT ty k :=
    match a with
      | GMCall name sig ar cont =>
        match getGenGenBody name dn dm sig with
          | Some (existT dm e) =>
            appendGenGenAction (GLet_ ar (eq_rect _ _ (projT2 dm) _ e ty))
                            (fun ak => inlineGenGenDm (cont ak) dn dm)
          | None => GMCall name sig ar (fun ak => inlineGenGenDm (cont ak) dn dm)
        end
      | GLet_ _ ar cont => GLet_ ar (fun a => inlineGenGenDm (cont a) dn dm)
      | GReadReg reg k cont => GReadReg reg k (fun a => inlineGenGenDm (cont a) dn dm)
      | GWriteReg reg _ e cont => GWriteReg reg e (inlineGenGenDm cont dn dm)
      | GIfElse ce _ ta fa cont =>
        GIfElse ce (inlineGenGenDm ta dn dm) (inlineGenGenDm fa dn dm)
                (fun a => inlineGenGenDm (cont a) dn dm)
      | GAssert_ ae cont => GAssert_ ae (inlineGenGenDm cont dn dm)
      | GReturn e => GReturn e
    end.

  Definition getActionFromGen (gr: GenAction Void) := fun i ty => getGenAction i (gr ty).

  Definition getMethFromGen (gf: sigT GenMethodT) :=
    fun i =>
      existT
        (fun sig => forall ty, ty (arg sig) -> ActionT ty (ret sig))
        (projT1 gf)
        (fun ty (argv: ty (arg (projT1 gf))) =>
           getGenAction i (projT2 gf ty argv): ActionT ty (ret (projT1 gf))).

  
  Lemma inlineGenGenDm_matches ty k (a: GenActionT ty k) dn (dm: sigT GenMethodT):
    forall i,
      getGenAction i (inlineGenGenDm a dn dm) =
      inlineDm (getGenAction i a) (addIndexToStr i dn :: getMethFromGen dm i)%struct.
  Proof.
    induction a; simpl in *; intros; auto; f_equal; try extensionality v; auto.
    unfold getGenGenBody, getBody, strFromName; simpl in *.
    destruct meth; destruct nameRec0; simpl in *; subst.
    unfold andb, eqb; subst; simpl in *; simpl.
    destruct isRep0; simpl in *; subst.
    - case_eq (string_eq nameVal0 dn); intros; subst; simpl in *.
      + apply eq_sym in H0; apply string_eq_dec_eq in H0; subst; simpl in *.
        rewrite string_eq_true.
        destruct (SignatureT_dec (projT1 dm) s); simpl in *.
        * f_equal; extensionality v; simpl in *; subst.
          unfold eq_rect; simpl in *.
          rewrite appendGenGenAction_matches; auto.
          f_equal; extensionality v'; auto.
        * f_equal; extensionality v; simpl in *; subst.
          auto.
      + case_eq (string_eq (addIndexToStr i nameVal0) (addIndexToStr i dn)); intros;
        [|f_equal; extensionality v; auto].
        apply eq_sym in H1; apply string_eq_dec_eq in H1; subst;
        unfold addIndexToStr in *; simpl in *.
        apply append_same in H1; subst.
        rewrite string_eq_true in H0; discriminate.
    - case_eq (string_eq nameVal0 dn); intros.
      + apply eq_sym in H0; apply string_eq_dec_eq in H0; subst; simpl in *.
        case_eq (string_eq dn (addIndexToStr i dn)); intros.
        * apply eq_sym in H0; apply string_eq_dec_eq in H0; simpl in *;
          unfold addIndexToStr in H0.
          rewrite <- append_empty with (s := dn) in H0 at 1.
          apply prepend_same in H0.
          discriminate.
        * f_equal; auto;
          extensionality v'; auto.
      + case_eq (string_eq nameVal0 (addIndexToStr i dn)); intros.
        * apply eq_sym in H1; apply string_eq_dec_eq in H1.
          unfold addIndexToStr in H1; subst.
          pose proof (badIndex _ _ goodName0); intuition.
        * simpl in *.
          f_equal; extensionality v; auto.
  Qed.
End Rep.

Section Sin.
  Variable A: Type.
  Variable strA: A -> string.
  Variable goodf: forall i j, strA i = strA j -> i = j.

  Section Ty.
    Variable ty: Kind -> Type.

    Inductive SinActionT (lretT: Kind) : Type :=
    | SMCall (meth: NameRec) s:
        Expr ty (SyntaxKind (arg s)) ->
        (ty (ret s) -> SinActionT lretT) ->
        SinActionT lretT
    | SLet_ lretT': Expr ty lretT' -> (fullType ty lretT' -> SinActionT lretT) ->
                    SinActionT lretT
    | SReadReg (r: NameRec):
        forall k, (fullType ty k -> SinActionT lretT) -> SinActionT lretT
    | SWriteReg (r: NameRec) k:
        Expr ty k -> SinActionT lretT -> SinActionT lretT
    | SIfElse: Expr ty (SyntaxKind Bool) -> forall k,
                                              SinActionT k ->
                                              SinActionT k ->
                                              (ty k -> SinActionT lretT) ->
                                              SinActionT lretT
    | SAssert_: Expr ty (SyntaxKind Bool) -> SinActionT lretT -> SinActionT lretT
    | SReturn: Expr ty (SyntaxKind lretT) -> SinActionT lretT.

    Fixpoint convSinToGen k (a: SinActionT k): GenActionT ty k :=
      match a with
        | SMCall name sig ar cont => GMCall (convNameRec name) sig ar
                                            (fun a => convSinToGen (cont a))
        | SLet_ _ ar cont => GLet_ ar (fun a => convSinToGen (cont a))
        | SReadReg reg k cont => GReadReg (convNameRec reg) k
                                          (fun a => convSinToGen (cont a))
        | SWriteReg reg _ e cont => GWriteReg (convNameRec reg) e (convSinToGen cont)
        | SIfElse ce _ ta fa cont => GIfElse ce (convSinToGen ta) (convSinToGen fa)
                                             (fun a => convSinToGen (cont a))
        | SAssert_ ae cont => GAssert_ ae (convSinToGen cont)
        | SReturn e => GReturn e
      end.
    
    Fixpoint appendSinGenAction {retT1 retT2} (a1: SinActionT retT1)
           (a2: ty retT1 -> GenActionT ty retT2): GenActionT ty retT2 :=
    match a1 with
      | SMCall name sig ar cont => GMCall (convNameRec name) sig ar
                                          (fun a => appendSinGenAction (cont a) a2)
      | SLet_ _ ar cont => GLet_ ar (fun a => appendSinGenAction (cont a) a2)
      | SReadReg reg k cont => GReadReg (convNameRec reg) k
                                        (fun a => appendSinGenAction (cont a) a2)
      | SWriteReg reg _ e cont => GWriteReg (convNameRec reg) e (appendSinGenAction cont a2)
      | SIfElse ce _ ta fa cont => GIfElse ce (convSinToGen ta) (convSinToGen fa)
                                           (fun a => appendSinGenAction (cont a) a2)
      | SAssert_ ae cont => GAssert_ ae (appendSinGenAction cont a2)
      | SReturn e => GLet_ e a2
    end.

    Fixpoint appendSinSinAction {retT1 retT2} (a1: SinActionT retT1)
             (a2: ty retT1 -> SinActionT retT2): SinActionT retT2 :=
    match a1 with
      | SMCall name sig ar cont => SMCall name sig ar
                                          (fun a => appendSinSinAction (cont a) a2)
      | SLet_ _ ar cont => SLet_ ar (fun a => appendSinSinAction (cont a) a2)
      | SReadReg reg k cont => SReadReg reg k
                                        (fun a => appendSinSinAction (cont a) a2)
      | SWriteReg reg _ e cont => SWriteReg reg e (appendSinSinAction cont a2)
      | SIfElse ce _ ta fa cont => SIfElse ce ta fa
                                           (fun a => appendSinSinAction (cont a) a2)
      | SAssert_ ae cont => SAssert_ ae (appendSinSinAction cont a2)
      | SReturn e => SLet_ e a2
    end.
    
    Fixpoint getSinAction k (a: SinActionT k): ActionT ty k :=
      match a with
        | SMCall meth s e c => MCall (nameVal meth) s e (fun v => getSinAction (c v))
        | SLet_ k' e c => Let_ e (fun v => getSinAction (c v))
        | SReadReg r k c => ReadReg (nameVal r) k (fun v => getSinAction (c v))
        | SWriteReg r k e c => WriteReg (nameVal r) e (getSinAction c)
        | SIfElse e k aT aF c => IfElse e (getSinAction aT) (getSinAction aF)
                                        (fun v => getSinAction (c v))
        | SAssert_ e c => Assert_ e (getSinAction c)
        | SReturn e => Return e
      end.

    Section SpecificIdx.
      Variable i: A.

      Lemma genSinSame k (a: SinActionT k):
        getGenAction strA i (convSinToGen a) = getSinAction a.
      Proof.
        induction a; simpl in *; f_equal; try extensionality v; auto.
      Qed.

      Lemma appendSinGenAction_matches k1 k2 (a1: SinActionT k1):
        forall (a2: ty k1 -> GenActionT ty k2),
          (getGenAction strA i ((appendSinGenAction a1 a2): GenActionT ty k2)) =
          (appendAction (getSinAction a1) (fun argv => getGenAction strA i (a2 argv))).
      Proof.
        induction a1; simpl in *; intros; f_equal;
        repeat let x := fresh in extensionality x; auto.
        apply IHa1.
        apply genSinSame.
        apply genSinSame.
        apply IHa1.
      Qed.
    End SpecificIdx.
  End Ty.

  Definition SinAction (retTy : Kind) := forall ty, SinActionT ty retTy.
  Definition SinMethodT (sig : SignatureT) := forall ty, ty (arg sig) -> SinActionT ty (ret sig).
  
  Definition getGenSinBody (n: NameRecIdx) dn (dm: sigT SinMethodT)
             (sig: SignatureT):
    option (sigT (fun x: sigT SinMethodT => projT1 x = sig)) :=
    if andb (string_eq (nameVal (nameRec n)) dn) (negb (isRep n)) then
      match SignatureT_dec (projT1 dm) sig with
        | left e => Some (existT _ dm e)
        | right _ => None
      end
    else None.

  Fixpoint inlineGenSinDm ty k (a: GenActionT ty k) dn (dm: sigT SinMethodT):
    GenActionT ty k :=
    match a with
      | GMCall name sig ar cont =>
        match getGenSinBody name dn dm sig with
          | Some (existT dm e) =>
            appendSinGenAction (SLet_ ar (eq_rect _ _ (projT2 dm) _ e ty))
                               (fun ak => inlineGenSinDm (cont ak) dn dm)
          | None => GMCall name sig ar (fun ak => inlineGenSinDm (cont ak) dn dm)
        end
      | GLet_ _ ar cont => GLet_ ar (fun a => inlineGenSinDm (cont a) dn dm)
      | GReadReg reg k cont => GReadReg reg k (fun a => inlineGenSinDm (cont a) dn dm)
      | GWriteReg reg _ e cont => GWriteReg reg e (inlineGenSinDm cont dn dm)
      | GIfElse ce _ ta fa cont =>
        GIfElse ce (inlineGenSinDm ta dn dm) (inlineGenSinDm fa dn dm)
                (fun a => inlineGenSinDm (cont a) dn dm)
      | GAssert_ ae cont => GAssert_ ae (inlineGenSinDm cont dn dm)
      | GReturn e => GReturn e
    end.

  Definition getActionFromSin (gr: SinAction Void) := fun ty => getSinAction (gr ty).

  Definition getMethFromSin (gf: sigT SinMethodT) :=
    existT
      (fun sig => forall ty, ty (arg sig) -> ActionT ty (ret sig))
      (projT1 gf)
      (fun ty (argv: ty (arg (projT1 gf))) =>
         getSinAction (projT2 gf ty argv): ActionT ty (ret (projT1 gf))).

  
  Lemma inlineGenSinDm_matches ty k (a: GenActionT ty k) dn
        (dnGood: index 0 indexSymbol dn = None) (dm: sigT SinMethodT):
    forall i,
      getGenAction strA i (inlineGenSinDm a dn dm) =
      inlineDm (getGenAction strA i a) (dn :: getMethFromSin dm)%struct.
  Proof.
    induction a; simpl in *; intros; auto; f_equal; try extensionality v; auto.
    unfold getGenSinBody, getBody, strFromName; simpl in *.
    destruct meth; destruct nameRec0; simpl in *; subst.
    unfold andb, eqb; subst; simpl in *; simpl.
    destruct isRep0; simpl in *; subst.
    - case_eq (string_eq nameVal0 dn); intros; subst; simpl in *.
      + apply eq_sym in H0; apply string_eq_dec_eq in H0; subst; simpl in *.
        case_eq (string_eq (addIndexToStr strA i dn) dn); intros; subst; simpl in *.
        * apply eq_sym in H0; apply string_eq_dec_eq in H0.
          unfold addIndexToStr in H0.
          assert (sth: String.length (dn ++ indexSymbol ++ strA i)%string = String.length dn)
            by (f_equal; assumption).
          repeat rewrite append_length in sth; simpl in sth.
          exfalso; omega.
        * unfold strFromName; simpl in *.
          f_equal; extensionality v; auto.
      + case_eq (string_eq (addIndexToStr strA i nameVal0) dn); intros;
        [|f_equal; extensionality v; auto].
        apply eq_sym in H1; apply string_eq_dec_eq in H1; subst; simpl in *.
        apply badIndex in dnGood.
        intuition.
    - case_eq (string_eq nameVal0 dn); intros.
      + apply eq_sym in H0; apply string_eq_dec_eq in H0; subst; simpl in *.
        { destruct (SignatureT_dec (projT1 dm) s); subst; simpl in *.
          - f_equal; extensionality v; auto.
            rewrite appendSinGenAction_matches.
            f_equal; extensionality v'; auto.
          - f_equal; extensionality v; auto.
        }
      + simpl in *; unfold strFromName; simpl in *.
        f_equal; extensionality v; auto.
  Qed.

  Definition getSinSinBody (n: NameRec) dn (dm: sigT SinMethodT)
             (sig: SignatureT):
    option (sigT (fun x: sigT SinMethodT => projT1 x = sig)) :=
    if string_eq (nameVal n) dn then
      match SignatureT_dec (projT1 dm) sig with
        | left e => Some (existT _ dm e)
        | right _ => None
      end
    else None.

  Fixpoint inlineSinSinDm ty k (a: SinActionT ty k) dn (dm: sigT SinMethodT):
    SinActionT ty k :=
    match a with
      | SMCall name sig ar cont =>
        match getSinSinBody name dn dm sig with
          | Some (existT dm e) =>
            appendSinSinAction (SLet_ ar (eq_rect _ _ (projT2 dm) _ e ty))
                               (fun ak => inlineSinSinDm (cont ak) dn dm)
          | None => SMCall name sig ar (fun ak => inlineSinSinDm (cont ak) dn dm)
        end
      | SLet_ _ ar cont => SLet_ ar (fun a => inlineSinSinDm (cont a) dn dm)
      | SReadReg reg k cont => SReadReg reg k (fun a => inlineSinSinDm (cont a) dn dm)
      | SWriteReg reg _ e cont => SWriteReg reg e (inlineSinSinDm cont dn dm)
      | SIfElse ce _ ta fa cont =>
        SIfElse ce (inlineSinSinDm ta dn dm) (inlineSinSinDm fa dn dm)
                (fun a => inlineSinSinDm (cont a) dn dm)
      | SAssert_ ae cont => SAssert_ ae (inlineSinSinDm cont dn dm)
      | SReturn e => SReturn e
    end.

  Lemma appendSinSinAction_matches ty k1 k2 (a1: SinActionT ty k1):
    forall (a2: ty k1 -> SinActionT ty k2),
      (getSinAction ((appendSinSinAction a1 a2): SinActionT ty k2)) =
      (appendAction (getSinAction a1) (fun argv => getSinAction (a2 argv))).
  Proof.
    induction a1; simpl in *; intros; f_equal;
    repeat let x := fresh in extensionality x; auto.
    apply IHa1.
    apply IHa1.
  Qed.
  
  Lemma inlineSinSinDm_matches ty k (a: SinActionT ty k) dn
        (dnGood: index 0 indexSymbol dn = None) (dm: sigT SinMethodT):
    getSinAction (inlineSinSinDm a dn dm) =
    inlineDm (getSinAction a) (dn :: getMethFromSin dm)%struct.
  Proof.
    induction a; simpl in *; intros; auto; f_equal; try extensionality v; auto.
    unfold getSinSinBody, getBody, strFromName; simpl in *.
    destruct meth; simpl in *; subst.
    case_eq (string_eq nameVal0 dn); intros; subst; simpl in *.
    + apply eq_sym in H0; apply string_eq_dec_eq in H0; subst; simpl in *.
      destruct (SignatureT_dec (projT1 dm) s); simpl in *.
      * f_equal; extensionality v; subst; simpl in *.
        rewrite appendSinSinAction_matches.
        f_equal; extensionality v'; auto.
      * f_equal; extensionality v; auto.
    + f_equal; extensionality v; auto.
  Qed.
End Sin.

Section MoreThm.
  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable goodStrFn2: forall si sj i j,
                         addIndexToStr strA i si = addIndexToStr strA j sj ->
                         si = sj /\ i = j.

  Section GetAttrList.
    Variable B: Type.
    Variable gen: A -> B.
    Variable s: string.
    Variable ls: list A.
    
    Definition getListFromRep :=
      map (fun i => (addIndexToStr strA i s :: gen i)%struct) ls.
  End GetAttrList.
  
  Definition repRule (gr: GenAction Void) :=
    getListFromRep (getActionFromGen strA gr).

  Definition repMeth (gf: sigT GenMethodT) :=
    getListFromRep (getMethFromGen strA gf).

  Section BadInline.
    Variable ty: Kind -> Type.
    Variable gf: sigT GenMethodT.
    Variable fname: string.
    Variable fnameGood: index 0 indexSymbol fname = None.

    Section GenBad.
      Variable i i': A.
      Variable HNeq: i <> i'.
      
      Lemma badGenInlineGenGen_matches k (a: GenActionT ty k):
        inlineDm (getGenAction strA i a)
                 (addIndexToStr strA i' fname :: getMethFromGen strA gf i')%struct =
        getGenAction strA i a.
      Proof.
        unfold getMethFromGen; simpl in *.
        induction a; simpl in *; subst; simpl in *; auto; intros;
        unfold strFromName in *; unfold getBody; simpl in *; f_equal; try extensionality v; auto.
        destruct meth; destruct nameRec0; simpl in *.
        destruct isRep0; simpl in *.
        - case_eq (string_eq (addIndexToStr strA i nameVal0) (addIndexToStr strA i' fname));
          intros; simpl in *.
          + apply eq_sym in H0; apply string_eq_dec_eq in H0.
            apply goodStrFn2 in H0; dest.
            intuition.
          + f_equal; extensionality v; auto.
        - case_eq (string_eq nameVal0 (addIndexToStr strA i' fname)); intros; simpl in *.
          + apply eq_sym in H0; apply string_eq_dec_eq in H0; subst.
            apply badIndex in goodName0; intuition auto.
          + f_equal; extensionality v; auto.
      Qed.

      Lemma badGenInlineGenGen2_matches k (a: GenActionT ty k):
        inlineDm (inlineDm (getGenAction strA i a)
                           (addIndexToStr strA i fname :: getMethFromGen strA gf i)%struct)
                 (addIndexToStr strA i' fname :: getMethFromGen strA gf i')%struct =
        inlineDm (getGenAction strA i a)
                 (addIndexToStr strA i fname :: getMethFromGen strA gf i)%struct.
      Proof.
        rewrite <- inlineGenGenDm_matches.
        apply badGenInlineGenGen_matches.
      Qed.
    End GenBad.
  End BadInline.
    
  Section FoldSimpleGenGen.
    Variable gf: sigT GenMethodT.
    Variable fname: string.
    Variable fnameGood: index 0 indexSymbol fname = None.

    Lemma foldInlineDmsGenGen_matches is:
      forall gr rname i,
        In i is ->
        NoDup is ->
        fold_left inlineDmToRule (repMeth gf fname is)
                  (addIndexToStr strA i rname :: getActionFromGen strA gr i)%struct =
        inlineDmToRule (addIndexToStr strA i rname :: getActionFromGen strA gr i)%struct
                       (addIndexToStr strA i fname :: getMethFromGen strA gf i)%struct.
    Proof.
      intros.
      unfold repMeth, getListFromRep.
      rewrite fold_map.
      match goal with
        | [|- fold_left ?f is ?init = ?q] =>
          remember f as sth;
          assert (sth2: f init i =
                        inlineDmToRule
                          init (addIndexToStr strA i fname :: getMethFromGen strA gf i)%struct)
            by reflexivity
      end.
      rewrite <- Heqsth in sth2.
      rewrite <- sth2.
      apply fold_single with (ls := is); auto; subst; clear sth2; intros; simpl in *.
      - unfold inlineDmToRule; simpl in *; f_equal; extensionality ty.
        apply badGenInlineGenGen_matches; auto.
      - unfold inlineDmToRule; simpl in *; f_equal; extensionality ty.
        apply badGenInlineGenGen2_matches; auto.
    Qed.
    
    Lemma foldInlineDmsGenGen_matchesGen is:
      forall gr rname i,
        In i is ->
        NoDup is ->
        (addIndexToStr strA i rname ::
                       getActionFromGen strA
                       (fun ty => inlineGenGenDm (gr ty) fname gf) i)%struct =
        fold_left inlineDmToRule (repMeth gf fname is)
                  (addIndexToStr strA i rname :: getActionFromGen strA gr i)%struct.
    Proof.
      intros.
      rewrite foldInlineDmsGenGen_matches; auto; unfold inlineDmToRule; simpl.
      f_equal; extensionality ty.
      apply inlineGenGenDm_matches.
    Qed.
  End FoldSimpleGenGen.

  Lemma mapFoldInlineDmsGenGen_matches is:
    forall gr rname gf fname,
      NoDup is ->
      map (fold_left inlineDmToRule (repMeth gf fname is))
          (repRule gr rname is) =
      map (fun i =>
             inlineDmToRule (addIndexToStr strA i rname :: getActionFromGen strA gr i)%struct
                            (addIndexToStr strA i fname :: getMethFromGen strA gf i)%struct) is.
  Proof.
    intros.
    unfold repRule.
    unfold getListFromRep.
    apply eq_sym.
    apply map_in.
    intros; apply eq_sym.
    apply foldInlineDmsGenGen_matches; auto.
  Qed.

  Lemma mapFoldInlineDmsGenGen_matchesGen is:
    forall gr rname gf fname,
      NoDup is ->
      map (fun i => addIndexToStr strA i rname ::
                                  getActionFromGen strA
                                  (fun ty => inlineGenGenDm (gr ty) fname gf) i)%struct is =
      map (fold_left inlineDmToRule (repMeth gf fname is))
          (repRule gr rname is).
  Proof.
    intros.
    unfold repRule.
    unfold getListFromRep.
    apply map_in.
    intros; apply foldInlineDmsGenGen_matchesGen; auto.
  Qed.

  Section FoldSimpleGenSin.
    Variable f: sigT SinMethodT.
    Variable fname: string.
    Variable fnameGood: index 0 indexSymbol fname = None.

    Lemma mapInlineDmsGenSin_matches is:
      forall gr rname,
        map (fun r => inlineDmToRule r (fname :: getMethFromSin f)%struct)
            (repRule gr rname is) =
        map (fun i => inlineDmToRule
                        (addIndexToStr strA i rname :: getActionFromGen strA gr i)%struct
                        (fname :: getMethFromSin f)%struct) is.
    Proof.
      intros.
      apply map_map.
    Qed.

    Lemma mapInlineDmsGenSin_matchesGen is:
      forall gr rname,
        map (fun i => addIndexToStr strA i rname ::
                                    getActionFromGen strA
                                    (fun ty => inlineGenSinDm (gr ty) fname f) i)%struct is =
        map (fun r => inlineDmToRule r (fname :: getMethFromSin f)%struct)
            (repRule gr rname is).
    Proof.
      intros.
      rewrite mapInlineDmsGenSin_matches.
      f_equal; auto.
      extensionality i.
      unfold inlineDmToRule, getActionFromGen; simpl in *; f_equal; auto.
      extensionality ty.
      rewrite inlineGenSinDm_matches; auto.
    Qed.
  End FoldSimpleGenSin.
End MoreThm.
