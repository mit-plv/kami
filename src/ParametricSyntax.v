Require Import Kami.Syntax String Lib.Word Lib.Struct Lib.FMap List.
Require Import Kami.Inline Kami.InlineFacts.
Require Import Lib.CommonTactics Program.Equality Lib.StringEq FunctionalExtensionality.
Require Import Bool Lib.Indexer Kami.Semantics Kami.SemFacts Kami.RefinementFacts Lib.StringAsList Ascii.
Require Import Lib.Concat Omega Lib.ListSupport.

Set Implicit Arguments.
Set Asymmetric Patterns.

Ltac dest_str :=
  match goal with
    | |- context[string_eq ?p ?q] =>
      case_eq (string_eq p q);
        [let x := fresh in intros x; apply eq_sym in x;
                           apply string_eq_dec_eq in x; subst|
         let x := fresh in intros x; apply eq_sym in x;
                           apply string_eq_dec_neq in x; subst]
    | H: context[string_eq ?p ?q] |- _ =>
      case_eq (string_eq p q);
        [let x := fresh in intros x; apply eq_sym in x;
                           apply string_eq_dec_eq in x; subst|
         let x := fresh in intros x; apply eq_sym in x;
                           apply string_eq_dec_neq in x; subst]
  end.


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

Section AboutFoldRight1.
  Variable A B: Type.
  Variable ls: list A.
  Variable b: B.
  Variable f: A -> B -> B.
  Variable a: A.
  Variable Hb: forall a', a <> a' -> f a' b = b.

  Variable HNotIn: ~ In a ls.

  Lemma fold_same': fold_right f b ls = b.
  Proof.
    generalize b Hb.
    clear b Hb.
    induction ls; simpl in *; intros.
    - intuition.
    - assert (s1: a0 <> a) by intuition.
      assert (s2: ~ In a l) by intuition.
      specialize (IHl s2 _ Hb).
      rewrite <- IHl at 2.
      rewrite IHl in *.
      apply Hb; auto.
  Qed.
End AboutFoldRight1.

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

Section AboutFoldRight2.
  Variable A B: Type.
  Variable ls: list A.
  Variable b: B.
  Variable f: A -> B -> B.
  Variable a: A.
  Variable Hb: forall a', a <> a' -> f a' b = b.
  Variable Hfb: forall a', a <> a' -> f a' (f a b) = f a b.

  Variable HIn: In a ls.
  Variable HNoDups: NoDup ls.
  
  Lemma fold_single': fold_right f b ls = f a b.
  Proof.
    generalize b Hb Hfb HNoDups.
    clear b Hb Hfb HNoDups.
    induction ls; simpl in *; intros.
    - intuition.
    - inv HNoDups.
      inv HIn; subst.
      f_equal; apply fold_same' with (a := a); auto.
      rewrite IHl; auto.
      apply Hfb; auto.
      unfold not; intros; subst; intuition.
  Qed.
End AboutFoldRight2.

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

Section AboutFoldRight3.
  Variable A B C: Type.
  Variable ls: list C.
  Variable f: A -> B -> B.
  Variable m: C -> A.
  
  Lemma fold_map': forall init,
                     fold_right f init (map m ls) = fold_right
                                                      (fun c b =>
                                                         f (m c) b) init ls.
  Proof.
    induction ls; simpl in *; intros.
    - reflexivity.
    - f_equal. apply IHl; auto.
  Qed.
End AboutFoldRight3.

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

Definition convNameRec rep n := {| isRep := rep;
                                   nameRec := n |}.

Section Rep.
  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable GenK: Kind.
  Variable getConstK: A -> ConstT GenK.
  
  Section Ty.
    Variable ty: Kind -> Type.

    Inductive GenActionT (lretT: Kind) : Type :=
    | GMCall (meth: NameRecIdx) s:
        Expr ty (SyntaxKind (arg s)) ->
        (ty (ret s) -> GenActionT lretT) ->
        GenActionT lretT
    | GIndex: (ty GenK -> GenActionT lretT) -> GenActionT lretT
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
      | GIndex cont => GIndex (fun a => appendGenGenAction (cont a) a2)
      | GLet_ _ ar cont => GLet_ ar (fun a => appendGenGenAction (cont a) a2)
      | GReadReg reg k cont => GReadReg reg k (fun a => appendGenGenAction (cont a) a2)
      | GWriteReg reg _ e cont => GWriteReg reg e (appendGenGenAction cont a2)
      | GIfElse ce _ ta fa cont => GIfElse ce ta fa (fun a => appendGenGenAction (cont a) a2)
      | GAssert_ ae cont => GAssert_ ae (appendGenGenAction cont a2)
      | GReturn e => GLet_ e a2
    end.
    
    Section SpecificIdx.
      Variable i: A.
      Definition strFromName n := if isRep n
                                  then addIndexToStr strA i (nameVal (nameRec n))
                                  else nameVal (nameRec n).
      
      Notation "^ n" := (strFromName n) (at level 0).
      
      Fixpoint getGenAction k (a: GenActionT k): ActionT ty k :=
        match a with
          | GMCall meth s e c => MCall ^meth s e (fun v => getGenAction (c v))
          | GIndex c => Let_ (Const ty (getConstK i)) (fun v => getGenAction (c v))
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

  Fixpoint getCallsGenA k (a: GenActionT typeUT k) :=
    match a with
      | GMCall meth s e c => meth :: getCallsGenA (c tt)
      | GIndex c => getCallsGenA (c tt)
      | GLet_ fk e c => getCallsGenA (c match fk as fk' return fullType typeUT fk' with
                                          | SyntaxKind _ => tt
                                          | NativeKind _ c' => c'
                                        end)
      | GReadReg _ fk c => getCallsGenA
                             (c match fk as fk' return fullType typeUT fk' with
                                  | SyntaxKind _ => tt
                                  | NativeKind _ c' => c'
                                end)
      | GWriteReg r k e c => getCallsGenA c
      | GIfElse e k aT aF c => getCallsGenA aT ++ getCallsGenA aF ++ getCallsGenA (c tt)
      | GAssert_ e c => getCallsGenA c
      | GReturn e => nil
    end.

  Fixpoint noCallDmSigGenA {retT} (a: GenActionT typeUT retT) (dmn: NameRecIdx)
           (dsig: SignatureT) :=
    match a with
    | GMCall name sig _ cont =>
      ((negb (string_eq (nameVal (nameRec name)) (nameVal (nameRec dmn)) &&
                        eqb (isRep name) (isRep dmn)))
       || (if SignatureT_dec sig dsig then false else true))
        && (noCallDmSigGenA (cont tt) dmn dsig)
    | GIndex c => noCallDmSigGenA (c tt) dmn dsig
    | GLet_ _ ar cont => noCallDmSigGenA (cont (getUT _)) dmn dsig
    | GReadReg reg k cont => noCallDmSigGenA (cont (getUT _)) dmn dsig
    | GWriteReg reg _ e cont => noCallDmSigGenA cont dmn dsig
    | GIfElse ce _ ta fa cont =>
      (noCallDmSigGenA ta dmn dsig) &&
                                    (noCallDmSigGenA fa dmn dsig) &&
                                    (noCallDmSigGenA (cont tt) dmn dsig)
    | GAssert_ ae cont => noCallDmSigGenA cont dmn dsig
    | GReturn e => true
    end.

  Definition getFullCallsGenA k (gr: GenActionT typeUT k) ls :=
    concat (map (fun i => map (strFromName i) (getCallsGenA gr)) ls).

  Lemma getCallsGenA_matches (i: A) k (a: GenActionT typeUT k):
    getCallsA (getGenAction i a) = map (strFromName i) (getCallsGenA a).
  Proof.
    induction a; simpl in *; auto.
    - f_equal; auto.
    - repeat rewrite map_app.
      rewrite IHa1, IHa2, H.
      reflexivity.
  Qed.

  Lemma noCallDmSigGenA_matches (i: A) dmn dsig k (a: GenActionT typeUT k):
    noCallDmSigA (getGenAction i a) (strFromName i dmn) dsig =
    noCallDmSigGenA a dmn dsig.
  Proof.
    induction a; simpl in *; auto; unfold strFromName.
    - rewrite H.
      repeat dest_str; simpl in *; auto.
      + rewrite H1 in *;
        destruct (isRep meth), (isRep dmn); simpl in *; auto;
        try (match goal with
               | H: addIndexToStr ?strA ?i ?l1 = ?l2 |- _ =>
                 assert (sth: String.length (addIndexToStr strA i l1) =
                              String.length l2) by (f_equal; auto)
               | H: ?l2 = addIndexToStr ?strA ?i ?l1 |- _ =>
                 assert (sth: String.length l2 =
                              String.length (addIndexToStr strA i l1)) by (f_equal; auto)
             end;
             unfold addIndexToStr in *;
               rewrite S_app_length in sth; simpl in *; omega).
      + destruct meth as [mRep [mNm mPf]];
        destruct dmn as [nRep [nNm nPf]]; simpl in *;
        pose proof (proj1 (index_not_in _ _) mPf) as mPf1;
        pose proof (proj1 (index_not_in _ _) nPf) as nPf1.
        destruct mRep, nRep; simpl in *; auto; unfold addIndexToStr in *; simpl in *;
        repeat match goal with
                 | H: (?l1 ++ ?l2)%string = (?l3 ++ ?l2)%string |- _ =>
                   apply S_app_inv_tail in H; intuition auto
                 | H: ?l3 = (?l1 ++ String ?a ?l2)%string |- _ => apply eq_sym in H
                 | H: (?l1 ++ String ?a ?l2)%string = ?l3 |- _ =>
                   assert (S_In a l3) by (rewrite <- H; apply S_in_or_app; simpl in *; right;
                                          intuition auto); intuition auto
                 | _ => idtac
               end; intuition auto.
      + destruct meth as [mRep [mNm mPf]];
        destruct dmn as [nRep [nNm nPf]]; simpl in *;
        pose proof (proj1 (index_not_in _ _) mPf) as mPf1;
        pose proof (proj1 (index_not_in _ _) nPf) as nPf1.
        destruct mRep, nRep; simpl in *; auto; unfold addIndexToStr in *; simpl in *; subst;
        intuition auto.
    - rewrite <- H, <- IHa1, <- IHa2; simpl in *; unfold strFromName;
      destruct (isRep dmn); simpl in *; reflexivity.
  Qed.

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
      | GIndex cont => GIndex (fun a => inlineGenGenDm (cont a) dn dm)
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
      inlineDm (getGenAction i a) (addIndexToStr strA i dn :: getMethFromGen dm i)%struct.
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
      + case_eq (string_eq (addIndexToStr strA i nameVal0) (addIndexToStr strA i dn)); intros;
        [|f_equal; extensionality v; auto].
        apply eq_sym in H1; apply string_eq_dec_eq in H1; subst;
        unfold addIndexToStr in *; simpl in *.
        apply append_same in H1; subst.
        rewrite string_eq_true in H0; discriminate.
    - case_eq (string_eq nameVal0 dn); intros.
      + apply eq_sym in H0; apply string_eq_dec_eq in H0; subst; simpl in *.
        case_eq (string_eq dn (addIndexToStr strA i dn)); intros.
        * apply eq_sym in H0; apply string_eq_dec_eq in H0; simpl in *;
          unfold addIndexToStr in H0.
          rewrite <- append_empty with (s := dn) in H0 at 1.
          apply prepend_same in H0.
          discriminate.
        * f_equal; auto;
          extensionality v'; auto.
      + case_eq (string_eq nameVal0 (addIndexToStr strA i dn)); intros.
        * apply eq_sym in H1; apply string_eq_dec_eq in H1.
          subst.
          pose proof (badIndex goodName0); intuition.
        * simpl in *.
          f_equal; extensionality v; auto.
  Qed.
End Rep.

Lemma noCallDmSigGenA_implies_true GenK k
      (a: GenActionT GenK typeUT k):
  forall dmn dsig,
    noCallDmSigGenA a dmn dsig = true ->
    forall dmn',
      isRep dmn' = isRep dmn ->
      nameVal (nameRec dmn') = nameVal (nameRec dmn) ->
      noCallDmSigGenA a dmn' dsig = true.
Proof.
  induction a; simpl in *; auto; intros.
  - dest_str; simpl in *; auto;
    apply andb_true_iff in H0; dest.
    + rewrite <- H2, H3 in H0.
      rewrite string_eq_true in H0.
      rewrite <- H1 in H0.
      apply andb_true_iff.
      constructor; auto.
      eapply H; eauto.
    + eapply H; eauto.
  - eapply H; eauto.
  - eapply H; eauto.
  - eapply H; eauto.
  - repeat (apply andb_true_iff in H0; dest);
    repeat (apply andb_true_iff; constructor).
    + eapply IHa1; eauto.
    + eapply IHa2; eauto.
    + eapply H; eauto.
Qed.

Lemma index_addIndexToStr_notNone A str i n:
  index 0 indexSymbol (@addIndexToStr A str i n) <> None.
Proof.
  unfold not, addIndexToStr; intros.
  apply index_not_in in H.
  assert (S_In "$"%char (n ++ indexSymbol ++ str i)) by
      (apply S_in_or_app; right; simpl; auto).
  intuition auto.
Qed.  

Lemma prefixNoMatch A A' strA strA' n1 n2 i i':
  @addIndexToStr A strA i (nameVal n1) = @addIndexToStr A' strA' i' (nameVal n2) ->
  nameVal n1 = nameVal n2 /\
  strA i = strA' i'.
Proof.
  intros.
  unfold addIndexToStr in H.
  destruct n1, n2; simpl in *.
  apply index_not_in in goodName0.
  apply index_not_in in goodName1.
  remember (strA i) as sth1.
  remember (strA' i') as sth2.
  clear i i' A A' strA strA' Heqsth1 Heqsth2.
  generalize goodName0 nameVal1 goodName1 sth1 sth2 H.
  clear goodName0 nameVal1 goodName1 sth1 sth2 H.
  induction nameVal0; destruct nameVal1; simpl in *; intuition auto.
  - inv H; auto.
  - inv H1; intuition auto.
  - inv H1; intuition auto.
  - inv H2; intuition auto.
  - inv H2; intuition auto.
  - inv H4.
    specialize (H1 _ H3 _ _ H7); dest.
    f_equal; auto.
  - inv H4.
    specialize (H1 _ H3 _ _ H7); dest.
    auto.
Qed.

Lemma noCallDmSigGenA_implies GenK k (a: GenActionT GenK typeUT k) A A' strA strA' getConstK:
  forall dmn dsig,
    noCallDmSigGenA a {| isRep := true; nameRec := dmn |} dsig = true ->
    forall (i: A) (i': A'),
    noCallDmSigA (getGenAction strA getConstK i a)
                 (addIndexToStr strA' i' (nameVal dmn)) dsig = true.
Proof.
  dependent induction a; simpl in *; auto; simpl in *; intros.
  - dest_str; simpl in *; unfold strFromName in *.
    + case_eq (isRep meth); intros X; rewrite X in *.
      * { dest_str; simpl in *; rewrite <- H1.
          - rewrite H2 in *; rewrite string_eq_true in *; simpl in *.
            apply andb_true_iff in H0; dest.
            rewrite <- noCallDmSigGenA_matches
            with
            (strA := strA)
              (getConstK := getConstK) (i := i) in H3.
            unfold strFromName in *; simpl in *.
            rewrite H0, H3; auto.
          - apply prefixNoMatch in H1; dest; auto.
        }
      * pose proof (goodName (nameRec meth)).
        rewrite H1 in H2.
        apply index_addIndexToStr_notNone in H2; intuition auto.
    + apply H.
      apply andb_true_iff in H0; dest; auto.
  - repeat (apply andb_true_iff in H0; dest).
    repeat (apply andb_true_iff; constructor).
    apply IHa1; auto.
    apply IHa2; auto.
    apply H; auto.
Qed.

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

    Fixpoint convSinToGen rep GenK k (a: SinActionT k): GenActionT GenK ty k :=
      match a with
        | SMCall name sig ar cont => GMCall (convNameRec rep name) sig ar
                                            (fun a => convSinToGen rep GenK (cont a))
        | SLet_ _ ar cont => GLet_ ar (fun a => convSinToGen rep GenK (cont a))
        | SReadReg reg k cont => GReadReg (convNameRec rep reg) k
                                          (fun a => convSinToGen rep GenK (cont a))
        | SWriteReg reg _ e cont => GWriteReg (convNameRec rep reg) e
                                              (convSinToGen rep GenK cont)
        | SIfElse ce _ ta fa cont => GIfElse ce (convSinToGen rep GenK ta)
                                             (convSinToGen rep GenK fa)
                                             (fun a => convSinToGen rep GenK (cont a))
        | SAssert_ ae cont => GAssert_ ae (convSinToGen rep GenK cont)
        | SReturn e => GReturn _ e
      end.
    
    Fixpoint appendSinGenAction GenK {retT1 retT2} (a1: SinActionT retT1)
           (a2: ty retT1 -> GenActionT GenK ty retT2): GenActionT GenK ty retT2 :=
    match a1 with
      | SMCall name sig ar cont => GMCall (convNameRec false name) sig ar
                                          (fun a => appendSinGenAction (cont a) a2)
      | SLet_ _ ar cont => GLet_ ar (fun a => appendSinGenAction (cont a) a2)
      | SReadReg reg k cont => GReadReg (convNameRec false reg) k
                                        (fun a => appendSinGenAction (cont a) a2)
      | SWriteReg reg _ e cont => GWriteReg (convNameRec false reg) e
                                            (appendSinGenAction cont a2)
      | SIfElse ce _ ta fa cont => GIfElse ce (convSinToGen false GenK ta)
                                           (convSinToGen false GenK fa)
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

      Lemma genSinSameF GenK (getConstK: A -> ConstT GenK) k (a: SinActionT k):
        getGenAction strA getConstK i (convSinToGen false GenK a) = getSinAction a.
      Proof.
        induction a; simpl in *; f_equal; try extensionality v; auto.
      Qed.

      Lemma appendSinGenAction_matches GenK (getConstK: A -> ConstT GenK)
            k1 k2 (a1: SinActionT k1):
        forall (a2: ty k1 -> GenActionT GenK ty k2),
          (getGenAction strA getConstK i ((appendSinGenAction a1 a2): GenActionT GenK ty k2)) =
          (appendAction (getSinAction a1) (fun argv => getGenAction strA getConstK i (a2 argv))).
      Proof.
        induction a1; simpl in *; intros; f_equal;
        repeat let x := fresh in extensionality x; auto.
        apply IHa1.
        apply genSinSameF.
        apply genSinSameF.
        apply IHa1.
      Qed.
    End SpecificIdx.
  End Ty.

  Definition SinAction (retTy : Kind) := forall ty, SinActionT ty retTy.
  Definition SinMethodT (sig : SignatureT) := forall ty, ty (arg sig) -> SinActionT ty (ret sig).

  Fixpoint getCallsSinA k (a: SinActionT typeUT k) :=
    match a with
      | SMCall meth s e c => meth :: getCallsSinA (c tt)
      | SLet_ fk e c => getCallsSinA (c match fk as fk' return fullType typeUT fk' with
                                          | SyntaxKind _ => tt
                                          | NativeKind _ c' => c'
                                        end)
      | SReadReg _ fk c => getCallsSinA
                             (c match fk as fk' return fullType typeUT fk' with
                                  | SyntaxKind _ => tt
                                  | NativeKind _ c' => c'
                                end)
      | SWriteReg r k e c => getCallsSinA c
      | SIfElse e k aT aF c => getCallsSinA aT ++ getCallsSinA aF ++ getCallsSinA (c tt)
      | SAssert_ e c => getCallsSinA c
      | SReturn e => nil
    end.

  Fixpoint noCallDmSigSinA {retT} (a: SinActionT typeUT retT) (dmn: NameRec)
           (dsig: SignatureT) :=
    match a with
    | SMCall name sig _ cont =>
      ((negb (string_eq (nameVal name) (nameVal dmn)))
       || (if SignatureT_dec sig dsig then false else true))
        && (noCallDmSigSinA (cont tt) dmn dsig)
    | SLet_ _ ar cont => noCallDmSigSinA (cont (getUT _)) dmn dsig
    | SReadReg reg k cont => noCallDmSigSinA (cont (getUT _)) dmn dsig
    | SWriteReg reg _ e cont => noCallDmSigSinA cont dmn dsig
    | SIfElse ce _ ta fa cont =>
      (noCallDmSigSinA ta dmn dsig) &&
                                    (noCallDmSigSinA fa dmn dsig) &&
                                    (noCallDmSigSinA (cont tt) dmn dsig)
    | SAssert_ ae cont => noCallDmSigSinA cont dmn dsig
    | SReturn e => true
    end.
  
  Lemma getCallsSinA_matches k (a: SinActionT typeUT k):
    getCallsA (getSinAction a) = map nameVal (getCallsSinA a).
  Proof.
    induction a; simpl in *; auto.
    - f_equal; auto.
    - repeat rewrite map_app.
      rewrite IHa1, IHa2, H.
      reflexivity.
  Qed.
  
  Lemma noCallDmSigSinA_matches (i: A) dmn dsig k (a: SinActionT typeUT k):
    noCallDmSigA (getSinAction a) (nameVal dmn) dsig =
    noCallDmSigSinA a dmn dsig.
  Proof.
    induction a; simpl in *; auto; unfold strFromName.
    - rewrite H.
      repeat dest_str; simpl in *; auto.
    - rewrite <- H, <- IHa1, <- IHa2; reflexivity.
  Qed.  

  Lemma noCallDmSigA_forSin_true:
    forall k (a: SinActionT typeUT k) n dmBody i,
      noCallDmSigA (getSinAction a) (addIndexToStr strA i n) dmBody = true.
  Proof.
    induction a; simpl in *; auto; intros.
    dest_str; simpl in *;
    destruct meth; simpl in *;
    unfold addIndexToStr, indexSymbol in *; subst.
    apply index_not_in in goodName0.
    assert (S_In "$"%char (n ++ "$" ++ strA i)) by
        (apply S_in_or_app; right; left; intuition auto); intuition auto.
    apply H; auto.
    rewrite H, IHa1, IHa2; auto.
  Qed.
    
  Definition getGenSinBody (n: NameRecIdx) dn (dm: sigT SinMethodT)
             (sig: SignatureT):
    option (sigT (fun x: sigT SinMethodT => projT1 x = sig)) :=
    if andb (string_eq (nameVal (nameRec n)) dn) (negb (isRep n)) then
      match SignatureT_dec (projT1 dm) sig with
        | left e => Some (existT _ dm e)
        | right _ => None
      end
    else None.

  Fixpoint inlineGenSinDm GenK ty k (a: GenActionT GenK ty k) dn (dm: sigT SinMethodT):
    GenActionT GenK ty k :=
    match a with
      | GMCall name sig ar cont =>
        match getGenSinBody name dn dm sig with
          | Some (existT dm e) =>
            appendSinGenAction (SLet_ ar (eq_rect _ _ (projT2 dm) _ e ty))
                               (fun ak => inlineGenSinDm (cont ak) dn dm)
          | None => GMCall name sig ar (fun ak => inlineGenSinDm (cont ak) dn dm)
        end
      | GIndex cont => GIndex (fun a => inlineGenSinDm (cont a) dn dm)
      | GLet_ _ ar cont => GLet_ ar (fun a => inlineGenSinDm (cont a) dn dm)
      | GReadReg reg k cont => GReadReg reg k (fun a => inlineGenSinDm (cont a) dn dm)
      | GWriteReg reg _ e cont => GWriteReg reg e (inlineGenSinDm cont dn dm)
      | GIfElse ce _ ta fa cont =>
        GIfElse ce (inlineGenSinDm ta dn dm) (inlineGenSinDm fa dn dm)
                (fun a => inlineGenSinDm (cont a) dn dm)
      | GAssert_ ae cont => GAssert_ ae (inlineGenSinDm cont dn dm)
      | GReturn e => GReturn _ e
    end.

  Definition getActionFromSin (gr: SinAction Void) := fun ty => getSinAction (gr ty).

  Definition getMethFromSin (gf: sigT SinMethodT) :=
    existT
      (fun sig => forall ty, ty (arg sig) -> ActionT ty (ret sig))
      (projT1 gf)
      (fun ty (argv: ty (arg (projT1 gf))) =>
         getSinAction (projT2 gf ty argv): ActionT ty (ret (projT1 gf))).

  
  Lemma inlineGenSinDm_matches GenK (getConstK: A -> ConstT GenK) ty k
        (a: GenActionT GenK ty k) dn
        (dnGood: index 0 indexSymbol dn = None) (dm: sigT SinMethodT):
    forall i,
      getGenAction strA getConstK i (inlineGenSinDm a dn dm) =
      inlineDm (getGenAction strA getConstK i a) (dn :: getMethFromSin dm)%struct.
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

Lemma inlineSinSinDmFn_matches:
  forall (k : Kind) (a : SinAction k) (dn : string),
    index 0 indexSymbol dn = None ->
    forall dm : sigT SinMethodT,
      (fun ty => getSinAction (inlineSinSinDm (a ty) dn dm)) =
      fun ty => inlineDm (getSinAction (a ty)) (dn :: getMethFromSin dm)%struct.
Proof.
  intros.
  extensionality ty.
  apply inlineSinSinDm_matches; auto.
Qed.

Section MoreThm.
  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable GenK: Kind.
  Variable getConstK: A -> ConstT GenK.
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
  
  Definition repRule (gr: GenAction GenK Void) :=
    getListFromRep (getActionFromGen strA getConstK gr).

  Lemma getFullCallsGenRule_matches (gr: GenAction GenK Void) s ls:
    concat (map (fun (r: Attribute (forall ty, ActionT ty Void)) => getCallsA ((attrType r) typeUT)) (repRule gr s ls)) =
    getFullCallsGenA strA (gr typeUT) ls.
  Proof.
    unfold getFullCallsGenA, repRule, getListFromRep; f_equal.
    rewrite map_map; f_equal.
    extensionality v.
    apply getCallsGenA_matches.
  Qed.

  Definition repMeth (gf: sigT (GenMethodT GenK)) :=
    getListFromRep (getMethFromGen strA getConstK gf).

  Lemma getFullCallsGenMeth_matches (gr: sigT (GenMethodT GenK)) s ls:
    concat (map (fun (r: Attribute (sigT MethodT)) => getCallsA (projT2 (attrType r) typeUT tt)) (repMeth gr s ls)) =
    getFullCallsGenA strA (projT2 gr typeUT tt) ls.
  Proof.
    unfold getFullCallsGenA, repMeth, getListFromRep; f_equal.
    rewrite map_map; f_equal.
    extensionality v; simpl in *.
    apply getCallsGenA_matches.
  Qed.
  
  Section BadInline.
    Variable ty: Kind -> Type.
    Variable gf: sigT (GenMethodT GenK).
    Variable fname: string.
    Variable fnameGood: index 0 indexSymbol fname = None.

    Section GenBad.
      Variable i i': A.
      Variable HNeq: i <> i'.
      
      Lemma badGenInlineGenGen_matches k (a: GenActionT GenK ty k):
        inlineDm (getGenAction strA getConstK i a)
                 (addIndexToStr strA i' fname :: getMethFromGen strA getConstK gf i')%struct =
        getGenAction strA getConstK i a.
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

      Lemma badGenInlineGenGen2_matches k (a: GenActionT GenK ty k):
        inlineDm (inlineDm (getGenAction strA getConstK i a)
                           (addIndexToStr strA i fname ::
                                          getMethFromGen strA getConstK gf i)%struct)
                 (addIndexToStr strA i' fname :: getMethFromGen strA getConstK gf i')%struct =
        inlineDm (getGenAction strA getConstK i a)
                 (addIndexToStr strA i fname :: getMethFromGen strA getConstK gf i)%struct.
      Proof.
        rewrite <- inlineGenGenDm_matches.
        apply badGenInlineGenGen_matches.
      Qed.
    End GenBad.
  End BadInline.
    
  Section FoldSimpleGenGen.
    Variable gf: sigT (GenMethodT GenK).
    Variable fname: string.
    Variable fnameGood: index 0 indexSymbol fname = None.

    Lemma foldInlineDmsGenGen_matches is:
      forall gr rname i,
        In i is ->
        NoDup is ->
        fold_right (fun dm' r' => inlineDmToRule r' dm')
                   (addIndexToStr strA i rname ::
                                  getActionFromGen strA getConstK gr i)%struct
                   (repMeth gf fname is)
        =
        inlineDmToRule (addIndexToStr strA i rname ::
                                      getActionFromGen strA getConstK gr i)%struct
                       (addIndexToStr strA i fname ::
                                      getMethFromGen strA getConstK gf i)%struct.
    Proof.
      intros.
      unfold repMeth, getListFromRep.
      rewrite fold_map'.
      match goal with
        | [|- fold_right ?f ?init is = ?q] =>
          remember f as sth;
          assert (sth2: f i init =
                        inlineDmToRule
                          init (addIndexToStr strA i fname ::
                                              getMethFromGen strA getConstK gf i)%struct)
            by reflexivity
      end.
      rewrite <- Heqsth in sth2.
      rewrite <- sth2.
      apply fold_single' with (ls := is); auto; subst; clear sth2; intros; simpl in *.
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
                       getActionFromGen strA getConstK
                       (fun ty => inlineGenGenDm (gr ty) fname gf) i)%struct =
        fold_right (fun dm' r' => inlineDmToRule r' dm')
                   (addIndexToStr strA i rname :: getActionFromGen strA
                                  getConstK gr i)%struct
                   (repMeth gf fname is).
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
      map (fun rule' =>
             fold_right (fun dm' r' => inlineDmToRule r' dm') rule' (repMeth gf fname is))
          (repRule gr rname is) =
      map (fun i =>
             inlineDmToRule (addIndexToStr strA i rname ::
                                           getActionFromGen strA getConstK gr i)%struct
                            (addIndexToStr strA i fname ::
                                           getMethFromGen strA getConstK gf i)%struct) is.
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
                                  getActionFromGen strA getConstK
                                  (fun ty => inlineGenGenDm (gr ty) fname gf) i)%struct is =
      map (fun rule' =>
             fold_right (fun dm' r' => inlineDmToRule r' dm') rule' (repMeth gf fname is))
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
                        (addIndexToStr strA i rname ::
                                       getActionFromGen strA getConstK gr i)%struct
                        (fname :: getMethFromSin f)%struct) is.
    Proof.
      intros.
      apply map_map.
    Qed.

    Lemma mapInlineDmsGenSin_matchesGen is:
      forall gr rname,
        map (fun i => addIndexToStr strA i rname ::
                                    getActionFromGen strA getConstK
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

Inductive MetaReg :=
| OneReg (b: RegInitValue) (s: NameRec)
| RepReg A (strA: A -> string) (goodStrFn: forall i j, strA i = strA j -> i = j)
         (goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                        si = sj /\ i = j)
         (bgen: A -> RegInitValue) (s: NameRec) (ls: list A) (noDup: NoDup ls).

Definition getMetaRegName m :=
  match m with
  | OneReg b s => nameVal s
  | RepReg _ _ _ _ _ s _ _ => nameVal s
  end.

Definition getListFromMetaReg m :=
  match m with
    | OneReg b s => (nameVal s :: b)%struct :: nil
    | RepReg A strA goodStrFn goodStrFn2 bgen s ls _ => getListFromRep strA bgen (nameVal s) ls
  end.

Inductive MetaRule :=
| OneRule (b: SinAction Void) (s: NameRec)
| RepRule A (strA: A -> string) (goodStrFn: forall i j, strA i = strA j -> i = j)
          (GenK: Kind) (getConstK: A -> ConstT GenK)
          (goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                         si = sj /\ i = j)
          (bgen: GenAction GenK Void) (s: NameRec) (ls: list A) (noDup: NoDup ls).

Definition getMetaRuleName m :=
  match m with
    | OneRule _ s => nameVal s
    | RepRule _ _ _ _ _ _ _ s _ _ => nameVal s
  end.

Definition getCallsMetaRule r :=
  match r with
    | OneRule b _ => map (fun a => {| isRep := false;
                                      nameRec := a |}) (getCallsSinA (b typeUT))
    | RepRule _ _ _ _ _ _ bgen _ _ _ => getCallsGenA (bgen typeUT)
  end.

Definition getListFromMetaRule m :=
  match m with
    | OneRule b s => (nameVal s :: getActionFromSin b)%struct :: nil
    | RepRule A strA goodStrFn GenK getConstK goodStrFn2 bgen s ls _ =>
      repRule strA getConstK bgen (nameVal s) ls
  end.

Inductive MetaMeth :=
| OneMeth (b: sigT SinMethodT) (s: NameRec)
| RepMeth A (strA: A -> string) (goodStrFn: forall i j, strA i = strA j -> i = j)
          (GenK: Kind) (getConstK: A -> ConstT GenK)
          (goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                         si = sj /\ i = j)
          (bgen: sigT (GenMethodT GenK)) (s: NameRec) (ls: list A) (noDup: NoDup ls).

Definition getMetaMethName m :=
  match m with
    | OneMeth _ s => nameVal s
    | RepMeth _ _ _ _ _ _ _ s _ _ => nameVal s
  end.

Definition getCallsMetaMeth dm :=
  match dm with
    | OneMeth b _ => map (fun a => {| isRep := false;
                                      nameRec := a |}) (getCallsSinA (projT2 b typeUT tt))
    | RepMeth _ _ _ _ _ _ bgen _ _ _ => getCallsGenA (projT2 bgen typeUT tt)
  end.

Definition getListFromMetaMeth m :=
  match m with
    | OneMeth b s => (nameVal s :: getMethFromSin b)%struct :: nil
    | RepMeth A strA goodStrFn GenK getConstK goodStrFn2 bgen s ls _ =>
      repMeth strA getConstK bgen (nameVal s) ls
  end.

Record MetaModule :=
  { metaRegs: list MetaReg;
    metaRules: list MetaRule;
    metaMeths: list MetaMeth
  }.

Definition modFromMeta m := Mod (concat (map getListFromMetaReg (metaRegs m)))
                               (concat (map getListFromMetaRule (metaRules m)))
                               (concat (map getListFromMetaMeth (metaMeths m))).

Definition concatMetaMod (m1 m2: MetaModule) :=
  {| metaRegs := metaRegs m1 ++ metaRegs m2;
     metaRules := metaRules m1 ++ metaRules m2;
     metaMeths := metaMeths m1 ++ metaMeths m2 |}.

Notation "m1 +++ m2" := (concatMetaMod m1 m2) (at level 0).

Lemma map_getListFromMetaReg_comm:
  forall r1 r2,
    map getListFromMetaReg r1 ++ map getListFromMetaReg r2 =
    map getListFromMetaReg (r1 ++ r2).
Proof.
  induction r1; simpl; intros; auto.
  rewrite IHr1; auto.
Qed.

Lemma map_getListFromMetaRule_comm:
  forall r1 r2,
    map getListFromMetaRule r1 ++ map getListFromMetaRule r2 =
    map getListFromMetaRule (r1 ++ r2).
Proof.
  induction r1; simpl; intros; auto.
  rewrite IHr1; auto.
Qed.

Lemma map_getListFromMetaMeth_comm:
  forall r1 r2,
    map getListFromMetaMeth r1 ++ map getListFromMetaMeth r2 =
    map getListFromMetaMeth (r1 ++ r2).
Proof.
  induction r1; simpl; intros; auto.
  rewrite IHr1; auto.
Qed.

Lemma modFromMeta_comm_1:
  forall m1 m2,
    modFromMeta (m1 +++ m2) <<== (modFromMeta m1 ++ modFromMeta m2)%kami.
Proof.
  unfold traceRefines; intros.
  exists s1, sig1; split.
  - inv H; constructor.
    remember (initRegs (getRegInits (modFromMeta (m1 +++ m2)))).
    induction HMultistepBeh.
    + subst; constructor.
      subst; simpl.
      rewrite <-concat_app; repeat f_equal.
      apply map_getListFromMetaReg_comm.
    + constructor; auto.
      clear -HStep.
      apply module_structure_indep_step with (m1:= modFromMeta m1 +++ m2); auto.
      * split; simpl; rewrite <-concat_app, <-map_getListFromMetaRule_comm; apply SubList_refl.
      * split; simpl; rewrite <-concat_app, <-map_getListFromMetaMeth_comm; apply SubList_refl.
      
  - clear; induction sig1; constructor; auto.
    rewrite idElementwiseId.
    constructor; destruct (annot a); auto.
Qed.

Lemma modFromMeta_comm_2:
  forall m1 m2,
    (modFromMeta m1 ++ modFromMeta m2)%kami <<== modFromMeta (m1 +++ m2).
Proof.
  unfold traceRefines; intros.
  exists s1, sig1; split.
  - inv H; constructor.
    remember (initRegs (getRegInits (modFromMeta m1 ++ modFromMeta m2)%kami)).
    induction HMultistepBeh.
    + subst; constructor.
      subst; simpl.
      rewrite <-concat_app; repeat f_equal.
      rewrite map_getListFromMetaReg_comm; auto.
    + constructor; auto.
      clear -HStep.
      apply module_structure_indep_step with (m1:= (modFromMeta m1 ++ modFromMeta m2)%kami); auto.
      * split; simpl; rewrite <-concat_app, map_getListFromMetaRule_comm; apply SubList_refl.
      * split; simpl; rewrite <-concat_app, map_getListFromMetaMeth_comm; apply SubList_refl.
        
  - clear; induction sig1; constructor; auto.
    rewrite idElementwiseId.
    constructor; destruct (annot a); auto.
Qed.

Fixpoint getNatListToN (n: nat) :=
  match n with
  | O => [ O ]
  | S n' => n :: getNatListToN n'
  end.

Lemma getNatListToN_NoDup n:
  NoDup (getNatListToN n).
Proof.
  assert (NoDup (getNatListToN n) /\ forall i, In i (getNatListToN n) -> le i n).
  { induction n; simpl in *; auto.
    - constructor; intros; intuition auto; omega.
    - destruct IHn.
      constructor; auto.
      constructor; unfold not; intros; auto.
      specialize (H0 _ H1).
      omega.
      intros.
      destruct H1; auto.
      omega.
  }
  destruct H; intuition auto.
Qed.

Lemma getNatListToN_le:
  forall i n, In i (getNatListToN n) <-> (i <= n)%nat.
Proof.
  induction n; simpl; split; intros; intuition.
  inv H; intuition idtac.
Qed.

Lemma getRegInits_modFromMeta_concat:
  forall mm1 mm2,
    getRegInits (modFromMeta (mm1 +++ mm2)) =
    (getRegInits (modFromMeta mm1))
      ++ (getRegInits (modFromMeta mm2)).
Proof.
  intros; simpl; rewrite map_app.
  apply Concat.concat_app.
Qed.

Lemma getListFromRep_In:
  forall {A} (strA: A -> string)
         (Hgood: forall (si sj : string) (i j : A),
             addIndexToStr strA i si = addIndexToStr strA j sj -> si = sj /\ i = j)
         {B} (bgen: A -> B) a s ls,
    In (addIndexToStr strA a s) (namesOf (getListFromRep strA bgen s ls)) ->
    In a ls.
Proof.
  induction ls; simpl; intros; [inv H|].
  destruct H.
  - specialize (Hgood _ _ _ _ H); dest; auto.
  - right; auto.
Qed.
  
Lemma getListFromRep_NoDup:
  forall {A} (strA: A -> string)
         (Hgood: forall (si sj : string) (i j : A),
             addIndexToStr strA i si = addIndexToStr strA j sj -> si = sj /\ i = j)
         {B} (bgen: A -> B) s ls,
    NoDup ls ->
    NoDup (namesOf (getListFromRep strA bgen (nameVal s) ls)).
Proof.
  induction ls; simpl; intros; auto.
  inv H; constructor; auto.
  intro Hx; elim H2; clear H2.
  eapply getListFromRep_In; eauto.
Qed.

Lemma getListFromMetaReg_NoDup:
  forall mr, NoDup (namesOf (getListFromMetaReg mr)).
Proof.
  destruct mr; simpl; auto.
  apply getListFromRep_NoDup; auto.
Qed.

Lemma getListFromRep_In_exists:
  forall e {A} (strA: A -> string) {B} (bgen: A -> B) s ls,
    In e (namesOf (getListFromRep strA bgen s ls)) ->
    exists ei, e = addIndexToStr strA ei s.
Proof.
  induction ls; simpl; intros; [inv H|].
  destruct H; auto; subst.
  eexists; auto.
Qed.

Lemma addIndexToStr_eq:
  forall {A1} (strA1: A1 -> string) {A2} (strA2: A2 -> string) i1 i2 s1 s2,
    index 0 indexSymbol s1 = None ->
    index 0 indexSymbol s2 = None ->
    addIndexToStr strA1 i1 s1 = addIndexToStr strA2 i2 s2 ->
    s1 = s2.
Proof.
  induction s1; intros.
  - destruct s2; auto.
    unfold addIndexToStr in H1; simpl in H1; inv H1.
    simpl in H0; rewrite prefix_empty in H0; inv H0.
  - destruct s2.
    + unfold addIndexToStr in H1; simpl in H1; inv H1.
      simpl in H; rewrite prefix_empty in H; inv H.
    + unfold addIndexToStr in H1; simpl in H1; inv H1.
      f_equal; apply IHs1; auto.
      * apply index_not_in in H; apply index_not_in.
        simpl in H; auto.
      * apply index_not_in in H0; apply index_not_in.
        simpl in H0; auto.
Qed.

Lemma disjList_metaReg:
  forall mr1 mr2,
    getMetaRegName mr1 <> getMetaRegName mr2 ->
    DisjList (namesOf (getListFromMetaReg mr1)) (namesOf (getListFromMetaReg mr2)).
Proof.
  destruct mr1 as [mr1|mr1], mr2 as [mr2|mr2]; simpl; intros.
  - unfold DisjList; intros.
    destruct (in_dec string_dec e (nameVal s :: nil)); auto.
    destruct (in_dec string_dec e (nameVal s0 :: nil)); auto.
    inv i; auto.
    inv i0; auto.
  - clear; induction ls; simpl; intros; [unfold DisjList; intros; auto|].
    unfold DisjList; intros.
    specialize (IHls e); destruct IHls; auto.
    destruct (in_dec string_dec e (nameVal s :: nil)); auto.
    inv i; auto; right.
    intro Hx; inv Hx; auto.
    destruct s as [s]; simpl in *; subst.
    generalize goodName0; apply index_addIndexToStr_notNone.
  - clear; induction ls; simpl; intros; [unfold DisjList; intros; auto|].
    unfold DisjList; intros.
    specialize (IHls e); destruct IHls; auto.
    destruct (in_dec string_dec e (nameVal s0 :: nil)); auto.
    inv i; auto; left.
    intro Hx; inv Hx; auto.
    destruct s0 as [s0]; simpl in *; subst.
    generalize goodName0; apply index_addIndexToStr_notNone.
  - unfold DisjList; intros.
    destruct (in_dec string_dec e (namesOf (getListFromRep strA bgen (nameVal s) ls))); auto.
    destruct (in_dec string_dec e (namesOf (getListFromRep strA0 bgen0 (nameVal s0) ls0))); auto.
    exfalso.
    apply getListFromRep_In_exists in i.
    apply getListFromRep_In_exists in i0.
    dest; subst; clear -H H0.

    destruct s as [s], s0 as [t]; simpl in *.
    apply addIndexToStr_eq in H0; auto.
Qed.

Lemma disjList_metaRegs:
  forall mr ml,
    ~ In (getMetaRegName mr) (map getMetaRegName ml) ->
    DisjList (namesOf (getListFromMetaReg mr)) (namesOf (concat (map getListFromMetaReg ml))).
Proof.
  induction ml; simpl; intros; [unfold DisjList; intros; right; auto|].
  destruct (string_dec (getMetaRegName a) (getMetaRegName mr)); [elim H; auto|].
  destruct (in_dec string_dec (getMetaRegName mr) (map getMetaRegName ml)); [elim H; auto|].
  clear H; specialize (IHml n0); clear n0.
  rewrite namesOf_app.
  apply DisjList_comm, DisjList_app_4, DisjList_comm; auto.
  apply disjList_metaReg; auto.
Qed.

Lemma noDup_metaRegs:
  forall mm,
    NoDup (map getMetaRegName (metaRegs mm)) ->
    NoDup (namesOf (getRegInits (modFromMeta mm))).
Proof.
  simpl; intros.
  induction (metaRegs mm); intros; auto.
  inv H; specialize (IHl H3); clear H3.
  simpl; rewrite namesOf_app.
  apply NoDup_DisjList; auto.
  - apply getListFromMetaReg_NoDup.
  - apply disjList_metaRegs; auto.
Qed.

Definition natToVoid (_: nat): ConstT Void := ConstBit WO.
Definition natToWordConst (sz: nat) (i: nat) := ConstBit (natToWord sz i).

Record SinReg A :=
  { regGen: A -> RegInitValue;
    regName: NameRec }.

Record SinRule :=
  { ruleGen: SinAction Void;
    ruleName: NameRec }.

Record SinMeth :=
  { methGen: sigT SinMethodT;
    methName: NameRec }.

Record SinModule A :=
  { sinRegs: list (SinReg A);
    sinRules: list SinRule;
    sinMeths: list SinMeth
  }.

Section SinModuleToMeta.
  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable GenK: Kind.
  Variable getConstK: A -> ConstT GenK.
  Variable goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                         si = sj /\ i = j.
  Variable ls: list A.
  Variable noDupLs: NoDup ls.
  
  Fixpoint regsToRep (rs: list (SinReg A)) :=
    match rs with
      | nil => nil
      | {| regGen := rg; regName := rn |} :: rs' =>
        RepReg strA goodStrFn goodStrFn2 rg rn noDupLs :: regsToRep rs'
    end.

  Lemma regsToRepIsMap rs: regsToRep rs = map (fun sr => RepReg strA goodStrFn goodStrFn2 (regGen sr) (regName sr) noDupLs) rs.
  Proof.
    induction rs; simpl; auto.
    rewrite IHrs.
    destruct a; reflexivity.
  Qed.
  
  Fixpoint rulesToRep (rs: list SinRule) :=
    match rs with
      | nil => nil
      | {| ruleGen := rg; ruleName := rn |} :: rs' =>
        RepRule strA goodStrFn getConstK goodStrFn2
                (fun ty => convSinToGen true _ (rg ty)) rn noDupLs ::
                rulesToRep rs'
    end.

  Lemma rulesToRepIsMap rs: rulesToRep rs =
                            map (fun sr => RepRule strA goodStrFn getConstK goodStrFn2
                                                   (fun ty => convSinToGen true _ (ruleGen sr ty)) (ruleName sr) noDupLs) rs.
  Proof.
    induction rs; simpl; auto.
    rewrite IHrs.
    destruct a; reflexivity.
  Qed.
  
  Fixpoint methsToRep (rs: list SinMeth) :=
    match rs with
      | nil => nil
      | {| methGen := rg; methName := rn |} :: rs' =>
        RepMeth strA goodStrFn getConstK goodStrFn2
                (existT (fun sig: SignatureT =>
                           GenMethodT GenK sig) (projT1 rg)
                        (fun ty argv => convSinToGen true GenK (projT2 rg ty argv)))
                rn noDupLs :: methsToRep rs'
    end.

  Lemma methsToRepIsMap rs: methsToRep rs =
                            map (fun sr => RepMeth strA goodStrFn getConstK goodStrFn2
                                                   (existT (fun sig: SignatureT =>
                                                              GenMethodT GenK sig) (projT1 (methGen sr))
                                                           (fun ty argv => convSinToGen true GenK (projT2 (methGen sr) ty argv)))
                                                   (methName sr) noDupLs) rs.
  Proof.
    induction rs; simpl; auto.
    rewrite IHrs.
    destruct a; reflexivity.
  Qed.
  
  Definition getMetaFromSin m :=
    {| metaRegs := regsToRep (sinRegs m);
       metaRules := rulesToRep (sinRules m);
       metaMeths := methsToRep (sinMeths m) |}.
End SinModuleToMeta.

(* NOTE: it's assuming register types are independent to indices *)
Definition getModFromSin (sm: SinModule nat) :=
  Syntax.Mod (map (fun sr => ((nameVal (regName sr))
                                :: ((regGen sr O)))%struct) (sinRegs sm))
             (map (fun sr => ((nameVal (ruleName sr))
                                :: (getActionFromSin (ruleGen sr)))%struct) (sinRules sm))
             (map (fun sd => ((nameVal (methName sd))
                                :: (getMethFromSin (methGen sd)))%struct) (sinMeths sm)).

Definition getMetaFromSinNat lgn s :=
  getMetaFromSin string_of_nat string_of_nat_into (natToWordConst lgn) withIndex_index_eq
                 (getNatListToN_NoDup (Word.wordToNat (Word.wones lgn))) s.

Lemma getMetaRegName_sinRegs:
  forall {A} (strA: A -> string) Hgood1 Hgood2 {ls} (HnoDup: NoDup ls) sregs,
    map getMetaRegName (regsToRep strA Hgood1 Hgood2 HnoDup sregs) =
    map (fun sr => nameVal (regName sr)) sregs.
Proof.
  induction sregs; simpl; intros; auto.
  destruct a; simpl; f_equal; auto.
Qed.

Lemma getDefs_sinModule_eq':
  forall n sm1 sm2,
    map (fun dm => nameVal (methName dm)) sm1 =
    map (fun dm => nameVal (methName dm)) sm2 ->
    namesOf
      (Concat.concat
         (map getListFromMetaMeth
              (methsToRep Indexer.string_of_nat Indexer.string_of_nat_into (natToWordConst n)
                          Indexer.withIndex_index_eq (getNatListToN_NoDup
                                                        (Word.wordToNat (Word.wones n))) 
                          sm1))) =
    namesOf
      (Concat.concat
         (map getListFromMetaMeth
              (methsToRep Indexer.string_of_nat Indexer.string_of_nat_into (natToWordConst n)
                          Indexer.withIndex_index_eq (getNatListToN_NoDup
                                                        (Word.wordToNat (Word.wones n))) 
                          sm2))).
Proof.
  induction sm1; intros; [destruct sm2; [auto|inv H]|].
  destruct sm2; [inv H|].
  inv H. specialize (IHsm1 _ H2).
  destruct a as [sig1 n1], s as [sig2 n2]; simpl in *.
  do 2 rewrite namesOf_app; f_equal; auto.

  rewrite H1; clear.
  induction (getNatListToN (Word.wordToNat (Word.wones n))); simpl; [reflexivity|].
  f_equal; auto.
Qed.

Lemma getDefs_sinModule_eq:
  forall sm1 sm2 n,
    map (fun dm => nameVal (methName dm)) (sinMeths sm1) =
    map (fun dm => nameVal (methName dm)) (sinMeths sm2) ->
    getDefs (modFromMeta (getMetaFromSinNat n sm1)) =
    getDefs (modFromMeta (getMetaFromSinNat n sm2)).
Proof.
  intros; apply getDefs_sinModule_eq'; auto.
Qed.

Lemma getCallsSinA_getCallsA_rep:
  forall {A} (strA: A -> string) {genK} (getConst: A -> ConstT genK) i
         {retK} (sa: SinActionT typeUT retK),
    getCallsA (getGenAction strA getConst i (convSinToGen true genK sa)) =
    map (fun nr => addIndexToStr strA i (nameVal nr)) (getCallsSinA sa).
Proof.
  induction sa; simpl; intros; auto.
  - f_equal; auto.
  - do 2 rewrite map_app; repeat f_equal; auto.
Qed.

Lemma getCallsSinA_getCallsR:
  forall (sa1 sa2: SinAction Void) sn1 sn2
         {A} (strA: A -> string) {genK} (getConst: A -> ConstT genK) ls,
    getCallsSinA (sa1 typeUT) = getCallsSinA (sa2 typeUT) ->
    getCallsR (repRule strA getConst (fun ty => convSinToGen true genK (sa1 ty)) sn1 ls) =
    getCallsR (repRule strA getConst (fun ty => convSinToGen true genK (sa2 ty)) sn2 ls).
Proof.
  induction ls; simpl; intros; [reflexivity|].
  f_equal; auto.
  unfold getActionFromGen.
  do 2 rewrite getCallsSinA_getCallsA_rep.
  rewrite H; auto.
Qed.

Lemma getCallsR_rulesToRep_eq:
  forall sr1 sr2,
    map (fun r : SinRule => getCallsSinA (ruleGen r typeUT)) sr1 =
    map (fun r : SinRule => getCallsSinA (ruleGen r typeUT)) sr2 ->
    forall {A} (strA: A -> string) Hgood1 {genK} (getConst: A -> ConstT genK) Hgood2
           {ls} (HnoDup: NoDup ls),
      getCallsR
        (concat
           (map getListFromMetaRule
                (rulesToRep strA Hgood1 getConst Hgood2 HnoDup sr1))) =
      getCallsR
        (concat
           (map getListFromMetaRule
                (rulesToRep strA Hgood1 getConst Hgood2 HnoDup sr2))).
Proof.
  induction sr1; simpl; intros;
    [apply eq_sym, map_eq_nil in H; subst; reflexivity|].
  destruct sr2; [inv H|]; simpl in H; inv H.
  destruct a as [ra na], s as [rs ns]; simpl in *.
  do 2 rewrite getCallsR_app; f_equal; auto.
  apply getCallsSinA_getCallsR; auto.
Qed.

Lemma getCallsSinA_getCallsM:
  forall (sa1 sa2: sigT SinMethodT) sn1 sn2
         {A} (strA: A -> string) {genK} (getConst: A -> ConstT genK) ls,
    getCallsSinA (projT2 sa1 typeUT tt) = getCallsSinA (projT2 sa2 typeUT tt) ->
    getCallsM
      (repMeth strA getConst
               (existT (fun sig => GenMethodT genK sig)
                       (projT1 sa1)
                       (fun ty argv => convSinToGen true genK (projT2 sa1 ty argv)))
               sn1 ls) =
    getCallsM
      (repMeth strA getConst
               (existT (fun sig => GenMethodT genK sig)
                       (projT1 sa2)
                       (fun ty argv => convSinToGen true genK (projT2 sa2 ty argv)))
               sn2 ls).
Proof.
  induction ls; simpl; intros; [reflexivity|].
  f_equal; auto.
  do 2 rewrite getCallsSinA_getCallsA_rep.
  rewrite H; auto.
Qed.

Lemma getCallsM_methsToRep_eq:
  forall sm1 sm2,
    map (fun d : SinMeth => getCallsSinA (projT2 (methGen d) typeUT tt)) sm1 =
    map (fun d : SinMeth => getCallsSinA (projT2 (methGen d) typeUT tt)) sm2 ->
    forall {A} (strA: A -> string) Hgood1 {genK} (getConst: A -> ConstT genK) Hgood2
           {ls} (HnoDup: NoDup ls),
      getCallsM
        (concat
           (map getListFromMetaMeth
                (methsToRep strA Hgood1 getConst Hgood2 HnoDup sm1))) =
      getCallsM
        (concat
           (map getListFromMetaMeth
                (methsToRep strA Hgood1 getConst Hgood2 HnoDup sm2))).
Proof.
  induction sm1; simpl; intros;
    [apply eq_sym, map_eq_nil in H; subst; reflexivity|].
  destruct sm2; [inv H|]; simpl in H; inv H.
  destruct a as [ma na], s as [ms ns]; simpl in *.
  do 2 rewrite getCallsM_app; f_equal; auto.
  apply getCallsSinA_getCallsM; auto.
Qed.

Lemma getCalls_sinModule_eq:
  forall sm1 sm2 n,
    map (fun r => getCallsSinA (ruleGen r typeUT)) (sinRules sm1) =
    map (fun r => getCallsSinA (ruleGen r typeUT)) (sinRules sm2) ->
    map (fun d => getCallsSinA (projT2 (methGen d) typeUT tt)) (sinMeths sm1) =
    map (fun d => getCallsSinA (projT2 (methGen d) typeUT tt)) (sinMeths sm2) ->
    getCalls (modFromMeta (getMetaFromSinNat n sm1)) =
    getCalls (modFromMeta (getMetaFromSinNat n sm2)).
Proof.
  intros.
  unfold getCalls, modFromMeta; simpl; f_equal.
  - apply getCallsR_rulesToRep_eq; auto.
  - apply getCallsM_methsToRep_eq; auto.
Qed.

Lemma getDefs_modFromMeta_app:
  forall mm1 mm2,
    getDefs (modFromMeta (mm1 +++ mm2)) =
    getDefs (modFromMeta mm1) ++ getDefs (modFromMeta mm2).
Proof.
  destruct mm1 as [? ? dm1], mm2 as [? ? dm2]; intros.
  unfold getDefs, modFromMeta; simpl.
  rewrite map_app, Concat.concat_app, namesOf_app; auto.
Qed.

Lemma getCalls_modFromMeta_app:
  forall mm1 mm2,
    EquivList (getCalls (modFromMeta (mm1 +++ mm2)))
              (getCalls (modFromMeta mm1) ++ getCalls (modFromMeta mm2)).
Proof.
  destruct mm1 as [? rules1 dms1], mm2 as [? rules2 dms2]; intros.
  unfold getCalls, modFromMeta; simpl.
  repeat rewrite map_app, concat_app.
  rewrite getCallsR_app, getCallsM_app.
  equivList_app_tac.
Qed.

Lemma repRule_in_exists:
  forall {A} rn rb (strA: A -> string) {B} (getConstK: A -> ConstT B) gr s ls,
    In (rn :: rb)%struct (repRule strA getConstK gr s ls) ->
    exists i,
      In i ls /\
      rn = addIndexToStr strA i s /\
      rb = getActionFromGen strA getConstK gr i.
Proof.
  induction ls; simpl; intros; [inv H|].
  destruct H.
  - inv H; exists a; repeat split; auto.
  - specialize (IHls H); dest; subst.
    eexists; repeat split; auto.
Qed.

Lemma repMeth_in:
  forall {A} i (strA: A -> string) {B} (getConstK: A -> ConstT B) fn fb ls,
    In i ls ->
    In ((addIndexToStr strA i fn) :: (getMethFromGen strA getConstK fb i))%struct
       (repMeth strA getConstK fb fn ls).
Proof.
  induction ls; simpl; intros; auto.
  inv H; auto.
Qed.

Inductive MetaModules :=
| MetaRegFile (dataArray: NameRec) (read: list NameRec) (write: NameRec) (IdxBits: nat)
              (Data: Kind) (init: ConstT (Vector Data IdxBits)): MetaModules
| MetaMod (m: MetaModule): MetaModules
| ConcatMetaMod (m1 m2: MetaModules): MetaModules
| RepeatSinMod
    (A: Type)
    (strA: A -> string)
    (goodStrFn: forall i j, strA i = strA j -> i = j)
    (GenK: Kind)
    (getConstK: A -> ConstT GenK)
    (goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                   si = sj /\ i = j)
    (ls: list A)
    (noDupLs: NoDup ls)
    (sm: SinModule A): MetaModules
| RepeatRegFile
    (A: Type)
    (strA: A -> string)
    (goodStrFn: forall i j, strA i = strA j -> i = j)
    (GenK: Kind)
    (getConstK: A -> ConstT GenK)
    (goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                   si = sj /\ i = j)
    (ls: list A)
    (noDupLs: NoDup ls)
    (dataArray: NameRec) (read: list NameRec) (write: NameRec)
    (IdxBits: nat) (Data: Kind) (init: ConstT (Vector Data IdxBits)): MetaModules.

Section RepeatSinMod.
  Variable A: Type.
  Variable strA: A -> string.
  Variable GenK: Kind.
  Variable getConstK: A -> ConstT GenK.

  Fixpoint repeatSinMod sm ls :=
    match ls with
      | nil => Mod nil nil nil
      | x :: xs =>
        ConcatMod
          (Mod
             (map (fun sr => (addIndexToStr strA x (nameVal (regName sr)) :: regGen sr x)%struct)
                  (sinRegs sm))
             (map
                (fun sr =>
                   (addIndexToStr
                      strA x (nameVal (ruleName sr)) ::
                      getActionFromGen strA getConstK (fun ty => convSinToGen true GenK (ruleGen sr ty)) x
                   )%struct) (sinRules sm))
             (map
                (fun sf =>
                   (addIndexToStr
                      strA x (nameVal (methName sf)) ::
                      (getMethFromGen strA getConstK
                                      (existT (fun sig: SignatureT =>
                                                 GenMethodT GenK sig) (projT1 (methGen sf))
                                              (fun ty argv => convSinToGen true GenK (projT2 (methGen sf) ty argv))) x)
                      )%struct) (sinMeths sm))
          ) (repeatSinMod sm xs)
    end.

  Fixpoint repeatRegFile dataArray reads write IdxBits Data (init: ConstT (Vector Data IdxBits)) ls :=
    match ls with
      | nil => Mod nil nil nil
      | x :: xs =>
        ConcatMod (RegFile (addIndexToStr strA x (nameVal dataArray))
                           (map (fun read => addIndexToStr strA x (nameVal read)) reads)
                           (addIndexToStr strA x (nameVal write))
                           init) (repeatRegFile dataArray reads write init xs)
    end.
End RepeatSinMod.


Fixpoint modFromMetaModules m :=
  match m with
    | MetaRegFile dataArray read write IdxBits Data init => RegFile (nameVal dataArray) (map nameVal read) (nameVal write) init
    | MetaMod (Build_MetaModule regs rules dms) =>
      Mod (concat (map getListFromMetaReg regs))
          (concat (map getListFromMetaRule rules))
          (concat (map getListFromMetaMeth dms))
    | ConcatMetaMod m1 m2 => ConcatMod (modFromMetaModules m1) (modFromMetaModules m2)
    | RepeatSinMod A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs sm =>
      repeatSinMod strA getConstK sm ls
    | RepeatRegFile A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs dataArray read write IdxBits Data init =>
      repeatRegFile strA dataArray read write init ls
  end.

Notation "m1 ++++ m2" := (ConcatMetaMod m1 m2) (at level 0).

Fixpoint metaModulesRegs m :=
  match m with
    | MetaRegFile dataArray read write IdxBits Data init =>
      OneReg (RegInitCustom (existT ConstFullT (SyntaxKind (Vector Data IdxBits)) (SyntaxConst init))) dataArray :: nil
    | MetaMod (Build_MetaModule regs _ _) => regs
    | ConcatMetaMod m1 m2 => metaModulesRegs m1 ++ metaModulesRegs m2
    | RepeatSinMod A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs sm =>
      regsToRep strA goodStrFn goodStrFn2 noDupLs (sinRegs sm)
    | RepeatRegFile A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs dataArray read write IdxBits Data init =>
      RepReg strA goodStrFn goodStrFn2 (fun _ => RegInitCustom (existT ConstFullT (SyntaxKind (Vector Data IdxBits))
                                                                       (SyntaxConst init))) dataArray noDupLs :: nil
  end.

Fixpoint metaModulesRules m :=
  match m with
    | MetaRegFile dataArray read write IdxBits Data init =>
      nil
    | MetaMod (Build_MetaModule regs rules meths) => rules
    | ConcatMetaMod m1 m2 => metaModulesRules m1 ++ metaModulesRules m2
    | RepeatSinMod A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs sm =>
      rulesToRep strA goodStrFn getConstK goodStrFn2 noDupLs (sinRules sm)
    | RepeatRegFile A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs dataArray read write IdxBits Data init =>
      nil
  end.

Fixpoint metaModulesMeths m :=
  match m with
    | MetaRegFile dataArray reads write IdxBits Data init =>
        OneMeth
        (existT SinMethodT
                {| arg := Struct
                            (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                         (Vector.cons _ {| attrName := "data"%string; attrType := Data |} _ (Vector.nil _)));
                   ret := Void |}
                (fun ty
                     (ar:ty
                           (Struct
                              (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                           (Vector.cons _ {| attrName := "data"%string; attrType := Data |} _ (Vector.nil _)))))
                 =>
                   (SReadReg dataArray
                            (SyntaxKind (Vector Data IdxBits))
                            (fun x: ty (Vector Data IdxBits) =>
                               SWriteReg dataArray
                                        (UpdateVector (Var ty (SyntaxKind (Vector Data IdxBits)) x)
                                                      (ReadField Fin.F1 (Var ty (SyntaxKind _) ar))
                                                      (ReadField (Fin.FS Fin.F1) (Var ty (SyntaxKind _) ar)))
                                        (SReturn (Const _ (k := Void) WO)))))
        ) write ::
        map (fun read => OneMeth
                           (existT SinMethodT {| arg := Bit IdxBits; ret := Data |}
                                   (fun ty (ar: ty (Bit IdxBits)) =>
                                      (SReadReg dataArray
                                                (SyntaxKind (Vector Data IdxBits))
                                                (fun x: ty (Vector Data IdxBits) =>
                                                   SReturn
                                                     (ReadIndex
                                                        (Var ty (SyntaxKind (Bit IdxBits)) ar)
                                                        (Var ty (SyntaxKind (Vector Data IdxBits)) x)))))
                           ) read) reads

        
    | MetaMod (Build_MetaModule regs rules meths) => meths
    | ConcatMetaMod m1 m2 => metaModulesMeths m1 ++ metaModulesMeths m2
    | RepeatSinMod A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs sm =>
      methsToRep strA goodStrFn getConstK goodStrFn2 noDupLs (sinMeths sm)
    | RepeatRegFile A strA goodStrFn GenK getConstK goodStrFn2 ls noDupLs dataArray reads write IdxBits Data init =>
      RepMeth strA goodStrFn  getConstK goodStrFn2
              (existT (GenMethodT GenK)
                      {| arg := Struct
                                  (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                               (Vector.cons _ {| attrName := "data"%string; attrType := Data |} _ (Vector.nil _)));
                         ret := Void |}
                      (fun ty
                           (ar:ty
                                 (Struct
                                    (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                                 (Vector.cons _ {| attrName := "data"%string; attrType := Data |} _ (Vector.nil _)))))
                       =>
                         (GReadReg {| isRep := true; nameRec := dataArray |}
                                   (SyntaxKind (Vector Data IdxBits))
                                   (fun x: ty (Vector Data IdxBits) =>
                                      GWriteReg {| isRep := true; nameRec := dataArray |}
                                                (UpdateVector (Var ty (SyntaxKind (Vector Data IdxBits)) x)
                                                              (ReadField Fin.F1 (Var ty (SyntaxKind _) ar))
                                                              (ReadField (Fin.FS Fin.F1) (Var ty (SyntaxKind _) ar)))
                                                (GReturn GenK (Const _ (k := Void) WO)))))
              ) write noDupLs ::
              map (fun read =>
                     RepMeth strA goodStrFn getConstK goodStrFn2
                             (existT (GenMethodT GenK) {| arg := Bit IdxBits; ret := Data |}
                                     (fun ty (ar: ty (Bit IdxBits)) =>
                                        (GReadReg {| isRep := true; nameRec := dataArray |}
                                                  (SyntaxKind (Vector Data IdxBits))
                                                  (fun x: ty (Vector Data IdxBits) =>
                                                     GReturn GenK
                                                             (ReadIndex
                                                                (Var ty (SyntaxKind (Bit IdxBits)) ar)
                                                                (Var ty (SyntaxKind (Vector Data IdxBits)) x)))))
                             ) read noDupLs) reads
  end.

Section InRepeatSinMod.
  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn:
    (forall i j : A, strA i = strA j -> i = j).
  Variable GenK: Kind.
  Variable getConstK: A -> ConstT GenK.
  Variable goodStrFn2:
    (forall (si sj : string) (i j : A),
       addIndexToStr strA i si = addIndexToStr strA j sj ->
       si = sj /\ i = j).
  Variable ls: list A.
  Variable noDupLs: NoDup ls.

  Lemma In_getRegInits_repeatSinMod m:
    forall r, In r (getRegInits (repeatSinMod strA getConstK m ls)) <->
              exists x rf, In x ls /\ In rf (sinRegs m) /\
                           r = {| attrName := addIndexToStr strA x (nameVal (regName rf));
                                  attrType := regGen rf x |}.
  Proof.
    clear goodStrFn goodStrFn2 noDupLs.
    induction ls; intros; simpl; auto.
    - constructor; intros; dest; tauto.
    - constructor; intros.
      + rewrite app_or in H; simpl in H.
        destruct H; [|
                     destruct (IHl r) as [sth1 sth2]; specialize (sth1 H); dest; subst;
                     repeat eexists; intuition idtac; f_equal].
        rewrite in_map_iff in H; dest; subst; repeat eexists; tauto.
      + dest; subst.
        rewrite app_or.
        destruct H; subst.
        * rewrite in_map_iff.
          left; eexists; tauto.
        * right.
          apply IHl.
          exists x, x0.
          tauto.
  Qed.

  Lemma In_getRules_repeatSinMod m:
    forall r, In r (getRules (repeatSinMod strA getConstK m ls)) <->
              exists x rf, In x ls /\ In rf (sinRules m) /\
                           r = {| attrName := addIndexToStr strA x (nameVal (ruleName rf));
                                  attrType := getActionFromGen strA getConstK
                                                               (fun ty => convSinToGen true GenK (ruleGen rf ty))
                                                               x |}.
  Proof.
    clear goodStrFn goodStrFn2 noDupLs.
    induction ls; intros; simpl; auto.
    - constructor; intros; dest; tauto.
    - constructor; intros.
      + rewrite app_or in H; simpl in H.
        destruct H; [|
                     destruct (IHl r) as [sth1 sth2]; specialize (sth1 H); dest; subst;
                     repeat eexists; intuition idtac; f_equal].
        rewrite in_map_iff in H; dest; subst; repeat eexists; tauto.
      + dest; subst.
        rewrite app_or.
        destruct H; subst.
        * rewrite in_map_iff.
          left; eexists; tauto.
        * right.
          apply IHl.
          exists x, x0.
          tauto.
  Qed.

  Lemma In_getDefsBodies_repeatSinMod m:
    forall r, In r (getDefsBodies (repeatSinMod strA getConstK m ls)) <->
              exists x rf, In x ls /\ In rf (sinMeths m) /\
                           r =
                           (addIndexToStr
                              strA x (nameVal (methName rf)) ::
                              (getMethFromGen strA getConstK
                                              (existT (fun sig: SignatureT =>
                                                         GenMethodT GenK sig) (projT1 (methGen rf))
                                                      (fun ty argv => convSinToGen true GenK (projT2 (methGen rf) ty argv))) x)
                           )%struct.
  Proof.
    clear goodStrFn goodStrFn2 noDupLs.
    induction ls; intros; simpl; auto.
    - constructor; intros; dest; tauto.
    - constructor; intros.
      + rewrite app_or in H; simpl in H.
        destruct H; [|
                     destruct (IHl r) as [sth1 sth2]; specialize (sth1 H); dest; subst;
                     repeat eexists; intuition idtac; f_equal].
        rewrite in_map_iff in H; dest; subst; repeat eexists; tauto.
      + dest; subst.
        rewrite app_or.
        destruct H; subst.
        * rewrite in_map_iff.
          left; eexists; tauto.
        * right.
          apply IHl.
          exists x, x0.
          tauto.
  Qed.

  Lemma In_getRegInits_repeatRegFile dataArray read write IdxBits Data init:
    forall r, In r (getRegInits (repeatRegFile strA dataArray read write init ls)) <->
              exists x, In x ls /\ r = {| attrName := addIndexToStr strA x (nameVal dataArray);
                                          attrType := RegInitCustom
                                                        (existT ConstFullT (SyntaxKind (Vector Data IdxBits)) (SyntaxConst init)) |}.
  Proof.
    clear goodStrFn goodStrFn2 noDupLs.
    induction ls; intros; simpl; auto.
    - constructor; intros; dest; tauto.
    - constructor; intros.
      + destruct H; [|
                     destruct (IHl r) as [sth1 sth2]; specialize (sth1 H); dest; subst;
                     repeat eexists; intuition idtac; f_equal].
        subst; repeat eexists; tauto.
      + dest; subst.
        destruct H; subst.
        * subst;
          left; eexists; tauto.
        * right.
          apply IHl.
          exists x.
          tauto.
  Qed.

  Lemma In_getRules_repeatRegFile dataArray read write (IdxBits: nat) (Data: Kind) (init: ConstT (Vector Data IdxBits)):
    forall r, In r (getRules (repeatRegFile strA dataArray read write init ls)) <-> False.
  Proof.
    clear goodStrFn goodStrFn2 noDupLs.
    induction ls; intros; simpl; auto; tauto.
  Qed.

  Lemma In_getDefsBodies_repeatRegFile
        dataArray read write (IdxBits: nat) (Data: Kind) (init: ConstT (Vector Data IdxBits)):
    forall g: DefMethT,
      In g (getDefsBodies (repeatRegFile strA dataArray read write init ls)) <->
      exists x, In x ls /\
                ((In g
                     (map
                        (fun read =>
                           (addIndexToStr
                              strA x (nameVal read) ::
                              (getMethFromGen strA getConstK
                                              (existT (GenMethodT GenK)
                                                      {| arg := Bit IdxBits; ret := Data |}
                                                      (fun ty (ar: ty (Bit IdxBits)) =>
                                                         (GReadReg {| isRep := true; nameRec := dataArray |}
                                                                   (SyntaxKind (Vector Data IdxBits))
                                                                   (fun x: ty (Vector Data IdxBits) =>
                                                                      GReturn GenK
                                                                              (ReadIndex
                                                                                 (Var ty (SyntaxKind (Bit IdxBits)) ar)
                                                                                 (Var ty (SyntaxKind (Vector Data IdxBits)) x)))))) x)
                           )%struct) read) \/
                 g =
                 (addIndexToStr
                    strA x (nameVal write) ::
                    (getMethFromGen
                       strA getConstK
                       (existT (GenMethodT GenK)
                               {| arg := Struct
                                           (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                                        (Vector.cons _ {| attrName := "data"%string; attrType := Data |}
                                                                     _ (Vector.nil _)));
                                  ret := Void |}
                               (fun ty
                                    (ar:ty
                                          (Struct
                                             (Vector.cons _ {| attrName := "addr"%string; attrType := Bit IdxBits |} _
                                                          (Vector.cons _ {| attrName := "data"%string; attrType := Data |}
                                                                       _ (Vector.nil _)))))
                                =>
                                  (GReadReg {| isRep := true; nameRec := dataArray |}
                                            (SyntaxKind (Vector Data IdxBits))
                                            (fun x: ty (Vector Data IdxBits) =>
                                               GWriteReg {| isRep := true; nameRec := dataArray |}
                                                         (UpdateVector (Var ty (SyntaxKind (Vector Data IdxBits)) x)
                                                                       (ReadField Fin.F1 (Var ty (SyntaxKind _) ar))
                                                                       (ReadField (Fin.FS Fin.F1) (Var ty (SyntaxKind _) ar)))
                                                         (GReturn GenK (Const _ (k := Void) WO)))))) x))%struct)).
  Proof.
    clear goodStrFn goodStrFn2 noDupLs.
    induction ls; intros; simpl; auto.
    - constructor; intros; dest; tauto.
    - split; intros.
      + simpl in H; subst.
        destruct H; subst.
        * dest; subst; repeat eexists; tauto.
        * rewrite map_map in H; simpl in *.
          apply in_app_or in H.
          { destruct H; subst.
            - repeat eexists; tauto.
            - destruct (IHl g) as [sth1 sth2]; specialize (sth1 H); dest; subst.
              exists x.
              split; [tauto|].
              auto.
          }
      + dest; subst; simpl in *; subst.
        destruct H; subst.
        * repeat destruct H0; subst; try tauto.
          right.
          apply in_or_app.
          rewrite map_map.
          tauto.
        * simpl in *.
          rewrite map_map in *.
          simpl in *.
          setoid_rewrite app_or.
          do 2 right.
          apply IHl.
          eexists; eauto.
  Qed.
End InRepeatSinMod.

Definition flattenMeta m := MetaMod (Build_MetaModule (metaModulesRegs m) (metaModulesRules m) (metaModulesMeths m)).

Lemma EquivList_In_iff A l1 l2: (forall x: A, In x l1 <-> In x l2) <-> (EquivList l1 l2).
Proof.
  unfold EquivList, SubList; intros; firstorder fail.
Qed.

Ltac concat_map_iff :=
  repeat (match goal with
            | H: context [In _ (concat _)] |- _ => setoid_rewrite in_concat_iff in H
            | |- context [In _ (concat _)] => setoid_rewrite in_concat_iff
            | H: context [In _ (map _ _)] |- _ => setoid_rewrite in_map_iff in H
            | |- context [In _ (map _ _)] => setoid_rewrite in_map_iff
          end; dest; subst).

Ltac handleReps :=
  rewrite ?map_map in *;
  unfold getListFromRep in *;
  repeat (concat_map_iff; eexists; eauto).

Lemma metaModulesRegsSame' m:
  forall x, In x (concat (map getListFromMetaReg (metaModulesRegs m))) <-> In x (getRegInits (modFromMetaModules m)).
Proof.
  induction m; simpl; intuition idtac; rewrite ?map_app, ?concat_app, ?app_or in *.
  - destruct m; simpl in *; auto.
  - destruct m; simpl in *; auto.
  - specialize (IHm1 x); specialize (IHm2 x).
    tauto.
  - specialize (IHm1 x); specialize (IHm2 x).
    tauto.
  - unfold getListFromMetaReg in *;
    rewrite regsToRepIsMap, In_getRegInits_repeatSinMod in *;
    handleReps.
  - unfold getListFromMetaReg in *;
    rewrite regsToRepIsMap, In_getRegInits_repeatSinMod in *;
    handleReps.
  - unfold getListFromMetaReg in *;
    rewrite In_getRegInits_repeatRegFile with (GenK := GenK) in *; eauto.
    destruct H; [|simpl in H; tauto].
    handleReps.
  - unfold getListFromMetaReg in *;
    rewrite In_getRegInits_repeatRegFile with (GenK := GenK) in *; eauto.
    dest; subst; left.
    handleReps.
Qed.

Lemma metaModulesRegsSame m: EquivList (concat (map getListFromMetaReg (metaModulesRegs m))) (getRegInits (modFromMetaModules m)).
Proof.
  apply EquivList_In_iff.
  apply metaModulesRegsSame'.
Qed.

Lemma metaModulesRulesSame' m:
  forall x, In x (concat (map getListFromMetaRule (metaModulesRules m))) <-> In x (getRules (modFromMetaModules m)).
Proof.
  induction m; simpl; intuition idtac; rewrite ?map_app, ?concat_app, ?app_or in *.
  - destruct m; simpl in *; auto.
  - destruct m; simpl in *; auto.
  - specialize (IHm1 x); specialize (IHm2 x).
    tauto.
  - specialize (IHm1 x); specialize (IHm2 x).
    tauto.
  - unfold getListFromMetaRule, repRule in *.
    rewrite rulesToRepIsMap, In_getRules_repeatSinMod in *.
    handleReps.
  - unfold getListFromMetaRule, repRule in *.
    rewrite rulesToRepIsMap, In_getRules_repeatSinMod in *.
    handleReps.
  - rewrite In_getRules_repeatRegFile in H; auto.
Qed.

Lemma metaModulesRulesSame m:
  EquivList (concat (map getListFromMetaRule (metaModulesRules m))) (getRules (modFromMetaModules m)).
Proof.
  apply EquivList_In_iff.
  apply metaModulesRulesSame'.
Qed.

Lemma metaModulesMethsSame' m:
  forall x, In x (concat (map getListFromMetaMeth (metaModulesMeths m))) <-> In x (getDefsBodies (modFromMetaModules m)).
Proof.
  induction m; simpl; intuition idtac; rewrite ?map_app, ?concat_app, ?app_or in *.
  - simpl in *.
    rewrite? map_map in *.
    right.
    simpl in *.
    induction read; simpl in *; auto.
    destruct H0; auto.
  - simpl in *.
    rewrite? map_map in *.
    right.
    simpl in *.
    induction read; simpl in *; auto.
    destruct H0; auto.
  - destruct m; simpl in *; auto.
  - destruct m; simpl in *; auto.
  - specialize (IHm1 x); specialize (IHm2 x).
    tauto.
  - specialize (IHm1 x); specialize (IHm2 x).
    tauto.
  - unfold getListFromMetaMeth, repMeth in *.
    rewrite methsToRepIsMap, In_getDefsBodies_repeatSinMod in *.
    handleReps.
  - unfold getListFromMetaMeth, repMeth in *.
    rewrite methsToRepIsMap, In_getDefsBodies_repeatSinMod in *.
    handleReps.
  - unfold repMeth in *.
    rewrite In_getDefsBodies_repeatRegFile in *.
    destruct H.
    + handleReps.
    + concat_map_iff; simpl in *.
      induction read; simpl; auto; simpl in *; try tauto.
      destruct H1; subst; simpl in *.
      * clear IHread.
        unfold repMeth, getListFromRep, getMethFromGen in *; simpl in *.
        rewrite in_map_iff in H0; dest.
        handleReps.
      * specialize (IHread H).
        dest.
        { destruct H2; dest.
          - exists x1.
            split; auto.
            left.
            exists x2; split; tauto.
          - exists x1.
            split; auto.
        } 
  - unfold repMeth, getMethFromGen in *.
    simpl in *.
    rewrite In_getDefsBodies_repeatRegFile with (GenK := GenK) (getConstK := getConstK) in H.
    dest; subst.
    destruct H0; subst.
    + right; handleReps.
      induction read; simpl; auto; simpl in *; try tauto.
      destruct H1; subst.
      * clear IHread.
        unfold repMeth, getListFromRep, getMethFromGen in *; simpl in *.
        rewrite in_map_iff.
        exists x0; auto.
      * specialize (IHread H0).
        auto.
    + left; handleReps.
Qed.

Lemma metaModulesMethsSame m:
  EquivList (concat (map getListFromMetaMeth (metaModulesMeths m))) (getDefsBodies (modFromMetaModules m)).
Proof.
  apply EquivList_In_iff.
  apply metaModulesMethsSame'.
Qed.

Section PigeonHole.
  Variable A: Type.
  Variable a: A.
  Variable l1 l2: list A.
  Variable in_in: forall x, (a = x \/ In x l1) -> (a = x \/ In x l2).
  Variable sameLength: length l1 = length l2.
  Variable notIn: ~ In a l1.
  Variable noDup: NoDup l1.
  Variable is_in: In a l2.

  Lemma pigeon_hole: exists x, In x l1 /\ ~ In x l2.
  Proof.
    generalize a l2 in_in sameLength notIn noDup is_in.
    clear a l2 in_in sameLength notIn noDup is_in.
    induction l1; intros.
    - simpl in *.
      apply eq_sym in sameLength.
      rewrite length_zero_iff_nil in sameLength; subst.
      exfalso; assumption.
    - assert (sth: In a l2).
      { specialize (@in_in a).
        specialize (@in_in (or_intror (or_introl eq_refl))).
        destruct in_in as [ez|hard]; [subst; simpl in *; tauto| assumption].
      }
      apply in_split in sth.
      destruct sth as [l3 [l4 l4Eq]]; subst.
      specialize (IHl a0 (l3 ++ l4)).
      rewrite app_length in *; simpl in *.
      rewrite <- plus_n_Sm in sameLength.
      inversion sameLength; clear sameLength.
      assert (forall x, a0 = x \/ In x l -> a0 = x \/ In x (l3 ++ l4)).
      { intros.
        specialize (@in_in x).
        assert (a0 = x \/ In x (l3 ++ a :: l4)) by tauto.
        destruct H; [tauto |].
        destruct H1; [tauto|].
        rewrite ListSupport.app_or in *; simpl in H1.
        inversion noDup; subst; clear noDup.
        destruct H1; [tauto|].
        destruct H1; [subst|]; tauto.
      }
      assert (~ In a0 l) by tauto.
      inversion noDup; subst; clear noDup.
      assert (In a0 (l3 ++ l4)).
      { rewrite ListSupport.app_or in *; simpl in *.
        destruct is_in; [tauto|].
        destruct H2; [subst; tauto|tauto].
      } 
      apply IHl in H5; try assumption.
      destruct H5 as [x [inx notinx]].
      exists x.
      split; [tauto | intro].
      rewrite ListSupport.app_or in *; simpl in *.
      destruct H3; [tauto | destruct H3; [subst; tauto | tauto] ].
  Qed.
End PigeonHole.

Section Dup.
  Variable A: Type.

  Lemma NoDup_remove_inv:
    forall l1 l2 (x: A),
      ~ In x (l1 ++ l2) ->
      NoDup (l1 ++ l2) ->
      NoDup (l1 ++ x :: l2).
  Proof.
    induction l1; simpl; auto; intros.
    - apply NoDup_cons; assumption.
    - inversion H0; subst; clear H0.
      apply IHl1 with (x := x) in H4; try tauto.
      apply NoDup_cons with (x := a) in H4; try assumption.
      intro.
      rewrite ListSupport.app_or in *; simpl in *; intuition congruence.
  Qed.
  
  Variable l1 l2: list A.
  Variable in_in: forall x, In x l1 -> In x l2.
  Variable sameLength: length l1 = length l2.
  Variable noDup: NoDup l1.

  Lemma NoDup_superlist: NoDup l2.
  Proof.
    generalize l2 in_in sameLength noDup.
    clear l2 in_in sameLength noDup.
    induction l1; intros.
    - simpl in *.
      apply eq_sym in sameLength.
      rewrite length_zero_iff_nil in sameLength; subst.
      assumption.
    - assert (sth: In a l2).
      { specialize (@in_in a).
        apply (@in_in (or_introl eq_refl)).
      } 
      apply in_split in sth.
      destruct sth as [l3 [l4 l4Eq]]; subst.
      specialize (IHl (l3 ++ l4)).
      rewrite app_length in *; simpl in *.
      rewrite <- plus_n_Sm in sameLength.
      inversion sameLength; clear sameLength.
      inversion noDup; subst; clear noDup.
      assert (forall x, In x l -> In x (l3 ++ l4)).
      { intros.
        specialize (@in_in x).
        assert (In x (l3 ++ a :: l4)) by tauto.
        rewrite ListSupport.app_or in *; simpl in H1.
        destruct H1; [tauto |].
        destruct H1; [subst |tauto].
        tauto.
      }
      apply IHl in H; try assumption.
      apply NoDup_remove_inv; try assumption.
      clear - in_in H0 H2 H3.
      setoid_rewrite ListSupport.app_or in in_in; simpl in *.
      setoid_rewrite or_comm at 2 in in_in.
      setoid_rewrite or_assoc in in_in.
      setoid_rewrite or_comm at 3 in in_in.
      setoid_rewrite <- ListSupport.app_or in in_in; simpl in *.
      rewrite <- app_length in H0.
      intro sth.
      eapply pigeon_hole in sth; eauto.
      destruct sth as [x [inx notinx]].
      specialize (in_in x (or_intror inx)).
      destruct in_in; intuition congruence.
  Qed.
End Dup.

Lemma NoDup_samelist A:
  forall (l1 l2: list A)
         (in_in: forall x, In x l1 <-> In x l2)
         (sameLength: length l1 = length l2),
    NoDup l1 <-> NoDup l2.
Proof.
  unfold iff at 2; intros.
  constructor; apply NoDup_superlist; auto; firstorder idtac.
Qed.

Lemma concat_nil_length_zero A B: forall (ls: list A), length (concat (map (fun _ => @nil B) ls)) = 0.
Proof.
  induction ls; simpl; auto.
Qed.


Lemma concat_nil_length_map_cons A B (f: A -> list B) (b: A -> B):
  forall (ls: list A), length (concat (map (fun a => b a :: f a) ls))
                       = length (map b ls ++ concat (map f ls)).
Proof.
  induction ls; simpl; auto.
  f_equal.
  rewrite ?app_length.
  rewrite IHls.
  rewrite ?app_length.
  rewrite ?Nat.add_assoc.
  f_equal.
  rewrite Nat.add_comm.
  reflexivity.
Qed.


Lemma metaRegsSameLength m:
  length (concat (map getListFromMetaReg (metaModulesRegs m))) = length (getRegInits (modFromMetaModules m)).
Proof.
  induction m; simpl; intuition auto; rewrite ?map_app, ?concat_app, ?ListSupport.app_or in *.
  - destruct m; simpl in *; auto.
  - rewrite ?app_length; congruence.
  - rewrite regsToRepIsMap.
    rewrite map_map; simpl.
    clear.
    induction ls; simpl.
    + rewrite concat_nil_length_zero; reflexivity.
    + rewrite ?app_length.
      rewrite <- IHls.
      rewrite <- app_length.
      rewrite concat_nil_length_map_cons.
      reflexivity.
  - rewrite app_nil_r.
    unfold getListFromRep.
    rewrite map_length.
    clear.
    induction ls; simpl; auto.
Qed.


Lemma metaRegs_NoDup_names:
  forall mm,
    NoDup (map getMetaRegName (metaModulesRegs mm)) ->
    NoDup (namesOf (getRegInits (modFromMetaModules mm))).
Proof.
  simpl; intros.
  induction mm.
  - simpl in *; auto.
  - simpl in *; destruct m as [regs rules meths].
    induction regs; intros; auto.
    inv H; specialize (IHregs H3); clear H3.
    simpl; rewrite namesOf_app.
    apply NoDup_DisjList; auto.
    + apply getListFromMetaReg_NoDup.
    + apply disjList_metaRegs; auto.
  - simpl in *;
    rewrite map_app in H.
    specialize (IHmm1 (ListSupport.NoDup_app_1 _ _ H)).
    specialize (IHmm2 (ListSupport.NoDup_app_2 _ _ H)).
    unfold namesOf in *; rewrite map_app; auto.
    apply NoDup_DisjList; auto.
    clear - H; intros.
    unfold DisjList.
    setoid_rewrite in_map_iff.
    setoid_rewrite <- metaModulesRegsSame'.
    setoid_rewrite <- in_map_iff.
    match goal with
      | |- forall _, ~ In _ ?x \/ ~ In _ ?y =>
        fold (DisjList x y)
    end.
    induction (metaModulesRegs mm1); simpl in *; auto; intros.
    + intro; tauto.
    + apply NoDup_cons_iff in H; dest.
      specialize (IHl H0).
      rewrite map_app.
      apply DisjList_app_4; auto.
      clear IHl.
      assert (sth: ~ In (getMetaRegName a) (map getMetaRegName (metaModulesRegs mm2))) by (rewrite app_or in H; tauto).
      apply disjList_metaRegs; auto.
  - pose proof (metaModulesRegsSame' (RepeatSinMod strA goodStrFn getConstK goodStrFn2 noDupLs sm)).
    pose proof (metaRegsSameLength (RepeatSinMod strA goodStrFn getConstK goodStrFn2 noDupLs sm)).
    simpl in *; auto.
    rewrite regsToRepIsMap, map_map in *; simpl in *.
    match goal with
      | H: forall x, In x ?l1 <-> In x ?l2 |- _ =>
        assert (forall x, In x (namesOf l1) <-> In x (namesOf l2))
    end.
    { intros.
      constructor; intros; unfold namesOf in *.
      - rewrite in_map_iff in *; dest; subst.
        apply H0 in H3.
        exists x0; auto.
      - rewrite in_map_iff in *; dest; subst.
        apply H0 in H3.
        exists x0; auto.
    }
    clear H0.
    rewrite <- ?map_length with (f := (@attrName _)) in H1.
    apply NoDup_samelist in H2; try assumption.
    apply H2.
    clear H1 H2.
    generalize H.
    clear H.
    induction (sinRegs sm); simpl; auto; intros.
    + inversion H; subst; clear H.
      apply IHl in H3; try assumption.
      unfold namesOf in *.
      rewrite map_app in *.
      apply noDupApp; try assumption; intros.
      * fold (namesOf (getListFromRep strA (regGen a) (nameVal (regName a)) ls)).
        eapply getListFromRep_NoDup; auto.
      * intro.
        rewrite in_map_iff in H2; dest; subst.
        rewrite in_map_iff in H0; dest; subst.
        apply getListFromRep_In_exists in H; dest; subst.
        rewrite in_concat_iff in H1; dest; subst.
        rewrite in_map_iff in H0; dest; subst.
        apply in_map with (f := @attrName _) in H1.        
        apply getListFromRep_In_exists in H1; dest; subst.
        rewrite H0 in H.
        apply goodStrFn2 in H.
        dest; subst.
        clear - H2 H H4.
        firstorder fail.
  - simpl in *.
    generalize noDupLs.
    clear - goodStrFn2.
    induction ls; simpl; auto.
    intros noDupLs.
    inv noDupLs.
    pose proof (IHls H2).
    apply NoDup_cons; auto.
    unfold namesOf; intro.
    rewrite in_map_iff in H0; dest.
    destruct x; simpl in *; subst.
    clear - H1 H2 H3 goodStrFn2.
    induction ls; simpl; auto.
    inv H2.
    simpl in H1.
    assert (a0 <> a /\ ~ In a ls) by tauto; dest.
    specialize (IHls H0 H5).
    simpl in H3.
    destruct H3.
    inv H2.
    apply goodStrFn2 in H6; dest; subst; tauto.
    apply IHls; auto.
Qed.

Section PermuteRefines.
  Variable A B: Modules.
  Variable sameRegs: EquivList (getRegInits A) (getRegInits B).
  Variable sameRules: EquivList (getRules A) (getRules B).
  Variable sameMeths: EquivList (getDefsBodies A) (getDefsBodies B).
  Variable noDupImpl: NoDup (namesOf (getRegInits A)).
  Variable noDupSpec: NoDup (namesOf (getRegInits B)).

  Lemma permute_refines_left: A <<== B.
  Proof.
    unfold traceRefines; intros.
    exists s1, sig1; split.
    - inv H; constructor; simpl in *.
      remember (initRegs (getRegInits A)).
      induction HMultistepBeh; subst.
      + constructor; subst.
        apply eq_sym.
        erewrite initRegs_eq; eauto.
      + constructor; auto.
        specialize (IHHMultistepBeh eq_refl).
        eapply module_structure_indep_step; eauto.
    - clear; induction sig1; constructor; auto.
      rewrite idElementwiseId.
      constructor; destruct (annot a); auto.
  Qed.
End PermuteRefines.

Section PermuteRefines2.
  Variable A B: Modules.
  Variable sameRegs: EquivList (getRegInits A) (getRegInits B).
  Variable sameRules: EquivList (getRules A) (getRules B).
  Variable sameMeths: EquivList (getDefsBodies A) (getDefsBodies B).
  Variable noDupImpl: NoDup (namesOf (getRegInits A)).
  Variable noDupSpec: NoDup (namesOf (getRegInits B)).

  Lemma permute_equivalent: (A <<== B) /\ (B <<== A).
  Proof.
    constructor.
    apply permute_refines_left; auto; try apply EquivList_comm; auto.
    apply permute_refines_left; auto; try apply EquivList_comm; auto.
  Qed.

  Lemma permute_refines_right: (B <<== A).
  Proof.
    apply permute_refines_left; auto; try apply EquivList_comm; auto.
  Qed.
End PermuteRefines2.

Notation "a <|=|> b" := ((modFromMetaModules (a) <<== modFromMetaModules (b)) /\
                         (modFromMetaModules (b) <<== modFromMetaModules (a))) (at level 70).

Section concat_Map.
  Variable A B: Type.
  Variable f: A -> B.
  Lemma map_concat: forall l, map f (concat l) = concat (map (map f) l).
  Proof.
    induction l; simpl; auto.
    rewrite map_app.
    f_equal.
    assumption.
  Qed.
End concat_Map.

Lemma mapRegName:
  (fun x =>
     map (attrName (A:=RegInitValue))
         match x with
           | OneReg b s => [(nameVal s :: b)%struct]
           | @RepReg A strA _ _ bgen s ls _ =>
             map
               (fun i : A =>
                  (addIndexToStr strA i (nameVal s) :: bgen i)%struct) ls
         end) = fun x => match x with
                           | OneReg _ s => [nameVal s]
                           | @RepReg A strA _ _ _ s ls _ =>
                             map (fun i => addIndexToStr strA i (nameVal s)) ls
                         end.
Proof.
  extensionality x.
  intros.
  destruct x; auto.
  rewrite map_map; auto.
Qed.

Section string.
  Variable v: Ascii.ascii.
  Open Scope string.
  Lemma notPresentPrefix:
    forall p1 p2 s1 s2,
      ~ S_In v p1 ->
      ~ S_In v p2 ->
      (p1 ++ String v s1 = p2 ++ String v s2)%string ->
      p1 = p2 /\ s1 = s2.
  Proof.
    induction p1; intros; auto.
    - destruct p2; rewrite ?S_app_nil_l in H1.
      + inversion H1.
        auto.
      + rewrite <- S_app_comm_cons in H1.
        inversion H1; subst.
        simpl in H0.
        tauto.
    - destruct p2; rewrite ?S_app_nil_l in H1.
      + rewrite <- S_app_comm_cons in H1.
        inversion H1; subst.
        simpl in H.
        tauto.
      + rewrite <- ?S_app_comm_cons in H1.
        inversion H1; subst.
        apply S_not_in_cons in H0.
        apply S_not_in_cons in H.
        destruct H0, H.
        apply IHp1 in H4; auto.
        repeat (split; f_equal; tauto).
  Qed.
End string.


Section flattenRefines.
  Variable m: MetaModules.
  Variable noDupRegs:  NoDup (map getMetaRegName (metaModulesRegs m)).

  Lemma flattenMetaEquiv: flattenMeta m <|=|> m.
  Proof.
    unfold flattenMeta.
    apply permute_equivalent.
    - apply metaModulesRegsSame.
    - apply metaModulesRulesSame.
    - apply metaModulesMethsSame.
    - simpl.
      unfold getListFromMetaReg, namesOf, getMetaRegName, getListFromRep in *.
      rewrite map_concat, map_map, mapRegName.
      generalize noDupRegs; clear noDupRegs.
      induction (metaModulesRegs m); clear m; simpl; auto; intros.
      inv noDupRegs.
      specialize (IHl H2).
      apply noDupApp; auto; intros.
      + generalize H2; clear.
        induction l; simpl; auto; intros.
        * destruct a; simpl; auto.
          pose proof (@getListFromRep_NoDup A strA goodStrFn2 _ bgen s ls noDup) as sth.
          unfold getListFromRep, namesOf in *.
          rewrite map_map in *; simpl in *.
          auto.
        * inv H2.
          specialize (IHl H3).
          apply IHl.
      + intro.
        destruct a; simpl in *; intuition idtac; subst.
        * destruct s; simpl in *.
          concat_map_iff.
          { destruct x0; simpl in *; intuition idtac; subst.
            - match goal with
                | H: ?A -> False |- _ => assert A by (exists (OneReg b0 s); auto)
              end.
              auto.
            - concat_map_iff.
              apply badIndex in goodName0; auto.
          }
        * concat_map_iff.
          { destruct x0; simpl in *; intuition idtac; subst.
            - destruct s0; simpl in *; subst.
              exfalso; clear - goodName0.
              apply badIndex in goodName0.
              auto.
            - concat_map_iff.
              unfold addIndexToStr in H.
              unfold indexSymbol in *.
              apply notPresentPrefix in H; dest; subst.
              + apply H1.
                match type of H4 with
                  | In ?x l => exists x; auto
                end.
              + apply index_not_in; destruct s0; auto.
              + apply index_not_in; destruct s; auto.
          } 
    - apply metaRegs_NoDup_names; assumption.
  Qed.
End flattenRefines.

Definition getMetaModulesFromSinNat lgn s :=
  RepeatSinMod string_of_nat string_of_nat_into (natToWordConst lgn) withIndex_index_eq
               (getNatListToN_NoDup (Word.wordToNat (Word.wones lgn))) s.

Definition getMetaModulesFromRegFile lgn dataArray read write (IdxBits: nat) (Data: Kind) (init: ConstT (Vector Data IdxBits)) :=
  RepeatRegFile string_of_nat string_of_nat_into (natToWordConst lgn) withIndex_index_eq
                (getNatListToN_NoDup (Word.wordToNat (Word.wones lgn))) dataArray read write init.

