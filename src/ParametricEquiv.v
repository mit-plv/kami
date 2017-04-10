Require Import String Kami.ParametricSyntax Kami.Syntax List Lib.CommonTactics Kami.Wf Program.Equality Lib.Struct Lib.Concat Lib.StringEq Lib.StringAsList.

Set Asymmetric Patterns.

Section Equiv.
  Variable t1 t2: Kind -> Type.

  Definition ft1 := fullType t1.
  Definition ft2 := fullType t2.
  Hint Unfold ft1 ft2.

  Section ForGenK.
    Variable GenK: Kind.
    Inductive GenActionEquiv: forall {k}, GenActionT GenK t1 k -> GenActionT GenK t2 k -> Prop :=
    | GAEMCall: forall {k} n s (e1: Expr t1 (SyntaxKind (arg s)))
                       (e2: Expr t2 (SyntaxKind (arg s)))
                       (cont1: t1 (ret s) -> GenActionT GenK t1 k)
                       (cont2: t2 (ret s) -> GenActionT GenK t2 k),
                  (forall (v1: ft1 (SyntaxKind (ret s)))
                          (v2: ft2 (SyntaxKind (ret s))),
                     GenActionEquiv (cont1 v1) (cont2 v2)) ->
                  GenActionEquiv (GMCall n s e1 cont1) (GMCall n s e2 cont2)
    | GAEIndex: forall k
                       (cont1: t1 GenK -> GenActionT GenK t1 k)
                       (cont2: t2 GenK -> GenActionT GenK t2 k),
                  (forall (v1: t1 GenK) (v2: t2 GenK),
                     GenActionEquiv (cont1 v1) (cont2 v2)) ->
                  GenActionEquiv (GIndex cont1) (GIndex cont2)
    | GAELet: forall {k k1' k2'} (e1: Expr t1 k1') (e2: Expr t2 k2')
                     (cont1: fullType t1 k1' -> GenActionT GenK t1 k)
                     (cont2: fullType t2 k2' -> GenActionT GenK t2 k),
                (forall (v1: ft1 k1') (v2: ft2 k2'),
                   GenActionEquiv (cont1 v1) (cont2 v2)) ->
                GenActionEquiv (GLet_ e1 cont1) (GLet_ e2 cont2)
    | GAEReadReg: forall {k k1' k2'} rn
                         (cont1: fullType t1 k1' -> GenActionT GenK t1 k)
                         (cont2: fullType t2 k2' -> GenActionT GenK t2 k),
                    (forall (v1: ft1 k1') (v2: ft2 k2'),
                       GenActionEquiv (cont1 v1) (cont2 v2)) ->
                    GenActionEquiv (GReadReg rn _ cont1) (GReadReg rn _ cont2)
    | GAEWriteReg: forall {k k1' k2'} rn (e1: Expr t1 k1') (e2: Expr t2 k2')
                          (cont1: GenActionT GenK t1 k) (cont2: GenActionT GenK t2 k),
                     (* ExprEquiv G e1 e2 -> *)
                     GenActionEquiv cont1 cont2 ->
                     GenActionEquiv (GWriteReg rn e1 cont1) (GWriteReg rn e2 cont2)
    | GAEIfElse: forall {k k'} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                        (ta1 fa1: GenActionT GenK t1 k') (ta2 fa2: GenActionT GenK t2 k')
                        (cont1: t1 k' -> GenActionT GenK t1 k) (cont2: t2 k' ->
                                                                       GenActionT GenK t2 k),
                   (* ExprEquiv G e1 e2 -> *)
                   GenActionEquiv ta1 ta2 -> GenActionEquiv fa1 fa2 ->
                   (forall (v1: ft1 (SyntaxKind k')) (v2: ft2 (SyntaxKind k')),
                      GenActionEquiv (cont1 v1) (cont2 v2)) ->
                   GenActionEquiv (GIfElse e1 ta1 fa1 cont1) (GIfElse e2 ta2 fa2 cont2)
    | GAEAssert: forall {k} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                        (cont1: GenActionT GenK t1 k) (cont2: GenActionT GenK t2 k),
                   (* ExprEquiv G e1 e2 -> *)
                   GenActionEquiv cont1 cont2 ->
                   GenActionEquiv (GAssert_ e1 cont1) (GAssert_ e2 cont2)
    | GAERet: forall {k} (e1: Expr t1 (SyntaxKind k))
                     (e2: Expr t2 (SyntaxKind k)),
                (* ExprEquiv G e1 e2 -> *)
                GenActionEquiv (GReturn GenK e1) (GReturn GenK e2).

    Lemma GenActionEquiv_ActionEquiv A k str getConstK:
      forall a1 a2,
        GenActionEquiv (k := k) a1 a2 ->
        forall i: A,
          ActionEquiv (getGenAction str getConstK i a1)
                      (getGenAction str getConstK i a2).
    Proof.
      intros.
      dependent induction H; simpl in *; constructor; intuition auto.
    Qed.
      
  End ForGenK.
    
  Inductive SinActionEquiv: forall {k}, SinActionT t1 k -> SinActionT t2 k -> Prop :=
  | SAEMCall: forall {k} n s (e1: Expr t1 (SyntaxKind (arg s)))
                     (e2: Expr t2 (SyntaxKind (arg s)))
                     (cont1: t1 (ret s) -> SinActionT t1 k)
                     (cont2: t2 (ret s) -> SinActionT t2 k),
                (forall (v1: ft1 (SyntaxKind (ret s)))
                        (v2: ft2 (SyntaxKind (ret s))),
                   SinActionEquiv (cont1 v1) (cont2 v2)) ->
                SinActionEquiv (SMCall n s e1 cont1) (SMCall n s e2 cont2)
  | SAELet: forall {k k1' k2'} (e1: Expr t1 k1') (e2: Expr t2 k2')
                   (cont1: fullType t1 k1' -> SinActionT t1 k)
                   (cont2: fullType t2 k2' -> SinActionT t2 k),
              (forall (v1: ft1 k1') (v2: ft2 k2'),
                 SinActionEquiv (cont1 v1) (cont2 v2)) ->
              SinActionEquiv (SLet_ e1 cont1) (SLet_ e2 cont2)
  | SAEReadReg: forall {k k1' k2'} rn
                       (cont1: fullType t1 k1' -> SinActionT t1 k)
                       (cont2: fullType t2 k2' -> SinActionT t2 k),
                  (forall (v1: ft1 k1') (v2: ft2 k2'),
                     SinActionEquiv (cont1 v1) (cont2 v2)) ->
                  SinActionEquiv (SReadReg rn _ cont1) (SReadReg rn _ cont2)
  | SAEWriteReg: forall {k k1' k2'} rn (e1: Expr t1 k1') (e2: Expr t2 k2')
                        (cont1: SinActionT t1 k) (cont2: SinActionT t2 k),
                   (* ExprEquiv G e1 e2 -> *)
                   SinActionEquiv cont1 cont2 ->
                   SinActionEquiv (SWriteReg rn e1 cont1) (SWriteReg rn e2 cont2)
  | SAEIfElse: forall {k k'} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                      (ta1 fa1: SinActionT t1 k') (ta2 fa2: SinActionT t2 k')
                      (cont1: t1 k' -> SinActionT t1 k) (cont2: t2 k' -> SinActionT t2 k),
                 (* ExprEquiv G e1 e2 -> *)
                 SinActionEquiv ta1 ta2 -> SinActionEquiv fa1 fa2 ->
                 (forall (v1: ft1 (SyntaxKind k')) (v2: ft2 (SyntaxKind k')),
                    SinActionEquiv (cont1 v1) (cont2 v2)) ->
                 SinActionEquiv (SIfElse e1 ta1 fa1 cont1) (SIfElse e2 ta2 fa2 cont2)
  | SAEAssert: forall {k} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                      (cont1: SinActionT t1 k) (cont2: SinActionT t2 k),
                 (* ExprEquiv G e1 e2 -> *)
                 SinActionEquiv cont1 cont2 ->
                 SinActionEquiv (SAssert_ e1 cont1) (SAssert_ e2 cont2)
  | SAERet: forall {k} (e1: Expr t1 (SyntaxKind k))
                   (e2: Expr t2 (SyntaxKind k)),
              (* ExprEquiv G e1 e2 -> *)
              SinActionEquiv (SReturn e1) (SReturn e2).

  Lemma convSinToGen_Equiv GenK k a1 a2:
    SinActionEquiv (k := k) a1 a2 ->
    GenActionEquiv GenK (k := k) (convSinToGen false GenK a1) (convSinToGen false GenK a2).
  Proof.
    induction 1; intros; simpl in *; try (constructor; auto).
  Qed.
  
  Lemma appendSinGenAction_Equiv GenK kd d1 d2 k a1 a2:
    SinActionEquiv (k := kd) d1 d2 ->
    (forall v1 v2, GenActionEquiv GenK (k := k) (a1 v1) (a2 v2)) ->
    GenActionEquiv GenK (k := k)
                   (appendSinGenAction d1 a1) (appendSinGenAction d2 a2).
  Proof.
    induction 1; intros; simpl in *; try (constructor; auto); try apply convSinToGen_Equiv; auto.
  Qed.

  Lemma appendGenGenAction_Equiv GenK kd d1 d2 k a1 a2:
    GenActionEquiv GenK (k := kd) d1 d2 ->
    (forall v1 v2, GenActionEquiv GenK (k := k) (a1 v1) (a2 v2)) ->
    GenActionEquiv GenK (k := k)
                   (appendGenGenAction d1 a1) (appendGenGenAction d2 a2).
  Proof.
    induction 1; intros; simpl in *; try (constructor; auto); auto.
  Qed.
  
  Lemma appendSinSinAction_Equiv kd d1 d2 k a1 a2:
    SinActionEquiv (k := kd) d1 d2 ->
    (forall v1 v2, SinActionEquiv (k := k) (a1 v1) (a2 v2)) ->
    SinActionEquiv (k := k)
                   (appendSinSinAction d1 a1) (appendSinSinAction d2 a2).
  Proof.
    induction 1; intros; simpl in *; try (constructor; auto); auto.
  Qed.

  Lemma SinActionEquiv_ActionEquiv k:
    forall a1 a2,
      SinActionEquiv (k := k) a1 a2 ->
      ActionEquiv (getSinAction a1)
                  (getSinAction a2).
  Proof.
    intros.
    dependent induction H; simpl in *; constructor; intuition auto.
  Qed.

  Definition MetaRuleEquiv r :=
    match r with
      | OneRule b s => SinActionEquiv (b t1) (b t2)
      | RepRule _ _ _ GenK _ _ bgen s _ _ => GenActionEquiv GenK (bgen t1) (bgen t2)
    end.

  Inductive MetaRulesEquiv: list MetaRule -> Prop :=
  | MetaRulesEquivNil: MetaRulesEquiv nil
  | MetaRulesEquivCons:
      forall r,
        MetaRuleEquiv r ->
        forall rules,
          MetaRulesEquiv rules -> MetaRulesEquiv (r :: rules).

  Lemma MetaRulesEquiv_in:
    forall rules,
      MetaRulesEquiv rules <-> (forall r, In r rules -> MetaRuleEquiv r).
  Proof.
    intros; constructor.
    - induction 1; intros; intuition.
      inv H1; auto.
    - induction rules; intros; simpl in *; auto.
      + constructor.
      + assert (sth: forall r, In r rules -> MetaRuleEquiv r) by intuition.
        specialize (IHrules sth).
        assert (sth2: MetaRuleEquiv a) by intuition.
        constructor; auto.
  Qed.

  Lemma MetaRulesEquiv_app:
    forall r1 r2,
      MetaRulesEquiv r1 -> MetaRulesEquiv r2 -> MetaRulesEquiv (r1 ++ r2).
  Proof.
    induction r1; simpl; intros; auto.
    inv H; constructor; auto.
  Qed.

  Lemma MetaRulesEquiv_RulesEquiv rs:
    MetaRulesEquiv rs ->
    RulesEquiv t1 t2 (concat (map getListFromMetaRule rs)).
  Proof.
    intros.
    apply RulesEquiv_in; intros.
    pose proof (proj1 (MetaRulesEquiv_in rs) H) as sth; clear H.
    apply in_concat_iff in H0; dest.
    apply in_map_iff in H; dest.
    unfold getListFromMetaRule in H.
    specialize (sth _ H1).
    subst.
    destruct x0; simpl in *; auto.
    + destruct H0; [| intuition auto]; subst.
      apply SinActionEquiv_ActionEquiv; auto.
    + unfold repRule, getListFromRep in H0.
      apply in_map_iff in H0; dest; subst.
      apply GenActionEquiv_ActionEquiv; auto.
  Qed.
  
  Definition MetaMethEquiv r :=
    match r with
      | OneMeth b s => forall v1 v2, SinActionEquiv (projT2 b t1 v1) (projT2 b t2 v2)
      | RepMeth _ _ _ _ _ _ bgen s _ _ => forall v1 v2, GenActionEquiv _ (projT2 bgen t1 v1)
                                                                     (projT2 bgen t2 v2)
    end.

  Lemma inlineGenSinDm_Equiv GenK k a1 a2 dmName dmBody:
    GenActionEquiv GenK (k := k) a1 a2 ->
    MetaMethEquiv (OneMeth dmBody dmName) ->
    GenActionEquiv GenK (k := k) (inlineGenSinDm a1 (nameVal dmName) dmBody)
                   (inlineGenSinDm a2 (nameVal dmName) dmBody).
  Proof.
    simpl in *.
    induction 1; simpl in *; try (constructor; auto); intros.
    case_eq (getGenSinBody n (nameVal dmName) dmBody s); intros; simpl in *.
    - unfold getGenSinBody in H2.
      destruct n; simpl in *.
      destruct isRep; simpl in *;
      unfold andb in H2; simpl in *.
      + destruct (string_eq (nameVal nameRec) (nameVal dmName)); simpl in *; discriminate.
      + dest_str; simpl in *.
        * rewrite H3 in H2.
          rewrite string_eq_true in H2.
          destruct (SignatureT_dec (projT1 dmBody) s); [| discriminate].
          inv H2; simpl in *.
          constructor; auto; intros.
          simpl in *.
          apply appendSinGenAction_Equiv; auto.
        * apply string_eq_dec_false in H3.
          rewrite H3 in H2; discriminate.
    - constructor; auto.
  Qed.

  Lemma inlineGenGenDm_Equiv GenK k a1 a2 A strA goodFn1 getConstK goodFn2
        dmBody dmName ls noDup:
    GenActionEquiv GenK (k := k) a1 a2 ->
    MetaMethEquiv
      (@RepMeth A strA goodFn1 GenK getConstK goodFn2 dmBody dmName ls noDup) ->
    GenActionEquiv GenK (k := k) (inlineGenGenDm a1 (nameVal dmName) dmBody)
                   (inlineGenGenDm a2 (nameVal dmName) dmBody).
  Proof.
    simpl in *.
    induction 1; simpl in *; try (constructor; auto); intros.
    case_eq (getGenGenBody n (nameVal dmName) dmBody s); intros; simpl in *.
    - unfold getGenGenBody in H2; destruct n; simpl in *.
      destruct isRep; simpl in *; unfold andb in *; simpl in *.
      + dest_str; simpl in *.
        * rewrite H3 in H2.
          rewrite string_eq_true in H2.
          destruct (SignatureT_dec (projT1 dmBody) s); [| discriminate].
          inv H2; simpl in *.
          constructor; auto; intros.
          simpl in *.
          apply appendGenGenAction_Equiv; auto.
        * apply string_eq_dec_false in H3.
          rewrite H3 in *; discriminate.
      + destruct (string_eq (nameVal nameRec) (nameVal dmName)); simpl in *; discriminate.
    - constructor; auto.
  Qed.

  Lemma inlineSinSinDm_Equiv k a1 a2
        dmBody dmName:
    SinActionEquiv (k := k) a1 a2 ->
    MetaMethEquiv
      (@OneMeth dmBody dmName) ->
    SinActionEquiv (k := k) (inlineSinSinDm a1 (nameVal dmName) dmBody)
                   (inlineSinSinDm a2 (nameVal dmName) dmBody).
  Proof.
    induction 1; simpl in *; try (constructor; auto); intros.
    case_eq (getSinSinBody n (nameVal dmName) dmBody s); intros; simpl in *.
    - unfold getSinSinBody in H2; simpl in *.
      dest_str; simpl in *.
      * rewrite H3 in H2.
        rewrite string_eq_true in H2.
        destruct (SignatureT_dec (projT1 dmBody) s); [| discriminate].
        inv H2; simpl in *.
        constructor; auto; intros.
        simpl in *.
        apply appendSinSinAction_Equiv; auto.
      * apply string_eq_dec_false in H3.
        rewrite H3 in *; discriminate.
    - constructor; auto.
  Qed.

  Inductive MetaMethsEquiv: list MetaMeth -> Prop :=
  | MetaMethsEquivNil: MetaMethsEquiv nil
  | MetaMethsEquivCons:
      forall dm, MetaMethEquiv dm ->
                 forall meths,
                   MetaMethsEquiv meths -> MetaMethsEquiv (dm :: meths).

  Lemma MetaMethsEquiv_in:
    forall meths,
      MetaMethsEquiv meths <-> (forall m, In m meths -> MetaMethEquiv m).
  Proof.
    intros; constructor.
    - induction 1; intros; intuition.
      inv H1; auto.
    - induction meths; intros; simpl in *; auto.
      + constructor.
      + assert (sth: forall m, In m meths -> MetaMethEquiv m) by intuition.
        specialize (IHmeths sth).
        assert (sth2: MetaMethEquiv a) by intuition.
        constructor; auto.
  Qed.

  Lemma MetaMethsEquiv_app:
    forall r1 r2,
      MetaMethsEquiv r1 -> MetaMethsEquiv r2 -> MetaMethsEquiv (r1 ++ r2).
  Proof.
    induction r1; simpl; intros; auto.
    inv H; constructor; auto.
  Qed.

  Lemma MetaMethsEquiv_MethsEquiv rs:
    MetaMethsEquiv rs ->
    MethsEquiv t1 t2 (concat (map getListFromMetaMeth rs)).
  Proof.
    intros.
    apply MethsEquiv_in; intros.
    pose proof (proj1 (MetaMethsEquiv_in rs) H) as sth; clear H.
    apply in_concat_iff in H0; dest.
    apply in_map_iff in H; dest.
    unfold getListFromMetaMeth in H.
    specialize (sth _ H1).
    subst.
    destruct x0; simpl in *; auto.
    + destruct H0; [| intuition auto]; subst.
      unfold MethEquiv; intros; simpl in *.
      apply SinActionEquiv_ActionEquiv; auto.
    + unfold repMeth, getListFromRep in H0.
      apply in_map_iff in H0; dest; subst.
      unfold MethEquiv; intros; simpl in *.
      apply GenActionEquiv_ActionEquiv; auto.
  Qed.
  
  Definition MetaModEquiv m := MetaRulesEquiv (metaRules m) /\ MetaMethsEquiv (metaMeths m).

  Lemma metaModEquiv_modEquiv m:
    MetaModEquiv m -> ModEquiv t1 t2 (modFromMeta m).
  Proof.
    intros.
    destruct H.
    apply MetaRulesEquiv_RulesEquiv in H.
    apply MetaMethsEquiv_MethsEquiv in H0.
    constructor; auto.
  Qed.

  Lemma metaModEquiv_modular:
    forall m1 m2,
      MetaModEquiv m1 ->
      MetaModEquiv m2 ->
      MetaModEquiv (m1 +++ m2).
  Proof.
    destruct m1 as [r1 l1 d1], m2 as [r2 l2 d2]; simpl; intros.
    inv H; inv H0; simpl in *.
    constructor; simpl.
    - apply MetaRulesEquiv_app; auto.
    - apply MetaMethsEquiv_app; auto.
  Qed.

  Definition SinRuleEquiv r :=
    SinActionEquiv (ruleGen r t1) (ruleGen r t2).

  Inductive SinRulesEquiv: list SinRule -> Prop :=
  | SinRulesEquivNil: SinRulesEquiv nil
  | SinRulesEquivCons: forall r: SinRule, SinRuleEquiv r -> forall rules: list SinRule, SinRulesEquiv rules ->
                                                                                        SinRulesEquiv (r :: rules).

  Definition SinMethEquiv m :=
    forall (v1: t1 (arg (projT1 (methGen m)))) (v2: t2 (arg (projT1 (methGen m)))),
                SinActionEquiv (projT2 (methGen m) t1 v1) (projT2 (methGen m) t2 v2).

  Inductive SinMethsEquiv: list SinMeth -> Prop :=
  | SinMethsEquivNil: SinMethsEquiv nil
  | SinMethsEquivCons: forall m: SinMeth, SinMethEquiv m -> forall meths: list SinMeth, SinMethsEquiv meths ->
                                                                                        SinMethsEquiv (m :: meths).

  Fixpoint MetaModulesEquiv m :=
    match m with
      | MetaRegFile _ _ _ _ _ _ => MetaModEquiv (Build_MetaModule (metaModulesRegs m) (metaModulesRules m) (metaModulesMeths m))
      | MetaMod m' => MetaModEquiv m'
      | ConcatMetaMod m1 m2 => MetaModulesEquiv m1 /\ MetaModulesEquiv m2
      | RepeatSinMod _ _ _ _ _ _ _ _ m => SinRulesEquiv (sinRules m) /\ SinMethsEquiv (sinMeths m)
      | RepeatRegFile _ _ _ _ _ _ _ _ dataArray read write IdxBits Data init => True
    end.

  Lemma SinActionEquiv_GetGenActionEquiv A strA GenK getConstK (i: A):
    forall k (a1: SinActionT t1 k) (a2: SinActionT t2 k),
      SinActionEquiv a1 a2 ->
      ActionEquiv
        (getGenAction strA getConstK i (convSinToGen true GenK a1))
        (getGenAction strA getConstK i (convSinToGen true GenK a2)).
  Proof.
    induction 1; simpl; try constructor; auto; intros; simpl in *.
  Qed.
  
  Lemma SinRulesEquiv_RulesEquiv A strA GenK getConstK (i: A) rules:
    SinRulesEquiv rules ->
    RulesEquiv t1 t2
               (map
                  (fun sr : SinRule =>
                     (Indexer.addIndexToStr strA i (nameVal (ruleName sr))
                                            :: getActionFromGen strA getConstK
                                            (fun ty : Kind -> Type =>
                                               convSinToGen true GenK (ruleGen sr ty)) i)%struct)
                  rules).
  Proof.
    unfold getActionFromGen.
    induction rules; auto; simpl; intros; [constructor |].
    inv H.
    specialize (IHrules H3).
    constructor; auto.
    clear - H2.
    unfold SinRuleEquiv, RuleEquiv in *; simpl.
    eapply SinActionEquiv_GetGenActionEquiv in H2; eauto.
  Qed.

  Lemma SinMethsEquiv_MethsEquiv A strA GenK getConstK (i: A) meths:
    SinMethsEquiv meths ->
    MethsEquiv t1 t2
               (map
                  (fun sf : SinMeth =>
                     (Indexer.addIndexToStr strA i (nameVal (methName sf))
                                            :: getMethFromGen strA getConstK
                                            (existT (fun sig : SignatureT => GenMethodT GenK sig)
                                                    (projT1 (methGen sf))
                                                    (fun (ty : Kind -> Type)
                                                         (argv : ty (arg (projT1 (methGen sf)))) =>
                                                       convSinToGen true GenK (projT2 (methGen sf) ty argv))) i)%struct)
                  meths).
  Proof.
    unfold getMethFromGen.
    induction meths; auto; simpl; intros; [constructor |].
    inv H.
    specialize (IHmeths H3).
    constructor; auto.
    clear - H2.
    unfold SinMethEquiv, MethEquiv in *; simpl.
    intros.
    specialize (H2 arg1 arg2).
    eapply SinActionEquiv_GetGenActionEquiv in H2; eauto.
  Qed.

  Lemma metaModulesEquiv_modEquiv m:
    MetaModulesEquiv m -> ModEquiv t1 t2 (modFromMetaModules m).
  Proof.
    intros.
    induction m.
    - simpl in *.
      unfold ModEquiv; simpl in *.
      apply metaModEquiv_modEquiv in H; simpl in *.
      auto.
      simpl in *.
      inv H; simpl in *.
      split; auto.
      unfold getMethFromSin in *; simpl in *.
      inv H1.
      constructor; auto.
      clear - H4.
      induction read; concat_map_iff; auto.
      simpl in H4.
      inv H4.
      specialize (IHread H2).
      constructor; auto.
    - simpl in *.
      destruct m.
      apply metaModEquiv_modEquiv in H; simpl in *.
      auto.
    - simpl in *; dest.
      apply ModEquiv_modular; tauto.
    - simpl in *; dest.
      induction ls; simpl in *; auto.
      + repeat constructor.
      + inv noDupLs.
        specialize (IHls H4).
        apply ModEquiv_modular; auto.
        split; simpl in *.
        * eapply SinRulesEquiv_RulesEquiv; eauto.
        * eapply SinMethsEquiv_MethsEquiv; eauto.
    - simpl in *; dest.
      induction ls; simpl; auto.
      + constructor; simpl; auto; constructor.
      + inv noDupLs.
        specialize (IHls H3).
        destruct IHls.
        constructor; simpl; auto.
        constructor.
        constructor.
        intros.
        simpl in *.
        repeat constructor; auto.
        rewrite map_map.
        simpl in *.
        apply MethsEquiv_app; auto.
        clear H0 H1.
        induction read; simpl; auto; repeat constructor; auto.
  Qed.
End Equiv.

(* NOTE: Defining "MetaModPhoasWf" by Gallina definition affects proof automation by "kequiv". *)
Notation "'MetaModPhoasWf' m" := (forall ty1 ty2, MetaModEquiv ty1 ty2 m) (at level 0).
Notation "'MetaModulesPhoasWf' m" := (forall ty1 ty2, MetaModulesEquiv ty1 ty2 m) (at level 0).
