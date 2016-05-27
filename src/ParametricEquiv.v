Require Import ParametricSyntax Syntax List Lib.CommonTactics Equiv.

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
  
  Definition MetaMethEquiv r :=
    match r with
      | OneMeth b s => forall v1 v2, SinActionEquiv (projT2 b t1 v1) (projT2 b t2 v2)
      | RepMeth _ _ _ _ _ _ bgen s _ _ => forall v1 v2, GenActionEquiv _ (projT2 bgen t1 v1)
                                                                     (projT2 bgen t2 v2)
    end.

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
  
  Definition MetaModEquiv m := MetaRulesEquiv (metaRules m) /\ MetaMethsEquiv (metaMeths m).

  Lemma metaModEquiv_modEquiv m:
    MetaModEquiv m -> ModEquiv t1 t2 (makeModule m).
  Proof.
    admit.
  Qed.
End Equiv.
