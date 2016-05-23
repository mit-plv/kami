Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax.

Set Implicit Arguments.

Section Equiv.
  Variable t1 t2: Kind -> Type.

  Definition ft1 := fullType t1.
  Definition ft2 := fullType t2.
  Hint Unfold ft1 ft2.

  (*
  Inductive ExprEquiv: ctxt ft1 ft2 -> forall {k1 k2}, Expr t1 k1 -> Expr t2 k2 -> Prop :=
  | EEVar:
      forall G {k1 k2} (x1: fullType t1 k1) (x2: fullType t2 k2),
        In (vars x1 x2) G ->
        ExprEquiv G (Var _ _ x1) (Var _ _ x2)
  | EEConst:
      forall G {k1 k2} (c1: ConstT k1) (c2: ConstT k2),
        ExprEquiv G (Const _ c1) (Const _ c2)
  | EEUniBool:
      forall G uop (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool)),
        ExprEquiv G e1 e2 ->
        ExprEquiv G (UniBool uop e1) (UniBool uop e2)
  | EEBinBool:
      forall G bop (e11 e12: Expr t1 (SyntaxKind Bool))
             (e21 e22: Expr t2 (SyntaxKind Bool)),
        ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
        ExprEquiv G (BinBool bop e11 e12) (BinBool bop e21 e22)
  | EEUniBit:
      forall G {n1 n2} (uop: UniBitOp n1 n2)
             (e1: Expr t1 (SyntaxKind (Bit n1))) (e2: Expr t2 (SyntaxKind (Bit n1))),
        ExprEquiv G e1 e2 ->
        ExprEquiv G (UniBit uop e1) (UniBit uop e2)
  | EEBinBit:
      forall G {n1 n2 n3} (bop: BinBitOp n1 n2 n3)
             (e11: Expr t1 (SyntaxKind (Bit n1))) (e12: Expr t1 (SyntaxKind (Bit n2)))
             (e21: Expr t2 (SyntaxKind (Bit n1))) (e22: Expr t2 (SyntaxKind (Bit n2))),
        ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
        ExprEquiv G (BinBit bop e11 e12) (BinBit bop e21 e22)
  | EEBinBitBool:
      forall G {n1 n2} (bop: BinBitBoolOp n1 n2)
             (e11: Expr t1 (SyntaxKind (Bit n1))) (e12: Expr t1 (SyntaxKind (Bit n2)))
             (e21: Expr t2 (SyntaxKind (Bit n1))) (e22: Expr t2 (SyntaxKind (Bit n2))),
        ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
        ExprEquiv G (BinBitBool bop e11 e12) (BinBitBool bop e21 e22)
  | EEITE:
      forall G {k} (ce1: Expr t1 (SyntaxKind Bool)) (ce2: Expr t2 (SyntaxKind Bool))
             (te1 fe1: Expr t1 k) (te2 fe2: Expr t2 k),
        ExprEquiv G ce1 ce2 -> ExprEquiv G te1 te2 -> ExprEquiv G fe1 fe2 ->
        ExprEquiv G (ITE ce1 te1 fe1) (ITE ce2 te2 fe2)
  | EEEq:
      forall G {k} (e11 e12: Expr t1 (SyntaxKind k)) (e21 e22: Expr t2 (SyntaxKind k)),
        ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
        ExprEquiv G (Eq e11 e12) (Eq e21 e22)
  | EEReadIndex:
      forall G {i k} (e11: Expr t1 (SyntaxKind (Bit i)))
             (e12: Expr t1 (SyntaxKind (Vector k i)))
             (e21: Expr t2 (SyntaxKind (Bit i)))
             (e22: Expr t2 (SyntaxKind (Vector k i))),
        ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
        ExprEquiv G (ReadIndex e11 e12) (ReadIndex e21 e22)
  | EEReadField:
      forall G {attrs} attr (e1: Expr t1 (SyntaxKind (Struct attrs)))
             (e2: Expr t2 (SyntaxKind (Struct attrs))),
        ExprEquiv G e1 e2 ->
        ExprEquiv G (ReadField attr e1) (ReadField attr e2)
  | EEBuildVector:
      forall G {n k}
             (v1: Vec (Expr t1 (SyntaxKind n)) k)
             (v2: Vec (Expr t2 (SyntaxKind n)) k),
        (forall w: word k, ExprEquiv G (evalVec v1 w) (evalVec v2 w)) ->
        ExprEquiv G (BuildVector v1) (BuildVector v2)
  | EEBuildStruct:
      forall G {attrs: list (Attribute Kind)}
             (s1: ilist (fun a => Expr t1 (SyntaxKind (attrType a))) attrs)
             (s2: ilist (fun a => Expr t2 (SyntaxKind (attrType a))) attrs),
        (forall i a (Ha: Some a = nth_error attrs i)
                (e1: Expr t1 (SyntaxKind (attrType a)))
                (e2: Expr t2 (SyntaxKind (attrType a))),
            ith_error s1 i = match Ha with eq_refl => Dep_Some _ _ e1 end ->
            ith_error s2 i = match Ha with eq_refl => Dep_Some _ _ e2 end ->
            ExprEquiv G e1 e2) ->
        ExprEquiv G (BuildStruct s1) (BuildStruct s2)
  | EEUpdateVector:
      forall G {i k} (e11: Expr t1 (SyntaxKind (Vector k i)))
             (e12: Expr t1 (SyntaxKind (Bit i)))
             (e13: Expr t1 (SyntaxKind k))
             (e21: Expr t2 (SyntaxKind (Vector k i)))
             (e22: Expr t2 (SyntaxKind (Bit i)))
             (e23: Expr t2 (SyntaxKind k)),
        ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 -> ExprEquiv G e13 e23 ->
        ExprEquiv G (UpdateVector e11 e12 e13) (UpdateVector e21 e22 e23).
  *)

  Inductive ActionEquiv: forall {k}, ActionT t1 k -> ActionT t2 k -> Prop :=
  | AEMCall: forall {k} n s (e1: Expr t1 (SyntaxKind (arg s)))
                    (e2: Expr t2 (SyntaxKind (arg s)))
                    (cont1: t1 (ret s) -> ActionT t1 k)
                    (cont2: t2 (ret s) -> ActionT t2 k),
      (forall (v1: ft1 (SyntaxKind (ret s)))
              (v2: ft2 (SyntaxKind (ret s))),
          ActionEquiv (cont1 v1) (cont2 v2)) ->
      ActionEquiv (MCall n s e1 cont1) (MCall n s e2 cont2)
  | AELet: forall {k k1' k2'} (e1: Expr t1 k1') (e2: Expr t2 k2')
                  (cont1: fullType t1 k1' -> ActionT t1 k)
                  (cont2: fullType t2 k2' -> ActionT t2 k),
      (forall (v1: ft1 k1') (v2: ft2 k2'),
          ActionEquiv (cont1 v1) (cont2 v2)) ->
      ActionEquiv (Let_ e1 cont1) (Let_ e2 cont2)
  | AEReadReg: forall {k k1' k2'} rn
                      (cont1: fullType t1 k1' -> ActionT t1 k)
                      (cont2: fullType t2 k2' -> ActionT t2 k),
      (forall (v1: ft1 k1') (v2: ft2 k2'),
          ActionEquiv (cont1 v1) (cont2 v2)) ->
      ActionEquiv (ReadReg rn _ cont1) (ReadReg rn _ cont2)
  | AEWriteReg: forall {k k1' k2'} rn (e1: Expr t1 k1') (e2: Expr t2 k2')
                       (cont1: ActionT t1 k) (cont2: ActionT t2 k),
      (* ExprEquiv G e1 e2 -> *)
      ActionEquiv cont1 cont2 ->
      ActionEquiv (WriteReg rn e1 cont1) (WriteReg rn e2 cont2)
  | AEIfElse: forall {k k'} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                     (ta1 fa1: ActionT t1 k') (ta2 fa2: ActionT t2 k')
                     (cont1: t1 k' -> ActionT t1 k) (cont2: t2 k' -> ActionT t2 k),
      (* ExprEquiv G e1 e2 -> *)
      ActionEquiv ta1 ta2 -> ActionEquiv fa1 fa2 ->
      (forall (v1: ft1 (SyntaxKind k')) (v2: ft2 (SyntaxKind k')),
          ActionEquiv (cont1 v1) (cont2 v2)) ->
      ActionEquiv (IfElse e1 ta1 fa1 cont1) (IfElse e2 ta2 fa2 cont2)
  | AEAssert: forall {k} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                     (cont1: ActionT t1 k) (cont2: ActionT t2 k),
      (* ExprEquiv G e1 e2 -> *)
      ActionEquiv cont1 cont2 ->
      ActionEquiv (Assert_ e1 cont1) (Assert_ e2 cont2)
  | AERet: forall {k} (e1: Expr t1 (SyntaxKind k))
                  (e2: Expr t2 (SyntaxKind k)),
      (* ExprEquiv G e1 e2 -> *)
      ActionEquiv (Return e1) (Return e2).

  Definition RuleEquiv (r: Attribute (Action Void)) : Prop :=
    ActionEquiv (attrType r t1) (attrType r t2).
  
  Inductive RulesEquiv: list (Attribute (Action Void)) -> Prop :=
  | RulesEquivNil: RulesEquiv nil
  | RulesEquivCons:
      forall r,
        RuleEquiv r ->
        forall rules,
          RulesEquiv rules -> RulesEquiv (r :: rules).

  Lemma RulesEquiv_in:
    forall rules,
      RulesEquiv rules <-> (forall r, In r rules -> RuleEquiv r).
  Proof.
    intros; constructor.
    - induction 1; simpl in *; intros.
      + intuition.
      + destruct H1; subst; auto.
    - induction rules; intros; simpl in *.
      + constructor.
      + constructor; auto.
  Qed.

  Lemma RulesEquiv_sub:
    forall rules1 rules2,
      RulesEquiv rules1 ->
      SubList rules2 rules1 ->
      RulesEquiv rules2.
  Proof.
    induction rules2; simpl; intros; [constructor|].
    destruct a; constructor.
    - intros; eapply RulesEquiv_in.
      + exact H.
      + apply H0; left; auto.
    - apply IHrules2; auto.
      apply SubList_cons_inv in H0; dest; auto.
  Qed.

  Lemma RulesEquiv_app:
    forall rules1 rules2
           (Hequiv1: RulesEquiv rules1)
           (Hequiv2: RulesEquiv rules2),
      RulesEquiv (rules1 ++ rules2).
  Proof.
    induction rules1; intros; auto.
    simpl; inv Hequiv1.
    constructor; auto.
  Qed.

  Definition MethEquiv (dm: DefMethT) : Prop :=
    forall arg1 arg2,
      ActionEquiv (projT2 (attrType dm) t1 arg1) (projT2 (attrType dm) t2 arg2).

  Inductive MethsEquiv: list DefMethT -> Prop :=
  | MethsEquivNil: MethsEquiv nil
  | MethsEquivCons:
      forall dm, MethEquiv dm ->
                 forall meths,
                   MethsEquiv meths -> MethsEquiv (dm :: meths).

  Lemma MethsEquiv_in:
    forall meths,
      MethsEquiv meths <-> (forall m, In m meths -> MethEquiv m).
  Proof.
    intros; constructor.
    - induction 1; simpl in *; intros.
      + intuition.
      + destruct H1; subst; auto.
    - induction meths; intros; simpl in *.
      + constructor.
      + constructor; auto.
  Qed.

  Lemma MethsEquiv_sub:
    forall meths1 meths2,
      MethsEquiv meths1 ->
      SubList meths2 meths1 ->
      MethsEquiv meths2.
  Proof.
    induction meths2; simpl; intros; [constructor|].
    apply SubList_cons_inv in H0; dest.
    destruct a as [? [? ?]]; constructor; auto.
    intros; apply (MethsEquiv_in meths1); auto.
  Qed.

  Lemma MethsEquiv_app:
    forall meths1 meths2
           (Hequiv1: MethsEquiv meths1)
           (Hequiv2: MethsEquiv meths2),
      MethsEquiv (meths1 ++ meths2).
  Proof.
    induction meths1; intros; auto.
    simpl; inv Hequiv1.
    constructor; auto.
  Qed.

  Definition ModEquiv (m: Modules): Prop :=
    RulesEquiv (getRules m) /\ MethsEquiv (getDefsBodies m).
  
End Equiv.

Section Facts.
  Lemma actionEquiv_appendAction:
    forall type1 type2
           {retT1} (a11: ActionT type1 retT1) (a21: ActionT type2 retT1)
           (Hequiv1: ActionEquiv a11 a21)
           {retT2} (a12: type1 retT1 -> ActionT type1 retT2)
           (a22: type2 retT1 -> ActionT type2 retT2)
           (Hequiv2: forall (argV1: ft1 type1 (SyntaxKind retT1))
                            (argV2: ft2 type2 (SyntaxKind retT1)),
                       ActionEquiv (a12 argV1) (a22 argV2)),
      ActionEquiv (appendAction a11 a12) (appendAction a21 a22).
  Proof.
    induction 1; intros; try (simpl; constructor; intros; eauto).
  Qed.

  Lemma ModEquiv_split:
    forall t1 t2 m1 m2,
      ModEquiv t1 t2 (ConcatMod m1 m2) ->
      ModEquiv t1 t2 m1 /\ ModEquiv t1 t2 m2.
  Proof.
    intros; inv H; split.
    - constructor.
      + eapply RulesEquiv_sub; eauto.
        apply SubList_app_1, SubList_refl.
      + eapply MethsEquiv_sub; eauto.
        apply SubList_app_1, SubList_refl.
    - constructor.
      + eapply RulesEquiv_sub; eauto.
        apply SubList_app_2, SubList_refl.
      + eapply MethsEquiv_sub; eauto.
        apply SubList_app_2, SubList_refl.
  Qed.
      
  Lemma ModEquiv_modular:
    forall t1 t2 m1 m2,
      ModEquiv t1 t2 m1 ->
      ModEquiv t1 t2 m2 ->
      ModEquiv t1 t2 (ConcatMod m1 m2).
  Proof.
    intros; inv H; inv H0.
    constructor; simpl.
    - apply RulesEquiv_app; auto.
    - apply MethsEquiv_app; auto.
  Qed.

End Facts.

