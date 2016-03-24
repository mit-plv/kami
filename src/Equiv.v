Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax.

Set Implicit Arguments.

Section Context.
  Variable type: Type.
  Variables t1 t2: type -> Type.
  
  Definition ctxt := list { t : type & (t1 t * t2 t)%type }.
  Definition vars := existT (fun t => (t1 t * t2 t)%type).

End Context.

Implicit Arguments vars [type t1 t2 x].

Section Equiv.
  Variable t1 t2: Kind -> Type.

  Definition ft1 := fullType t1.
  Definition ft2 := fullType t2.
  Hint Unfold ft1 ft2.

  Inductive ExprEquiv: ctxt ft1 ft2 -> forall {k}, Expr t1 k -> Expr t2 k -> Prop :=
  | EEVar: forall G {k} (x1: fullType t1 k) (x2: fullType t2 k),
             In (vars (x1, x2)) G ->
             ExprEquiv G (Var _ _ x1) (Var _ _ x2)
  | EEConst: forall G {k} (c: ConstT k),
               ExprEquiv G (Const _ c) (Const _ c)
  | EEUniBool: forall G uop (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool)),
                 ExprEquiv G e1 e2 ->
                 ExprEquiv G (UniBool uop e1) (UniBool uop e2)
  | EEBinBool: forall G bop (e11 e12: Expr t1 (SyntaxKind Bool))
                      (e21 e22: Expr t2 (SyntaxKind Bool)),
                 ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
                 ExprEquiv G (BinBool bop e11 e12) (BinBool bop e21 e22)
  | EEUniBit: forall G {n1 n2} (uop: UniBitOp n1 n2)
                     (e1: Expr t1 (SyntaxKind (Bit n1))) (e2: Expr t2 (SyntaxKind (Bit n1))),
                ExprEquiv G e1 e2 ->
                ExprEquiv G (UniBit uop e1) (UniBit uop e2)
  | EEBinBit: forall G {n1 n2 n3} (bop: BinBitOp n1 n2 n3)
                     (e11: Expr t1 (SyntaxKind (Bit n1))) (e12: Expr t1 (SyntaxKind (Bit n2)))
                     (e21: Expr t2 (SyntaxKind (Bit n1))) (e22: Expr t2 (SyntaxKind (Bit n2))),
                ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
                ExprEquiv G (BinBit bop e11 e12) (BinBit bop e21 e22)
  | EEITE: forall G {k} (ce1: Expr t1 (SyntaxKind Bool)) (ce2: Expr t2 (SyntaxKind Bool))
                  (te1 fe1: Expr t1 k) (te2 fe2: Expr t2 k),
             ExprEquiv G ce1 ce2 -> ExprEquiv G te1 te2 -> ExprEquiv G fe1 fe2 ->
             ExprEquiv G (ITE ce1 te1 fe1) (ITE ce2 te2 fe2)
  | EEEq: forall G {k} (e11 e12: Expr t1 (SyntaxKind k)) (e21 e22: Expr t2 (SyntaxKind k)),
            ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
            ExprEquiv G (Eq e11 e12) (Eq e21 e22)
  | EEReadIndex: forall G {i k} (e11: Expr t1 (SyntaxKind (Bit i)))
                        (e12: Expr t1 (SyntaxKind (Vector k i)))
                        (e21: Expr t2 (SyntaxKind (Bit i)))
                        (e22: Expr t2 (SyntaxKind (Vector k i))),
                   ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 ->
                   ExprEquiv G (ReadIndex e11 e12) (ReadIndex e21 e22)
  | EEReadField: forall G {attrs} attr (e1: Expr t1 (SyntaxKind (Struct attrs)))
                        (e2: Expr t2 (SyntaxKind (Struct attrs))),
                   ExprEquiv G e1 e2 ->
                   ExprEquiv G (ReadField attr e1) (ReadField attr e2)
  | EEBuildVector: forall G {n k}
                          (v1: Vec (Expr t1 (SyntaxKind n)) k)
                          (v2: Vec (Expr t2 (SyntaxKind n)) k),
                     (forall w: word k, ExprEquiv G (evalVec v1 w) (evalVec v2 w)) ->
                     ExprEquiv G (BuildVector v1) (BuildVector v2)
  | EEBuildStruct: forall G {attrs: list (Attribute Kind)}
                          (s1: ilist (fun a => Expr t1 (SyntaxKind (attrType a))) attrs)
                          (s2: ilist (fun a => Expr t2 (SyntaxKind (attrType a))) attrs),
                     (forall a, In a attrs ->
                                forall (e1: Expr t1 (SyntaxKind (attrType a)))
                                       (e2: Expr t2 (SyntaxKind (attrType a))),
                                  ilist_In e1 s1 -> ilist_In e2 s2 ->
                                  ExprEquiv G e1 e2) ->
                     ExprEquiv G (BuildStruct s1) (BuildStruct s2)
  | EEUpdateVector: forall G {i k} (e11: Expr t1 (SyntaxKind (Vector k i)))
                           (e12: Expr t1 (SyntaxKind (Bit i)))
                           (e13: Expr t1 (SyntaxKind k))
                           (e21: Expr t2 (SyntaxKind (Vector k i)))
                           (e22: Expr t2 (SyntaxKind (Bit i)))
                           (e23: Expr t2 (SyntaxKind k)),
                      ExprEquiv G e11 e21 -> ExprEquiv G e12 e22 -> ExprEquiv G e13 e23 ->
                      ExprEquiv G (UpdateVector e11 e12 e13) (UpdateVector e21 e22 e23).

  Lemma ExprEquiv_ctxt:
    forall G1 G2 {k} (e1: Expr t1 k) e2,
      ExprEquiv G1 e1 e2 -> SubList G1 G2 -> ExprEquiv G2 e1 e2.
  Proof. induction 1; intros; constructor; auto. Qed.

  Inductive ActionEquiv: forall {k}, ctxt ft1 ft2 -> ActionT t1 k -> ActionT t2 k -> Prop :=
  | AEMCall: forall G {k} n s (e1: Expr t1 (SyntaxKind (arg s)))
                    (e2: Expr t2 (SyntaxKind (arg s)))
                    (cont1: t1 (ret s) -> ActionT t1 k)
                    (cont2: t2 (ret s) -> ActionT t2 k),
               (forall (v1: ft1 (SyntaxKind (ret s)))
                       (v2: ft2 (SyntaxKind (ret s))),
                  ActionEquiv (vars (v1, v2) :: G) (cont1 v1) (cont2 v2)) ->
               ActionEquiv G (MCall n s e1 cont1) (MCall n s e2 cont2)
  | AELet: forall G {k k'} (e1: Expr t1 k') (e2: Expr t2 k')
                  (cont1: fullType t1 k' -> ActionT t1 k)
                  (cont2: fullType t2 k' -> ActionT t2 k),
             (forall (v1: ft1 k') (v2: ft2 k'),
                ActionEquiv (vars (v1, v2) :: G) (cont1 v1) (cont2 v2)) ->
             ActionEquiv G (Let_ e1 cont1) (Let_ e2 cont2)
  | AEReadReg: forall G {k k'} rn
                      (cont1: fullType t1 k' -> ActionT t1 k)
                      (cont2: fullType t2 k' -> ActionT t2 k),
                 (forall (v1: ft1 k') (v2: ft2 k'),
                    ActionEquiv (vars (v1, v2) :: G) (cont1 v1) (cont2 v2)) ->
                 ActionEquiv G (ReadReg rn _ cont1) (ReadReg rn _ cont2)
  | AEWriteReg: forall G {k k'} rn (e1: Expr t1 k') (e2: Expr t2 k')
                       (cont1: ActionT t1 k) (cont2: ActionT t2 k),
                  ExprEquiv G e1 e2 -> ActionEquiv G cont1 cont2 ->
                  ActionEquiv G (WriteReg rn e1 cont1) (WriteReg rn e2 cont2)
  | AEIfElse: forall G {k k'} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                     (ta1 fa1: ActionT t1 k') (ta2 fa2: ActionT t2 k')
                     (cont1: t1 k' -> ActionT t1 k) (cont2: t2 k' -> ActionT t2 k),
                ExprEquiv G e1 e2 -> ActionEquiv G ta1 ta2 -> ActionEquiv G fa1 fa2 ->
                (forall (v1: ft1 (SyntaxKind k')) (v2: ft2 (SyntaxKind k')),
                   ActionEquiv (vars (v1, v2) :: G) (cont1 v1) (cont2 v2)) ->
                ActionEquiv G (IfElse e1 ta1 fa1 cont1) (IfElse e2 ta2 fa2 cont2)
  | AEAssert: forall G {k} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                     (cont1: ActionT t1 k) (cont2: ActionT t2 k),
                ExprEquiv G e1 e2 -> ActionEquiv G cont1 cont2 ->
                ActionEquiv G (Assert_ e1 cont1) (Assert_ e2 cont2)
  | AERet: forall G {k} (e1: Expr t1 (SyntaxKind k))
                  (e2: Expr t2 (SyntaxKind k)),
             ExprEquiv G e1 e2 ->
             ActionEquiv G (Return e1) (Return e2).

  Lemma ActionEquiv_ctxt:
    forall G1 {k} (a1: ActionT t1 k) a2,
      ActionEquiv G1 a1 a2 ->
      forall G2, SubList G1 G2 -> ActionEquiv G2 a1 a2.
  Proof.
    induction 1; intros.
    - constructor; intros.
      apply H0.
      unfold SubList; intros; inv H2; [left; reflexivity|right; auto].
    - constructor; intros.
      apply H0.
      unfold SubList; intros; inv H2; [left; reflexivity|right; auto].
    - constructor; intros.
      apply H0.
      unfold SubList; intros; inv H2; [left; reflexivity|right; auto].
    - constructor; intros.
      + eapply ExprEquiv_ctxt; eauto.
      + apply IHActionEquiv; auto.
    - constructor; auto.
      + eapply ExprEquiv_ctxt; eauto.
      + intros; apply H3.
        unfold SubList; intros; inv H5; [left; reflexivity|right; auto].
    - constructor; auto.
      eapply ExprEquiv_ctxt; eauto.
    - constructor; auto.
      eapply ExprEquiv_ctxt; eauto.
  Qed.

  Inductive RulesEquiv: list (Attribute (Action Void)) -> Prop :=
  | RulesEquivNil: RulesEquiv nil
  | RulesEquivCons:
      forall r ar,
        (forall G, ActionEquiv G (ar t1) (ar t2)) ->
        forall rules,
          RulesEquiv rules -> RulesEquiv ({| attrName:= r; attrType:= ar |} :: rules).

  Lemma RulesEquiv_in:
    forall rules r ar G
           (Hequiv: RulesEquiv rules)
           (Hin: In (r :: ar)%struct rules),
      ActionEquiv G (ar t1) (ar t2).
  Proof.
    induction 1; intros; inv Hin.
    - inv H0; auto.
    - apply IHHequiv; assumption.
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

  Inductive MethsEquiv: list DefMethT -> Prop :=
  | MethsEquivNil: MethsEquiv nil
  | MethsEquivCons:
      forall dmn dsig (dm: forall ty, ty (arg dsig) -> ActionT ty (ret dsig)),
        (forall (argV1: fullType t1 (SyntaxKind (arg dsig)))
                (argV2: fullType t2 (SyntaxKind (arg dsig))) G,
            ActionEquiv (vars (argV1, argV2) :: G)
                        (dm t1 argV1) (dm t2 argV2)) ->
        forall meths,
          MethsEquiv meths -> MethsEquiv ({| attrName := dmn;
                                             attrType := existT _ dsig dm
                                          |} :: meths).

  Lemma MethsEquiv_in:
    forall meths m
           (Hequiv: MethsEquiv meths)
           (Hin: In m meths),
    forall (v1: ft1 (SyntaxKind (arg (projT1 (attrType m)))))
           (v2: ft2 (SyntaxKind (arg (projT1 (attrType m))))) G,
      ActionEquiv (vars (v1, v2) :: G)
                  (projT2 (attrType m) t1 v1) (projT2 (attrType m) t2 v2).
  Proof.
    induction 1; intros; inv Hin.
    - simpl in *; apply H.
    - apply IHHequiv; auto.
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
    intros; pose proof (MethsEquiv_in _ H H0); auto.
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
           {retT1} G (a11: ActionT type1 retT1) (a21: ActionT type2 retT1)
           (Hequiv1: ActionEquiv G a11 a21)
           {retT2} (a12: type1 retT1 -> ActionT type1 retT2)
           (a22: type2 retT1 -> ActionT type2 retT2)
           (Hequiv2: forall (argV1: ft1 type1 (SyntaxKind retT1))
                            (argV2: ft2 type2 (SyntaxKind retT1)),
                       ActionEquiv (vars (argV1, argV2) :: G) (a12 argV1) (a22 argV2)),
      ActionEquiv G (appendAction a11 a12) (appendAction a21 a22).
  Proof.
    induction 1; intros; try (simpl; constructor; intros; eauto).

    - eapply H0; eauto.
      intros; eapply ActionEquiv_ctxt; eauto.
      unfold SubList; intros; inv H1; intuition.
    - eapply H0; eauto.
      intros; eapply ActionEquiv_ctxt; eauto.
      unfold SubList; intros; inv H1; intuition.
    - eapply H0; eauto.
      intros; eapply ActionEquiv_ctxt; eauto.
      unfold SubList; intros; inv H1; intuition.
    - eapply H1; eauto.
      intros; eapply ActionEquiv_ctxt; eauto.
      unfold SubList; intros; inv H2; intuition.
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

Ltac equiv_tac_with tac :=
  repeat
    (repeat autounfold with MethDefs;
     try tac;
     match goal with
     | [ |- ModEquiv _ _ _ ] => constructor; intros
     | [ |- RulesEquiv _ _ _ ] => constructor; intros
     | [ |- MethsEquiv _ _ _ ] => constructor; intros
     | [ |- ActionEquiv _ _ _ ] => constructor; intros
     | [ |- ExprEquiv _ _ _ ] => constructor; intros
     | [ |- @ExprEquiv _ _ _ ?fk (ReadField ?a _) (ReadField ?a _) ] =>
       change fk with (SyntaxKind (GetAttrType a)); constructor; intros
     | [ |- In _ _] => simpl; tauto
     end).

Ltac equiv_tac := equiv_tac_with idtac.

