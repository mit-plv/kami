Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics.
Require Import Lib.ilist Lib.FMap Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* PHOAS equivalence *)
Section Equiv.
  Variable t1 t2: Kind -> Type.

  Definition ft1 := fullType t1.
  Definition ft2 := fullType t2.
  #[local] Hint Unfold ft1 ft2.

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
  | AEReadNondet: forall {k k1' k2'}
                         (cont1: fullType t1 k1' -> ActionT t1 k)
                         (cont2: fullType t2 k2' -> ActionT t2 k),
      (forall (v1: ft1 k1') (v2: ft2 k2'),
          ActionEquiv (cont1 v1) (cont2 v2)) ->
      ActionEquiv (ReadNondet _ cont1) (ReadNondet _ cont2)
  | AEReadReg: forall {k k1' k2'} rn
                      (cont1: fullType t1 k1' -> ActionT t1 k)
                      (cont2: fullType t2 k2' -> ActionT t2 k),
      (forall (v1: ft1 k1') (v2: ft2 k2'),
          ActionEquiv (cont1 v1) (cont2 v2)) ->
      ActionEquiv (ReadReg rn _ cont1) (ReadReg rn _ cont2)
  | AEWriteReg: forall {k k1' k2'} rn (e1: Expr t1 k1') (e2: Expr t2 k2')
                       (cont1: ActionT t1 k) (cont2: ActionT t2 k),
      ActionEquiv cont1 cont2 ->
      ActionEquiv (WriteReg rn e1 cont1) (WriteReg rn e2 cont2)
  | AEIfElse: forall {k k'} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                     (ta1 fa1: ActionT t1 k') (ta2 fa2: ActionT t2 k')
                     (cont1: t1 k' -> ActionT t1 k) (cont2: t2 k' -> ActionT t2 k),
      ActionEquiv ta1 ta2 -> ActionEquiv fa1 fa2 ->
      (forall (v1: ft1 (SyntaxKind k')) (v2: ft2 (SyntaxKind k')),
          ActionEquiv (cont1 v1) (cont2 v2)) ->
      ActionEquiv (IfElse e1 ta1 fa1 cont1) (IfElse e2 ta2 fa2 cont2)
  | AEAssert: forall {k} (e1: Expr t1 (SyntaxKind Bool)) (e2: Expr t2 (SyntaxKind Bool))
                     (cont1: ActionT t1 k) (cont2: ActionT t2 k),
      ActionEquiv cont1 cont2 ->
      ActionEquiv (Assert_ e1 cont1) (Assert_ e2 cont2)
  | AERet: forall {k} (e1: Expr t1 (SyntaxKind k))
                  (e2: Expr t2 (SyntaxKind k)),
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

(* NOTE: Defining "ModPhoasWf" by Gallina definition affects proof automation by "kequiv". *)
Notation "'ModPhoasWf' m" := (forall ty1 ty2, ModEquiv ty1 ty2 m) (at level 0).

Section EquivFacts.
  
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

  Lemma ModEquiv_flatten:
    forall t1 t2 m,
      ModEquiv t1 t2 m ->
      ModEquiv t1 t2 (Mod (getRegInits m) (getRules m) (getDefsBodies m)).
  Proof. auto. Qed.
  
  Lemma ModEquiv_deflatten:
    forall t1 t2 m,
      ModEquiv t1 t2 (Mod (getRegInits m) (getRules m) (getDefsBodies m)) ->
      ModEquiv t1 t2 m.
  Proof. auto. Qed.

End EquivFacts.

(* Valid register uses (reads and writes) *)
Section ValidRegs.
  Variable type: Kind -> Type.

  Section GivenRegs.
    Variable regs: list string.

    Inductive ValidRegsAction:
      forall {retT}, ActionT type retT -> Prop :=
    | VRMCall:
        forall name sig ar {retT} cont,
          (forall t, ValidRegsAction (cont t)) ->
          ValidRegsAction (MCall (lretT:= retT) name sig ar cont)
    | VRLet:
        forall {argT retT} ar cont,
          (forall t, ValidRegsAction (cont t)) ->
          ValidRegsAction (Let_ (lretT':= argT) (lretT:= retT) ar cont)
    | VRReadNondet:
        forall {retT} k cont,
          (forall t, ValidRegsAction (cont t)) ->
          ValidRegsAction (ReadNondet (lretT:= retT) k cont)
    | VRReadReg:
        forall {retT} reg k cont,
          In reg regs ->
          (forall t, ValidRegsAction (cont t)) ->
          ValidRegsAction (ReadReg (lretT:= retT) reg k cont)
    | VRWriteReg:
        forall {writeT retT} reg e cont,
          In reg regs ->
          ValidRegsAction cont ->
          ValidRegsAction (WriteReg (k:= writeT) (lretT:= retT)
                                    reg e cont)
    | VRIfElse:
        forall {retT1 retT2} ce (ta fa: ActionT type retT1)
               (cont: type retT1 -> ActionT type retT2),
          ValidRegsAction ta ->
          ValidRegsAction fa ->
          (forall t, ValidRegsAction (cont t)) ->
          ValidRegsAction (IfElse ce ta fa cont)
    | VRAssert:
        forall {retT} e cont,
          ValidRegsAction cont ->
          ValidRegsAction (Assert_ (lretT:= retT) e cont)
    | VRReturn:
        forall {retT} (e: Expr type (SyntaxKind retT)),
          ValidRegsAction (Return e).

    Inductive ValidRegsRules: list (Attribute (Action Void)) -> Prop :=
    | ValidRegsRulesNil: ValidRegsRules nil
    | ValidRegsRulesCons:
        forall rule rules,
          ValidRegsRules rules ->
          ValidRegsAction ((attrType rule) type) ->
          ValidRegsRules (rule :: rules).

    Lemma validRegsRules_app:
      forall r1 r2,
        ValidRegsRules r1 -> ValidRegsRules r2 ->
        ValidRegsRules (r1 ++ r2).
    Proof.
      induction r1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

    Inductive ValidRegsDms: list DefMethT -> Prop :=
    | ValidRegsDmsNil: ValidRegsDms nil
    | ValidRegsDmsCons:
        forall (dm: DefMethT) dms,
          ValidRegsDms dms ->
          (forall argV,
              ValidRegsAction (projT2 (attrType dm) type argV)) ->
          ValidRegsDms (dm :: dms).

    Lemma validRegsDms_app:
      forall dms1 dms2,
        ValidRegsDms dms1 -> ValidRegsDms dms2 ->
        ValidRegsDms (dms1 ++ dms2).
    Proof.
      induction dms1; simpl; intros; auto.
      inv H; constructor; auto.
    Qed.

  End GivenRegs.

  Fixpoint ValidRegsModules (m: Modules): Prop :=
    match m with
    | PrimMod _ =>
      ValidRegsRules (namesOf (getRegInits m)) (getRules m) /\
      ValidRegsDms (namesOf (getRegInits m)) (getDefsBodies m)
    | Mod regs rules dms =>
      ValidRegsRules (namesOf regs) rules /\
      ValidRegsDms (namesOf regs) dms
    | ConcatMod ma mb =>
      ValidRegsModules ma /\ ValidRegsModules mb
    end.

End ValidRegs.

(* NOTE: Defining "ModRegsWf" by Gallina definition affects proof automation by "kvr". *)
Notation "'ModRegsWf' m" := (forall ty, ValidRegsModules ty m) (at level 0).

Section ValidRegsFacts.

  Lemma validRegsAction_regs_weakening:
    forall {retT type} (a: ActionT type retT) regs,
      ValidRegsAction regs a ->
      forall regs',
        SubList regs regs' ->
        ValidRegsAction regs' a.
  Proof.
    induction 1; simpl; intros; try (constructor; auto).
  Qed.

  Lemma validRegsRules_regs_weakening:
    forall type regs rules,
      ValidRegsRules type regs rules ->
      forall regs',
        SubList regs regs' ->
        ValidRegsRules type regs' rules.
  Proof.
    induction 1; simpl; intros; [constructor|].
    constructor; auto.
    eapply validRegsAction_regs_weakening; eauto.
  Qed.

  Lemma validRegsDms_regs_weakening:
    forall type regs dms,
      ValidRegsDms type regs dms ->
      forall regs',
        SubList regs regs' ->
        ValidRegsDms type regs' dms.
  Proof.
    induction 1; simpl; intros; [constructor|].
    constructor; auto.
    intros; eapply validRegsAction_regs_weakening; eauto.
  Qed.

  Lemma validRegsRules_rules_app:
    forall type regs rules1 rules2,
      ValidRegsRules type regs rules1 ->
      ValidRegsRules type regs rules2 ->
      ValidRegsRules type regs (rules1 ++ rules2).
  Proof.
    induction 1; simpl; intros; auto.
    constructor; auto.
  Qed.

  Lemma validRegsModules_validRegsRules:
    forall type m,
      ValidRegsModules type m ->
      ValidRegsRules type (namesOf (getRegInits m)) (getRules m).
  Proof.
    induction m; simpl; intros; intuition.
    apply validRegsRules_rules_app.
    - eapply validRegsRules_regs_weakening; eauto.
      unfold namesOf; simpl; rewrite map_app; apply SubList_app_1, SubList_refl.
    - eapply validRegsRules_regs_weakening; eauto.
      unfold namesOf; simpl; rewrite map_app; apply SubList_app_2, SubList_refl.
  Qed.

  Lemma validRegsDms_dms_app:
    forall type regs dms1 dms2,
      ValidRegsDms type regs dms1 ->
      ValidRegsDms type regs dms2 ->
      ValidRegsDms type regs (dms1 ++ dms2).
  Proof.
    induction 1; simpl; intros; auto.
    constructor; auto.
  Qed.

  Lemma validRegsModules_validRegsDms:
    forall type m,
      ValidRegsModules type m ->
      ValidRegsDms type (namesOf (getRegInits m)) (getDefsBodies m).
  Proof.
    induction m; simpl; intros; intuition.
    apply validRegsDms_dms_app.
    - eapply validRegsDms_regs_weakening; eauto.
      unfold namesOf; simpl; rewrite map_app; apply SubList_app_1, SubList_refl.
    - eapply validRegsDms_regs_weakening; eauto.
      unfold namesOf; simpl; rewrite map_app; apply SubList_app_2, SubList_refl.
  Qed.

  Lemma validRegsRules_rule:
    forall type regs rules,
      ValidRegsRules type regs rules ->
      forall rn rb,
        In (rn :: rb)%struct rules ->
        ValidRegsAction regs (rb type).
  Proof.
    induction 1; simpl; intros; [inv H|].
    inv H1; eauto.
  Qed.

  Lemma validRegsRules_weakening:
    forall type regs rules,
      ValidRegsRules type regs rules ->
      forall rules',
        SubList rules' rules ->
        ValidRegsRules type regs rules'.
  Proof.
    induction rules'; simpl; intros; [constructor|].
    constructor.
    - apply IHrules'.
      apply SubList_cons_inv in H0; dest; auto.
    - eapply validRegsRules_rule with (rn:= attrName a); eauto using H.
      apply H0; left; destruct a; auto.
  Qed.

  Lemma validRegsDms_dm:
    forall type regs dms,
      ValidRegsDms type regs dms ->
      forall dm argV,
        In dm dms ->
        ValidRegsAction regs (projT2 (attrType dm) type argV).
  Proof.
    induction 1; simpl; intros; [inv H|].
    inv H1; eauto.
  Qed.

  Lemma validRegsDms_weakening:
    forall type regs dms,
      ValidRegsDms type regs dms ->
      forall dms',
        SubList dms' dms ->
        ValidRegsDms type regs dms'.
  Proof.
    induction dms'; simpl; intros; [constructor|].
    constructor.
    - apply IHdms'.
      apply SubList_cons_inv in H0; dest; auto.
    - intros; eapply validRegsDms_dm; eauto.
      intuition.
  Qed.
  
  Lemma validRegsAction_old_regs_restrict:
    forall regs {retT} (a: ActionT type retT),
      ValidRegsAction regs a ->
      forall or u calls retV,
        SemAction or a u calls retV ->
        SemAction (M.restrict or regs) a u calls retV.
  Proof.
    induction 1; simpl; intros.
    - inv H1; destruct_existT; econstructor; eauto.
    - inv H1; destruct_existT; econstructor; eauto.
    - inv H1; destruct_existT; econstructor; eauto.
    - inv H2; destruct_existT; econstructor; eauto.
      findeq.
    - inv H1; destruct_existT; econstructor; eauto.
    - inv H3; destruct_existT;
        [eapply SemIfElseTrue|eapply SemIfElseFalse]; eauto.
    - inv H0; destruct_existT; econstructor; eauto.
    - inv H; destruct_existT; econstructor; eauto.
  Qed.

  Lemma validRegsAction_new_regs_subset:
    forall regs {retT} (a: ActionT type retT),
      ValidRegsAction regs a ->
      forall or u calls retV,
        SemAction or a u calls retV ->
        M.KeysSubset u regs.
  Proof.
    induction 1; simpl; intros.
    - inv H1; destruct_existT; eapply H0; eauto.
    - inv H1; destruct_existT; eapply H0; eauto.
    - inv H1; destruct_existT; eapply H0; eauto.
    - inv H2; destruct_existT; eapply H1; eauto.
    - inv H1; destruct_existT.
      apply M.KeysSubset_add; auto.
      eapply IHValidRegsAction; eauto.
    - inv H3; destruct_existT.
      + apply M.KeysSubset_union; auto.
        * eapply IHValidRegsAction1; eauto.
        * eapply H2; eauto.
      + apply M.KeysSubset_union; auto.
        * eapply IHValidRegsAction2; eauto.
        * eapply H2; eauto.
    - inv H0; destruct_existT; eapply IHValidRegsAction; eauto.
    - inv H; destruct_existT; apply M.KeysSubset_empty.
  Qed.

  Lemma validRegsModules_substep_new_regs_subset:
    forall m,
      ValidRegsModules type m ->
      forall or u ul cs,
        Substep m or u ul cs ->
        M.KeysSubset u (namesOf (getRegInits m)).
  Proof.
    induction 2; simpl; intros.
    - apply M.KeysSubset_empty.
    - apply M.KeysSubset_empty.
    - apply validRegsModules_validRegsRules in H.
      eapply validRegsAction_new_regs_subset; eauto.
      + eapply validRegsRules_rule; eauto.
    - apply validRegsModules_validRegsDms in H.
      eapply validRegsAction_new_regs_subset; eauto.
      eapply validRegsDms_dm; eauto.
  Qed.

  Lemma validRegsModules_substepsInd_newregs_subset:
    forall m,
      ValidRegsModules type m ->
      forall or u l,
        SubstepsInd m or u l ->
        M.KeysSubset u (namesOf (getRegInits m)).
  Proof.
    induction 2; simpl; intros; [apply M.KeysSubset_empty|].
    subst; apply M.KeysSubset_union; auto.
    eapply validRegsModules_substep_new_regs_subset; eauto.
  Qed.

  Lemma validRegsModules_stepInd_newregs_subset:
    forall m,
      ValidRegsModules type m ->
      forall or u l,
        StepInd m or u l ->
        M.KeysSubset u (namesOf (getRegInits m)).
  Proof.
    induction 2; simpl; intros; auto.
    eapply validRegsModules_substepsInd_newregs_subset; eauto.
  Qed.

  Lemma validRegsModules_step_newregs_subset:
    forall m,
      ValidRegsModules type m ->
      forall or u l,
        Step m or u l ->
        M.KeysSubset u (namesOf (getRegInits m)).
  Proof.
    intros; apply step_consistent in H0.
    eapply validRegsModules_stepInd_newregs_subset; eauto.
  Qed.

  Lemma validRegsModules_multistep_newregs_subset:
    forall m,
      ValidRegsModules type m ->
      forall or u ll,
        Multistep m or u ll ->
        or = initRegs (getRegInits m) ->
        M.KeysSubset u (namesOf (getRegInits m)).
  Proof.
    induction 2; simpl; intros.
    - do 2 subst; rewrite rawInitRegs_namesOf; apply makeMap_KeysSubset.
    - apply M.KeysSubset_union; auto.
      apply step_consistent in HStep.
      eapply validRegsModules_stepInd_newregs_subset; eauto.
  Qed.

  Lemma validRegsModules_flatten:
    forall ty m,
      ValidRegsModules ty m ->
      ValidRegsModules ty (Syntax.Mod (getRegInits m) (getRules m) (getDefsBodies m)).
  Proof.
    induction m; simpl; intros; auto.
    dest; specialize (IHm1 H); specialize (IHm2 H0).
    inv IHm1; inv IHm2.
    split.
    - apply validRegsRules_app.
      + eapply validRegsRules_regs_weakening; eauto.
        unfold RegInitT; rewrite namesOf_app.
        apply SubList_app_1, SubList_refl.
      + eapply validRegsRules_regs_weakening; eauto.
        unfold RegInitT; rewrite namesOf_app.
        apply SubList_app_2, SubList_refl.
    - apply validRegsDms_app.
      + eapply validRegsDms_regs_weakening; eauto.
        unfold RegInitT; rewrite namesOf_app.
        apply SubList_app_1, SubList_refl.
      + eapply validRegsDms_regs_weakening; eauto.
        unfold RegInitT; rewrite namesOf_app.
        apply SubList_app_2, SubList_refl.
  Qed.

End ValidRegsFacts.

