Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics.
Require Import Lib.StringBound Lib.ilist Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.SemanticsExprAction Lts.Semantics Lts.Equiv.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* Well-formedness w.r.t. valid register uses (read/writes) *)
Section ValidRegs.
  Variable type: Kind -> Type.

  Section Regs.
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

  End Regs.

  Fixpoint ValidRegsModules (m: Modules): Prop :=
    match m with
    | Mod regs rules dms =>
      ValidRegsRules (namesOf regs) rules /\
      ValidRegsDms (namesOf regs) dms
    | ConcatMod ma mb =>
      ValidRegsModules ma /\ ValidRegsModules mb
    end.

End ValidRegs.

Section Facts.

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
      + exact HAction.
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
    - do 2 subst; apply makeMap_KeysSubset.
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

End Facts.

