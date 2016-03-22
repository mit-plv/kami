Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics.
Require Import Lib.StringBound Lib.ilist Lib.FMap Lib.StringEq.
Require Import Syntax SemanticsExprAction Semantics Equiv.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* Well-formedness w.r.t. structural hazards:
 * 1) No double-writes and 2) No double-calls for all actions in Modules
 *)
Section WfInd1.
  Variable type: Kind -> Type.

  Inductive WfAction: list string -> list string -> forall {retT}, ActionT type retT -> Prop :=
  | WfMCall:
      forall regs calls name sig ar {retT} cont (Hnin: ~ In name calls),
        (forall t, WfAction regs (name :: calls) (cont t)) ->
        WfAction regs calls (MCall (lretT:= retT) name sig ar cont)
  | WfLet:
      forall regs calls {argT retT} ar cont,
        (forall t, WfAction regs calls (cont t)) ->
        WfAction regs calls (Let_ (lretT':= argT) (lretT:= retT) ar cont)
  | WfReadReg:
      forall regs calls {retT} reg k cont,
        (forall t, WfAction regs calls (cont t)) ->
        WfAction regs calls (ReadReg (lretT:= retT) reg k cont)
  | WfWriteReg:
      forall regs calls {writeT retT} reg e cont (Hnin: ~ In reg regs),
        WfAction (reg :: regs) calls cont ->
        WfAction regs calls (WriteReg (k:= writeT) (lretT:= retT) reg e cont)
  | WfIfElse:
      forall regs calls {retT1 retT2} ce ta fa cont,
        WfAction regs calls (appendAction (retT1:= retT1) (retT2:= retT2) ta cont) ->
        WfAction regs calls (appendAction (retT1:= retT1) (retT2:= retT2) fa cont) ->
        WfAction regs calls (IfElse ce ta fa cont)
  | WfAssert:
      forall regs calls {retT} e cont,
        WfAction regs calls cont ->
        WfAction regs calls (Assert_ (lretT:= retT) e cont)
  | WfReturn:
      forall regs calls {retT} (e: Expr type (SyntaxKind retT)), WfAction regs calls (Return e).

  Lemma wfAction_regs_weakening:
    forall {retK} (a: ActionT type retK) r1 c,
      WfAction r1 c a ->
      forall r2,
        SubList r2 r1 ->
        WfAction r2 c a.
  Proof.
    induction 1; intros; simpl in *; constructor; auto.

    apply IHWfAction.
    apply SubList_cons; intuition.
    unfold SubList; intros; right; auto.
  Qed.

  Lemma wfAction_calls_weakening:
    forall {retK} (a: ActionT type retK) r c1,
      WfAction r c1 a ->
      forall c2,
        SubList c2 c1 ->
        WfAction r c2 a.
  Proof.
    induction 1; intros; simpl in *; constructor; auto.

    intros; apply H0.
    apply SubList_cons; intuition.
    unfold SubList; intros; right; auto.
  Qed.

  Inductive WfRules: list (Attribute (Action Void)) -> Prop :=
  | WfRulesNil: WfRules nil
  | WfRulesCons:
      forall rule rules,
        WfRules rules ->
        WfAction nil nil ((attrType rule) type) ->
        WfRules (rule :: rules).

  Lemma wfRules_rule:
    forall rules,
      WfRules rules ->
      forall rn rb,
        In (rn :: rb)%struct rules ->
        WfAction nil nil (rb type).
  Proof.
    induction rules; intros; inv H0.
    - inv H; auto.
    - inv H; eapply IHrules; eauto.
  Qed.

  Inductive WfDms: list DefMethT -> Prop :=
  | WfDmsNil: WfDms nil
  | WfDmsCons:
      forall (dm: DefMethT) dms,
        WfDms dms ->
        (forall argV, WfAction nil nil (projT2 (attrType dm) type argV)) ->
        WfDms (dm :: dms).

  Lemma wfDms_dms:
    forall dms,
      WfDms dms ->
      forall dm argV,
        In dm dms ->
        WfAction nil nil (projT2 (attrType dm) type argV).
  Proof.
    induction dms; intros; inv H0.
    - inv H; auto.
    - inv H; eapply IHdms; eauto.
  Qed.

  Inductive WfModules: Modules -> Prop :=
  | WfIntro:
      forall m,
        WfRules (getRules m) -> WfDms (getDefsBodies m) ->
        WfModules m.
    
End WfInd1.

Section WfEval1.
  Variable type: Kind -> Type.
    
  Fixpoint maxPathLength {retT} (a: ActionT typeUT retT) :=
    match a with
      | MCall _ _ _ cont => S (maxPathLength (cont tt))
      | Let_ _ _ cont => S (maxPathLength (cont (getUT _)))
      | ReadReg _ _ cont => S (maxPathLength (cont (getUT _)))
      | WriteReg _ _ _ cont => S (maxPathLength cont)
      | IfElse _ _ ta fa cont =>
        S ((max (maxPathLength ta) (maxPathLength fa)) + (maxPathLength (cont tt)))
      | Assert_ _ cont => S (maxPathLength cont)
      | Return _ => S O
    end.
  
  Fixpoint wfActionC (wr cc: list string) {retT} (a: ActionT typeUT retT) (cdn: nat) :=
    match cdn with
    | O => false
    | S n =>
      match a with
      | MCall name _ _ cont =>
        (negb (string_in name cc)) && (wfActionC wr (name :: cc) (cont tt) n)
      | Let_ _ _ cont => wfActionC wr cc (cont (getUT _)) n
      | ReadReg _ _ cont => wfActionC wr cc (cont (getUT _)) n
      | WriteReg reg _ _ cont =>
        (negb (string_in reg wr)) && (wfActionC (reg :: wr) cc cont n)
      | IfElse _ _ ta fa cont =>
        wfActionC wr cc (appendAction ta cont) n && wfActionC wr cc (appendAction fa cont) n
      | Assert_ _ cont => wfActionC wr cc cont n
      | Return _ => true
      end
    end.

  Definition wfAction {retT} (a: ActionT typeUT retT) :=
    wfActionC nil nil a (maxPathLength a).

  Lemma wfActionC_WfAction_appendAction:
    forall G {retT retT'} (cont1: ft1 type (SyntaxKind retT) -> ActionT type retT')
           (cont2: ft2 typeUT (SyntaxKind retT) -> ActionT typeUT retT')
           (Hcequiv: forall v1 v2, ActionEquiv (vars (v1, v2) :: G) (cont1 v1) (cont2 v2))
           (Hcwf: forall v1 v2 wr cc cdn,
                    wfActionC wr cc (cont2 v2) cdn = true -> WfAction wr cc (cont1 v1)),
    forall a1 a2 (Hequiv: ActionEquiv G a1 a2),
    forall wr cc cdn,
      wfActionC wr cc (appendAction a2 cont2) cdn = true ->
      WfAction wr cc (appendAction a1 cont1).
  Proof.
    induction 3; intros; try (destruct cdn; simpl in *; [discriminate|]).

    - rewrite andb_true_iff in H1; dest.
      remember (string_in _ _) as sin; destruct sin; [discriminate|].
      apply string_in_dec_not_in in Heqsin.
      constructor; auto.
      intros; eapply H0; eauto.
      intros; eapply ActionEquiv_ctxt; eauto.
      unfold SubList; intros; inv H3; intuition.

    - constructor; auto.
      intros; eapply H0; eauto.
      intros; eapply ActionEquiv_ctxt; eauto.
      unfold SubList; intros; inv H2; intuition.

    - constructor; auto.
      intros; eapply H0; eauto.
      intros; eapply ActionEquiv_ctxt; eauto.
      unfold SubList; intros; inv H2; intuition.

    - rewrite andb_true_iff in H0; dest.
      remember (string_in _ _) as sin; destruct sin; [discriminate|].
      apply string_in_dec_not_in in Heqsin.
      constructor; eauto.

    - apply andb_true_iff in H2; dest.
      constructor.
      + eapply IHHequiv1; eauto.
        * intros; simpl.
          eapply actionEquiv_appendAction; eauto.
          intros; eapply ActionEquiv_ctxt; eauto.
          unfold SubList; intros; inv H4; intuition.
        * intros; simpl in H4.
          apply H1 with (v2:= v2) (cont2:= cont2) (cdn:= cdn0); auto.
          intros; eapply ActionEquiv_ctxt; eauto.
          unfold SubList; intros; inv H5; intuition.
      + eapply IHHequiv2; eauto.
        * intros; simpl.
          eapply actionEquiv_appendAction; eauto.
          intros; eapply ActionEquiv_ctxt; eauto.
          unfold SubList; intros; inv H4; intuition.
        * intros; simpl in H4.
          apply H1 with (v2:= v2) (cont2:= cont2) (cdn:= cdn0); auto.
          intros; eapply ActionEquiv_ctxt; eauto.
          unfold SubList; intros; inv H5; intuition.

    - constructor; eauto.
    - constructor; eauto.
  Qed.

  Lemma wfActionC_WfAction:
    forall {retT} aU (aT: ActionT type retT) {G} (Hequiv: ActionEquiv G aT aU)
           wr cc cdn,
      wfActionC wr cc aU cdn = true -> WfAction wr cc aT.
  Proof.
    induction 1; intros;
    try (destruct cdn; simpl in *; [discriminate|]);
    try (constructor; eauto; fail).

    - apply andb_true_iff in H1; dest.
      remember (string_in _ _) as sin; destruct sin; [discriminate|].
      apply string_in_dec_not_in in Heqsin.
      constructor; eauto.
    - apply andb_true_iff in H0; dest.
      remember (string_in _ _) as sin; destruct sin; [discriminate|].
      apply string_in_dec_not_in in Heqsin.
      constructor; eauto.
    - apply andb_true_iff in H2; dest.
      constructor; eapply wfActionC_WfAction_appendAction; eauto.
  Qed.

  Lemma wfAction_WfAction:
    forall {retT} aU (aT: ActionT type retT) G (Hequiv: ActionEquiv G aT aU),
      wfAction aU = true -> WfAction nil nil aT.
  Proof. intros; eapply wfActionC_WfAction; eauto. Qed.

  Fixpoint wfRules (rules: list (Attribute (Action Void))) :=
    match rules with
      | nil => true
      | rule :: rules' =>
        wfAction ((attrType rule) typeUT) && wfRules rules'
    end.

  Lemma wfRules_WfRules:
    forall rules,
      RulesEquiv type typeUT rules ->
      wfRules rules = true -> WfRules type rules.
  Proof.
    induction rules; simpl; intros; [constructor|].
    inv H; constructor; apply andb_true_iff in H0; dest; auto.
    simpl in *; eapply wfAction_WfAction with (G:= nil); eauto.
  Qed.

  Fixpoint wfDms (dms: list DefMethT) :=
    match dms with
      | nil => true
      | dm :: dms' =>
        wfAction (projT2 (attrType dm) typeUT tt) && wfDms dms'
    end.

  Lemma wfDms_WfDms:
    forall dms,
      MethsEquiv type typeUT dms ->
      wfDms dms = true -> WfDms type dms.
  Proof.
    induction dms; simpl; intros; [constructor|].
    inv H; constructor; apply andb_true_iff in H0; dest; auto.
    simpl in *; intros; eapply wfAction_WfAction; eauto.
    Grab Existential Variables.
    exact nil.
  Qed.

  Definition wfModules (m: Modules) :=
    wfRules (getRules m) && wfDms (getDefsBodies m).

  Lemma wfModules_WfModules:
    forall m (Hequiv: ModEquiv type typeUT m),
      wfModules m = true -> WfModules type m.
  Proof.
    intros; simpl in *.
    unfold wfModules in H; apply andb_true_iff in H; dest.
    inv Hequiv.
    constructor.
    - apply wfRules_WfRules; auto.
    - apply wfDms_WfDms; auto.
  Qed.

End WfEval1.

(* Well-formedness w.r.t. valid register uses (read/writes) *)
Section WfInd2.
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

    Inductive ValidRegsDms: list DefMethT -> Prop :=
    | ValidRegsDmsNil: ValidRegsDms nil
    | ValidRegsDmsCons:
        forall (dm: DefMethT) dms,
          ValidRegsDms dms ->
          (forall argV,
              ValidRegsAction (projT2 (attrType dm) type argV)) ->
          ValidRegsDms (dm :: dms).

  End Regs.

  Fixpoint ValidRegsModules (m: Modules): Prop :=
    match m with
    | Mod regs rules dms =>
      ValidRegsRules (namesOf regs) rules /\
      ValidRegsDms (namesOf regs) dms
    | ConcatMod ma mb =>
      ValidRegsModules ma /\ ValidRegsModules mb
    end.

End WfInd2.

Section SemProps1.

  Lemma wfAction_SemAction_calls:
    forall wr cc {retK} (a: ActionT type retK),
      WfAction wr cc a ->
      forall or u calls retV,
        SemAction or a u calls retV ->
        forall c,
          In c cc -> M.find c calls = None.
  Proof.
    induction 1; intros; simpl in *.
    - inv H1; destruct_existT.
      destruct (string_dec c name); [subst; elim Hnin; auto|].
      rewrite M.find_add_2 by assumption.
      eapply H0; eauto.
    - inv H1; destruct_existT; eapply H0; eauto.
    - inv H1; destruct_existT; eapply H0; eauto.
    - inv H0; destruct_existT; eapply IHWfAction; eauto.
    - inv H1; destruct_existT.
      + eapply IHWfAction1; eauto.
        eapply appendAction_SemAction; eauto.
      + eapply IHWfAction2; eauto.
        eapply appendAction_SemAction; eauto.
    - inv H0; destruct_existT; eapply IHWfAction; eauto.
    - inv H; destruct_existT; apply M.find_empty; auto.
  Qed.

  Lemma wfAction_appendAction_calls_1':
    forall wr cc {retT2} a3,
      WfAction wr cc a3 ->
      forall {retT1} (a1: ActionT type retT1)
             (a2: type retT1 -> ActionT type retT2),
        a3 = appendAction a1 a2 ->
        WfAction wr cc a1.
  Proof.
    induction 1; intros.
    - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
      econstructor; eauto.
    - destruct a1; simpl in *; try discriminate.
      + inv H1; destruct_existT; econstructor; eauto.
      + inv H1; destruct_existT; econstructor.
    - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
      econstructor; eauto.
    - destruct a1; simpl in *; try discriminate; inv H0; destruct_existT.
      econstructor; eauto.
    - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
      constructor.
      + eapply IHWfAction1; eauto; apply appendAction_assoc.
      + eapply IHWfAction2; eauto; apply appendAction_assoc.
    - destruct a1; simpl in *; try discriminate; inv H0; destruct_existT.
      econstructor; eauto.
    - destruct a1; simpl in *; try discriminate.
  Qed.

  Lemma wfAction_appendAction_calls_1:
    forall {retT1 retT2} (a1: ActionT type retT1)
           (a2: type retT1 -> ActionT type retT2) wr cc,
      WfAction wr cc (appendAction a1 a2) ->
      WfAction wr cc a1.
  Proof. intros; eapply wfAction_appendAction_calls_1'; eauto. Qed.

  Lemma wfAction_appendAction_calls_2':
    forall {retT2} wr cc a3,
      WfAction wr cc a3 ->
      forall {retT1} (a1: ActionT type retT1)
             (a2: type retT1 -> ActionT type retT2) retV1,
        a3 = appendAction a1 a2 ->
        WfAction wr cc (a2 retV1).
  Proof.
    induction 1; intros.

    - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
      eapply wfAction_calls_weakening with (c1:= meth :: calls); eauto.
      unfold SubList; intros; right; auto.
    - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
      + eapply H0; eauto.
      + apply H.
    - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
      eapply H0; eauto.
    - destruct a1; simpl in *; try discriminate; inv H0; destruct_existT.
      eapply wfAction_regs_weakening with (r1:= r :: regs); eauto.
      unfold SubList; intros; right; auto.
    - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
      eapply IHWfAction1; eauto.
      apply appendAction_assoc.
    - destruct a1; simpl in *; try discriminate; inv H0; destruct_existT.
      eapply IHWfAction; eauto.
    - destruct a1; simpl in *; try discriminate.

      Grab Existential Variables.
      { exact (evalConstFullT (getDefaultConstFull _)). }
      { exact (evalConstFullT (getDefaultConstFull _)). }
      { exact (evalConstT (getDefaultConst _)). }
  Qed.
  
  Lemma wfAction_appendAction_calls_2:
    forall {retT1 retT2} (a1: ActionT type retT1)
           (a2: type retT1 -> ActionT type retT2) retV1 wr cc,
      WfAction wr cc (appendAction a1 a2) ->
      WfAction wr cc (a2 retV1).
  Proof. intros; eapply wfAction_appendAction_calls_2'; eauto. Qed.

  Lemma wfAction_appendAction_calls_disj':
    forall {retT2} a3 wr cc,
      WfAction wr cc a3 ->
      forall {retT1} a1 a2,
        a3 = appendAction a1 a2 ->
        forall or newRegs1 newRegs2 calls1 calls2
               (retV1: type retT1) (retV2: type retT2),
          SemAction or a1 newRegs1 calls1 retV1 ->
          SemAction or (a2 retV1) newRegs2 calls2 retV2 ->
          M.Disj calls1 calls2.
  Proof.
    induction 1; intros; simpl; intuition idtac; destruct a1; simpl in *; try discriminate.
    unfold M.Disj; intros lb.
    
    - inv H1; destruct_existT.
      invertAction H2; specialize (H x).
      specialize (H0 _ _ _ _ eq_refl _ _ _ _ _ _ _ H1 H3 lb).
      destruct H0; [|right; assumption].
      destruct (string_dec lb meth); [subst; right|left].
      + pose proof (wfAction_appendAction_calls_2 _ _ retV1 H).
        apply M.F.P.F.not_find_in_iff.
        eapply wfAction_SemAction_calls; eauto.
        intuition.
      + apply M.F.P.F.not_find_in_iff.
        apply M.F.P.F.not_find_in_iff in H0.
        rewrite M.find_add_2; auto.
    - inv H1; destruct_existT; invertAction H2; eapply H0; eauto.
    - inv H1; destruct_existT; invertAction H2; apply M.Disj_empty_1.
    - inv H1; destruct_existT; invertAction H2; eapply H0; eauto.
    - inv H0; destruct_existT; invertAction H1; eapply IHWfAction; eauto.
    - inv H1; destruct_existT.
      invertAction H2.
      destruct (evalExpr e); dest; subst.
      + specialize (@IHWfAction1 _ (appendAction a1_1 a) a2 (appendAction_assoc _ _ _)).
        eapply IHWfAction1; eauto.
        eapply appendAction_SemAction; eauto.
      + specialize (@IHWfAction2 _ (appendAction a1_2 a) a2 (appendAction_assoc _ _ _)).
        eapply IHWfAction2; eauto.
        eapply appendAction_SemAction; eauto.
    - inv H0; destruct_existT; invertAction H1; eapply IHWfAction; eauto.
  Qed.

  Lemma wfAction_appendAction_calls_disj:
    forall {retT1 retT2} a1 a2 or newRegs1 calls1 (retV1: type retT1)
           newRegs2 calls2 (retV2: type retT2),
      WfAction nil nil (appendAction a1 a2) ->
      SemAction or a1 newRegs1 calls1 retV1 ->
      SemAction or (a2 retV1) newRegs2 calls2 retV2 ->
      M.Disj calls1 calls2.
  Proof. intros; eapply wfAction_appendAction_calls_disj'; eauto. Qed.

End SemProps1.

Section SemProps2.    

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
  
End SemProps2.


