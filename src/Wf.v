Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax SemanticsExprAction Equiv.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* Well-formedness w.r.t. structural hazards:
 * 1) No double-writes and 2) No double-calls for all actions in Modules
 *)
Section WfInd.
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
    apply SubList_cons; auto.
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
    apply SubList_cons; auto.
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
        (forall argV, WfAction nil nil (objVal (attrType dm) type argV)) ->
        WfDms (dm :: dms).

  Lemma wfDms_dms:
    forall dms,
      WfDms dms ->
      forall dm argV,
        In dm dms ->
        WfAction nil nil (objVal (attrType dm) type argV).
  Proof.
    induction dms; intros; inv H0.
    - inv H; auto.
    - inv H; eapply IHdms; eauto.
  Qed.

  Inductive WfModules: Modules -> Prop :=
  | WfMod:
      forall regs rules dms,
        WfRules rules -> WfDms dms -> WfModules (Mod regs rules dms)
  | WfConcatMod:
      forall m1 m2,
        WfModules m1 -> WfModules m2 -> WfModules (ConcatMod m1 m2).
    
End WfInd.

Section WfEval.
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
            if in_dec string_dec name cc then false
            else wfActionC wr (name :: cc) (cont tt) n
          | Let_ _ _ cont => wfActionC wr cc (cont (getUT _)) n
          | ReadReg _ _ cont => wfActionC wr cc (cont (getUT _)) n
          | WriteReg reg _ _ cont =>
            if in_dec string_dec reg wr then false
            else wfActionC (reg :: wr) cc cont n
          | IfElse _ _ ta fa cont =>
            wfActionC wr cc (appendAction ta cont) n && wfActionC wr cc (appendAction fa cont) n
          | Assert_ _ cont => wfActionC wr cc cont n
          | Return _ => true
        end
    end.

  Definition wfAction {retT} (a: ActionT typeUT retT) := wfActionC nil nil a (maxPathLength a).

  Lemma wfActionC_WfAction:
    forall {retT type} aU (aT: ActionT type retT) {G} (Hequiv: ActionEquiv G aU aT)
           wr cc cdn,
      wfActionC wr cc aU cdn = true -> WfAction wr cc aT.
  Proof.
    induction 1; intros; try (destruct cdn; simpl in *; [discriminate|]);
    try (constructor; eauto; fail).

    - destruct (in_dec _ n cc); [discriminate|].
      constructor; eauto.
    - destruct (in_dec _ rn wr); [discriminate|].
      constructor; eauto.
    - apply andb_true_iff in H2; dest.
      constructor; admit.
  Qed.

  Lemma wfAction_WfAction:
    forall {retT type} aU (aT: ActionT type retT) (Hequiv: ActionEquiv nil aU aT),
      wfAction aU = true -> WfAction nil nil aT.
  Proof. intros; eapply wfActionC_WfAction; eauto. Qed.

  Fixpoint wfRules (rules: list (Attribute (Action Void))) :=
    match rules with
      | nil => true
      | rule :: rules' =>
        wfAction ((attrType rule) typeUT) && wfRules rules'
    end.

  Fixpoint wfDms (dms: list DefMethT) :=
    match dms with
      | nil => true
      | dm :: dms' =>
        wfAction (objVal (attrType dm) typeUT tt) && wfDms dms'
    end.

  Fixpoint wfModules (m: Modules) :=
    match m with
      | Mod _ rules dms => wfRules rules && wfDms dms
      | ConcatMod m1 m2 => wfModules m1 && wfModules m2
    end.

  Lemma wfModules_WfModules:
    forall m type (Hequiv: ModEquiv typeUT type m),
      wfModules m = true -> WfModules type m.
  Proof.
    admit.
  Qed.

End WfEval.

Section SemProps.

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

End SemProps.

