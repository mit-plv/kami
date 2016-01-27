Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax Semantics Equiv.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* Well-formedness w.r.t. structural hazards:
 * 1) No double-writes and 2) No double-calls for all actions in Modules
 *)
Section WfInd.
  Variable type: Kind -> Type.

  Fixpoint appendAction {retT1 retT2} (a1: ActionT type retT1)
           (a2: type retT1 -> ActionT type retT2): ActionT type retT2 :=
    match a1 with
      | MCall name sig ar cont => MCall name sig ar (fun a => appendAction (cont a) a2)
      | Let_ _ ar cont => Let_ ar (fun a => appendAction (cont a) a2)
      | ReadReg reg k cont => ReadReg reg k (fun a => appendAction (cont a) a2)
      | WriteReg reg _ e cont => WriteReg reg e (appendAction cont a2)
      | IfElse ce _ ta fa cont => IfElse ce ta fa (fun a => appendAction (cont a) a2)
      | Assert_ ae cont => Assert_ ae (appendAction cont a2)
      | Return e => Let_ e a2
    end.

  Lemma appendAction_assoc:
    forall {retT1 retT2 retT3}
           (a1: ActionT type retT1) (a2: type retT1 -> ActionT type retT2)
           (a3: type retT2 -> ActionT type retT3),
      appendAction a1 (fun t => appendAction (a2 t) a3) = appendAction (appendAction a1 a2) a3.
  Proof.
    induction a1; simpl; intuition idtac; f_equal; try extensionality x; eauto.
  Qed.

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

Section SemProps.

  Lemma appendAction_SemAction:
    forall retK1 retK2 a1 a2 olds news1 news2 calls1 calls2
           (retV1: type retK1) (retV2: type retK2),
      SemAction olds a1 news1 calls1 retV1 ->
      SemAction olds (a2 retV1) news2 calls2 retV2 ->
      SemAction olds (appendAction a1 a2) (M.union news1 news2) (M.union calls1 calls2) retV2.
  Proof.
    induction a1; intros.

    - invertAction H0; specialize (H _ _ _ _ _ _ _ _ _ H0 H1);
      econstructor; eauto.
      apply M.union_add.
    - invertAction H0; econstructor; eauto. 
    - invertAction H0; econstructor; eauto.
    - invertAction H; econstructor; eauto.
      apply M.union_add.
    - invertAction H0.
      simpl; remember (evalExpr e) as cv; destruct cv; dest; subst.
      + eapply SemIfElseTrue.
        * eauto.
        * eassumption.
        * eapply H; eauto.
        * rewrite M.union_assoc; reflexivity.
        * rewrite M.union_assoc; reflexivity.
      + eapply SemIfElseFalse.
        * eauto.
        * eassumption.
        * eapply H; eauto.
        * rewrite M.union_assoc; reflexivity.
        * rewrite M.union_assoc; reflexivity.

    - invertAction H; specialize (IHa1 _ _ _ _ _ _ _ _ H H0);
      econstructor; eauto.
    - invertAction H; econstructor; eauto.
  Qed.

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

  Lemma wfAction_appendAction_calls_1:
    forall {retT1 retT2} (a1: ActionT type retT1)
           (a2: type retT1 -> ActionT type retT2) wr cc,
      WfAction wr cc (appendAction a1 a2) ->
      WfAction wr cc a1.
  Proof.
    induction a1; intros; simpl in *.
    - inv H0; destruct_existT.
      constructor; auto.
      intros; eapply H; eauto.
    - inv H0; destruct_existT; constructor; intros; eapply H; eauto.
    - inv H0; destruct_existT; constructor; intros; eapply H; eauto.
    - inv H; destruct_existT; constructor; auto; intros; eapply IHa1; eauto.
    - admit.
    - inv H; destruct_existT; constructor; eapply IHa1; eauto.
    - constructor.
  Qed.

  Lemma wfAction_appendAction_calls_2:
    forall {retT1 retT2} (a1: ActionT type retT1)
           (a2: type retT1 -> ActionT type retT2) retV1 wr cc,
      WfAction wr cc (appendAction a1 a2) ->
      WfAction wr cc (a2 retV1).
  Proof.
    admit.
  Qed.

  Lemma wfAction_appendAction_calls_disj:
    forall {retT1 retT2} a1 a2 or newRegs1 calls1 (retV1: type retT1)
           newRegs2 calls2 (retV2: type retT2),
      WfAction nil nil (appendAction a1 a2) ->
      SemAction or a1 newRegs1 calls1 retV1 ->
      SemAction or (a2 retV1) newRegs2 calls2 retV2 ->
      M.Disj calls1 calls2.
  Proof.
    admit.
  Qed.

End SemProps.

