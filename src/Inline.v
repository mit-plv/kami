Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FnMap.
Require Import Syntax Wf Equiv.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section PhoasUT.
  Definition typeUT (k: Kind): Type := unit.
  Definition fullTypeUT := fullType typeUT.
  Definition getUT (k: FullKind): fullTypeUT k :=
    match k with
      | SyntaxKind _ => tt
      | NativeKind t c => c
    end.

  Fixpoint getCalls {retT} (a: ActionT typeUT retT) (cs: list DefMethT)
  : list DefMethT :=
    match a with
      | MCall name _ _ cont =>
        match getAttribute name cs with
          | Some dm => dm :: (getCalls (cont tt) cs)
          | None => getCalls (cont tt) cs
        end
      | Let_ _ ar cont => getCalls (cont (getUT _)) cs
      | ReadReg reg k cont => getCalls (cont (getUT _)) cs
      | WriteReg reg _ e cont => getCalls cont cs
      | IfElse ce _ ta fa cont =>
        (getCalls ta cs) ++ (getCalls fa cs) ++ (getCalls (cont tt) cs)
      | Assert_ ae cont => getCalls cont cs
      | Return e => nil
    end.

  Lemma getCalls_nil: forall {retT} (a: ActionT typeUT retT), getCalls a nil = nil.
  Proof.
    induction a; intros; simpl; intuition.
    rewrite IHa1, IHa2, (H tt); reflexivity.
  Qed.

  Lemma getCalls_sub: forall {retT} (a: ActionT typeUT retT) cs ccs,
                        getCalls a cs = ccs -> SubList ccs cs.
  Proof.
    induction a; intros; simpl; intuition; try (eapply H; eauto; fail).
    - simpl in H0.
      remember (getAttribute meth cs); destruct o.
      + pose proof (getAttribute_Some_body _ _ Heqo); subst.
        unfold SubList; intros.
        inv H0; [assumption|].
        eapply H; eauto.
      + eapply H; eauto.
    - simpl in H0; subst.
      unfold SubList; intros.
      apply in_app_or in H0; destruct H0; [|apply in_app_or in H0; destruct H0].
      + eapply IHa1; eauto.
      + eapply IHa2; eauto.
      + eapply H; eauto.
    - simpl in H; subst.
      unfold SubList; intros; inv H.
  Qed.

  Section NoCalls.
    (* Necessary condition for inlining correctness *)
    Fixpoint noCalls {retT} (a: ActionT typeUT retT) (cs: list string) :=
      match a with
        | MCall name _ _ cont =>
          if in_dec string_dec name cs then false else noCalls (cont tt) cs
        | Let_ _ ar cont => noCalls (cont (getUT _)) cs
        | ReadReg reg k cont => noCalls (cont (getUT _)) cs
        | WriteReg reg _ e cont => noCalls cont cs
        | IfElse ce _ ta fa cont => (noCalls ta cs) && (noCalls fa cs) && (noCalls (cont tt) cs)
        | Assert_ ae cont => noCalls cont cs
        | Return e => true
      end.

    Fixpoint noCallsRules (rules: list (Attribute (Action Void))) (cs: list string) :=
      match rules with
        | nil => true
        | {| attrType := r |} :: rules' => (noCalls (r typeUT) cs) && (noCallsRules rules' cs)
      end.
  
    Fixpoint noCallsDms (dms: list DefMethT) (cs: list string) :=
      match dms with
        | nil => true
        | {| attrType := {| objVal := dm |} |} :: dms' =>
          (noCalls (dm typeUT tt) cs) && (noCallsDms dms' cs)
      end.

    Fixpoint noCallsMod (m: Modules) (cs: list string) :=
      match m with
        | Mod _ rules dms => (noCallsRules rules cs) && (noCallsDms dms cs)
        | ConcatMod m1 m2 => (noCallsMod m1 cs) && (noCallsMod m2 cs)
      end.

  End NoCalls.

End PhoasUT.

Section Phoas.
  Variable type: Kind -> Type.

  Definition inlineArg {argT retT} (a: Expr type (SyntaxKind argT))
             (m: type argT -> ActionT type retT): ActionT type retT :=
    Let_ a m.

  Fixpoint getMethod (n: string) (dms: list DefMethT) :=
    match dms with
      | nil => None
      | {| attrName := mn; attrType := mb |} :: dms' =>
        if string_dec n mn then Some mb else getMethod n dms'
    end.
  
  Definition getBody (n: string) (dms: list DefMethT) (sig: SignatureT):
    option (sigT (fun x: DefMethT => objType (attrType x) = sig)) :=
    match getAttribute n dms with
      | Some a =>
        match SignatureT_dec (objType (attrType a)) sig with
          | left e => Some (existT _ a e)
          | right _ => None
        end
      | None => None
    end.

  Fixpoint inlineDms {retT} (a: ActionT type retT) (dms: list DefMethT): ActionT type retT :=
    match a with
      | MCall name sig ar cont =>
        match getBody name dms sig with
          | Some (existT dm e) =>
            appendAction (inlineArg ar ((eq_rect _ _ (objVal (attrType dm)) _ e)
                                          type))
                         (fun ak => inlineDms (cont ak) dms)
          | None => MCall name sig ar (fun ak => inlineDms (cont ak) dms)
        end
      | Let_ _ ar cont => Let_ ar (fun a => inlineDms (cont a) dms)
      | ReadReg reg k cont => ReadReg reg k (fun a => inlineDms (cont a) dms)
      | WriteReg reg _ e cont => WriteReg reg e (inlineDms cont dms)
      | IfElse ce _ ta fa cont => IfElse ce (inlineDms ta dms) (inlineDms fa dms)
                                         (fun a => inlineDms (cont a) dms)
      | Assert_ ae cont => Assert_ ae (inlineDms cont dms)
      | Return e => Return e
    end.

  Fixpoint inlineDmsRep {retT} (a: ActionT type retT) (dms: list DefMethT) (n: nat) :=
    match n with
      | O => inlineDms a dms
      | S n' => inlineDms (inlineDmsRep a dms n') dms
    end.

End Phoas.

Section Exts.
  Definition inlineToRule (r: Attribute (Action (Bit 0)))
             (dms: list DefMethT): Attribute (Action (Bit 0)) :=
    {| attrName := attrName r;
       attrType := (fun t => inlineDms (attrType r t) dms) |}.

  Definition inlineToRules (rules: list (Attribute (Action (Bit 0))))
             (dms: list DefMethT): list (Attribute (Action (Bit 0))) :=
    map (fun r => inlineToRule r dms) rules.

  Lemma inlineToRules_In:
    forall r rules dms, In r rules -> In (inlineToRule r dms) (inlineToRules rules dms).
  Proof.
    induction rules; intros; inv H.
    - left; reflexivity.
    - right; apply IHrules; auto.
  Qed.

  Lemma inlineToRules_names:
    forall rules dms, namesOf rules = namesOf (inlineToRules rules dms).
  Proof.
    induction rules; intros; simpl in *; [reflexivity|].
    f_equal; apply IHrules.
  Qed.

  Fixpoint inlineToRulesRep rules dms (n: nat) :=
    match n with
      | O => inlineToRules rules dms
      | S n' => inlineToRules (inlineToRulesRep rules dms n') dms
    end.

  Lemma inlineToRulesRep_inlineDmsRep:
    forall n rules dms,
      inlineToRulesRep rules dms n =
      map (fun ar => {| attrName := attrName ar;
                        attrType := fun t => inlineDmsRep (attrType ar t) dms n |}) rules.
  Proof.
    induction n; intros; [simpl; reflexivity|].
    simpl; rewrite IHn.
    unfold inlineToRules.
    rewrite map_map; reflexivity.
  Qed.

  Lemma inlineToRulesRep_names:
    forall n dms rules, namesOf rules = namesOf (inlineToRulesRep rules dms n).
  Proof.
    intros; rewrite inlineToRulesRep_inlineDmsRep.
    unfold namesOf; rewrite map_map; reflexivity.
  Qed.

  Definition inlineToDm (n: string) {argT retT} (m: forall ty, ty argT -> ActionT ty retT)
             (dms: list DefMethT): forall ty, ty argT -> ActionT ty retT :=
    fun ty a => inlineDms (m ty a) dms.

  Fixpoint inlineToDms (dms: list DefMethT): list DefMethT :=
    match dms with
      | nil => nil
      | {| attrName := n; attrType := {| objType := s; objVal := a |} |} :: dms' =>
        {| attrName := n; attrType := {| objType := s; objVal := inlineToDm n a dms |} |}
          :: (inlineToDms dms')
    end.

  Fixpoint inlineToDmsRep (dms: list DefMethT) (n: nat): list DefMethT :=
    match n with
      | O => inlineToDms dms
      | S n' => inlineToDms (inlineToDmsRep dms n')
    end.

  Definition inlineMod (m1 m2: Modules) (cdn: nat): Modules :=
    match m1, m2 with
      | Mod regs1 r1 dms1, Mod regs2 r2 dms2 =>
        Mod (regs1 ++ regs2) (inlineToRulesRep (r1 ++ r2) (dms1 ++ dms2) cdn)
            (inlineToDmsRep (dms1 ++ dms2) cdn)
      | _, _ => m1 (* undefined *)
    end.

End Exts.

Fixpoint collectCalls {retK} (a: ActionT typeUT retK) (dms: list DefMethT) (cdn: nat) :=
  match cdn with
    | O => getCalls a dms
    | S n => (getCalls (inlineDmsRep a dms n) dms) ++ (collectCalls a dms n)
  end.

Lemma collectCalls_sub: forall cdn {retT} (a: ActionT typeUT retT) cs ccs,
                          collectCalls a cs cdn = ccs -> SubList ccs cs.
Proof.
  induction cdn; intros; simpl in H.
  - eapply getCalls_sub; eauto.
  - subst; unfold SubList; intros.
    apply in_app_or in H; destruct H.
    + eapply getCalls_sub; eauto.
    + eapply IHcdn; eauto.
Qed.

Inductive WfInline: forall {retK}, ActionT typeUT retK -> list DefMethT -> nat -> Prop :=
| WfInlineO:
    forall {retK} (a: ActionT typeUT retK) dms,
      WfInline a dms O
| WfInlineS:
    forall {retK} (a: ActionT typeUT retK) dms n,
      WfInline a dms n ->
      DisjList (namesOf (getCalls (inlineDmsRep a dms n) dms)) (namesOf (collectCalls a dms n)) ->
      WfInline a dms (S n).

Require Import Semantics.

Lemma getCalls_cmMap:
  forall rules olds news dmsAll dmMap cmMap {retK} (a: ActionT typeUT retK),
    SemMod rules olds None news dmsAll dmMap cmMap ->
    InDomain dmMap (namesOf (getCalls a dmsAll)) ->
    InDomain (restrict cmMap (namesOf dmsAll)) (namesOf (getCalls (inlineDms a dmsAll) dmsAll)).
Proof.
  admit.
Qed.

Lemma appendAction_SemAction:
  forall retK1 retK2 a1 a2 olds1 olds2 news1 news2 calls1 calls2
         (retV1: type retK1) (retV2: type retK2),
    (Disj olds1 olds2 \/ FnMap.Sub olds1 olds2) ->
    SemAction olds1 a1 news1 calls1 retV1 ->
    SemAction olds2 (a2 retV1) news2 calls2 retV2 ->
    SemAction (union olds1 olds2) (appendAction a1 a2)
              (union news1 news2) (union calls1 calls2) retV2.
Proof.
  induction a1; intros.

  - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2); econstructor; eauto.
  - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2); econstructor; eauto.
  - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H3 H2); econstructor; eauto.
    repeat autounfold with MapDefs; repeat autounfold with MapDefs in H1.
    rewrite H1; reflexivity.
  - invertAction H0; specialize (IHa1 _ _ _ _ _ _ _ _ _ H H0 H1); econstructor; eauto.

  - invertAction H1.
    simpl; remember (evalExpr e) as cv; destruct cv; dest; subst.
    + eapply SemIfElseTrue.
      * eauto.
      * eapply SemAction_olds_ext.
        { instantiate (1:= olds1); apply Sub_union. }
        { exact H1. }
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.
    + eapply SemIfElseFalse.
      * eauto.
      * eapply SemAction_olds_ext.
        { instantiate (1:= olds1); apply Sub_union. }
        { exact H1. }
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.

  - invertAction H0; specialize (IHa1 _ _ _ _ _ _ _ _ _ H H0 H1); econstructor; eauto.
  - invertAction H0; map_simpl_G; econstructor.
    destruct H.
    + eapply SemAction_olds_ext; eauto.
      rewrite Disj_union_unionR; auto.
      apply Sub_unionR.
    + rewrite Sub_merge; assumption.
Qed.

Lemma inlineDms_ActionEquiv:
  forall {retK} (a: Action retK) ast aut iast iaut dms,
    ast = a type -> aut = a typeUT ->
    ActionEquiv nil ast aut ->
    iast = (fun t => inlineDms (a t) dms) type ->
    iaut = (fun t => inlineDms (a t) dms) typeUT ->
    ActionEquiv nil iast iaut.
Proof.
  (* induction 3; intros; simpl in *; subst. *)
  admit.
Qed.

Lemma inlineDmsRep_ActionEquiv:
  forall {retK} (a: Action retK) ast aut iast iaut dms cdn,
    ast = a type -> aut = a typeUT ->
    ActionEquiv nil ast aut ->
    iast = (fun t => inlineDmsRep (a t) dms cdn) type ->
    iaut = (fun t => inlineDmsRep (a t) dms cdn) typeUT ->
    ActionEquiv nil iast iaut.
Proof.
  admit.
Qed.

Lemma getCalls_SemAction:
  forall {retK} (aut: ActionT typeUT retK) (ast: ActionT type retK)
         (Hequiv: ActionEquiv nil ast aut) dms cdms
         olds news calls retV,
    getCalls aut dms = cdms ->
    SemAction olds ast news calls retV ->
    OnDomain calls (namesOf cdms).
Proof.
  admit.
Qed.

Inductive WfmAction {ty}: list string -> forall {retT}, ActionT ty retT -> Prop :=
| WfmMCall:
    forall ll name sig ar {retT} cont (Hnin: ~ In name ll),
      (forall t, WfmAction (name :: ll) (cont t)) ->
      WfmAction ll (MCall (lretT:= retT) name sig ar cont)
| WfmLet:
    forall ll {argT retT} ar cont,
      (forall t, WfmAction ll (cont t)) ->
      WfmAction ll (Let_ (lretT':= argT) (lretT:= retT) ar cont)
| WfmReadReg:
    forall ll {retT} reg k cont,
      (forall t, WfmAction ll (cont t)) ->
      WfmAction ll (ReadReg (lretT:= retT) reg k cont)
| WfmWriteReg:
    forall ll {writeT retT} reg e cont,
      WfmAction ll cont ->
      WfmAction ll (WriteReg (k:= writeT) (lretT:= retT) reg e cont)
| WfmIfElse:
    forall ll {retT1 retT2} ce ta fa cont,
      WfmAction ll (appendAction (retT1:= retT1) (retT2:= retT2) ta cont) ->
      WfmAction ll (appendAction (retT1:= retT1) (retT2:= retT2) fa cont) ->
      WfmAction ll (IfElse ce ta fa cont)
| WfmAssert:
    forall ll {retT} e cont,
      WfmAction ll cont ->
      WfmAction ll (Assert_ (lretT:= retT) e cont)
| WfmReturn:
    forall ll {retT} (e: Expr ty (SyntaxKind retT)), WfmAction ll (Return e).

Hint Constructors WfmAction.

Inductive WfmActionRep {ty} (dms: list DefMethT):
  list string -> forall {retT}, ActionT ty retT -> nat -> Prop :=
| WfmInlineO: forall ll {retT} (a: ActionT ty retT),
                WfmAction ll a -> WfmAction ll (inlineDms a dms) ->
                WfmActionRep dms ll a O
| WfmInlineS: forall ll n {retT} (a: ActionT ty retT),
                WfmActionRep dms ll a n ->
                WfmAction ll (inlineDmsRep a dms (S n)) ->
                WfmActionRep dms ll a (S n).

Lemma WfmAction_init_sub {ty}:
  forall {retK} (a: ActionT ty retK) ll1
         (Hwfm: WfmAction ll1 a) ll2
         (Hin: forall k, In k ll2 -> In k ll1),
    WfmAction ll2 a.
Proof.
  induction 1; intros; simpl; intuition.

  econstructor; eauto; intros.
  apply H0; eauto.
  intros; inv H1; intuition.
Qed.

Lemma WfmAction_append_1' {ty}:
  forall {retT2} a3 ll,
    WfmAction ll a3 ->
    forall {retT1} (a1: ActionT ty retT1) (a2: ty retT1 -> ActionT ty retT2),
      a3 = appendAction a1 a2 -> WfmAction ll a1.
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
    + eapply IHWfmAction1; eauto; apply appendAction_assoc.
    + eapply IHWfmAction2; eauto; apply appendAction_assoc.
  - destruct a1; simpl in *; try discriminate; inv H0; destruct_existT.
    econstructor; eauto.
  - destruct a1; simpl in *; try discriminate.
Qed.

Lemma WfmAction_append_1 {ty}:
  forall {retT1 retT2} (a1: ActionT ty retT1) (a2: ty retT1 -> ActionT ty retT2) ll,
    WfmAction ll (appendAction a1 a2) ->
    WfmAction ll a1.
Proof. intros; eapply WfmAction_append_1'; eauto. Qed.

Lemma WfmAction_append_2' : let ty := type in
  forall {retT2} a3 ll,
    WfmAction ll a3 ->
    forall {retT1} (a1: ActionT ty retT1) (a2: ty retT1 -> ActionT ty retT2),
      a3 = appendAction a1 a2 ->
      forall t, WfmAction ll (a2 t).
Proof.
  induction 1; intros.

  - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
    apply WfmAction_init_sub with (ll1:= meth :: ll); [|intros; right; assumption].
    eapply H0; eauto.
  - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
    + eapply H0; eauto.
    + apply H.
  - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
    eapply H0; eauto.
  - destruct a1; simpl in *; try discriminate; inv H0; destruct_existT.
    eapply IHWfmAction; eauto.
  - destruct a1; simpl in *; try discriminate; inv H1; destruct_existT.
    eapply IHWfmAction1; eauto.
    apply appendAction_assoc.
  - destruct a1; simpl in *; try discriminate; inv H0; destruct_existT.
    eapply IHWfmAction; eauto.
  - destruct a1; simpl in *; try discriminate.

    Grab Existential Variables.
    { exact (evalConstFullT (getDefaultConstFull _)). }
    { exact (evalConstFullT (getDefaultConstFull _)). }
    { exact (evalConstT (getDefaultConst _)). }
Qed.

Lemma WfmAction_append_2:
  forall {retT1 retT2} (a1: ActionT type retT1) (a2: type retT1 -> ActionT type retT2) ll,
    WfmAction ll (appendAction a1 a2) ->
    forall t, WfmAction ll (a2 t).
Proof. intros; eapply WfmAction_append_2'; eauto. Qed.

Lemma WfmAction_cmMap:
  forall {retK} olds (a: ActionT type retK) news calls retV ll
         (Hsem: SemAction olds a news calls retV)
         (Hwfm: WfmAction ll a)
         lb (Hin: In lb ll),
    find lb calls = None.
Proof.
  induction 1; intros; simpl; subst; intuition idtac; inv Hwfm; destruct_existT.

  - rewrite find_add_2.
    { apply IHHsem; eauto.
      specialize (H2 mret); eapply WfmAction_init_sub; eauto.
      intros; right; assumption.
    }
    { unfold string_eq; destruct (string_dec _ _); [subst; elim Hnin; assumption|intuition]. }
  - eapply IHHsem; eauto.
  - eapply IHHsem; eauto.
  - eapply IHHsem; eauto.
  - assert (find lb calls1 = None).
    { eapply IHHsem1; eauto.
      eapply WfmAction_append_1; eauto.
    }
    assert (find lb calls2 = None).
    { eapply IHHsem2; eauto.
      eapply WfmAction_append_2; eauto.
    }
    repeat autounfold with MapDefs in *.
    rewrite H, H0; reflexivity.
  - assert (find lb calls1 = None).
    { eapply IHHsem1; eauto.
      eapply WfmAction_append_1; eauto.
    }
    assert (find lb calls2 = None).
    { eapply IHHsem2; eauto.
      eapply WfmAction_append_2; eauto.
    }
    repeat autounfold with MapDefs in *.
    rewrite H, H0; reflexivity.
  - eapply IHHsem; eauto.
Qed.

Lemma WfmAction_append_3':
  forall {retT2} a3 ll,
    WfmAction ll a3 ->
    forall {retT1} (a1: ActionT type retT1) (a2: type retT1 -> ActionT type retT2),
      a3 = appendAction a1 a2 ->
      forall olds1 olds2 news1 news2 calls1 calls2 retV1 retV2,
      SemAction olds1 a1 news1 calls1 retV1 ->
      SemAction olds2 (a2 retV1) news2 calls2 retV2 ->
      forall lb, find lb calls1 = None \/ find lb calls2 = None.
Proof.
  induction 1; intros; simpl; intuition idtac; destruct a1; simpl in *; try discriminate.
  
  - inv H1; destruct_existT.
    invertAction H2; specialize (H x).
    specialize (H0 _ _ _ _ eq_refl _ _ _ _ _ _ _ _ H1 H3 lb).
    destruct H0; [|right; assumption].
    destruct (string_dec lb meth); [subst; right|left].
    + pose proof (WfmAction_append_2 _ _ H retV1).
      eapply WfmAction_cmMap; eauto.
    + rewrite find_add_2; [assumption|unfold string_eq; destruct (string_dec _ _); intuition].

  - inv H1; destruct_existT; invertAction H2; eapply H0; eauto.
  - inv H1; destruct_existT; invertAction H2; left; reflexivity.
  - inv H1; destruct_existT; invertAction H2; eapply H0; eauto.
  - inv H0; destruct_existT; invertAction H1; eapply IHWfmAction; eauto.
  - inv H1; destruct_existT.
    invertAction H2.
    destruct (evalExpr e); dest; subst.
    + specialize (@IHWfmAction1 _ (appendAction a1_1 a) a2 (appendAction_assoc _ _ _)).
      eapply IHWfmAction1; eauto.
      instantiate (1:= union x x1); instantiate (1:= union olds1 olds1).
      eapply appendAction_SemAction; eauto.
      right; intuition.
    + specialize (@IHWfmAction2 _ (appendAction a1_2 a) a2 (appendAction_assoc _ _ _)).
      eapply IHWfmAction2; eauto.
      instantiate (1:= union x x1); instantiate (1:= union olds1 olds1).
      eapply appendAction_SemAction; eauto.
      right; intuition.
    
  - inv H0; destruct_existT; invertAction H1; eapply IHWfmAction; eauto.
Qed.

Lemma WfmAction_append_3:
  forall {retT1 retT2} (a1: ActionT type retT1) (a2: type retT1 -> ActionT type retT2) ll,
    WfmAction ll (appendAction a1 a2) ->
    forall olds1 olds2 news1 news2 calls1 calls2 retV1 retV2,
      SemAction olds1 a1 news1 calls1 retV1 ->
      SemAction olds2 (a2 retV1) news2 calls2 retV2 ->
      forall lb, find lb calls1 = None \/ find lb calls2 = None.
Proof. intros; eapply WfmAction_append_3'; eauto. Qed.

Lemma WfmAction_init:
  forall {retK} (a: ActionT type retK) ll
         (Hwfm: WfmAction ll a),
    WfmAction nil a.
Proof. intros; eapply WfmAction_init_sub; eauto; intros; inv H. Qed.

Lemma WfmAction_MCall:
  forall {retK} olds a news calls (retV: type retK) dms
         (Hsem: SemAction olds a news calls retV)
         (Hwfm: WfmAction dms a),
    complement calls dms = calls.
Proof.
  induction 1; intros; inv Hwfm; destruct_existT.

  - rewrite complement_add_2 by assumption; f_equal.
    apply IHHsem.
    specialize (H2 mret).
    apply (WfmAction_init_sub H2 dms).
    intros; right; assumption.
  - eapply IHHsem; eauto.
  - eapply IHHsem; eauto.
  - eapply IHHsem; eauto.
  - rewrite complement_union; f_equal.
    + eapply IHHsem1; eauto.
      eapply WfmAction_append_1; eauto.
    + eapply IHHsem2; eauto.
      eapply WfmAction_append_2; eauto.
  - rewrite complement_union; f_equal.
    + eapply IHHsem1; eauto.
      eapply WfmAction_append_1; eauto.
    + eapply IHHsem2; eauto.
      eapply WfmAction_append_2; eauto.
  - eapply IHHsem; eauto.
  - map_simpl_G; reflexivity.
Qed.

Lemma getAttribute_SemMod:
  forall rules olds dms news meth dmMap cmMap s sv
         (Hdms: NoDup (namesOf dms))
         (Hsem: SemMod rules olds None news dms dmMap cmMap)
         (Hdm: find meth dmMap = Some {| objType := s; objVal := sv |})
         (attr: Attribute (Typed MethodT))
         (Hattr: Some attr = getAttribute meth dms),
    objType (attrType attr) = s.
Proof.
  induction dms; intros; [discriminate|].

  simpl in Hattr.
  destruct (string_dec meth a).

  - subst; inv Hattr.
    inv Hsem; [map_simpl Hdm; inv Hdm; reflexivity|].
    exfalso; clear IHdms.
    inv Hdms.
    pose proof (SemMod_dmMap_InDomain HSemMod).
    elim H1; apply H.
    unfold InMap; rewrite Hdm; discriminate.

  - inv Hdms; inv Hsem; [|eapply IHdms; eauto].
    rewrite find_add_2 in Hdm; [|unfold string_eq; destruct (string_dec _ _); intuition].
    eapply IHdms; eauto.
Qed.

Section Preliminaries.

  Lemma inlineDms_prop:
    forall olds1 olds2 (Holds: FnMap.Sub olds1 olds2)
           retK (at1: ActionT type retK) (au1: ActionT typeUT retK)
           (Hequiv: ActionEquiv nil at1 au1)
           dmsAll rules
           news newsA (HnewsA: Disj news newsA)
           dmMap cmMap cmMapA (HcmA: Disj cmMap cmMapA)
           (retV: type retK) cdms,
      WfmAction nil at1 ->
      getCalls au1 dmsAll = cdms ->
      
      SemAction olds1 at1 newsA cmMapA retV ->
      NoDup (namesOf dmsAll) ->
      dmMap = restrict cmMapA (namesOf cdms) -> (* label matches *)
      SemMod rules olds2 None news dmsAll dmMap cmMap ->
      SemAction (union olds1 olds2) (inlineDms at1 dmsAll)
                (union news newsA)
                (complement (union cmMap cmMapA) (namesOf cdms))
                retV.
  Proof.
    admit.
  Qed.

  Lemma inlineToRules_prop:
    forall olds1 olds2 (Holds: FnMap.Sub olds1 olds2)
           r (ar: Action (Bit 0))
           (Hequiv: ActionEquiv nil (ar type) (ar typeUT))
           dmsAll rules
           news newsA (HnewsA: Disj news newsA)
           dmMap cmMap cmMapA (HcmA: Disj cmMap cmMapA) cdms,
      WfmAction nil (ar type) ->
      In {| attrName := r; attrType := ar |} rules -> NoDup (namesOf rules) ->
      getCalls (ar typeUT) dmsAll = cdms ->

      SemMod rules olds1 (Some r) newsA dmsAll empty cmMapA ->
      NoDup (namesOf dmsAll) ->
      restrict cmMapA (namesOf cdms) = dmMap -> (* label matches *)
      SemMod rules olds2 None news dmsAll dmMap cmMap ->
      SemMod (inlineToRules rules dmsAll) (union olds1 olds2) (Some r)
             (union news newsA) dmsAll empty
             (complement
                (union cmMap cmMapA)
                (namesOf cdms)).
  Proof.
    intros; inv H3.
    pose proof (SemMod_empty_inv HSemMod); dest; subst.
    
    econstructor.
    - pose proof (inlineToRules_In _ _ dmsAll HInRule); simpl in H2.
      eassumption.
    - assert (ar = ruleBody); subst.
      { clear -H0 H1 HInRule.
        generalize dependent r; generalize dependent ar; generalize dependent ruleBody.
        induction rules; intros; [inv H0|].
        inv H0.
        { inv HInRule.
          { inv H; reflexivity. }
          { inv H1; elim H3.
            apply in_map with (B:= string) (f:= (fun a => attrName a)) in H.
            simpl in H; assumption.
          }
        }
        { inv HInRule.
          { inv H1; elim H3.
            apply in_map with (B:= string) (f:= (fun a => attrName a)) in H.
            simpl in H; assumption.
          }
          { inv H1; eapply IHrules; eauto. }
        }
      }

      simpl; eapply inlineDms_prop with (newsA:= news0) (cmMapA:= calls);
      try assumption; try reflexivity.
      + eassumption.
      + apply Disj_union_1 in HnewsA; eauto.
      + apply Disj_union_1 in HcmA; eauto.
      + eassumption.
      + map_simpl H6; eassumption.
    - apply SemMod_empty.
    - auto.
    - auto.
    - map_simpl HnewsA.
      map_simpl_G; rewrite union_comm; auto.
    - map_simpl HcmA.
      map_simpl_G; rewrite union_comm; auto.
  Qed.

  Lemma inlineToRulesRep_prop:
    forall olds1 olds2 (Holds: FnMap.Sub olds1 olds2)
           cdn
           r (ar: Action (Bit 0))
           (Hequiv: ActionEquiv nil (ar type) (ar typeUT))
           dmsAll rules
           news newsA (HnewsA: Disj news newsA)
           dmMap cmMap cmMapA (HcmA: Disj cmMap cmMapA) cdms,
      WfmActionRep dmsAll nil (ar type) cdn ->
      WfInline (ar typeUT) dmsAll (S cdn) ->
      In {| attrName := r; attrType := ar |} rules -> NoDup (namesOf rules) ->
      collectCalls (ar typeUT) dmsAll cdn = cdms ->

      SemMod rules olds1 (Some r) newsA dmsAll empty cmMapA ->
      NoDup (namesOf dmsAll) ->
      SemMod rules olds2 None news dmsAll dmMap cmMap ->
      dmMap = restrict (union cmMapA cmMap) (namesOf cdms) ->
      SemMod (inlineToRulesRep rules dmsAll cdn) (union olds1 olds2) (Some r)
             (union news newsA) dmsAll empty
             (complement (union cmMap cmMapA) (namesOf cdms)).
  Proof.
    induction cdn; intros.

    - simpl; rewrite restrict_union in H7.

      assert (exists retV, SemAction olds1 (ar type) newsA cmMapA retV); dest.
      { inv H4; pose proof (SemMod_empty_inv HSemMod); dest; subst.
        eexists; map_simpl_G.
        assert (ruleBody = ar); subst.
        { clear -H1 HInRule H2.
          induction rules; [inv H1|].
          simpl in H2; inv H2.
          inv H1.
          { inv HInRule; [inv H; reflexivity|].
            elim H3. apply in_map with (B:= string) (f:= @attrName _) in H.
            assumption.
          }
          { inv HInRule; [|apply IHrules; auto].
            elim H3. apply in_map with (B:= string) (f:= @attrName _) in H.
            assumption.
          }
        }
        eassumption.
      }

      assert (cmMap = complement cmMap (namesOf cdms)).
      { simpl in H3.
        pose proof (@getCalls_SemAction _ _ _ Hequiv _ (getCalls (ar typeUT) dmsAll)
                                        _ _ _ _ eq_refl H8).
        symmetry; apply NotOnDomain_complement.
        subst; eapply Disj_OnDomain with (m1:= cmMapA); eauto.
        apply Disj_comm; assumption.
      }
      assert (empty = restrict cmMap (namesOf cdms)).
      { rewrite complement_restrict_nil; auto. }
      rewrite <-H10 in H7; clear H9 H10.
      map_simpl H7.

      eapply inlineToRules_prop; try assumption; try reflexivity.

      + eassumption.
      + inv H; destruct_existT; assumption.
      + assumption.
      + assumption.
      + rewrite <-H7; assumption.

    - simpl; simpl in H3; subst.

      (* Reallocate olds *)
      replace (union olds1 olds2) with (union (union olds1 olds2) (union olds1 olds2));
        [|rewrite union_idempotent; reflexivity].

      (* Reallocate dmMaps and news *)
      unfold namesOf in H6; rewrite map_app in H6;
      rewrite restrict_app in H6; apply SemMod_div in H6;
      [|apply Disj_DisjList_restrict; inv H0; inv H9; destruct_existT; assumption].
      destruct H6 as [news2 [news1 [cmMap2 [cmMap1 H6]]]].

      dest; subst.

      (* Reallocate news *)
      rewrite <-union_assoc with (m1:= news2).

      (* Reallocate cmMaps *)
      match goal with
        | [ |- SemMod _ _ _ _ _ _ ?cm ] =>
          replace cm with
          (complement
             (union
                (complement
                   cmMap2
                   (namesOf (collectCalls (ar typeUT) dmsAll cdn)))
                (union
                   (complement
                      cmMap1
                      (namesOf (collectCalls (ar typeUT) dmsAll cdn)))
                   (complement
                      cmMapA
                      (namesOf (collectCalls (ar typeUT) dmsAll cdn)))))
             (namesOf (getCalls (inlineDmsRep (ar typeUT) dmsAll cdn) dmsAll)))
            by (unfold namesOf;
                repeat rewrite <-complement_union;
                rewrite <-complement_app;
                rewrite <-map_app;
                f_equal; apply union_assoc)
      end.

      eapply inlineToRules_prop; try assumption; try reflexivity.

      + apply Sub_refl.
      + instantiate (1:= fun t => inlineDmsRep (ar t) dmsAll cdn).
        eapply inlineDmsRep_ActionEquiv; eauto.
      + apply Disj_union; [assumption|].
        apply Disj_comm, Disj_union_1, Disj_comm in HnewsA; assumption.
      + apply Disj_union.
        * apply Disj_complement, Disj_comm, Disj_complement, Disj_comm; assumption.
        * apply Disj_complement, Disj_comm, Disj_complement, Disj_comm.
          apply Disj_comm, Disj_union_1, Disj_comm in HcmA; assumption.
      + inv H; destruct_existT.
        inv H13; destruct_existT; auto.
      + rewrite inlineToRulesRep_inlineDmsRep.
        clear -H1.
        induction rules; [inv H1|].
        inv H1; [left; reflexivity|].
        right; apply IHrules; auto.
      + rewrite <-inlineToRulesRep_names; assumption.
      + reflexivity.
      + rewrite <-complement_union.
        eapply IHcdn; try assumption; try reflexivity.

        * assumption.
        * apply Disj_comm, Disj_union_2, Disj_comm in HnewsA; assumption.
        * apply Disj_comm, Disj_union_2, Disj_comm in HcmA; assumption.
        * inv H; destruct_existT; assumption.
        * inv H0; destruct_existT; assumption.
        * assumption.
        * pose proof (getCalls_cmMap (inlineDmsRep (ar typeUT) dmsAll cdn) H9).
          specialize (H6 (@restrict_InDomain _ _ _)).

          assert (restrict cmMap2 (namesOf (collectCalls (ar typeUT) dmsAll cdn)) = empty).
          { inv H0; destruct_existT.
            simpl in H15; unfold namesOf in H15;
            rewrite map_app in H15; apply DisjList_app_2 in H15.
            rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsAll).
            eapply InDomain_DisjList_restrict; eauto.
            apply SubList_map; eapply collectCalls_sub; eauto.
          }
          do 2 rewrite restrict_union in H10.
          unfold namesOf in H8.
          unfold DefMethT in H10; rewrite H8 in H10.

          map_simpl H10; rewrite <-restrict_union in H10.
          assumption.

      + apply SemMod_rules_ext with (rules1:= rules).
        apply SemMod_olds_ext with (or1:= olds2);
          [rewrite Sub_merge by assumption; apply Sub_refl|].

        pose proof (getCalls_cmMap (inlineDmsRep (ar typeUT) dmsAll cdn) H9).
        specialize (H6 (@restrict_InDomain _ _ _)).

        assert (restrict cmMap2 (namesOf (collectCalls (ar typeUT) dmsAll cdn)) = empty).
        { inv H0; destruct_existT.
          simpl in H15; unfold namesOf in H15;
          rewrite map_app in H15; apply DisjList_app_2 in H15.
          rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsAll).
          eapply InDomain_DisjList_restrict; eauto.
          apply SubList_map; eapply collectCalls_sub; eauto.
        }
        pose proof (restrict_complement_itself H8); rewrite H11; clear H8 H11.

        assert (restrict cmMap2 (namesOf (getCalls (inlineDmsRep (ar typeUT) dmsAll cdn) dmsAll))
                = empty).
        { inv H0; destruct_existT.
          simpl in H15; unfold namesOf in H15;
          rewrite map_app in H15; apply DisjList_app_1 in H15.
          rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsAll).
          eapply InDomain_DisjList_restrict; eauto.
          apply SubList_map; eapply getCalls_sub; eauto.
        }
        do 2 rewrite restrict_union in H9.
        unfold DefMethT in H9; unfold namesOf in H8; rewrite H8 in H9.

        map_simpl H9; rewrite <-restrict_union in H9.
        rewrite <-complement_union.

        inv H0; inv H14; destruct_existT; clear H15 H16.
        apply DisjList_comm in H18.
        rewrite restrict_complement_DisjList by assumption.
        rewrite union_comm;
          [|apply Disj_comm, Disj_union_2, Disj_comm in HcmA; assumption].
        assumption.
          
  Qed.

  Lemma inlineToRulesRep_prop':
    forall olds1 olds2 (Holds: Disj olds1 olds2 \/ FnMap.Sub olds1 olds2)
           r (ar: Action (Bit 0))
           dmsAll rules
           cdn news newsA (HnewsA: Disj news newsA)
           dmMap cmMap cmMapA (HcmA: Disj cmMap cmMapA),
      WfmActionRep dmsAll nil (ar type) cdn ->
      WfInline (ar typeUT) dmsAll (S cdn) ->
      In {| attrName := r; attrType := ar |} rules -> NoDup (namesOf rules) ->
      noCalls (inlineDmsRep (ar typeUT) dmsAll cdn) (namesOf dmsAll) = true ->

      SemMod rules olds1 (Some r) newsA dmsAll empty cmMapA ->
      NoDup (namesOf dmsAll) ->
      SemMod rules olds2 None news dmsAll dmMap cmMap ->
      dmMap = restrict (union cmMapA cmMap) (namesOf dmsAll) ->
      SemMod (inlineToRulesRep rules dmsAll cdn) (union olds1 olds2) (Some r)
             (union news newsA) dmsAll empty
             (complement (union cmMap cmMapA) (namesOf dmsAll)).
  Proof.
    admit.
  Qed.

End Preliminaries.

Section Facts.
  Variables (regs1 regs2: list RegInitT)
            (r1 r2: list (Attribute (Action (Bit 0))))
            (dms1 dms2: list DefMethT).

  Variable countdown: nat.

  Definition m1 := Mod regs1 r1 dms1.
  Definition m2 := Mod regs2 r2 dms2.

  Definition cm := ConcatMod m1 m2.
  Definition im := @inlineMod m1 m2 countdown.

  Lemma inline_correct:
    forall or nr rm dmMap cmMap,
      noCallsMod im (namesOf (dms1 ++ dms2)) = true ->
      LtsStep cm rm or nr dmMap cmMap -> LtsStep im rm or nr dmMap cmMap.
  Proof.
    intros; unfold im, cm in *; inv H0; inv Hlts1; inv Hlts2.
    constructor; [unfold namesOf; rewrite map_app; apply disjUnion_InDomain; auto|].

    simpl in H; apply andb_true_iff in H; dest.
    destConcatLabel; unfold CombineRm in Hcrm; dest.

    destruct rm1; destruct rm2; [destruct H1; discriminate| | |]; subst.

    - clear H1 HOldRegs1 HOldRegs2; simpl.
      move Hltsmod at bottom; move Hltsmod0 at bottom.
      unfold FiltDm in Hfd; simpl in Hfd; subst.
      unfold FiltCm in Hfc; simpl in Hfc; subst.
      unfold CallIffDef in Hcid; simpl in Hcid.

      admit.

    - admit.
    - admit.
  Qed.

End Facts.
