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

  Definition inlineToDm (dm: DefMethT) (dms: list DefMethT): DefMethT.
  Proof.
    destruct dm as [dmn [dmt dmv]].
    refine {| attrName := dmn; attrType := {| objType := dmt; objVal := _ |} |}.
    unfold MethodT; intros ty argV.
    exact (inlineDms (dmv ty argV) dms).
  Defined.    

  Definition inlineToDms (dms tdms: list DefMethT): list DefMethT :=
    map (fun dm => inlineToDm dm tdms) dms.

  Lemma inlineToDms_In:
    forall dm dms tdms, In dm dms -> In (inlineToDm dm tdms) (inlineToDms dms tdms).
  Proof.
    intros; apply in_map with (B := DefMethT) (f := fun d => inlineToDm d tdms) in H.
    assumption.
  Qed.

  Lemma inlineToDms_names:
    forall dms tdms, namesOf dms = namesOf (inlineToDms dms tdms).
  Proof.
    induction dms; intros; intuition auto.
    simpl; f_equal.
    - destruct a as [an [ ]]; reflexivity.
    - apply IHdms.
  Qed.

  Fixpoint inlineToDmsRep (dms tdms: list DefMethT) (n: nat): list DefMethT :=
    match n with
      | O => inlineToDms dms tdms
      | S n' => inlineToDms (inlineToDmsRep dms tdms n') tdms
    end.

  Program Lemma inlineToDmsRep_inlineDmsRep:
    forall n (dms tdms: list DefMethT),
      inlineToDmsRep dms tdms n =
      map (fun (ar: Attribute (Typed MethodT))
           => {| attrName := attrName ar;
                 attrType :=
                   {| objType := objType (attrType ar);
                      objVal := fun t av => inlineDmsRep ((objVal (attrType ar)) t av) tdms n
                   |}
              |}) dms.
  Proof.
    induction n; intros.
    - simpl; unfold inlineToDms, inlineToDm.
      f_equal; extensionality dm; destruct dm as [dmn [ ]]; simpl; reflexivity.
    - simpl; rewrite IHn; unfold inlineToDms.
      rewrite map_map; reflexivity.
  Qed.

  Lemma inlineToDmsRep_names:
    forall n dms tdms, namesOf dms = namesOf (inlineToDmsRep dms tdms n).
  Proof.
    intros; rewrite inlineToDmsRep_inlineDmsRep.
    unfold namesOf; rewrite map_map; reflexivity.
  Qed.

  Definition inlineMod (m1 m2: Modules) (cdn: nat): Modules :=
    match m1, m2 with
      | Mod regs1 r1 dms1, Mod regs2 r2 dms2 =>
        Mod (regs1 ++ regs2) (inlineToRulesRep (r1 ++ r2) (dms1 ++ dms2) cdn)
            (inlineToDmsRep (dms1 ++ dms2) (dms1 ++ dms2) cdn)
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

Inductive WfInline: forall {retK}, option string (* starting method *) ->
                                   ActionT typeUT retK -> list DefMethT -> nat -> Prop :=
| WfInlineO:
    forall {retK} odm (a: ActionT typeUT retK) dms,
      match odm with
        | Some dm => ~ In dm (namesOf (getCalls a dms))
        | None => True
      end ->
      WfInline odm a dms O
| WfInlineS:
    forall {retK} odm (a: ActionT typeUT retK) dms n,
      match odm with
        | Some dm => ~ In dm (namesOf (getCalls (inlineDmsRep a dms n) dms))
        | None => True
      end ->
      WfInline odm a dms n ->
      DisjList (namesOf (getCalls (inlineDmsRep a dms n) dms)) (namesOf (collectCalls a dms n)) ->
      WfInline odm a dms (S n).

Lemma WfInline_start:
  forall {retK} (a: ActionT typeUT retK) dm dms cdn,
    WfInline (Some dm) a dms cdn ->
    ~ In dm (namesOf (collectCalls a dms cdn)).
Proof.
  induction cdn; intros; simpl in *.
  - inv H; destruct_existT; assumption.
  - inv H; destruct_existT.
    specialize (IHcdn H5); clear H5.
    intro Hx; unfold namesOf in Hx; rewrite map_app in Hx; apply in_app_or in Hx;
    inv Hx; intuition.
Qed.

Require Import Semantics.

Lemma getCalls_cmMap:
  forall rules olds news dmsAll dmMap cmMap {retK} (a: ActionT typeUT retK),
    SemMod rules olds None news dmsAll dmMap cmMap ->
    InDomain dmMap (namesOf (getCalls a dmsAll)) ->
    InDomain (restrict cmMap (namesOf dmsAll)) (namesOf (getCalls (inlineDms a dmsAll) dmsAll)).
Proof.
  admit. (* Semantics stuff *)
Qed.

Lemma appendAction_SemAction:
  forall retK1 retK2 a1 a2 olds news1 news2 calls1 calls2
         (retV1: type retK1) (retV2: type retK2),
    SemAction olds a1 news1 calls1 retV1 ->
    SemAction olds (a2 retV1) news2 calls2 retV2 ->
    SemAction olds (appendAction a1 a2) (union news1 news2) (union calls1 calls2) retV2.
Proof.
  induction a1; intros.

  - invertAction H0; specialize (H _ _ _ _ _ _ _ _ _ H0 H1); econstructor; eauto.
  - invertAction H0; specialize (H _ _ _ _ _ _ _ _ _ H0 H1); econstructor; eauto.
  - invertAction H0; specialize (H _ _ _ _ _ _ _ _ _ H2 H1); econstructor; eauto.
  - invertAction H; specialize (IHa1 _ _ _ _ _ _ _ _ H H0); econstructor; eauto.

  - invertAction H0.
    simpl; remember (evalExpr e) as cv; destruct cv; dest; subst.
    + eapply SemIfElseTrue.
      * eauto.
      * eassumption.
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.
    + eapply SemIfElseFalse.
      * eauto.
      * eassumption.
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.

  - invertAction H; specialize (IHa1 _ _ _ _ _ _ _ _ H H0); econstructor; eauto.
  - invertAction H; map_simpl_G; econstructor; eauto.
Qed.

Lemma inlineDms_ActionEquiv:
  forall {retK} (ast: ActionT type retK) (aut: ActionT typeUT retK) dms,
    ActionEquiv nil ast aut ->
    ActionEquiv nil (inlineDms ast dms) (inlineDms aut dms).
Proof.
  induction 1; intros; subst; simpl; try (constructor; auto; fail).
  simpl; destruct (getBody n dms s).
  - destruct s0; subst; simpl.
    constructor; intros.
    admit. (* ActionEquiv appendAction: need "MethsEquiv dms" *)
  - constructor; intros.
    eapply H0; eauto.
Qed.

Lemma inlineDmsRep_ActionEquiv:
  forall {retK} (ast: ActionT type retK) (aut: ActionT typeUT retK) dms cdn,
    ActionEquiv nil ast aut ->
    ActionEquiv nil (inlineDmsRep ast dms cdn) (inlineDmsRep aut dms cdn).
Proof.
  induction cdn; intros; simpl in *; apply inlineDms_ActionEquiv; auto.
Qed.

Lemma getCalls_SemAction:
  forall {retK} (aut: ActionT typeUT retK) (ast: ActionT type retK)
         ectx (Hequiv: ActionEquiv ectx ast aut) dms cdms
         olds news calls retV,
    getCalls aut dms = cdms ->
    SemAction olds ast news calls retV ->
    OnDomain calls (namesOf cdms).
Proof.
  admit. (* Semantics stuff *)
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
      forall olds news1 news2 calls1 calls2 retV1 retV2,
      SemAction olds a1 news1 calls1 retV1 ->
      SemAction olds (a2 retV1) news2 calls2 retV2 ->
      forall lb, find lb calls1 = None \/ find lb calls2 = None.
Proof.
  induction 1; intros; simpl; intuition idtac; destruct a1; simpl in *; try discriminate.
  
  - inv H1; destruct_existT.
    invertAction H2; specialize (H x).
    specialize (H0 _ _ _ _ eq_refl _ _ _ _ _ _ _ H1 H3 lb).
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
      eapply appendAction_SemAction; eauto.
    + specialize (@IHWfmAction2 _ (appendAction a1_2 a) a2 (appendAction_assoc _ _ _)).
      eapply IHWfmAction2; eauto.
      eapply appendAction_SemAction; eauto.
    
  - inv H0; destruct_existT; invertAction H1; eapply IHWfmAction; eauto.
Qed.

Lemma WfmAction_append_3:
  forall {retT1 retT2} (a1: ActionT type retT1) (a2: type retT1 -> ActionT type retT2) ll,
    WfmAction ll (appendAction a1 a2) ->
    forall olds news1 news2 calls1 calls2 retV1 retV2,
      SemAction olds a1 news1 calls1 retV1 ->
      SemAction olds (a2 retV1) news2 calls2 retV2 ->
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

(* TODO: semantics stuff; move to Semantics.v *)
Lemma SemMod_dmMap_sig:
  forall rules or rm nr dms dmn dsig dm dmMap cmMap
         (Hdms: NoDup (namesOf dms))
         (Hin: In (dmn :: {| objType := dsig; objVal := dm |})%struct dms)
         (Hsem: SemMod rules or rm nr dms dmMap cmMap)
         (Hdmn: find dmn dmMap <> None),
  exists dv, find dmn dmMap = Some {| objType := dsig; objVal := dv |}.
Proof.
  admit. (* Semantics stuff *)
Qed.

Section Preliminaries.

  Lemma inlineDms_prop:
    forall olds retK (at1: ActionT type retK) (au1: ActionT typeUT retK)
           (Hequiv: ActionEquiv nil at1 au1)
           dmsAll rules
           news newsA (HnewsA: Disj news newsA)
           dmMap cmMap cmMapA (HcmA: Disj cmMap cmMapA)
           (retV: type retK) cdms,
      WfmAction nil at1 ->
      getCalls au1 dmsAll = cdms ->
      
      SemAction olds at1 newsA cmMapA retV ->
      NoDup (namesOf dmsAll) ->
      dmMap = restrict cmMapA (namesOf cdms) -> (* label matches *)
      SemMod rules olds None news dmsAll dmMap cmMap ->
      SemAction olds (inlineDms at1 dmsAll) (union news newsA)
                (complement (union cmMap cmMapA) (namesOf cdms))
                retV.
  Proof.
    induction 1; intros; simpl in *.

    - inv H1; destruct_existT.
      inv H3; destruct_existT.
      remember (getBody n dmsAll s) as odm; destruct odm.

      + destruct s0; generalize dependent HSemAction; subst; intros.
        rewrite <-Eqdep.Eq_rect_eq.eq_rect_eq.
        econstructor; eauto.

        unfold getBody in Heqodm.
        remember (getAttribute n dmsAll) as dmAttr; destruct dmAttr; [|discriminate].
        destruct (SignatureT_dec _ _); [|discriminate].
        generalize dependent HSemAction; inv Heqodm; inv e; intros.

        pose proof (getAttribute_Some_name _ _ HeqdmAttr); subst.

        (* dividing SemMod (a + calls) first *)
        specialize (H10 mret).
        rewrite restrict_add in H6 by (left; reflexivity).
        match goal with
          | [H: SemMod _ _ _ _ _ (add ?ak ?av ?dM) _ |- _] =>
            assert (add ak av dM = union (add ak av empty) dM) by admit (* map stuff *)
        end.
        rewrite H1 in H6; clear H1.
        replace (restrict calls (namesOf (a :: getCalls (cont2 tt) dmsAll))) with
        (restrict calls (namesOf (getCalls (cont2 tt) dmsAll))) in H6.
        2: (pose proof (WfmAction_MCall HSemAction H10); admit). (* map stuff: use H1 *)

        assert (NotOnDomain cmMap (namesOf (a :: getCalls (cont2 tt) dmsAll)))
          by admit. (* map stuff *)
        match goal with
          | [ |- SemAction _ _ _ ?cM _ ] =>
            replace cM with
            (union cmMap (complement calls (namesOf (getCalls (cont2 tt) dmsAll))))
              by admit (* map stuff; use HcmA, H1 *)
        end.
        apply Disj_add_2 in HcmA.
        
        match goal with
          | [H: SemMod _ _ _ _ _ (union ?m1 ?m2) _ |- _] =>
            assert (Disj m1 m2) by admit (* map stuff *)
        end.
        pose proof (SemMod_div H6 H2); dest; subst; clear H6 H2.
        pose proof (SemMod_meth_singleton HeqdmAttr H4 H9); clear H9.

        (* reordering arguments to apply appendAction_SemAction *)
        rewrite <-union_assoc with (m1:= x).
        rewrite <-union_assoc with (m1:= x1).

        apply appendAction_SemAction with (retV1:= mret); auto.
        assert (NotOnDomain x2 (namesOf (getCalls (cont2 tt) dmsAll)))
          by admit. (* map stuff using H1 *)
        apply NotOnDomain_complement in H5.
        rewrite <-H5; clear H5.
        rewrite <-complement_union.

        eapply H0; eauto.
        * apply Disj_comm, Disj_union_2, Disj_comm in HnewsA; assumption.
        * apply Disj_comm, Disj_union_2, Disj_comm in HcmA; assumption.
        * eapply WfmAction_init; eauto.

      + unfold getBody in Heqodm.
        remember (getAttribute n dmsAll) as mat; destruct mat.

        * destruct (SignatureT_dec _ _); [discriminate|].
          exfalso; elim n0; clear n0.
          pose proof (getAttribute_Some_name _ _ Heqmat); subst.
          pose proof (getAttribute_Some_body _ _ Heqmat).
          destruct a as [an [ ]]; pose proof (SemMod_dmMap_sig _ _ H4 H1 H6); simpl in *.
          map_compute H2; specialize (H2 (opt_discr _)); dest.
          clear -H2; inv H2; reflexivity.

        * econstructor; eauto.
          { instantiate (1:= complement (union cmMap calls)
                                        (namesOf (getCalls (cont2 tt) dmsAll))).
            instantiate (1:= mret).
            admit. (* map stuff *)
          }
          { eapply H0; eauto.
            { eapply Disj_add_2; eauto. }
            { specialize (H10 mret); eapply WfmAction_init; eauto. }
            { (* Note: map stuffs
               * 1) complement calls [n] = calls, by WfmAction_MCall with H10
               * 2) OnDomain calls (getCalls (cont2 tt) dmsAll), by getCalls_SemAction
               * 3) By 1) and 2), ListDisj [n] (getCalls (cont2 tt) dmsAll)
               *)
              p_equal H6.
              admit.
            }
          }

    - inv H1; destruct_existT.
      inv H3; destruct_existT.
      econstructor; eauto.

    - inv H1; destruct_existT.
      inv H3; destruct_existT.
      econstructor; eauto.

    - inv H0; destruct_existT.
      inv H2; destruct_existT.
      econstructor; eauto.

      + instantiate (1:= union news newRegs).
        admit. (* map stuff *)
      + eapply IHHequiv; eauto.
        eapply Disj_add_2; eauto.

    - inv H2; destruct_existT.
      inv H4; destruct_existT.

      admit.
      admit.

    - inv H0; destruct_existT.
      inv H2; destruct_existT.
      econstructor; eauto.

    - inv H0; destruct_existT.
      inv H2; destruct_existT.
      pose proof (SemMod_empty_inv H5); dest; subst.
      econstructor; eauto.

  Qed.

  Lemma inlineToRules_prop:
    forall olds r (ar: Action (Bit 0))
           (Hequiv: ActionEquiv nil (ar type) (ar typeUT))
           dmsAll rules
           news newsA (HnewsA: Disj news newsA)
           dmMap cmMap cmMapA (HcmA: Disj cmMap cmMapA) cdms,
      WfmAction nil (ar type) ->
      In {| attrName := r; attrType := ar |} rules -> NoDup (namesOf rules) ->
      getCalls (ar typeUT) dmsAll = cdms ->

      SemMod rules olds (Some r) newsA dmsAll empty cmMapA ->
      NoDup (namesOf dmsAll) ->
      restrict cmMapA (namesOf cdms) = dmMap -> (* label matches *)
      SemMod rules olds None news dmsAll dmMap cmMap ->
      SemMod (inlineToRules rules dmsAll) olds (Some r)
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

      simpl; eapply inlineDms_prop with (newsA:= news0) (cmMapA:= calls); eauto.
      + apply Disj_union_1 in HnewsA; eauto.
      + apply Disj_union_1 in HcmA; eauto.
      + map_simpl H6; eassumption.
        
    - apply SemMod_empty.
    - auto.
    - auto.
    - map_simpl HnewsA.
      map_simpl_G; rewrite union_comm; auto.
    - map_simpl HcmA.
      map_simpl_G; rewrite union_comm; auto.
  Qed.

  Lemma inlineToRulesRep_prop':
    forall olds cdn r (ar: Action (Bit 0))
           (Hequiv: ActionEquiv nil (ar type) (ar typeUT))
           dmsAll rules
           news newsA (HnewsA: Disj news newsA)
           dmMap cmMap cmMapA (HcmA: Disj cmMap cmMapA) cdms,
      WfmActionRep dmsAll nil (ar type) cdn ->
      WfInline None (ar typeUT) dmsAll (S cdn) ->
      In {| attrName := r; attrType := ar |} rules -> NoDup (namesOf rules) ->
      collectCalls (ar typeUT) dmsAll cdn = cdms ->

      SemMod rules olds (Some r) newsA dmsAll empty cmMapA ->
      NoDup (namesOf dmsAll) ->
      SemMod rules olds None news dmsAll dmMap cmMap ->
      dmMap = restrict (union cmMap cmMapA) (namesOf cdms) ->
      SemMod (inlineToRulesRep rules dmsAll cdn) olds (Some r)
             (union news newsA) dmsAll empty
             (complement (union cmMap cmMapA) (namesOf cdms)).
  Proof.
    induction cdn; intros.

    - simpl; rewrite restrict_union in H7.

      assert (exists retV, SemAction olds (ar type) newsA cmMapA retV); dest.
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
        pose proof (@getCalls_SemAction _ _ _ _ Hequiv _ (getCalls (ar typeUT) dmsAll)
                                        _ _ _ _ eq_refl H8).
        symmetry; apply NotOnDomain_complement.
        subst; eapply Disj_OnDomain with (m1:= cmMapA); eauto.
        apply Disj_comm; assumption.
      }
      assert (empty = restrict cmMap (namesOf cdms)).
      { rewrite complement_restrict_nil; auto. }
      rewrite <-H10 in H7; clear H9 H10.
      map_simpl H7.

      eapply inlineToRules_prop; eauto.
      + inv H; destruct_existT; assumption.
      + rewrite <-H7; assumption.

    - simpl; simpl in H3; subst.

      (* Reallocate dmMaps and news *)
      unfold namesOf in H6; rewrite map_app in H6;
      rewrite restrict_app in H6; apply SemMod_div in H6;
      [|apply Disj_DisjList_restrict; inv H0; inv H11; destruct_existT; assumption].
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
            simpl in H17; unfold namesOf in H17;
            rewrite map_app in H17; apply DisjList_app_2 in H17.
            rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsAll).
            eapply InDomain_DisjList_restrict; eauto.
            apply SubList_map; eapply collectCalls_sub; eauto.
          }
          do 2 rewrite restrict_union in H10.
          unfold namesOf in H8.
          unfold DefMethT in H10; rewrite H8 in H10.

          map_simpl H10; rewrite <-restrict_union in H10.
          assumption.

      + apply SemMod_rules_free with (rules1:= rules).
        pose proof (getCalls_cmMap (inlineDmsRep (ar typeUT) dmsAll cdn) H9).
        specialize (H6 (@restrict_InDomain _ _ _)).

        assert (restrict cmMap2 (namesOf (collectCalls (ar typeUT) dmsAll cdn)) = empty).
        { inv H0; destruct_existT.
          simpl in H17; unfold namesOf in H17;
          rewrite map_app in H17; apply DisjList_app_2 in H17.
          rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsAll).
          eapply InDomain_DisjList_restrict; eauto.
          apply SubList_map; eapply collectCalls_sub; eauto.
        }
        pose proof (restrict_complement_itself H8); rewrite H11; clear H8 H11.

        assert (restrict cmMap2 (namesOf (getCalls (inlineDmsRep (ar typeUT) dmsAll cdn) dmsAll))
                = empty).
        { inv H0; destruct_existT.
          simpl in H17; unfold namesOf in H17;
          rewrite map_app in H17; apply DisjList_app_1 in H17.
          rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsAll).
          eapply InDomain_DisjList_restrict; eauto.
          apply SubList_map; eapply getCalls_sub; eauto.
        }
        do 2 rewrite restrict_union in H9.
        unfold DefMethT in H9; unfold namesOf in H8; rewrite H8 in H9.

        map_simpl H9; rewrite <-restrict_union in H9.
        rewrite <-complement_union.

        inv H0; inv H16; destruct_existT.
        apply DisjList_comm in H21.
        rewrite restrict_complement_DisjList by assumption.
        assumption.
  Qed.

  Lemma inlineToRulesRep_prop:
    forall olds cdn r (ar: Action (Bit 0))
           (Hequiv: ActionEquiv nil (ar type) (ar typeUT))
           dmsAll rules news dmMap cmMap cdms,
      WfmActionRep dmsAll nil (ar type) cdn ->
      WfInline None (ar typeUT) dmsAll (S cdn) ->
      In {| attrName := r; attrType := ar |} rules -> NoDup (namesOf rules) ->
      collectCalls (ar typeUT) dmsAll cdn = cdms ->

      SemMod rules olds (Some r) news dmsAll dmMap cmMap ->
      NoDup (namesOf dmsAll) ->
      dmMap = restrict cmMap (namesOf cdms) ->
      SemMod (inlineToRulesRep rules dmsAll cdn) olds (Some r)
             news dmsAll empty (complement cmMap (namesOf cdms)).
  Proof.
    intros.
    replace dmMap with (union empty dmMap) in H4 by auto.

    apply SemMod_div in H4; [|auto].
    destruct H4 as [news2 [news1 [cmMap2 [cmMap1 H4]]]]; dest; subst.

    rewrite union_comm with (m1:= news2) by assumption.
    rewrite union_comm with (m1:= cmMap2) by assumption.
    rewrite union_comm with (m1:= cmMap2) in H11 by assumption.
    eapply inlineToRulesRep_prop'; eauto.
    - apply Disj_comm; assumption.
    - apply Disj_comm; assumption.
  Qed.

  Lemma inlineToDms_prop:
    forall olds dmn dsig (dargV: type (arg dsig)) (dretV: type (ret dsig)) (ad: MethodT dsig)
           (Hequiv: ActionEquiv nil (ad type dargV) (ad typeUT tt))
           dmsAll dmsConst rules
           news newsA (HnewsA: Disj news newsA)
           dmMap dmMapA cmMap cmMapA (HcmA: Disj cmMap cmMapA) cdms,
      WfmAction nil (ad type dargV) ->
      Some {| attrName := dmn; attrType := {| objType := dsig; objVal := ad |} |}
      = getAttribute dmn dmsAll ->
      NoDup (namesOf dmsAll) -> NoDup (namesOf dmsConst) ->
      getCalls (ad typeUT tt) dmsConst = cdms ->

      dmMapA = add dmn {| objType := dsig; objVal := (dargV, dretV) |} empty ->
      SemMod rules olds None newsA dmsAll dmMapA cmMapA ->
      restrict cmMapA (namesOf cdms) = dmMap -> (* label matches *)
      SemMod rules olds None news dmsConst dmMap cmMap ->
      SemMod rules olds None
             (union news newsA) (inlineToDms dmsAll dmsConst) dmMapA
             (complement
                (union cmMap cmMapA)
                (namesOf cdms)).
  Proof.
    intros; subst.
    inv H5; [exfalso; eapply add_empty_neq; eauto|].

    destruct meth as [methName [methT methBody]]; simpl in *.

    assert (dmn = methName /\ dsig = methT /\ dm2 = empty).
    { clear -HNew HDefs; pose proof HDefs.
      apply @Equal_val with (k:= methName) in HDefs.
      repeat autounfold with MapDefs in HDefs, HNew.
      rewrite string_dec_eq in HDefs; unfold string_eq in HDefs.
      destruct (string_dec _ _); [|inv HDefs].
      apply opt_some_eq, typed_type_eq in HDefs; dest; subst; inv H0.
      repeat split; auto.
      apply Equal_eq; unfold Equal; intros.
      apply @Equal_val with (k:= k) in H.
      destruct (string_dec methName k); subst; auto.
      map_compute H; rewrite string_dec_neq in H by assumption.
      map_compute_G; auto.
    }
    dest; subst.

    assert (dargV = argV /\ dretV = retV).
    { clear -HDefs; apply @Equal_val with (k:= methName) in HDefs.
      map_compute HDefs.
      apply opt_some_eq, typed_eq in HDefs; inv HDefs; auto.
    }
    dest; subst; clear HDefs.

    (* TODO: better to extract a lemma *)
    assert (ad = methBody).
    { clear -HIn H0 H1.
      pose proof (getAttribute_Some_body _ _ H0); clear H0.
      induction dmsAll; [inv HIn|].
      inv H1; inv HIn.
      { inv H.
        { inv H0; destruct_existT; reflexivity. }
        { elim H3; simpl.
          apply in_map with (B:= string) (f:= @attrName _) in H0; assumption.
        }
      }
      { inv H.
        { elim H3; simpl.
          apply in_map with (B:= string) (f:= @attrName _) in H0; assumption.
        }
        { apply IHdmsAll; auto. }
      }
    }
    subst.

    inv HSemMod; [|exfalso; eapply add_empty_neq; eauto].

    eapply SemAddMeth.
    - eapply inlineToDms_In; eauto.
    - eapply inlineDms_prop with (newsA:= news0) (cmMapA:= calls);
        try assumption; try reflexivity.
      + eassumption.
      + apply Disj_union_1 in HnewsA; exact HnewsA.
      + apply Disj_union_1 in HcmA; exact HcmA.
      + assumption.
      + eassumption.
      + map_simpl H7; eassumption.
    - eapply SemEmpty; eauto.
    - auto.
    - auto.
    - map_simpl_G; reflexivity.
    - map_simpl_G; reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma inlineToDmsRep_prop':
    forall olds cdn dmn dsig (dargV: type (arg dsig)) (dretV: type (ret dsig)) (ad: MethodT dsig)
           (Hequiv: ActionEquiv nil (ad type dargV) (ad typeUT tt))
           dmsAll dmsConst rules
           news newsA (HnewsA: Disj news newsA)
           dmMap dmMapA cmMap cmMapA (HcmA: Disj cmMap cmMapA) cdms,
      WfmActionRep dmsConst nil (ad type dargV) cdn ->
      WfInline (Some dmn) (ad typeUT tt) dmsConst (S cdn) ->
      Some {| attrName := dmn; attrType := {| objType := dsig; objVal := ad |} |}
      = getAttribute dmn dmsAll ->
      NoDup (namesOf dmsAll) -> NoDup (namesOf dmsConst) ->
      collectCalls (ad typeUT tt) dmsConst cdn = cdms ->

      dmMapA = add dmn {| objType := dsig; objVal := (dargV, dretV) |} empty ->
      SemMod rules olds None newsA dmsAll dmMapA cmMapA ->
      SemMod rules olds None news dmsConst dmMap cmMap ->
      dmMap = restrict (union cmMap cmMapA) (namesOf cdms) ->
      SemMod rules olds None
             (union news newsA) (inlineToDmsRep dmsAll dmsConst cdn) dmMapA
             (complement (union cmMap cmMapA) (namesOf cdms)).
  Proof.
    induction cdn; intros.

    - simpl in *; rewrite restrict_union in H8.

      assert (SemAction olds (ad type dargV) newsA cmMapA dretV); dest.
      { inv H6; [exfalso; eapply add_empty_neq; eauto|].
        admit. (* Very similar to what I did before, may be able to be extracted as a lemma? *)
      }

      assert (cmMap = complement cmMap (namesOf cdms)).
      { pose proof (@getCalls_SemAction _ _ _ _ Hequiv _ (getCalls (ad typeUT tt) dmsConst)
                                        _ _ _ _ eq_refl H9).
        symmetry; apply NotOnDomain_complement.
        subst; eapply Disj_OnDomain with (m1:= cmMapA); eauto.
        apply Disj_comm; assumption.
      }
      assert (empty = restrict cmMap (namesOf cdms)).
      { rewrite complement_restrict_nil; auto. }
      rewrite <-H11 in H8; clear H10 H11.
      map_simpl H8.

      subst; eapply inlineToDms_prop; eauto. 
      inv H; destruct_existT; assumption.

    - simpl; simpl in H4; subst.

      (* Reallocate dmMaps and news *)
      unfold namesOf in H7; rewrite map_app in H7;
      rewrite restrict_app in H7; apply SemMod_div in H7;
      [|apply Disj_DisjList_restrict; inv H0; inv H11; destruct_existT; assumption].
      destruct H7 as [news2 [news1 [cmMap2 [cmMap1 H7]]]].

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
                   (namesOf (collectCalls (ad typeUT tt) dmsConst cdn)))
                (union
                   (complement
                      cmMap1
                      (namesOf (collectCalls (ad typeUT tt) dmsConst cdn)))
                   (complement
                      cmMapA
                      (namesOf (collectCalls (ad typeUT tt) dmsConst cdn)))))
             (namesOf (getCalls (inlineDmsRep (ad typeUT tt) dmsConst cdn) dmsConst)))
            by (unfold namesOf;
                repeat rewrite <-complement_union;
                rewrite <-complement_app;
                rewrite <-map_app;
                f_equal; apply union_assoc)
      end.

      eapply inlineToDms_prop; try assumption; try reflexivity.

      + instantiate (1:= fun t av => inlineDmsRep (ad t av) dmsConst cdn).
        eapply inlineDmsRep_ActionEquiv; eauto.
      + apply Disj_union; [assumption|].
        apply Disj_comm, Disj_union_1, Disj_comm in HnewsA; assumption.
      + apply Disj_union.
        * apply Disj_complement, Disj_comm, Disj_complement, Disj_comm; assumption.
        * apply Disj_complement, Disj_comm, Disj_complement, Disj_comm.
          apply Disj_comm, Disj_union_1, Disj_comm in HcmA; assumption.
      + inv H; destruct_existT.
        inv H13; destruct_existT; auto.
      + rewrite inlineToDmsRep_inlineDmsRep.
        clear -H1; induction dmsAll; [inv H1|]; simpl in H1.
        simpl; destruct (string_dec dmn a).
        * clear -H1; subst; destruct a as [an [ ]].
          simpl in *; inv H1; destruct_existT.
          reflexivity.
        * apply IHdmsAll; auto.
      + rewrite <-inlineToDmsRep_names; assumption.
      + reflexivity.
      + rewrite <-complement_union.
        eapply IHcdn; try assumption; try reflexivity.

        * assumption.
        * apply Disj_comm, Disj_union_2, Disj_comm in HnewsA; assumption.
        * apply Disj_comm, Disj_union_2, Disj_comm in HcmA; assumption.
        * inv H; destruct_existT; assumption.
        * inv H0; destruct_existT; assumption.
        * assumption.
        * pose proof (getCalls_cmMap (inlineDmsRep (ad typeUT tt) dmsConst cdn) H9).
          specialize (H5 (@restrict_InDomain _ _ _)).

          assert (restrict cmMap2 (namesOf (collectCalls (ad typeUT tt) dmsConst cdn)) = empty).
          { inv H0; destruct_existT.
            simpl in H17; unfold namesOf in H17;
            rewrite map_app in H17; apply DisjList_app_2 in H17.
            rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsConst).
            eapply InDomain_DisjList_restrict; eauto.
            apply SubList_map; eapply collectCalls_sub; eauto.
          }
          do 2 rewrite restrict_union in H10.
          unfold namesOf in H8.
          unfold DefMethT in H10; rewrite H8 in H10.

          map_simpl H10; rewrite <-restrict_union in H10.
          assumption.

      + pose proof (getCalls_cmMap (inlineDmsRep (ad typeUT tt) dmsConst cdn) H9).
        specialize (H5 (@restrict_InDomain _ _ _)).

        assert (restrict cmMap2 (namesOf (collectCalls (ad typeUT tt) dmsConst cdn)) = empty).
        { inv H0; destruct_existT.
          simpl in H17; unfold namesOf in H17;
          rewrite map_app in H17; apply DisjList_app_2 in H17.
          rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsConst).
          eapply InDomain_DisjList_restrict; eauto.
          apply SubList_map; eapply collectCalls_sub; eauto.
        }
        pose proof (restrict_complement_itself H8); rewrite H11; clear H8 H11.

        assert (restrict cmMap2 (namesOf (getCalls (inlineDmsRep (ad typeUT tt) dmsConst cdn)
                                                   dmsConst)) = empty).
        { inv H0; destruct_existT.
          simpl in H17; unfold namesOf in H17;
          rewrite map_app in H17; apply DisjList_app_1 in H17.
          rewrite <-restrict_SubList with (m:= cmMap2) (l2:= namesOf dmsConst).
          eapply InDomain_DisjList_restrict; eauto.
          apply SubList_map; eapply getCalls_sub; eauto.
        }
        do 2 rewrite restrict_union in H9.
        unfold DefMethT in H9; unfold namesOf in H8; rewrite H8 in H9.

        map_simpl H9; rewrite <-restrict_union in H9.
        rewrite <-complement_union.

        inv H0; inv H16; destruct_existT.
        apply DisjList_comm in H21.
        rewrite restrict_complement_DisjList by assumption.
        assumption.
  Qed.

  Lemma inlineToDmsRep_prop:
    forall olds cdn dmn dsig (dargV: type (arg dsig)) (dretV: type (ret dsig)) (ad: MethodT dsig)
           (Hequiv: ActionEquiv nil (ad type dargV) (ad typeUT tt))
           dmsAll rules news dmMap dmMapA cmMap cdms,
      WfmActionRep dmsAll nil (ad type dargV) cdn ->
      WfInline (Some dmn) (ad typeUT tt) dmsAll (S cdn) ->
      Some {| attrName := dmn; attrType := {| objType := dsig; objVal := ad |} |}
      = getAttribute dmn dmsAll ->
      NoDup (namesOf dmsAll) ->
      collectCalls (ad typeUT tt) dmsAll cdn = cdms ->

      dmMapA = add dmn {| objType := dsig; objVal := (dargV, dretV) |} empty ->
      dmMap = restrict cmMap (namesOf cdms) ->
      SemMod rules olds None news dmsAll (union dmMap dmMapA) cmMap ->
      SemMod rules olds None news (inlineToDmsRep dmsAll dmsAll cdn)
             dmMapA (complement cmMap (namesOf cdms)).
  Proof.
    intros; subst.

    apply SemMod_div in H6.

    - destruct H6 as [news1 [news2 [cmMap1 [cmMap2 H6]]]]; dest; subst.
      eapply inlineToDmsRep_prop'; eauto.

    - clear -H0; inv H0; destruct_existT.
      pose proof (WfInline_start H5); clear -H.
      unfold Disj; intros.
      destruct (string_dec k dmn);
        [|right; apply find_add_2; unfold string_eq; destruct (string_dec _ _); intuition].
      subst; left.
      apply restrict_not_in; auto.
  Qed.

End Preliminaries.

Section Facts.

  Inductive Inlinable:
    nat (* countdown *) -> option (Attribute (Action Void)) ->
    list DefMethT (* meths executed *) -> list DefMethT (* meths fired *) ->
    list (Attribute (Action Void)) (* entire rules *) -> list DefMethT (* entire methods *) ->
    Prop :=
  | InlinableEmpty: forall cdn rules dmsAll, Inlinable cdn None nil nil rules dmsAll
  | InlinableRule:
      forall rules dmsAll pedms pfdms
             ruleName (rule: Action (Bit 0)) cdn edms,
        In {| attrName := ruleName; attrType := rule |} rules ->
        ActionEquiv nil (rule type) (rule typeUT) ->
        Inlinable cdn None pedms pfdms rules dmsAll ->
        WfmActionRep dmsAll nil (rule type) cdn ->
        WfInline None (rule typeUT) dmsAll (S cdn) ->
        collectCalls (rule typeUT) dmsAll cdn = edms ->
        DisjList (namesOf edms) (namesOf pedms) ->
        Inlinable cdn (Some {| attrName := ruleName; attrType := rule |})
                  (edms ++ pedms) pfdms rules dmsAll
  | InlinableMeth:
      forall rules dmsAll fdmn dsig (dm: MethodT dsig) cdn edms
             pedms pfdms,
        In {| attrName := fdmn; attrType := {| objType := dsig; objVal := dm |} |} dmsAll ->
        (forall argV, ActionEquiv nil (dm type argV) (dm typeUT tt)) ->
        Inlinable cdn None pedms pfdms rules dmsAll ->
        (forall argV, WfmActionRep dmsAll nil (dm type argV) cdn) ->
        WfInline (Some fdmn) (dm typeUT tt) dmsAll (S cdn) ->
        collectCalls (dm typeUT tt) dmsAll cdn = edms ->
        DisjList (fdmn :: (namesOf edms)) (namesOf pedms) ->
        Inlinable cdn None (({| attrName:= fdmn;
                                attrType := {| objType := dsig; objVal := dm |} |}
                               :: edms) ++ pedms)
                  ({| attrName:= fdmn; attrType := {| objType := dsig; objVal := dm |} |}
                     :: pfdms) rules dmsAll.

  Lemma inlinable_dms_Sublist:
    forall cdn rm edms fdms rules dmsAll,
      Inlinable cdn rm edms fdms rules dmsAll ->
      SubList fdms edms.
  Proof.
    induction 1; intros; unfold SubList; intros; [inv H| |].
    - apply in_or_app; right; auto.
    - inv H6; [left; reflexivity|].
      apply in_or_app; right; auto.
  Qed.

  Definition ValidLabel (dmMap cmMap: CallsT) (dmsAll: list DefMethT) :=
    dmMap = restrict cmMap (namesOf dmsAll).
  Hint Unfold ValidLabel.

  Lemma decompose_SemMod_rule:
    forall rules or nr (rule: Attribute (Action Void)) dmsAll dmMap cmMap
           (Hlbl: ValidLabel dmMap cmMap dmsAll)
           (Hsem: SemMod rules or (Some (attrName rule)) nr dmsAll dmMap cmMap),
    forall cdn edms (Hedms: collectCalls (attrType rule typeUT) dmsAll cdn = edms),
    exists cmMap1 cmMap2 nr1 nr2,
      SemMod rules or (Some (attrName rule)) nr1 dmsAll (restrict dmMap (namesOf edms)) cmMap1 /\
      SemMod rules or None nr2 dmsAll (complement dmMap (namesOf edms)) cmMap2 /\
      restrict cmMap1 (namesOf edms) = restrict dmMap (namesOf edms) /\
      Disj nr1 nr2 /\ nr = union nr1 nr2 /\ Disj cmMap1 cmMap2.
  Proof.
    admit. (* Semantics stuff *)
  Qed.

  Lemma decompose_SemMod_meth:
    forall rules or nr dmn dm dmsAll dmMap cmMap
           (Hlbl: ValidLabel dmMap cmMap dmsAll)
           (Hdm: In {| attrName := dmn; attrType := dm |} dmsAll)
           (HdmMap: find dmn dmMap <> None)
           (Hsem: SemMod rules or None nr dmsAll dmMap cmMap),
    forall cdn edms (Hedms: collectCalls (objVal dm typeUT tt) dmsAll cdn = edms),
    exists cmMap1 cmMap2 nr1 nr2,
      SemMod rules or None nr1 dmsAll (restrict dmMap (dmn :: (namesOf edms))) cmMap1 /\
      SemMod rules or None nr2 dmsAll (complement dmMap (dmn :: (namesOf edms))) cmMap2 /\
      restrict cmMap1 (namesOf edms) = restrict dmMap (namesOf edms) /\
      Disj nr1 nr2 /\ nr = union nr1 nr2 /\ Disj cmMap1 cmMap2.
  Proof.
    admit. (* Semantics stuff *)
  Qed.

  Variables (regs1 regs2: list RegInitT)
            (r1 r2: list (Attribute (Action Void)))
            (dms1 dms2: list DefMethT).

  Variable countdown: nat.

  Definition m1 := Mod regs1 r1 dms1.
  Definition m2 := Mod regs2 r2 dms2.

  Definition cm := ConcatMod m1 m2.
  Definition im := @inlineMod m1 m2 countdown.
  
  Lemma inline_correct:
    forall cdn rm edms fdms rules dmsAll
           (Hsep: Inlinable cdn rm edms fdms rules dmsAll)
           (Hcdn: cdn = countdown) (Hrules: rules = r1 ++ r2) (HdmsAll: dmsAll = dms1 ++ dms2)
           or nr dmMap cmMap rmn,
      NoDup (namesOf (r1 ++ r2)) -> NoDup (namesOf (dms1 ++ dms2)) ->
      rmn = match rm with
              | Some rm' => Some (attrName rm')
              | None => None
            end ->

      DomainOf dmMap (namesOf edms) -> ValidLabel dmMap cmMap dmsAll ->
      SemMod (getRules cm) or rmn nr (getDmsBodies cm) dmMap cmMap ->
      SemMod (getRules im) or rmn nr (getDmsBodies im)
             (restrict dmMap (namesOf fdms))
             (complement cmMap (namesOf edms)).
  Proof.
    induction 1; intros.

    - subst; map_simpl_G.

      assert (dmMap = empty); subst.
      { admit. (* map stuffs: easy *) }
      
      inv H4; [|exfalso; eapply add_empty_neq; eauto].
      map_simpl_G; apply SemMod_empty.

    - subst; simpl.

      pose proof (decompose_SemMod_rule _ H9 H10 countdown eq_refl); clear H10.
      destruct H3 as [cmMapR [cmMapO [newsR [newsO H3]]]]; dest; subst.

      simpl in *.
      repeat
        match goal with
          | [H: SemMod _ _ _ _ _ ?d cmMapR |- _] => remember d as dmMapR
          | [H: SemMod _ _ _ _ _ ?d cmMapO |- _] => remember d as dmMapO
        end.

      match goal with
        | [ |- SemMod _ _ _ _ _ ?d _ ] =>
          replace d with (union empty (restrict dmMapO (namesOf pfdms))) by admit
      end.
      match goal with
        | [ |- SemMod _ _ _ _ _ _ ?c ] =>
          replace c
          with (union (complement
                         cmMapR
                         (namesOf (collectCalls (rule typeUT) (dms1 ++ dms2) countdown)))
                      (complement cmMapO (namesOf pedms))) by admit
      end.

      apply SemMod_merge_rule; auto.

      + apply SemMod_dms_free with (dms1:= dms1 ++ dms2).
        eapply inlineToRulesRep_prop; eauto.
      + apply IHHsep; auto.
        * admit. (* map stuffs: easy *)
        * admit. (* TODO: think about it; it is true, but is it a right condition? *)
      + apply Disj_complement, Disj_comm, Disj_complement, Disj_comm; auto.

    - subst; simpl.

      assert (find fdmn dmMap <> None) by admit. (* map stuffs: easy with DomainOf condition *)
      pose proof (decompose_SemMod_meth _ _ H9 H H3 H10 countdown eq_refl); clear H10.
      destruct H7 as [cmMapM [cmMapO [newsM [newsO H7]]]]; dest; subst.

      simpl in *.
      repeat
        match goal with
          | [H: SemMod _ _ _ _ _ ?d cmMapM |- _] => remember d as dmMapM
          | [H: SemMod _ _ _ _ _ ?d cmMapO |- _] => remember d as dmMapO
        end.

      match goal with
        | [ |- SemMod _ _ _ _ _ ?d _ ] =>
          replace d with (union (restrict dmMapM [fdmn])
                                (restrict dmMapO (namesOf pfdms))) by admit
      end.
      match goal with
        | [ |- SemMod _ _ _ _ _ _ ?c ] =>
          replace c
          with (union (complement
                         cmMapM
                         (namesOf (collectCalls (dm typeUT tt) (dms1 ++ dms2) countdown)))
                      (complement cmMapO (namesOf pedms))) by admit
      end.

      apply SemMod_merge_meths; auto.

      + eapply inlineToDmsRep_prop; eauto.
        * apply getAttribute_In; auto.
        * do 2 instantiate (1:= cheat _).
          admit. (* TODO: map stuffs, use SemMod_dmMap_sig first *)
        * apply SemMod_rules_free with (rules1:= r1 ++ r2).
          p_equal H7.
          admit. (* map stuffs; easy *)
      + apply IHHsep; auto.
        * admit. (* easy *)
        * admit. (* TODO: think about it; it is true, but is it a right condition? *)
      + admit.
      + apply Disj_complement, Disj_comm, Disj_complement, Disj_comm; auto.
  Qed.

End Facts.

