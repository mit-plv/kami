Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FnMap.
Require Import Syntax Equiv.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Ltac destruct_existT :=
  repeat match goal with
           | [H: existT _ _ _ = existT _ _ _ |- _] =>
             (apply Eqdep.EqdepTheory.inj_pair2 in H; subst)
         end.

Fixpoint getAttribute (n: string) {t} (attrs: list (Attribute t)) :=
  match attrs with
    | nil => None
    | attr :: attrs' =>
      if string_dec n (attrName attr) then Some attr
      else getAttribute n attrs'
  end.

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

  Lemma getCalls_SubList: forall {retT} (a: ActionT typeUT retT) cs rcs,
                            getCalls a cs = rcs -> SubList rcs cs.
  Proof. admit. Qed.

  Lemma getCalls_nil: forall {retT} (a: ActionT typeUT retT), getCalls a nil = nil.
  Proof.
    induction a; intros; simpl; intuition.
    rewrite IHa1, IHa2, (H tt); reflexivity.
  Qed.

  Section NoCalls.
    (* Necessary condition for inlining correctness *)
    Fixpoint noCalls {retT} (a: ActionT typeUT retT) :=
      match a with
        | MCall _ _ _ _ => false
        | Let_ _ ar cont => noCalls (cont (getUT _))
        | ReadReg reg k cont => noCalls (cont (getUT _))
        | WriteReg reg _ e cont => noCalls cont
        | IfElse ce _ ta fa cont => (noCalls ta) && (noCalls fa) && (noCalls (cont tt))
        | Assert_ ae cont => noCalls cont
        | Return e => true
      end.

    Fixpoint noCallsRules (rules: list (Attribute (Action Void))) :=
      match rules with
        | nil => true
        | {| attrType := r |} :: rules' => (noCalls (r typeUT)) && (noCallsRules rules')
      end.
  
    Fixpoint noCallsDms (dms: list DefMethT) :=
      match dms with
        | nil => true
        | {| attrType := {| objVal := dm |} |} :: dms' =>
          (noCalls (dm typeUT tt)) && (noCallsDms dms')
      end.

    Fixpoint noCallsMod (m: Modules) :=
      match m with
        | Mod _ rules dms => (noCallsRules rules) && (noCallsDms dms)
        | ConcatMod m1 m2 => (noCallsMod m1) && (noCallsMod m2)
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

  Fixpoint inlineDms {retT} (a: ActionT type retT) (dms: list DefMethT): ActionT type retT :=
    match a with
      | MCall name sig ar cont =>
        match getAttribute name dms with
          | Some dm =>
            match SignatureT_dec (objType (attrType dm)) sig with
              | left e => appendAction (inlineArg ar ((eq_rect _ _ (objVal (attrType dm)) _ e)
                                                      type))
                                       (fun ak => inlineDms (cont ak) dms)
              | right _ => MCall name sig ar (fun ak => inlineDms (cont ak) dms)
            end
          | _ => MCall name sig ar (fun ak => inlineDms (cont ak) dms)
        end
      | Let_ _ ar cont => Let_ ar (fun a => inlineDms (cont a) dms)
      | ReadReg reg k cont => ReadReg reg k (fun a => inlineDms (cont a) dms)
      | WriteReg reg _ e cont => WriteReg reg e (inlineDms cont dms)
      | IfElse ce _ ta fa cont => IfElse ce (inlineDms ta dms) (inlineDms fa dms)
                                         (fun a => inlineDms (cont a) dms)
      | Assert_ ae cont => Assert_ ae (inlineDms cont dms)
      | Return e => Return e
    end.

  Fixpoint inlineDmsRep {retT} (a: ActionT type retT) (dms: list DefMethT)
           (n: nat): ActionT type retT :=
    match n with
      | O => a
      | S n' => inlineDmsRep (inlineDms a dms) dms n'
    end.

End Phoas.

Section Countdown.
  Variable countdown: nat.
  
  Definition inlineToRule (r: Attribute (Action (Bit 0)))
             (dms: list DefMethT): Attribute (Action (Bit 0)) :=
    match r with
      | {| attrName := rn; attrType := ra |} =>
        {| attrName := rn;
           attrType := (fun ty => inlineDmsRep (ra ty) dms countdown) |}
    end.

  Fixpoint inlineToRules (rules: list (Attribute (Action (Bit 0))))
           (dms: list DefMethT): list (Attribute (Action (Bit 0))) :=
    match rules with
      | nil => nil
      | r :: rules' => (inlineToRule r dms) :: (inlineToRules rules' dms)
    end.

  Lemma inlineToRules_In:
    forall r rules dms, In r rules -> In (inlineToRule r dms) (inlineToRules rules dms).
  Proof.
    induction rules; intros; inv H.
    - left; reflexivity.
    - right; apply IHrules; auto.
  Qed.

  Definition inlineToDm (n: string) {argT retT} (m: forall ty, ty argT -> ActionT ty retT)
             (dms: list DefMethT): forall ty, ty argT -> ActionT ty retT :=
    fun ty a => inlineDmsRep (m ty a) dms countdown.

  Fixpoint inlineToDms (dms: list DefMethT): list DefMethT :=
    match dms with
      | nil => nil
      | {| attrName := n; attrType := {| objType := s; objVal := a |} |} :: dms' =>
        {| attrName := n; attrType := {| objType := s; objVal := inlineToDm n a dms |} |}
          :: (inlineToDms dms')
    end.

  Definition inlineMod (m1 m2: Modules): Modules :=
    match m1, m2 with
      | Mod regs1 r1 dms1, Mod regs2 r2 dms2 =>
        Mod (regs1 ++ regs2) (inlineToRules (r1 ++ r2) (dms1 ++ dms2))
            (inlineToDms (dms1 ++ dms2))
      | _, _ => m1 (* undefined *)
    end.
  
End Countdown.

Require Import Semantics.

Lemma getCalls_prop:
  forall {retK} (aunit: ActionT typeUT retK) (asem: ActionT type retK)
         (Hequiv: ActionEquiv nil aunit asem)
         calls rcs (Hcalls: getCalls aunit calls = rcs)
         olds news cmMap retV
         (Hsem: SemAction olds asem news cmMap retV),
    InDomain cmMap (map (@attrName _) rcs).
Proof.
  admit.
Qed.

Lemma action_olds_ext:
  forall retK a olds1 olds2 news calls (retV: type retK),
    FnMap.Sub olds1 olds2 ->
    SemAction olds1 a news calls retV ->
    SemAction olds2 a news calls retV.
Proof.
  induction a; intros.
  - invertAction H1; econstructor; eauto.
  - invertAction H1; econstructor; eauto.
  - invertAction H1; econstructor; eauto.
    repeat autounfold with MapDefs; repeat autounfold with MapDefs in H1.
    rewrite <-H1; symmetry; apply H0; unfold InMap, find; rewrite H1; discriminate.
  - invertAction H0; econstructor; eauto.
  - invertAction H1.
    remember (evalExpr e) as cv; destruct cv; dest.
    + eapply SemIfElseTrue; eauto.
    + eapply SemIfElseFalse; eauto.
  - invertAction H0; econstructor; eauto.
  - invertAction H0; econstructor; eauto.
Qed.

Lemma appendAction_SemAction_1:
  forall retK1 retK2 a1 a2 olds1 olds2 news1 news2 calls1 calls2
         (retV1: type retK1) (retV2: type retK2),
    Disj olds1 olds2 ->
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
      * eapply action_olds_ext.
        { instantiate (1:= olds1); apply Sub_union. }
        { exact H1. }
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.
    + eapply SemIfElseFalse.
      * eauto.
      * eapply action_olds_ext.
        { instantiate (1:= olds1); apply Sub_union. }
        { exact H1. }
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.

  - invertAction H0; specialize (IHa1 _ _ _ _ _ _ _ _ _ H H0 H1); econstructor; eauto.
  - invertAction H0; map_simpl_G; econstructor.
    eapply action_olds_ext; eauto.
    rewrite Disj_union_unionR; auto.
    apply Sub_unionR.
    
Qed.

Lemma appendAction_SemAction_2:
  forall retK1 retK2 a1 a2 olds1 olds2 news1 news2 calls1 calls2
         (retV1: type retK1) (retV2: type retK2),
    FnMap.Sub olds1 olds2 ->
    SemAction olds1 a1 news1 calls1 retV1 ->
    SemAction olds2 (a2 retV1) news2 calls2 retV2 ->
    SemAction olds2 (appendAction a1 a2) (union news1 news2) (union calls1 calls2) retV2.
Proof.
  induction a1; intros.

  - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2); econstructor; eauto.
  - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2); econstructor; eauto.
  - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H3 H2); econstructor; eauto.
    specialize (H0 r); unfold InMap in H0; rewrite H1 in H0; specialize (H0 (opt_discr _)).
    rewrite <-H1; unfold find; auto.
  - invertAction H0; specialize (IHa1 _ _ _ _ _ _ _ _ _ H H0 H1); econstructor; eauto.

  - invertAction H1.
    simpl; remember (evalExpr e) as cv; destruct cv; dest; subst.
    + eapply SemIfElseTrue.
      * eauto.
      * eapply action_olds_ext; eauto.
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.
    + eapply SemIfElseFalse.
      * eauto.
      * eapply action_olds_ext; eauto.
      * eapply H; eauto.
      * rewrite union_assoc; reflexivity.
      * rewrite union_assoc; reflexivity.

  - invertAction H0; specialize (IHa1 _ _ _ _ _ _ _ _ _ H H0 H1); econstructor; eauto.
  - invertAction H0; map_simpl_G; econstructor; eauto.
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
      instantiate (1:= union x x1); instantiate (1:= olds1).
      eapply appendAction_SemAction_2; eauto.
      intuition.
    + specialize (@IHWfmAction2 _ (appendAction a1_2 a) a2 (appendAction_assoc _ _ _)).
      eapply IHWfmAction2; eauto.
      instantiate (1:= union x x1); instantiate (1:= olds1).
      eapply appendAction_SemAction_2; eauto.
      intuition.
    
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

Section Preliminaries.

  Lemma SemMod_singleton:
    forall rules olds news dm dmMap cmMap,
      SemMod rules olds None news (dm :: nil) dmMap cmMap ->
      DomainOf dmMap ((attrName dm) :: nil) ->
      exists argV retV,
        dm = {| attrName := attrName dm;
                attrType := {| objType := {| arg := arg (objType (attrType dm));
                                             ret := ret (objType (attrType dm)) |};
                               objVal := objVal (attrType dm) |} |} /\
        dmMap = add (attrName dm) {| objVal := (argV, retV) |} empty /\
        SemAction olds (objVal (attrType dm) type argV) news cmMap retV.
  Proof.
    intros.
    invertSemMod H.

    - invertSemMod HSemMod.
      exists argV; exists retV.
      split.
      
      + destruct dm as [dmn [[ ] ]]; simpl; reflexivity.
      + split; [reflexivity|].
        map_simpl_G; assumption.

    - invertSemMod HSemMod; exfalso.
      specialize (H0 (attrName dm)); destruct H0.
      specialize (H0 (or_introl eq_refl)).
      unfold InMap in H0; elim H0; reflexivity.
  Qed.

  Lemma SemMod_div:
    forall rules olds rm news dms dmMap cmMap
           (Hsem: SemMod rules olds rm news dms dmMap cmMap) divd,
    exists news1 news2 dmMap1 dmMap2 cmMap1 cmMap2,
      Disj news1 news2 /\ news = union news1 news2 /\
      dmMap = disjUnion dmMap1 dmMap2 divd /\
      Disj cmMap1 cmMap2 /\ cmMap = union cmMap1 cmMap2 /\
      SemMod rules olds rm news1 dms dmMap1 cmMap1 /\
      SemMod rules olds rm news2 dms dmMap2 cmMap2.
  Proof.
    admit.
  Qed.

  Lemma inlineDms_prop:
    forall olds1 olds2 (Holds: Disj olds1 olds2 \/ FnMap.Sub olds1 olds2)
           retK (au2: ActionT typeUT retK) (at2: ActionT type retK)
           (Hequiv: ActionEquiv nil au2 at2) (* induction base *)
           dmsAll1 dmsAll2 dms1 dms2 rules1 rules2
           news1 news2 newsA (Hnews12: Disj news1 news2)
           (Hnews1A: Disj news1 newsA) (Hnews2A: Disj news2 newsA)
           dmMap1 dmMap2 (Hdm: Disj dmMap1 dmMap2)
           cmMap1 cmMap2 cmMapA (Hcm12: Disj cmMap1 cmMap2)
           (Hcm1A: Disj cmMap1 cmMapA) (Hcm2A: Disj cmMap2 cmMapA)
           (retV: type retK),
      WfmAction nil at2 ->
      
      SemAction olds2 at2 newsA cmMapA retV ->

      DisjList (map (@attrName _) dmsAll1) (map (@attrName _) dmsAll2) ->
      dms1 = getCalls au2 dmsAll1 -> (* actually inlined methods *)
      dms2 = getCalls au2 dmsAll2 ->
      restrict cmMapA (map (@attrName _) dms1) = dmMap1 -> (* label matches *)
      restrict cmMapA (map (@attrName _) dms2) = dmMap2 ->
      DomainOf dmMap1 (map (@attrName _) dms1) -> (* valid SemMod *)
      DomainOf dmMap2 (map (@attrName _) dms2) ->
                     
      SemMod rules1 olds1 None news1 dmsAll1 dmMap1 cmMap1 ->
      SemMod rules2 olds2 None news2 dmsAll2 dmMap2 cmMap2 ->
      
      SemAction (union olds1 olds2) (inlineDms at2 (dmsAll1 ++ dmsAll2))
                (union news1 (union news2 newsA))
                (union cmMap1
                       (union cmMap2
                              (complement cmMapA (map (@attrName _) (dmsAll1 ++ dmsAll2)))))
                retV.
  Proof.
    induction 2; intros.

    - inv H1; destruct_existT.
      inv H2; destruct_existT.
      admit.
      
    - inv H1; destruct_existT.
      inv H2; destruct_existT.
      simpl; econstructor; eauto.

    - inv H1; destruct_existT.
      inv H2; destruct_existT.
      simpl; econstructor; eauto.
      destruct Holds.
      + apply Disj_find_union; auto.
      + rewrite Sub_merge; assumption.

    - inv H0; destruct_existT.
      inv H1; destruct_existT.
      simpl; econstructor; eauto.
      + instantiate (1:= union news1 (union news2 newRegs)).
        clear -Hnews1A Hnews2A.
        apply Equal_eq; repeat autounfold with MapDefs in *; intro k.
        specialize (Hnews1A k); specialize (Hnews2A k); destruct Hnews1A.
        * rewrite H; clear H.
          destruct Hnews2A.
          { rewrite H; clear H; reflexivity. }
          { rewrite H; unfold string_eq in *.
            destruct (string_dec rn k); [inv H|].
            rewrite H; reflexivity.
          }
        * rewrite H; unfold string_eq in *.
          destruct (string_dec rn k); [inv H|].
          rewrite H; reflexivity.
      + eapply IHHequiv with (news2:= news2) (cmMap2:= cmMap2); eauto.
        * eapply Disj_add_2; eauto.
        * eapply Disj_add_2; eauto.

    - inv H2; destruct_existT.
      inv H3; destruct_existT.

      + pose proof (SemMod_div H11 (map (@attrName _) (getCalls ta1 dmsAll1))).
        clear H11; dest; subst; clear H11.
        pose proof (SemMod_div H12 (map (@attrName _) (getCalls ta1 dmsAll2))).
        clear H12; dest; subst; clear H15.

        simpl; eapply SemIfElseTrue.

        * assumption.
        * eapply IHHequiv1 with (news1:= x) (news2:= x5) (newsA:= newRegs1)
                                            (cmMap1:= x3) (cmMap2:= x9) (cmMapA:= calls1)
                                            (retV:= r1);
            try reflexivity.

          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews12; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews1A; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews2A; assumption. }
          { apply Disj_DisjList_restrict.
            pose proof (getCalls_SubList ta1 dmsAll1 eq_refl).
            pose proof (getCalls_SubList ta1 dmsAll2 eq_refl).
            apply DisjList_SubList with (l1:= map (@attrName _) dmsAll1); apply DisjList_comm.
            apply DisjList_SubList with (l1:= map (@attrName _) dmsAll2); apply DisjList_comm.
            assumption.
          }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hcm12; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hcm1A; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hcm2A; assumption. }
          { eapply WfmAction_append_1; eauto. }
          { assumption. }
          { assumption. }
          { admit. (* map-related proof; possible. *) }
          { admit. (* map-related proof; possible. *) }
          { assert (x1 = restrict calls1 (map (@attrName _) (getCalls ta1 dmsAll1))); subst.
            { admit. (* map-related proof; possible. *) }
            eassumption.
          }
          { assert (x7 = restrict calls1 (map (@attrName _) (getCalls ta1 dmsAll2))); subst.
            { admit. (* map-related proof; possible. *) }
            eassumption.
          }
        * exfalso; admit.
        * instantiate (1:= union x0 (union x6 newRegs2)).
          admit. (* map-related proof; possible. *)
        * instantiate (1:= union x4 x9). (* ??? *)
          admit.

      + admit.
            
    - inv H0; destruct_existT.
      inv H1; destruct_existT.
      simpl; econstructor; eauto.

    - inv H0; destruct_existT.
      inv H1; destruct_existT.
      map_simpl H9; map_simpl H10.
      pose proof (SemMod_empty_inv H9); dest; subst.
      pose proof (SemMod_empty_inv H10); dest; subst.
      simpl; map_simpl_G.
      econstructor; eauto.

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
  Definition im := @inlineMod countdown m1 m2.

  Lemma inline_correct_rule:
    forall r or nr cmMap,
      (* noCallsMod getDefault im = true -> *)
      LtsStep cm (Some r) or nr empty cmMap -> LtsStep im (Some r) or nr empty cmMap.
  Proof.
    admit.
  Qed.

End Facts.
