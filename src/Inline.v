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
    forall rules dms, map (@attrName _) rules = map (@attrName _) (inlineToRules rules dms).
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
    induction n; intros; simpl in *; [reflexivity|].
    rewrite (IHn rules dms).
    unfold inlineToRules; clear.
    induction rules; simpl; [reflexivity|].
    unfold inlineToRule; simpl; f_equal.
    assumption.
  Qed.

  Lemma inlineToRulesRep_names:
    forall n rules dms, map (@attrName _) rules = map (@attrName _) (inlineToRulesRep rules dms n).
  Proof.
    induction n; intros; simpl in *; [apply inlineToRules_names|].
    rewrite <-inlineToRules_names with (dms:= dms).
    apply IHn.
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

End Exts.

Require Import Semantics.

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

(* Inductive WfmAction_InlineDms {ty} (dms: list DefMethT): *)
(*   list string -> forall {ty retT}, ActionT ty retT -> nat -> Prop := *)
(* | WfmInlineO: forall ll {retT} (a: ActionT ty retT), *)
(*                 WfmAction ll a -> WfmAction ll (inlineDms a dms) -> *)
(*                 WfmAction_InlineDms dms ll a O *)
(* | WfmInlineS: forall ll n {retT} (a: ActionT ty retT), *)
(*                 WfmAction_InlineDms dms ll (inlineDms a dms) n -> *)
(*                 WfmAction ll a -> *)
(*                 WfmAction_InlineDms dms ll a (S n). *)

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
         (Hdms: NoDup (map (@attrName _) dms))
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
    forall olds1 olds2 (Holds: Disj olds1 olds2 \/ FnMap.Sub olds1 olds2)
           retK (at2: ActionT type retK)
           dmsAll1 dmsAll2 rules1 rules2
           news1 news2 newsA (Hnews12: Disj news1 news2)
           (Hnews1A: Disj news1 newsA) (Hnews2A: Disj news2 newsA)
           dmMap1 dmMap2 (Hdm: Disj dmMap1 dmMap2)
           cmMap1 cmMap2 cmMapA (Hcm12: Disj cmMap1 cmMap2)
           (Hcm1A: Disj cmMap1 cmMapA) (Hcm2A: Disj cmMap2 cmMapA)
           (retV: type retK),
      WfmAction nil at2 ->
      
      SemAction olds2 at2 newsA cmMapA retV ->

      DisjList (map (@attrName _) dmsAll1) (map (@attrName _) dmsAll2) ->
      NoDup (map (@attrName _) dmsAll1) -> NoDup (map (@attrName _) dmsAll2) ->
      restrict cmMapA (map (@attrName _) dmsAll1) = dmMap1 -> (* label matches *)
      restrict cmMapA (map (@attrName _) dmsAll2) = dmMap2 ->
                     
      SemMod rules1 olds1 None news1 dmsAll1 dmMap1 cmMap1 ->
      SemMod rules2 olds2 None news2 dmsAll2 dmMap2 cmMap2 ->
      
      SemAction (union olds1 olds2) (inlineDms at2 (dmsAll1 ++ dmsAll2))
                (union news1 (union news2 newsA))
                (union cmMap1
                       (union cmMap2
                              (complement cmMapA (map (@attrName _) (dmsAll1 ++ dmsAll2)))))
                retV.
  Proof.
    induction at2; intros.

    - inv H0; destruct_existT.
      inv H1; destruct_existT.
      simpl; remember (getBody meth (dmsAll1 ++ dmsAll2) s) as odm; destruct odm.

      + destruct s0; generalize dependent HSemAction; subst; intros.
        rewrite <-Eqdep.Eq_rect_eq.eq_rect_eq.
        econstructor; eauto.

        unfold getBody in Heqodm.
        remember (getAttribute meth (dmsAll1 ++ dmsAll2)) as dmAttr.
        destruct dmAttr; [|discriminate].
        destruct (SignatureT_dec _ _); [|discriminate].
        generalize dependent HSemAction; inv Heqodm; inv e0; intros.
        apply getAttribute_app in HeqdmAttr; destruct HeqdmAttr.

        * (* dealing with dmsAll1 *)
          pose proof (getAttribute_Some _ _ H0).
          rewrite restrict_add in H7 by assumption.
          rewrite restrict_add in Hdm by assumption.
          match goal with
            | [H: SemMod _ olds1 _ _ _ (add ?mn ?mv (restrict ?m ?dom)) _ |- _] =>
              assert (add mn mv (restrict m dom) =
                      union (add mn mv empty) (restrict m dom))
          end.
          { apply Equal_eq; repeat autounfold with MapDefs; intros k.
            unfold string_eq; destruct (string_dec _ _); [reflexivity|].
            reflexivity.
          }
          rewrite H5 in *; clear H5.

          match goal with
            | [H: SemMod _ olds1 _ _ _ (union ?m1 ?m2) _ |- _] =>
              assert (Disj m1 m2)
          end.
          { pose proof (WfmAction_cmMap HSemAction (H12 mret) meth (or_introl eq_refl)).
            repeat autounfold with MapDefs in *; intros k.
            unfold string_eq; destruct (string_dec _ _); [|left; reflexivity].
            subst; rewrite H5; right; destruct (in_dec _ _ _); reflexivity.
          }

          (* dealing with dmsAll2 *)
          assert (~ In meth (map (@attrName _) dmsAll2)).
          { clear -H1 H2; specialize (H2 meth).
            destruct H2; [elim H; assumption|assumption].
          }
          match goal with
            | [H: SemMod _ olds2 _ _ _ (restrict (add ?mn ?mv ?m) ?dm) _ |- _] =>
              assert (restrict (add mn mv m) dm = restrict m dm)
          end.
          { apply restrict_add_not; auto. }
          rewrite H9 in *; clear H9.

          (* getting rid of "meth" stuffs in order to apply IH *)
          rewrite complement_add_1 by (rewrite map_app; apply in_or_app; left; assumption).
          apply Disj_comm, Disj_union_2, Disj_comm in Hdm.
          pose proof (SemMod_div H7 H5); clear H5 H7; dest; subst.
          apply Disj_add_2 in Hcm1A; apply Disj_add_2 in Hcm2A.

          (* getting SemAction for meth *)
          pose proof (SemMod_meth_singleton H0 H3 H11).

          (* ready to prove! *)
          rewrite <-union_idempotent with (m:= olds1).
          rewrite <-union_assoc with (m1:= olds1).
          rewrite <-union_assoc with (m1:= x).
          rewrite <-union_assoc with (m1:= x1).
          apply appendAction_SemAction with (retV1:= mret); auto; [right; apply Sub_union|].

          eapply H; try reflexivity.
          { apply Disj_comm, Disj_union_2, Disj_comm in Hnews12; assumption. }
          { apply Disj_comm, Disj_union_2, Disj_comm in Hnews1A; assumption. }
          { assumption. }
          { assumption. }
          { apply Disj_comm, Disj_union_2, Disj_comm in Hcm12; assumption. }
          { apply Disj_comm, Disj_union_2, Disj_comm in Hcm1A; assumption. }
          { assumption. }
          { specialize (H12 mret); eapply WfmAction_init_sub; eauto.
            intros; inv H10.
          }
          { assumption. }
          { assumption. }
          { assumption. }
          { assumption. }
          { eassumption. }
          { eassumption. }
          
        * (* dealing with dmsAll2 *)
          pose proof (getAttribute_Some _ _ H0).
          rewrite restrict_add in H8 by assumption.
          apply Disj_comm in Hdm; rewrite restrict_add in Hdm by assumption.
          apply Disj_comm in Hdm.
          match goal with
            | [H: SemMod _ olds2 _ _ _ (add ?mn ?mv (restrict ?m ?dom)) _ |- _] =>
              assert (add mn mv (restrict m dom) =
                      union (add mn mv empty) (restrict m dom))
          end.
          { apply Equal_eq; repeat autounfold with MapDefs; intros k.
            unfold string_eq; destruct (string_dec _ _); [reflexivity|].
            reflexivity.
          }
          rewrite H5 in *; clear H5.

          match goal with
            | [H: SemMod _ olds2 _ _ _ (union ?m1 ?m2) _ |- _] =>
              assert (Disj m1 m2)
          end.
          { pose proof (WfmAction_cmMap HSemAction (H12 mret) meth (or_introl eq_refl)).
            repeat autounfold with MapDefs in *; intros k.
            unfold string_eq; destruct (string_dec _ _); [|left; reflexivity].
            subst; rewrite H5; right; destruct (in_dec _ _ _); reflexivity.
          }

          (* dealing with dmsAll1 *)
          assert (~ In meth (map (@attrName _) dmsAll1)).
          { clear -H1 H2; specialize (H2 meth).
            destruct H2; [assumption|elim H; assumption].
          }
          match goal with
            | [H: SemMod _ olds1 _ _ _ (restrict (add ?mn ?mv ?m) ?dm) _ |- _] =>
              assert (restrict (add mn mv m) dm = restrict m dm)
          end.
          { apply restrict_add_not; auto. }
          rewrite H9 in *; clear H9.

          (* getting rid of "meth" stuffs in order to apply IH *)
          rewrite complement_add_1 by (rewrite map_app; apply in_or_app; right; assumption).
          apply Disj_union_2 in Hdm.
          pose proof (SemMod_div H8 H5); clear H5 H8; dest; subst.
          apply Disj_add_2 in Hcm1A; apply Disj_add_2 in Hcm2A.

          (* getting SemAction for meth *)
          pose proof (SemMod_meth_singleton H0 H4 H11).

          (* ready to prove! *)
          assert (union olds1 olds2 = union olds2 (union olds1 olds2)).
          { destruct Holds.
            { rewrite <-union_idempotent with (m:= olds2) at 1.
              rewrite union_assoc with (m1:= olds1) at 1.
              rewrite union_comm with (m1:= olds1) by assumption.
              rewrite <-union_assoc with (m1:= olds2); f_equal.
              apply union_comm; assumption.
            }
            { rewrite Sub_merge by assumption.
              rewrite union_idempotent; reflexivity.
            }
          }
          rewrite H10; clear H10.

          rewrite union_assoc with (m1:= news1).
          rewrite union_comm with (m1:= news1) by assumption.
          rewrite <-union_assoc with (m2:= news1).
          rewrite <-union_assoc with (m1:= x).
          rewrite union_assoc with (m1:= x0).
          rewrite union_comm with (m1:= x0) by
              (apply Disj_union_2, Disj_comm in Hnews12; assumption).
          rewrite <-union_assoc with (m1:= news1).

          rewrite union_assoc with (m1:= cmMap1).
          rewrite union_comm with (m1:= cmMap1) by assumption.
          rewrite <-union_assoc with (m2:= cmMap1).
          rewrite <-union_assoc with (m1:= x1).
          rewrite union_assoc with (m1:= x2).
          rewrite union_comm with (m1:= x2) by
              (apply Disj_union_2, Disj_comm in Hcm12; assumption).
          rewrite <-union_assoc with (m1:= cmMap1).

          apply appendAction_SemAction with (retV1:= mret); auto.
          { right; destruct Holds.
            { rewrite Disj_union_unionR by assumption; apply Sub_union. }
            { rewrite Sub_merge by assumption; apply Sub_refl. }
          }

          eapply H; try reflexivity.
          { apply Disj_union_2 in Hnews12; assumption. }
          { assumption. }
          { apply Disj_comm, Disj_union_2, Disj_comm in Hnews2A; assumption. }
          { assumption. }
          { apply Disj_union_2 in Hcm12; assumption. }
          { assumption. }
          { apply Disj_comm, Disj_union_2, Disj_comm in Hcm2A; assumption. }
          { specialize (H12 mret); eapply WfmAction_init_sub; eauto.
            intros; inv H10.
          }
          { assumption. }
          { assumption. }
          { assumption. }
          { assumption. }
          { eassumption. }
          { eassumption. }
        
      + unfold getBody in Heqodm.
        remember (getAttribute meth (dmsAll1 ++ dmsAll2)) as mat.
        destruct mat.

        * destruct (SignatureT_dec (objType (attrType a0)) s); [discriminate|].
          exfalso; elim n; clear n.

          apply getAttribute_app in Heqmat; destruct Heqmat.
          { eapply getAttribute_SemMod; [exact H3|exact H7| |exact H0].
            pose proof (getAttribute_Some _ _ H0).
            rewrite restrict_add by assumption.
            map_simpl_G; reflexivity.
          }
          { eapply getAttribute_SemMod; [exact H4|exact H8| |exact H0].
            pose proof (getAttribute_Some _ _ H0).
            rewrite restrict_add by assumption.
            map_simpl_G; reflexivity.
          } 

        * clear Heqodm; econstructor; eauto.

          { instantiate
              (1:= union cmMap1
                         (union cmMap2
                                (complement calls (map (@attrName _) (dmsAll1 ++ dmsAll2))))).
            instantiate (1:= mret).

            clear -Heqmat Hcm1A Hcm2A.
            apply Equal_eq; repeat autounfold with MapDefs in *; intros k.
            specialize (Hcm1A k); specialize (Hcm2A k).
            unfold string_eq in *; destruct (string_dec meth k); [subst|reflexivity].
            destruct Hcm1A; [|discriminate].
            destruct Hcm2A; [|discriminate].
            rewrite H, H0; destruct (in_dec _ _ _); [|reflexivity].
            pose proof (getAttribute_None _ _ Heqmat); elim H1; assumption.
          }
          { eapply H; eauto.
            { eapply Disj_add_2; eauto. }
            { eapply Disj_add_2; eauto. }
            { specialize (H12 mret).
              eapply WfmAction_init_sub; eauto.
              intros; inv H0.
            }
            { assert (~ In meth (map (@attrName _) dmsAll1)).
              { pose proof (getAttribute_None _ _ Heqmat).
                intro Hx; elim H0.
                rewrite map_app; apply in_or_app; left; assumption.
              }
              rewrite restrict_add_not by assumption; reflexivity.
            }
            { assert (~ In meth (map (@attrName _) dmsAll2)).
              { pose proof (getAttribute_None _ _ Heqmat).
                intro Hx; elim H0.
                rewrite map_app; apply in_or_app; right; assumption.
              }
              rewrite restrict_add_not by assumption; reflexivity.
            }
          }
        
    - inv H0; destruct_existT.
      inv H1; destruct_existT.
      simpl; econstructor; eauto.

    - inv H0; destruct_existT.
      inv H1; destruct_existT.
      simpl; econstructor; eauto.

      destruct Holds.
      + apply Disj_find_union; auto.
      + rewrite Sub_merge; assumption.

    - inv H; destruct_existT.
      inv H0; destruct_existT.
      simpl; econstructor; eauto.
      + instantiate (1:= union news1 (union news2 newRegs)).
        clear -Hnews1A Hnews2A.
        apply Equal_eq; repeat autounfold with MapDefs in *; intros.
        specialize (Hnews1A k0); specialize (Hnews2A k0); destruct Hnews1A.
        * rewrite H; clear H.
          destruct Hnews2A.
          { rewrite H; clear H; reflexivity. }
          { rewrite H; unfold string_eq in *.
            destruct (string_dec r k0); [inv H|].
            rewrite H; reflexivity.
          }
        * rewrite H; unfold string_eq in *.
          destruct (string_dec r k0); [inv H|].
          rewrite H; reflexivity.
      + eapply IHat2 with (news2:= news2) (cmMap2:= cmMap2); eauto.
        * eapply Disj_add_2; eauto.
        * eapply Disj_add_2; eauto.

    - inv H0; destruct_existT.
      inv H1; destruct_existT.

      + rewrite restrict_union in H7, H8.
        assert (Disj calls1 calls2)
          by (pose proof (WfmAction_append_3 _ H13 HAction HSemAction); assumption).
        assert (Disj (restrict calls1 (map (@attrName _) dmsAll1))
                     (restrict calls2 (map (@attrName _) dmsAll1)))
          by (apply Disj_restrict, Disj_comm, Disj_restrict, Disj_comm; assumption).
        assert (Disj (restrict calls1 (map (@attrName _) dmsAll2))
                     (restrict calls2 (map (@attrName _) dmsAll2)))
          by (apply Disj_restrict, Disj_comm, Disj_restrict, Disj_comm; assumption).
        clear H0.
        
        pose proof (SemMod_div H7 H1); clear H7; dest; subst.
        pose proof (SemMod_div H8 H5); clear H8; dest; subst.

        simpl; eapply SemIfElseTrue.

        * assumption.
        * eapply IHat2_1 with (news1:= x) (news2:= x3) (newsA:= newRegs1)
                                          (cmMap1:= x1) (cmMap2:= x5) (cmMapA:= calls1)
                                          (retV:= r1);
            try reflexivity.

          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews12; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews1A; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews2A; assumption. }
          { apply Disj_DisjList_restrict.
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
          { assumption. }
          { assumption. }
          { eassumption. }
          { eassumption. }

        * eapply H with (news1:= x0) (news2:= x4) (newsA:= newRegs2)
                                     (cmMap1:= x2) (cmMap2:= x6) (cmMapA := calls2);
            try reflexivity.

          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hnews12; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hnews1A; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hnews2A; assumption. }
          { rewrite 2! restrict_union in Hdm.
            apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hdm; assumption.
          }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hcm12; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hcm1A; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hcm2A; assumption. }
          { eapply WfmAction_append_2; eauto. }
          { assumption. }
          { assumption. }
          { assumption. }
          { assumption. }
          { eassumption. }
          { eassumption. }
          
        * clear -Hnews12 Hnews1A Hnews2A.

          do 2 rewrite <-union_assoc with (m1:= x); f_equal.
          do 2 rewrite union_assoc with (m1:= x0).
          rewrite union_comm with (m1:= x0);
            [|apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hnews12; assumption].
          do 3 rewrite <-union_assoc with (m1:= x3); f_equal.
          rewrite <-union_assoc with (m1:= x0).
          rewrite union_assoc with (m1:= newRegs1).
          rewrite union_comm with (m2:= x0);
            [|apply Disj_union_1, Disj_comm, Disj_union_2 in Hnews1A; assumption].
          rewrite <-union_assoc with (m1:= x0); f_equal.
          do 2 rewrite union_assoc; f_equal.
          apply union_comm.
          apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hnews2A; assumption.
          
        * clear -Hcm1A Hcm2A Hcm12.

          rewrite complement_union.
          apply Disj_complement with (l:= map (@attrName _) (dmsAll1 ++ dmsAll2)) in Hcm1A.
          rewrite complement_union in Hcm1A.
          apply Disj_complement with (l:= map (@attrName _) (dmsAll1 ++ dmsAll2)) in Hcm2A.
          rewrite complement_union in Hcm2A.
          remember (complement calls1 (map (@attrName _) (dmsAll1 ++ dmsAll2))) as ccs1.
          remember (complement calls2 (map (@attrName _) (dmsAll1 ++ dmsAll2))) as ccs2.
          clear Heqccs1 Heqccs2.

          do 2 rewrite <-union_assoc with (m1:= x1); f_equal.
          do 2 rewrite union_assoc with (m1:= x2).
          rewrite union_comm with (m1:= x2);
            [|apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hcm12; assumption].
          do 3 rewrite <-union_assoc with (m1:= x5); f_equal.
          rewrite <-union_assoc with (m1:= x2).
          rewrite union_assoc with (m1:= ccs1).
          rewrite union_comm with (m2:= x2);
            [|apply Disj_union_1, Disj_comm, Disj_union_2 in Hcm1A; assumption].
          rewrite <-union_assoc with (m1:= x2); f_equal.
          do 2 rewrite union_assoc; f_equal.
          apply union_comm.
          apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hcm2A; assumption.

      + rewrite restrict_union in H7, H8.
        assert (Disj calls1 calls2)
          by (pose proof (WfmAction_append_3 _ H17 HAction HSemAction); assumption).
        assert (Disj (restrict calls1 (map (@attrName _) dmsAll1))
                     (restrict calls2 (map (@attrName _) dmsAll1)))
          by (apply Disj_restrict, Disj_comm, Disj_restrict, Disj_comm; assumption).
        assert (Disj (restrict calls1 (map (@attrName _) dmsAll2))
                     (restrict calls2 (map (@attrName _) dmsAll2)))
          by (apply Disj_restrict, Disj_comm, Disj_restrict, Disj_comm; assumption).
        clear H0.
        
        pose proof (SemMod_div H7 H1); clear H7; dest; subst.
        pose proof (SemMod_div H8 H5); clear H8; dest; subst.

        simpl; eapply SemIfElseFalse.

        * assumption.
        * eapply IHat2_2 with (news1:= x) (news2:= x3) (newsA:= newRegs1)
                                          (cmMap1:= x1) (cmMap2:= x5) (cmMapA:= calls1)
                                          (retV:= r1);
          try reflexivity.

          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews12; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews1A; assumption. }
          { apply Disj_union_1, Disj_comm, Disj_union_1, Disj_comm in Hnews2A; assumption. }
          { apply Disj_DisjList_restrict.
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
          { assumption. }
          { assumption. }
          { eassumption. }
          { eassumption. }

        * eapply H with (news1:= x0) (news2:= x4) (newsA:= newRegs2)
                                     (cmMap1:= x2) (cmMap2:= x6) (cmMapA := calls2);
          try reflexivity.

          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hnews12; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hnews1A; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hnews2A; assumption. }
          { rewrite 2! restrict_union in Hdm.
            apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hdm; assumption.
          }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hcm12; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hcm1A; assumption. }
          { apply Disj_union_2, Disj_comm, Disj_union_2, Disj_comm in Hcm2A; assumption. }
          { eapply WfmAction_append_2; eauto. }
          { assumption. }
          { assumption. }
          { assumption. }
          { assumption. }
          { eassumption. }
          { eassumption. }
          
        * clear -Hnews12 Hnews1A Hnews2A.

          do 2 rewrite <-union_assoc with (m1:= x); f_equal.
          do 2 rewrite union_assoc with (m1:= x0).
          rewrite union_comm with (m1:= x0);
            [|apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hnews12; assumption].
          do 3 rewrite <-union_assoc with (m1:= x3); f_equal.
          rewrite <-union_assoc with (m1:= x0).
          rewrite union_assoc with (m1:= newRegs1).
          rewrite union_comm with (m2:= x0);
            [|apply Disj_union_1, Disj_comm, Disj_union_2 in Hnews1A; assumption].
          rewrite <-union_assoc with (m1:= x0); f_equal.
          do 2 rewrite union_assoc; f_equal.
          apply union_comm.
          apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hnews2A; assumption.
          
        * clear -Hcm1A Hcm2A Hcm12.

          rewrite complement_union.
          apply Disj_complement with (l:= map (@attrName _) (dmsAll1 ++ dmsAll2)) in Hcm1A.
          rewrite complement_union in Hcm1A.
          apply Disj_complement with (l:= map (@attrName _) (dmsAll1 ++ dmsAll2)) in Hcm2A.
          rewrite complement_union in Hcm2A.
          remember (complement calls1 (map (@attrName _) (dmsAll1 ++ dmsAll2))) as ccs1.
          remember (complement calls2 (map (@attrName _) (dmsAll1 ++ dmsAll2))) as ccs2.
          clear Heqccs1 Heqccs2.

          do 2 rewrite <-union_assoc with (m1:= x1); f_equal.
          do 2 rewrite union_assoc with (m1:= x2).
          rewrite union_comm with (m1:= x2);
            [|apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hcm12; assumption].
          do 3 rewrite <-union_assoc with (m1:= x5); f_equal.
          rewrite <-union_assoc with (m1:= x2).
          rewrite union_assoc with (m1:= ccs1).
          rewrite union_comm with (m2:= x2);
            [|apply Disj_union_1, Disj_comm, Disj_union_2 in Hcm1A; assumption].
          rewrite <-union_assoc with (m1:= x2); f_equal.
          do 2 rewrite union_assoc; f_equal.
          apply union_comm.
          apply Disj_union_1, Disj_comm, Disj_union_2, Disj_comm in Hcm2A; assumption.

    - inv H; destruct_existT.
      inv H0; destruct_existT.
      simpl; econstructor; eauto.

    - inv H; destruct_existT.
      inv H0; destruct_existT.
      map_simpl H6; map_simpl H7.
      pose proof (SemMod_empty_inv H6); dest; subst.
      pose proof (SemMod_empty_inv H7); dest; subst.
      simpl; map_simpl_G.
      econstructor; eauto.

  Qed.

  Lemma inlineToRules_prop:
    forall olds1 olds2 (Holds: Disj olds1 olds2 \/ FnMap.Sub olds1 olds2)
           r (ar: Action (Bit 0))
           dmsAll1 dmsAll2 rules1 rules2
           news1 news2 newsA (Hnews12: Disj news1 news2)
           (Hnews1A: Disj news1 newsA) (Hnews2A: Disj news2 newsA)
           dmMap1 dmMap2 (Hdm: Disj dmMap1 dmMap2)
           cmMap1 cmMap2 cmMapA (Hcm12: Disj cmMap1 cmMap2)
           (Hcm1A: Disj cmMap1 cmMapA) (Hcm2A: Disj cmMap2 cmMapA),
      WfmAction nil (ar type) ->
      In {| attrName := r; attrType := ar |} rules2 -> NoDup (map (@attrName _) rules2) ->

      SemMod rules2 olds2 (Some r) newsA dmsAll2 empty cmMapA ->

      DisjList (map (@attrName _) dmsAll1) (map (@attrName _) dmsAll2) ->
      NoDup (map (@attrName _) dmsAll1) -> NoDup (map (@attrName _) dmsAll2) ->
      restrict cmMapA (map (@attrName _) dmsAll1) = dmMap1 -> (* label matches *)
      restrict cmMapA (map (@attrName _) dmsAll2) = dmMap2 ->
                     
      SemMod rules1 olds1 None news1 dmsAll1 dmMap1 cmMap1 ->
      SemMod rules2 olds2 None news2 dmsAll2 dmMap2 cmMap2 ->

      SemMod (inlineToRules rules2 (dmsAll1 ++ dmsAll2)) (union olds1 olds2) (Some r)
             (union news1 (union news2 newsA)) (dmsAll1 ++ dmsAll2) empty
             (union cmMap1
                    (union cmMap2
                           (complement cmMapA (map (@attrName _) (dmsAll1 ++ dmsAll2))))).
  Proof.
    intros; inv H2.
    pose proof (SemMod_empty_inv HSemMod); dest; subst.
    
    econstructor.
    - pose proof (inlineToRules_In _ _ (dmsAll1 ++ dmsAll2) HInRule); simpl in H2.
      eassumption.
    - simpl; eapply inlineDms_prop with (newsA:= news) (cmMapA:= calls).
      + assumption.
      + exact Hnews12.
      + apply Disj_union_1 in Hnews1A; auto.
      + apply Disj_union_1 in Hnews2A; auto.
      + exact Hdm.
      + exact Hcm12.
      + apply Disj_union_1 in Hcm1A; auto.
      + apply Disj_union_1 in Hcm2A; auto.
      + assert (ar = ruleBody); subst.
        { clear -H0 H1 HInRule.
          generalize dependent r; generalize dependent ar; generalize dependent ruleBody.
          induction rules2; intros; [inv H0|].
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
            { inv H1; eapply IHrules2; eauto. }
          }
        }
        assumption.
      + eassumption.
      + assumption.
      + assumption.
      + assumption.
      + map_simpl_G; reflexivity.
      + map_simpl_G; reflexivity.
      + eassumption.
      + eassumption.
    - apply SemMod_empty.
    - auto.
    - auto.
    - map_simpl_G; rewrite union_assoc; reflexivity.
    - map_simpl_G; rewrite union_assoc; reflexivity.
  Qed.

  Lemma inlineToRulesRep_prop:
    forall olds1 olds2 (Holds: Disj olds1 olds2)
           cdn r (ar: Action (Bit 0))
           dmsAll1 dmsAll2 rules2 newsA cmMapA,
      WfmAction nil (ar type) ->
      In {| attrName := r; attrType := ar |} rules2 -> NoDup (map (@attrName _) rules2) ->
      noCallsRules (inlineToRulesRep rules2 (dmsAll1 ++ dmsAll2) cdn)
                   (map (@attrName _) (dmsAll1 ++ dmsAll2)) = true ->

      SemMod rules2 olds2 (Some r) newsA dmsAll2 empty cmMapA ->

      DisjList (map (@attrName _) dmsAll1) (map (@attrName _) dmsAll2) ->
      NoDup (map (@attrName _) dmsAll1) -> NoDup (map (@attrName _) dmsAll2) ->
      restrict cmMapA (map (@attrName _) dmsAll1) = empty -> (* label matches *)
      restrict cmMapA (map (@attrName _) dmsAll2) = empty ->
      
      SemMod (inlineToRulesRep rules2 (dmsAll1 ++ dmsAll2) cdn) (union olds1 olds2) (Some r)
             newsA (dmsAll1 ++ dmsAll2) empty
             (complement cmMapA (map (@attrName _) (dmsAll1 ++ dmsAll2))).
  Proof.
    induction cdn; intros.

    - simpl; simpl in H2.
      rewrite <-union_empty_1 with (m:= newsA).
      rewrite <-union_empty_1 with (m:= union empty newsA).
      rewrite <-union_empty_1 with (m:= complement _ _).
      rewrite <-union_empty_1 with (m:= union empty (complement _ _)).
      eapply inlineToRules_prop; eauto.
      + auto.
      + instantiate (1:= nil); apply SemMod_empty.
      + apply SemMod_empty.

    - simpl; simpl in H2.

      remember (noCallsRules (inlineToRulesRep rules2 (dmsAll1 ++ dmsAll2) cdn)
                             (map (@attrName _) (dmsAll1 ++ dmsAll2))) as pb.
      destruct pb; symmetry in Heqpb.

      + rewrite <-union_idempotent with (m:= olds1).
        rewrite <-union_assoc with (m1:= olds1).
        rewrite <-union_empty_1 with (m:= newsA).
        rewrite <-union_empty_1 with (m:= union empty newsA).
        rewrite <-union_empty_1 with (m:= complement _ _).
        rewrite <-union_empty_1 with (m:= union empty (complement _ _)).
        eapply inlineToRules_prop.

        (* * left; assumption. *)
        * right; apply Sub_union.
        * auto.
        * auto.
        * auto.
        * instantiate (1:= empty); instantiate (1:= empty); auto.
        * auto.
        * auto.
        * auto.
        * instantiate (1:= (fun t => inlineDmsRep (ar t) (dmsAll1 ++ dmsAll2) cdn)).
          admit. (* inlineDms Wfm *)
        * clear -H0 H1.
          rewrite inlineToRulesRep_inlineDmsRep.
          apply in_map with (B:= Attribute (Action (Bit 0)))
                              (f:= fun ar => (attrName ar :: (fun t => inlineDmsRep
                                                                         (attrType ar t)
                                                                         (dmsAll1 ++ dmsAll2)
                                                                         cdn))%struct) in H0.
          assumption.
        * clear -H1; rewrite <-inlineToRulesRep_names; assumption.
        * apply SemMod_dms_cut with (dms1:= dmsAll1 ++ dmsAll2); auto;
          [|intros; apply in_or_app; right; assumption].
          replace cmMapA with (complement cmMapA (map (@attrName _) (dmsAll1 ++ dmsAll2))).
          { eapply IHcdn; eauto. }
          { clear -H7 H8.
            apply restrict_complement_itself.
            apply Equal_eq; repeat autounfold with MapDefs in *; intro k.
            apply @Equal_val with (k:= k) in H7.
            apply @Equal_val with (k:= k) in H8.
            destruct (in_dec _ k (map (@attrName _) (dmsAll1 ++ dmsAll2))); [|reflexivity].
            rewrite map_app in i; apply in_app_or in i; destruct i.
            { destruct (in_dec _ k (map (@attrName _) dmsAll1)); intuition. }
            { destruct (in_dec _ k (map (@attrName _) dmsAll2)); intuition. }
          }
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * assumption.
        * instantiate (1:= nil); apply SemMod_empty.
        * apply SemMod_empty.

      + admit.

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
  (* Definition im := @inlineMod m1 m2 countdown. *)

  (* Lemma inline_correct_rule: *)
  (*   forall r or nr cmMap, *)
  (*     noCallsRules (getRules im) (map (@attrName _) (dms1 ++ dms2)) = true -> *)
  (*     LtsStep cm (Some r) or nr empty cmMap -> LtsStep im (Some r) or nr empty cmMap. *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)

End Facts.
