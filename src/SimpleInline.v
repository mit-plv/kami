Require Import Syntax Inline List Lib.Struct Program.Equality Equiv
        String FunctionalExtensionality InlineFacts_2.

Set Implicit Arguments.

Lemma notNamesNotIn: forall A l (x: Attribute A), ~ In (attrName x) (namesOf l) -> In x l -> False.
Proof.
  intros A.
  induction l; intros.
  - intuition.
  - simpl in *.
    destruct H0; subst.
    assert (sth: ~ attrName x = attrName x) by intuition.
    intuition.
    assert (sth: ~ In (attrName x) (namesOf l)) by intuition.
    eapply IHl; eauto.
Qed.

Section ActionNoCall.
  Variable k: Kind.
  Variable ty: Kind -> Type.
  Variable aUT: ActionT typeUT k.
  Variable dm: DefMethT.
  Variable noCalls: ~ In (attrName dm) (getCallsA aUT).
  Variable c: ctxt (fullType ty) (fullType typeUT).

  Theorem inlineNoCallsAction_matches a (aEquiv: ActionEquiv c a aUT): inlineDm a dm = a.
  Proof.
    dependent induction aEquiv; simpl in *; intuition auto.
    - unfold getBody.
      case_eq (StringEq.string_eq n (attrName dm)); intros.
      + apply eq_sym in H3.
        apply StringEq.string_eq_dec_eq in H3.
        intuition.
      + f_equal; extensionality v1.
        apply H0 with (v2 := tt); intuition auto.
    - f_equal; extensionality v1.
      destruct k1'; simpl in *.
      + eapply H0; eauto.
      + eapply H0; eauto.
    - f_equal; extensionality v1.
      destruct k1'; simpl in *.
      + eapply H0; eauto.
      + eapply H0; eauto.
    - f_equal; intuition.
    - f_equal.
      + assert (In (attrName dm) (getCallsA ta2) -> False) by intuition.
        intuition.
      + assert (In (attrName dm) (getCallsA fa2 ++ getCallsA (cont2 tt)) -> False) by intuition.
        assert (In (attrName dm) (getCallsA fa2) -> False) by intuition.
        intuition.
      + assert (In (attrName dm) (getCallsA fa2 ++ getCallsA (cont2 tt)) -> False) by intuition.
        assert (In (attrName dm) (getCallsA (cont2 tt)) -> False) by intuition.
        extensionality v1.
        apply (H1 v1 tt H3).
    - f_equal; auto.
  Qed.
End ActionNoCall.

Section MethNoCall.
  Variable dms: list DefMethT.
  Variable dm: DefMethT.
  Variable noCallsInDefs: ~ In (attrName dm) (getCallsM dms).

  Theorem inlineNoCallMeths_matches (equiv: forall ty, MethsEquiv ty typeUT dms)
  : inlineDmToDms dms dm = dms.
  Proof.
    generalize dependent dms; clear.
    intros dms.
    induction dms; intros; simpl in *.
    - intuition.
    - assert (eq': forall ty, MethsEquiv ty typeUT l).
      { intros.
        specialize (equiv ty).
        dependent destruction equiv.
        assumption.
      }
      assert (s1: ~ In (attrName dm) (getCallsA (projT2 (attrType a) typeUT tt))) by intuition.
      assert (s2: ~ In (attrName dm) (getCallsM l)) by intuition.
      specialize (IHl s2 eq').  
      f_equal; try assumption.
      unfold inlineDmToDm.
      destruct a; simpl in *.
      f_equal.
      destruct attrType.
      f_equal.
      simpl in *.
      extensionality ty'.
      extensionality arg1.
      specialize (equiv ty').
      dependent destruction equiv.
      specialize (H arg1 tt).
      eapply inlineNoCallsAction_matches; eauto.
      Grab Existential Variables.
      constructor.
  Qed.
End MethNoCall.

Lemma inlineDmToMod_ModEquiv_General:
  forall m dm ty,
    ModEquiv ty typeUT m ->
    ModEquiv ty typeUT (fst (inlineDmToMod m dm)).
Proof.
  intros.
  unfold inlineDmToMod.
  remember (getAttribute _ _) as oattr; destruct oattr; [|auto].
  simpl in Heqoattr.
  apply getAttribute_Some_body in Heqoattr.
  simpl; inversion H.
  pose proof (MethsEquiv_in _ H1 Heqoattr).
  constructor.
  - apply inlineDmToRules_RulesEquiv; auto.
  - apply inlineDmToDms_MethsEquiv; auto.
Qed.

Section NoCallsInDefs.
  Variable m: Modules.
  Variable noCallsInDefs: forall i, ~ (In i (getCallsM (getDefsBodies m)) /\ In i (getDefs m)).
  Variable noDups: NoDup (getDefs m).
  Variable equiv: forall ty, ModEquiv ty typeUT m.
  
  Definition simpleInlineDmToMod (dm: DefMethT) :=
    Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
        (getDefsBodies m).

  Lemma getAttribute_notNone:
    forall A (l: list (Attribute A)) x, NoDup (namesOf l) -> In x l ->
                                        getAttribute (attrName x) l = Some x.
  Proof.
    clear.
    intros A.
    induction l; intros; simpl in *.
    - intuition.
    - destruct H0; subst; try reflexivity.
      + case_eq (StringEq.string_eq (attrName x) (attrName x)); intros; try reflexivity.
        apply eq_sym in H0. apply StringEq.string_eq_dec_neq in H0; intuition.
      + dependent destruction H.
        specialize (IHl _ H0 H1).
        case_eq (StringEq.string_eq (attrName x) (attrName a)); intros; subst.
        apply eq_sym in H2; apply StringEq.string_eq_dec_eq in H2; intuition.
        * rewrite <- H2 in H.
          generalize H H1; clear; intros; exfalso.
          eapply notNamesNotIn; eauto.
        * apply eq_sym in H2; apply StringEq.string_eq_dec_neq in H2; intuition.
  Qed.

  Lemma simpleInlineDmToMod_matches:
    forall dm, In dm (getDefsBodies m) ->
               simpleInlineDmToMod dm = fst (inlineDmToMod m (attrName dm)).
  Proof.
    intros.
    unfold inlineDmToMod, simpleInlineDmToMod.
    rewrite getAttribute_notNone; simpl; auto.
    f_equal.
    rewrite inlineNoCallMeths_matches; auto.
    specialize (noCallsInDefs (attrName dm)); intuition auto.
    - apply notNamesNotIn in H2; intuition.
    - intros.
      specialize (equiv ty).
      dependent destruction equiv; subst.
      assumption.
  Qed.

  Lemma simpleInlineModEquiv dm (notIn: In dm (getDefsBodies m)):
    forall ty, ModEquiv ty typeUT (simpleInlineDmToMod dm).
  Proof.
    rewrite simpleInlineDmToMod_matches; auto; intros.
    eapply inlineDmToMod_ModEquiv_General; eauto.
  Qed.
End NoCallsInDefs.

Fixpoint simpleInlineDmsToMod m dms :=
  match dms with
    | nil => m
    | x :: xs => simpleInlineDmsToMod (simpleInlineDmToMod m x) xs
  end.

Lemma simpleInlineDmsToMod_matches dms:
  forall m,
    (forall dm, In dm dms -> In dm (getDefsBodies m)) ->
    (forall i, ~ (In i (getCallsM (getDefsBodies m)) /\ In i (getDefs m))) ->
    NoDup (getDefs m) ->
    (forall ty, ModEquiv ty typeUT m) ->
    simpleInlineDmsToMod m dms = fst (inlineDms' m (namesOf dms)).
Proof.
  unfold simpleInlineDmsToMod.
  induction dms; intuition; simpl in *.
  fold (simpleInlineDmsToMod (simpleInlineDmToMod m a) dms).
  rewrite simpleInlineDmToMod_matches; auto.
  case_eq (inlineDmToMod m (attrName a)); intros; simpl in *.
  assert (sth: m0 = simpleInlineDmToMod m a).
  {
    rewrite simpleInlineDmToMod_matches; auto.
    destruct (inlineDmToMod m (attrName a)).
    inversion H3; subst; simpl.
    reflexivity.
  }
  unfold simpleInlineDmToMod in sth.
  assert (eq': getDefsBodies m0 = getDefsBodies m).
  { subst.
    reflexivity.
  }
  specialize (IHdms m0).
  unfold getDefs in IHdms.
  rewrite eq' in IHdms.
  assert (sth2: forall dm, In dm dms -> In dm (getDefsBodies m)) by intuition.
  fold (simpleInlineDmToMod m a) in sth.
  specialize (IHdms sth2 H0 H1).
  assert (sth3: In a (getDefsBodies m)) by (subst; intuition).
  rewrite sth in *.
  pose proof (simpleInlineModEquiv H0 H1 H2 a sth3) as sth4.
  specialize (IHdms sth4).
  fold (simpleInlineDmsToMod (simpleInlineDmToMod m a) dms) in IHdms.
  destruct (inlineDms' (simpleInlineDmToMod m a) (namesOf dms)); simpl in *.
  assumption.
Qed.

Definition simpleInline m := simpleInlineDmsToMod m (getDefsBodies m).

Lemma simpleInline_matches1 m:
  (forall i, ~ (In i (getCallsM (getDefsBodies m)) /\ In i (getDefs m))) ->
  NoDup (getDefs m) ->
  (forall ty, ModEquiv ty typeUT m) ->
  simpleInline m = fst (inlineDms m).
Proof.
  intros.
  unfold simpleInline, inlineDms.
  apply simpleInlineDmsToMod_matches; auto.
Qed.

Lemma inNamesInList A name (l: list (Attribute A)):
  In name (namesOf l) ->
  exists v, In {| attrName := name; attrType := v |} l.
Proof.
  induction l; intros; simpl in *.
  - intuition.
  - destruct a; simpl in *.
    destruct H; simpl in *; subst.
    + exists attrType.
      intuition.
    + specialize (IHl H); destruct IHl.
      exists x.
      right; intuition.
Qed.

Lemma simpleInline_matches2 m:
  (forall dm dmBody, In dm (getDefsBodies m) ->
                     In dmBody (getDefsBodies m) ->
                     In (attrName dmBody) (getCallsDm dm) ->
                     False) ->
  NoDup (getDefs m) ->
  (forall ty, ModEquiv ty typeUT m) ->
  simpleInline m = fst (inlineDms m).
Proof.
  intros.
  apply simpleInline_matches1; auto.
  clear H0 H1; unfold not; intros.
  destruct H0.
  unfold getDefs in H1.
  apply inNamesInList in H1.
  destruct H1.
  apply getCallsM_implies_getCallsDm in H0.
  destruct H0.
  destruct H0.
  apply (H _ _ H0 H1 H2).
Qed.
