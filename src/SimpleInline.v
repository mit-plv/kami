Require Import List String.
Require Import Lib.Struct.
Require Import Lts.Equiv Lts.Syntax Lts.Inline Lts.InlineFacts_2.
Require Import Program.Equality FunctionalExtensionality.

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

  Theorem inlineNoCallAction_matches a (aEquiv: ActionEquiv c a aUT): inlineDm a dm = a.
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
        apply (H0 v1 tt H2).
    - f_equal; auto.
  Qed.
End ActionNoCall.

Section ActionNoCalls.
  Variable dms: list DefMethT.

  Theorem inlineNoCallsAction_matches:
    forall k ty a (aUT: ActionT typeUT k)
      (c: ctxt (fullType ty) (fullType typeUT)),
      (forall dm, In dm dms -> In (attrName dm) (getCallsA aUT) -> False) ->
      ActionEquiv c a aUT ->
      fold_left (@inlineDm _ _) dms a = a.
  Proof.
    induction dms; simpl in *; intros.
    - reflexivity.
    - assert (sth: forall dm, In dm l -> In (attrName dm) (getCallsA aUT) -> False) by
          (intros; specialize (H dm); intuition).
      assert (sth2: In (attrName a) (getCallsA aUT) -> False) by
          (specialize (H a); intuition).
      specialize (IHl _ _ _ aUT c sth H0).
      pose proof (inlineNoCallAction_matches a sth2 H0) as sth3.
      rewrite sth3.
      assumption.
  Qed.
End ActionNoCalls.

Section MethNoCallsInRules.
  Variable dms: list DefMethT.
  Variable r: Attribute (Action Void).
  Variable rEquiv: forall ty G,  ActionEquiv G (attrType r ty) (attrType r typeUT).
  
  Theorem inlineNoCallsRule_matches:
    (forall dm, In dm dms -> In (attrName dm) (getCallsA (attrType r typeUT)) -> False) ->
    fold_left inlineDmToRule dms r = r.
  Proof.
    intros.
    induction dms; simpl in *; intros.
    - reflexivity.
    - assert (sth1: In (attrName a) (getCallsA (attrType r typeUT)) -> False)
        by (specialize (H a); intuition).
      assert (sth2: forall dm, In dm l -> In (attrName dm) (getCallsA (attrType r typeUT)) ->
                               False) by (intros; specialize (H dm); intuition).
      specialize (IHl sth2).
      rewrite <- IHl at 2; f_equal.
      unfold inlineDmToRule; simpl; destruct r; simpl in *; f_equal.
      extensionality ty.
      rewrite inlineNoCallAction_matches with (aUT := attrType typeUT) (c := nil); auto.
  Qed.
End MethNoCallsInRules.

Section MethNoCallsInMeths.
  Variable dms: list DefMethT.
  Variable r: DefMethT.
  Variable rEquiv:
    forall ty (argV1: fullType ty (SyntaxKind (arg (projT1 (attrType r)))))
           (argV2: fullType typeUT (SyntaxKind (arg (projT1 (attrType r))))) G,
      ActionEquiv (vars argV1 argV2 :: G)
                  (projT2 (attrType r) ty argV1)
                  (projT2 (attrType r) typeUT argV2).
  
  Theorem inlineNoCallsMeth_matches:
    (forall dm, In dm dms ->
                In (attrName dm) (getCallsA (projT2 (attrType r) typeUT tt)) -> False) ->
    fold_left inlineDmToDm dms r = r.
  Proof.
    intros.
    induction dms; simpl in *; intros.
    - reflexivity.
    - assert (sth1: In (attrName a) (getCallsA (projT2 (attrType r) typeUT tt)) -> False)
        by (specialize (H a); intuition).
      assert (sth2: forall dm,
                      In dm l ->
                      In (attrName dm) (getCallsA (projT2 (attrType r) typeUT tt)) ->
                               False) by (intros; specialize (H dm); intuition).
      specialize (IHl sth2).
      rewrite <- IHl at 2; f_equal.
      unfold inlineDmToDm; simpl; destruct r; simpl in *; f_equal.
      destruct attrType.
      simpl in *.
      f_equal.
      extensionality ty.
      extensionality argv.
      pose (tt: fullType typeUT (SyntaxKind (arg x))) as f.
      pose (argv: fullType ty (SyntaxKind (arg x))) as f0.
      rewrite inlineNoCallAction_matches with (aUT := m typeUT tt)
                                                (c := vars f0 f :: nil); auto.
  Qed.
End MethNoCallsInMeths.

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
      eapply inlineNoCallAction_matches; eauto.
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
    | nil => Mod (getRegInits m) (getRules m) (getDefsBodies m)
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

Lemma commuteInlineDmMeths:
  forall rs meths,
    fold_left inlineDmToDms meths rs =
    map (fun r => fold_left inlineDmToDm meths r) rs.
Proof.
  induction rs; simpl in *; intros.
  - induction meths; simpl in *.
    + reflexivity.
    + assumption.
  - specialize (IHrs meths).
    rewrite <- IHrs.
    clear IHrs.
    generalize a rs; clear.
    induction meths; simpl in *; intros.
    + reflexivity.
    + specialize (IHmeths (inlineDmToDm a0 a) (inlineDmToDms rs a)).
      assumption.
Qed.


Section MethNoCalls.
  Variable dms1 dms2: list DefMethT.
  Variable notInCalls: forall dm, ~ (In (attrName dm) (getCallsM dms1) /\ In dm dms2).
  Theorem inlineNoCallsMeths_matches (equiv: forall ty, MethsEquiv ty typeUT dms1)
  : fold_left inlineDmToDms dms2 dms1 = dms1.
  Proof.
    rewrite commuteInlineDmMeths.
    induction dms1; simpl in *.
    - intuition.
    - f_equal.
      + clear IHl dms1.
        assert (sth: forall dm,
                       ~ (In (attrName dm)
                             (getCallsA (projT2 (attrType a) typeUT tt)) /\ In dm dms2))
          by (intros; specialize (notInCalls dm); intuition).
        induction dms2; simpl in *.
        * reflexivity.
        * assert
            (sth2:
               forall (dm: Attribute (sigT MethodT)),
                 ~ (In (attrName dm) (getCallsA (projT2 (attrType a) typeUT tt) ++ getCallsM l)
                    /\ In dm l0)) by
              (intros; specialize (notInCalls dm); intuition).
          specialize (IHl0 sth2).
          assert
            (sth3:
               forall dm, ~ (In (attrName dm) (getCallsA (projT2 (attrType a) typeUT tt)) /\
                             In dm l0)) by (intros; specialize (sth dm); intuition).
          specialize (IHl0 sth3).
          rewrite <- IHl0 at 2.
          f_equal.
          assert
            (sth4:
               forall dm,
                 ~ (In (attrName dm) (getCallsA (projT2 (attrType a) typeUT tt))
                    /\ a0 = dm)) by (intros; specialize (sth dm); intuition).
          specialize (sth4 a0).
          assert (sth5: ~ In (attrName a0) (getCallsA (projT2 (attrType a) typeUT tt))) by
              intuition.
          destruct a; unfold inlineDmToDm; simpl in *.
          f_equal.
          destruct attrType; simpl in *.
          f_equal.
          extensionality ty.
          extensionality v.
          specialize (equiv ty).
          dependent destruction equiv.
          specialize (H v tt nil).
          eapply inlineNoCallAction_matches; eauto.
      + apply IHl; intros.
        * specialize (notInCalls dm); intuition.
        * specialize (equiv ty).
          dependent destruction equiv.
          assumption.
  Qed.
End MethNoCalls.

Definition inlineDmsInMod m dms :=
  Mod (getRegInits m) (fold_left inlineDmToRules dms (getRules m))
      (fold_left inlineDmToDms dms (getDefsBodies m)).

Lemma inlineDmsInMod_correct ds:
  forall m,
    (forall dm, In dm ds -> In dm (getDefsBodies m)) ->
    (forall i, ~ (In i (getCallsM (getDefsBodies m)) /\ In i (getDefs m))) ->
    NoDup (getDefs m) ->
    (forall ty, ModEquiv ty typeUT m) ->
    inlineDmsInMod m ds =
    fst (inlineDms' m (namesOf ds)).
Proof.
  intros; rewrite <- simpleInlineDmsToMod_matches; auto.
  unfold inlineDmsInMod; simpl in *.
  generalize m H H0 H1 H2; clear.
  induction ds; intros; simpl in *.
  - reflexivity.
  - specialize (IHds (simpleInlineDmToMod m a)).
    unfold getDefs in IHds; simpl in *.
    assert (forall dm, In dm ds -> In dm (getDefsBodies m))
      by (intros;
          specialize (H dm); intuition).
    assert (sth: In a (getDefsBodies m)) by (specialize (H a); intuition).
    specialize (IHds H3 H0 H1 (simpleInlineModEquiv H0 H1 H2 _ sth)).
    rewrite inlineNoCallMeths_matches; auto.

    assert (sth2: In (attrName a) (getDefs m)).
    { unfold getDefs.
      clear - sth.
      induction (getDefsBodies m).
      - intuition.
      - destruct sth; subst; simpl in *.
        intuition.
        intuition.
    }
    specialize (H0 (attrName a)).
    intuition.
    intros.
    specialize (H2 ty).
    destruct H2.
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

Definition inlineDmsIn m := inlineDmsInMod m (getDefsBodies m).

Lemma inlineDmsIn_matches m:
  (forall dm dmBody, In dm (getDefsBodies m) ->
                     In dmBody (getDefsBodies m) ->
                     In (attrName dmBody) (getCallsDm dm) ->
                     False) ->
  NoDup (getDefs m) ->
  (forall ty, ModEquiv ty typeUT m) ->
  inlineDmsIn m = fst (inlineDms m).
Proof.
  intros.
  unfold inlineDmsIn.
  rewrite inlineDmsInMod_correct; auto.
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
