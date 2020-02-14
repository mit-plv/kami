Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq Lib.ListSupport.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts Kami.Wf Kami.Inline Kami.InlineFacts.
Require Import Program.Equality FunctionalExtensionality.

Import ListNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

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

  Theorem inlineNoCallAction_matches a (aEquiv: ActionEquiv (t1 := ty) a aUT): inlineDm a dm = a.
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
    forall k ty a (aUT: ActionT typeUT k),
      (forall dm, In dm dms -> In (attrName dm) (getCallsA aUT) -> False) ->
      ActionEquiv (t1 := ty) a aUT ->
      fold_left (@inlineDm _ _) dms a = a.
  Proof.
    induction dms; simpl in *; intros.
    - reflexivity.
    - assert (sth: forall dm, In dm l -> In (attrName dm) (getCallsA aUT) -> False) by
          (intros; specialize (H dm); intuition).
      assert (sth2: In (attrName a) (getCallsA aUT) -> False) by
          (specialize (H a); intuition).
      specialize (IHl _ _ _ aUT sth H0).
      pose proof (inlineNoCallAction_matches a sth2 H0) as sth3.
      rewrite sth3.
      assumption.
  Qed.
End ActionNoCalls.

Section MethNoCallsInRules.
  Variable dms: list DefMethT.
  Variable r: Attribute (Action Void).
  Variable rEquiv: forall ty,  ActionEquiv (attrType r ty) (attrType r typeUT).
  
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
      rewrite inlineNoCallAction_matches with (aUT := attrType typeUT); auto.
  Qed.
End MethNoCallsInRules.

Section MethNoCallsInMeths.
  Variable dms: list DefMethT.
  Variable r: DefMethT.
  Variable rEquiv:
    forall ty (argV1: fullType ty (SyntaxKind (arg (projT1 (attrType r)))))
           (argV2: fullType typeUT (SyntaxKind (arg (projT1 (attrType r))))),
      ActionEquiv (projT2 (attrType r) ty argV1)
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
      rewrite inlineNoCallAction_matches with (aUT := m typeUT tt); auto.
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
  pose proof (proj1 (MethsEquiv_in ty typeUT (getDefsBodies m)) H1 _ Heqoattr).
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
          specialize (H v tt).
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

Section AboutFilter.
  Variable A: Type.

  Lemma filter_app (f: A -> bool) l1 l2:
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof.
    induction l1; simpl in *.
    - reflexivity.
    - destruct (f a); simpl; f_equal; auto.
  Qed.
  
  Definition filterA (a dm: Attribute A) :=
    if string_dec (attrName dm) (attrName a) then false else true.

  Lemma filterA_eq (l: list (Attribute A)) a:
    ~ In (attrName a) (namesOf l) -> filter (filterA a) l = l.
  Proof.
    induction l; simpl in *; intros.
    - reflexivity.
    - assert (attrName a0 <> attrName a) by intuition.
      assert (~ In (attrName a) (namesOf l)) by intuition.
      case_eq (filterA a a0); intros; try subst; f_equal; auto.
      unfold filterA in H2.
      destruct (string_dec (attrName a0) (attrName a)); intuition.
  Qed.
End AboutFilter.

Lemma inlineDmCalls c dm k (a: ActionT typeUT k): In c (getCallsA a) -> c <> (attrName dm) ->
                                                  In c (getCallsA (inlineDm a dm)).
Proof.
  induction a; intros; simpl in *; auto.
  - case_eq (getBody meth dm s); intros; simpl in *; unfold getBody in *.
    + destruct s0; simpl in *.
      destruct x; simpl in *.
      destruct dm; simpl in *.
      destruct attrType; simpl in *.
      subst.
      rewrite getCallsA_appendAction.
      simpl in *.
      apply in_or_app.
      case_eq (string_eq meth attrName0); intros; rewrite H3 in H2.
      * apply eq_sym in H3; apply string_eq_dec_eq in H3; subst.
        destruct H0; [intuition|].
        destruct (SignatureT_dec (projT1 attrType0) s); [| discriminate].
        inversion H2; clear H2.
        rewrite <- H4, <- H5.
        right; apply H; intuition auto.
      * discriminate.
    + intuition auto.
  - apply in_app_or in H0.
    apply in_or_app.
    destruct H0; [left; apply IHa1; auto|].
    right; apply in_or_app.
    apply in_app_or in H0; destruct H0; [left; apply IHa2; auto|].
    right; apply H; auto.
Qed.

Section InlineDmsCalls.
  Variable n : string.
  Variable r : Attribute (Action Void).
  Variable HDmInR : In n (getCallsA (attrType r typeUT)).

  Lemma inlineDmsCalls l:
    ~ In n (namesOf l) ->
    In n (getCallsA (attrType (fold_right (fun dm' r' => inlineDmToRule r' dm') r l) typeUT)).
  Proof.
    induction l; simpl in *; intros; auto.
    assert (sth1: attrName a <> n) by intuition auto.
    assert (sth2: ~ In n (namesOf l)) by intuition auto.
    specialize (IHl sth2).
    apply inlineDmCalls; auto.
  Qed.
End InlineDmsCalls.
  
Section AboutList.
  Variable A: Type.
  Variable ls: list (Attribute A).
  Variable HNoDup: NoDup (namesOf ls).
  Variable a: Attribute A.
  Variable f: A -> A.
  Variable prefix suffix: list (Attribute A).
  Variable HIn: ls = prefix ++ a :: suffix.

  Definition attrF x := (attrName x :: f (attrType x))%struct.

  Definition changeA x := if string_dec (attrName a) (attrName x)
                          then attrF x
                          else x.

  Lemma aNotInPrefix: ~ In (attrName a) (namesOf prefix).
  Proof.
    generalize ls HNoDup HIn.
    clear ls HNoDup HIn.
    induction prefix; intros.
    - intuition.
    - destruct ls.
      pose proof (@app_cons_not_nil _ _ _ _ HIn); auto.
      simpl in HIn.
      injection HIn; intros.
      unfold namesOf in HNoDup.
      simpl in HNoDup.
      inv HNoDup.
      apply IHl in H4; auto.
      unfold not; intros.
      simpl in H.
      destruct H; subst.
      rewrite map_app in H3; simpl in H3.
      assert (sth: In (attrName a) (map (@attrName _) l ++
                                        attrName a :: map (@attrName _) suffix)) by
          (apply in_app_iff; intuition).
      rewrite H in *.
      auto.
      auto.
  Qed.

  Lemma aNotInSuffix: ~ In (attrName a) (namesOf suffix).
  Proof.
    generalize ls HNoDup HIn.
    clear ls HNoDup HIn.
    induction prefix; intros.
    - rewrite app_nil_l in HIn.
      subst.
      inv HNoDup.
      unfold not; intros.
      intuition.
    - destruct ls.
      pose proof (@app_cons_not_nil _ _ _ _ HIn); auto.
      simpl in HIn.
      injection HIn; intros.
      unfold namesOf in HNoDup.
      simpl in HNoDup.
      inv HNoDup.
      apply IHl in H4; auto.
  Qed.


  Lemma mapChangeNotIn: forall l, ~ In (attrName a) (namesOf l) -> map changeA l = l.
  Proof.
    clear.
    induction l; simpl in *; intros.
    - reflexivity.
    - assert (attrName a0 <> attrName a) by intuition.
      assert (~ In (attrName a) (namesOf l)) by intuition.
      specialize (IHl H1).
      f_equal; auto.
      unfold changeA.
      destruct (string_dec (attrName a) (attrName a0)).
      apply eq_sym in e; intuition auto.
      reflexivity.
  Qed.

  Lemma mapChangePrefix: map changeA prefix = prefix.
  Proof.
    apply mapChangeNotIn.
    apply aNotInPrefix.
  Qed.

  Lemma mapChangeSuffix: map changeA suffix = suffix.
  Proof.
    apply mapChangeNotIn.
    apply aNotInSuffix.
  Qed.  

  Lemma map_equiv': map changeA ls = map changeA prefix ++ attrF a :: map changeA suffix.
  Proof.
    simpl.
    assert (sth: changeA a = attrF a) by
        (unfold changeA; destruct (string_dec (attrName a) (attrName a)); intuition auto).
    rewrite <- sth.
    assert (sth2: changeA a :: map changeA suffix = map changeA (a :: suffix)) by reflexivity.
    rewrite sth2.
    rewrite <- map_app.
    f_equal; auto.
  Qed.

  Lemma map_equiv: map changeA ls = prefix ++ attrF a :: suffix.
  Proof.
    rewrite map_equiv'.
    rewrite mapChangePrefix.
    rewrite mapChangeSuffix.
    reflexivity.
  Qed.

  Lemma filter_equiv: filter (filterA a) ls = prefix ++ suffix.
  Proof.
    rewrite HIn.
    rewrite filter_app.
    f_equal.
    apply filterA_eq.
    apply aNotInPrefix.
    simpl.
    unfold filterA.
    destruct (string_dec (attrName a) (attrName a)); auto.
    apply filterA_eq.
    apply aNotInSuffix.
    tauto.
  Qed.
End AboutList.
  
Section Partial.
  Variable m: Modules.

  Variable dm: DefMethT. (* a method to be inlined *)
  Variable preDm sufDm: list DefMethT.
  Variable Hdm: getDefsBodies m = preDm ++ dm :: sufDm.
  Hypotheses (HnoDupMeths: NoDup (namesOf (getDefsBodies m))).
  Variable prefix suffix: list (Attribute (Action Void)).
  Variable r: Attribute (Action Void). (* a rule calling dm *)
  Hypothesis Hrule: getRules m = prefix ++ r :: suffix.
  Hypothesis HnoDupRules: NoDup (namesOf (getRules m)).

  Lemma inDmGetDefsBodies: In dm (getDefsBodies m).
  Proof.
    clear - Hdm.
    rewrite Hdm.
    apply in_or_app.
    right; intuition.
  Qed.
  
  Lemma inlineDmToRule_traceRefines_NoFilt:
    m <<== (Mod (getRegInits m)
                (prefix ++ inlineDmToRule r dm :: suffix)
                (getDefsBodies m)).
  Proof.
    assert (sth: inlineDmToRule r dm = attrF (fun a type => inlineDm (a type) dm) r) by
        (unfold inlineDmToRule; reflexivity).
    rewrite sth.
    rewrite <- map_equiv with (ls := getRules m); auto.
    apply inlineDmToRule_traceRefines_1.
    apply inDmGetDefsBodies; auto.
    auto.
  Qed.

  Hypothesis mEquiv: ModEquiv type typeUT m.
  Hypothesis HdmNoRule: forall r, In r (prefix ++ suffix) ->
                                  noCallDmSigA (attrType r typeUT) (attrName dm)
                                               (projT1 (attrType dm)) = true.
  Hypothesis HdmNoMeth: forall d, In d (getDefsBodies m) ->
                                  noCallDmSigA (projT2 (attrType d) typeUT tt)
                                               (attrName dm) (projT1 (attrType dm)) = true.
  
  Hypothesis HDmInR: In (attrName dm) (getCallsA (attrType r typeUT)).
  
  Lemma inlineDmToRule_traceRefines_Filt:
    m <<== (Mod (getRegInits m)
                (prefix ++ inlineDmToRule r dm :: suffix)
                (preDm ++ sufDm)).
  Proof.
    assert (sth: inlineDmToRule r dm = attrF (fun a type => inlineDm (a type) dm) r) by
        (unfold inlineDmToRule; reflexivity).
    rewrite sth.
    rewrite <- map_equiv with (ls := getRules m); auto.
    assert (sth2: filterDm (getDefsBodies m) (attrName dm) = preDm ++ sufDm).
    { unfold filterDm.
      apply filter_equiv; auto.
    }
    rewrite <- sth2.
    apply inlineDmToRule_traceRefines_2; intuition auto.
    rewrite Hdm; intuition.
    rewrite Hrule; apply in_or_app; right; intuition.
    apply HdmNoRule with (r := rule); auto.
    rewrite Hrule in H.
    apply in_app_or in H;
      apply in_or_app; intuition auto.
    right; simpl in H1; subst; intuition.
    subst; intuition.
  Qed.
End Partial.

Section PartialMultiDm.
  Variable m: Modules.
  
  Variable dms: list DefMethT. (* a method to be inlined *)
  Variable preDm sufDm: list DefMethT.
  Variable Hdm: getDefsBodies m = preDm ++ dms ++ sufDm.
  Hypotheses HnoDupMeths: NoDup (namesOf (getDefsBodies m)).
  Variable prefix suffix: list (Attribute (Action Void)).
  Variable r: Attribute (Action Void). (* a rule calling dm *)
  Hypothesis Hrule: getRules m = prefix ++ r :: suffix.
  Hypothesis HnoDupRules: NoDup (namesOf (getRules m)).
  
  Lemma inlineDmsToRule_traceRefines_NoFilt:
    m <<== (Mod (getRegInits m)
                (prefix ++ fold_right (fun dm' r' => inlineDmToRule r' dm') r dms :: suffix)
                (getDefsBodies m)).
  Proof.
    generalize dms preDm Hdm.
    clear dms preDm Hdm.
    induction dms; simpl in *; intros.
    - rewrite <- Hrule.
      apply flatten_traceRefines.
    - assert (sth: (preDm ++ [a]) ++ l ++ sufDm = preDm ++ a :: l ++ sufDm) by
          (rewrite <- app_assoc; reflexivity).
      assert (sth2: getDefsBodies m = (preDm ++ [a]) ++ l ++ sufDm) by
          (rewrite sth, Hdm; reflexivity).
      specialize (IHl (preDm ++ a :: nil) sth2).
      rewrite idElementwiseId in *.
      match goal with
        | [H: traceRefines id m ?P |- _] => apply traceRefines_trans with (mb := P); auto
      end.
      rewrite <- idElementwiseId.
      match goal with
        | [|- ?m <<== _] => pose proof (@inlineDmToRule_traceRefines_NoFilt m a preDm (l ++ sufDm) Hdm HnoDupMeths prefix suffix (fold_right (fun dm' r' => inlineDmToRule r' dm') r l) eq_refl) as sth3; simpl in *
      end.
      apply sth3.
      unfold namesOf in *; rewrite Hrule in HnoDupRules; repeat rewrite map_app in *; simpl in *.
      assert (sth4: attrName r =
                    attrName (fold_right (fun dm' r' => inlineDmToRule r' dm') r l)).
      { clear;
        induction l; simpl in *; auto.
      }
      rewrite <- sth4.
      assumption.
  Qed.

  Variable mEquiv: ModEquiv type typeUT m.
  Hypothesis HdmNoRule: forall r,
                          In r (prefix ++ suffix) ->
                          forall dm, In dm dms ->
                                     noCallDmSigA (attrType r typeUT) (attrName dm)
                                                  (projT1 (attrType dm)) = true.
  Hypothesis HdmNoMeth:
    forall d,
      In d (getDefsBodies m) ->
      forall dm, In dm dms ->
                 noCallDmSigA (projT2 (attrType d) typeUT tt)
                              (attrName dm) (projT1 (attrType dm)) = true.

  Hypothesis HDmsInR: forall dm, In dm dms -> In (attrName dm) (getCallsA (attrType r typeUT)).

  Lemma NoDup_app_rm A: forall (l1 l2 l3: list A), NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
  Proof.
    clear.
    intros.
    rewrite <- app_nil_r in H.
    rewrite <- app_assoc in H.
    apply NoDup_app_comm_ext in H.
    rewrite app_assoc in H.
    rewrite app_nil_r in H.
    rewrite app_assoc in H.
    apply NoDup_app_1 in H.
    auto.
  Qed.

  Lemma inlineDmsToRule_traceRefines_Filt:
    m <<== (Mod (getRegInits m)
                (prefix ++ fold_right (fun dm' r' => inlineDmToRule r' dm') r dms :: suffix)
                (preDm ++ sufDm)).
  Proof.
    generalize dms preDm Hdm HdmNoRule HdmNoMeth HDmsInR.
    clear dms preDm Hdm HdmNoRule HdmNoMeth HDmsInR.
    induction dms; simpl in *; intros.
    - rewrite <- Hrule.
      rewrite <- Hdm.
      apply flatten_traceRefines.
    - assert (sth: (preDm ++ [a]) ++ l ++ sufDm = preDm ++ a :: l ++ sufDm) by
          (rewrite <- app_assoc; reflexivity).
      assert (sth1: (preDm ++ [a]) ++ sufDm = preDm ++ a :: sufDm) by
          (rewrite <- app_assoc; reflexivity).
      assert (sth2: getDefsBodies m = (preDm ++ [a]) ++ l ++ sufDm) by
          (rewrite sth, Hdm; reflexivity).
      assert (sth3: forall r0, In r0 (prefix ++ suffix) ->
                               forall dm, In dm l ->
                                     noCallDmSigA (attrType r0 typeUT) (attrName dm)
                                                  (projT1 (attrType dm)) = true)
        by (intros; apply HdmNoRule; auto).
      assert (HDmsInR1: forall dm, In dm l -> In (attrName dm) (getCallsA (attrType r typeUT)))
        by (intros; apply HDmsInR; auto).
      assert (HDmsInR2: In (attrName a) (getCallsA (attrType r typeUT)))
        by (intros; apply HDmsInR; auto).
      assert (sth4:
                forall d, In d (getDefsBodies m) ->
                          forall dm, In dm l ->
                                     noCallDmSigA (projT2 (attrType d) typeUT tt)
                                                  (attrName dm) (projT1 (attrType dm)) = true)
        by (intros; apply HdmNoMeth; auto).
      specialize (IHl (preDm ++ [a]) sth2 sth3 sth4 HDmsInR1); clear sth3 sth4.
      rewrite idElementwiseId in *.
      match goal with
        | [H: traceRefines id m ?P |- _] => apply traceRefines_trans with (mb := P); auto
      end.
      rewrite <- idElementwiseId.
      assert (sth3: NoDup (namesOf ((preDm ++ [a]) ++ sufDm))).
      { unfold namesOf; repeat rewrite map_app.
        apply NoDup_app_rm with (l2 := map (@attrName _) l).
        repeat rewrite <- map_app.
        rewrite <- sth2.
        assumption.
      } 
      match goal with
        | [|- ?m <<== _] =>
          pose proof (@inlineDmToRule_traceRefines_Filt
                        m a preDm sufDm sth1 sth3
                        prefix suffix (fold_right (fun dm' r' => inlineDmToRule r' dm') r l)
                        eq_refl) as sth4; simpl in *
      end.
      apply sth4; auto.
      unfold namesOf in *; rewrite Hrule in HnoDupRules; repeat rewrite map_app in *; simpl in *.
      assert (sth5: attrName r =
                    attrName (fold_right (fun dm' r' => inlineDmToRule r' dm') r l)).
      { clear;
        induction l; simpl in *; auto.
      }
      rewrite <- sth5.
      assumption.
      destruct mEquiv as [rEquiv dmEquiv].
      rewrite Hrule in rEquiv; rewrite Hdm in dmEquiv.
      pose proof (proj1 (RulesEquiv_in _ _ _) rEquiv) as rEquiv'; clear rEquiv.
      pose proof (proj1 (MethsEquiv_in _ _ _) dmEquiv) as dEquiv'; clear dmEquiv.
      constructor; simpl in *.
      apply RulesEquiv_in; intros.
      apply in_app_or in H; simpl in *.
      destruct H; [apply rEquiv'; apply in_or_app; auto|].
      destruct H; [|apply rEquiv'; apply in_or_app; auto].
      assert (sth9: RuleEquiv type typeUT r) by (apply rEquiv'; apply in_or_app; intuition).
      assert (sth10: forall x, In x l -> MethEquiv type typeUT x).
      { intros; apply dEquiv'; apply in_or_app; simpl; right; right;
        apply in_or_app; left; auto.
      }
      clear - H sth9 sth10.
      { subst.
        generalize sth10; clear sth10.
        induction l; simpl in *; intros; auto.
        assert (forall x, In x l -> MethEquiv type typeUT x) by (intros; apply sth10; auto).
        assert (MethEquiv type typeUT a) by (apply sth10; auto).
        specialize (IHl H).
        unfold inlineDmToRule at 1; unfold RuleEquiv in *; simpl in *.
        apply inlineDm_ActionEquiv; auto.
      } 
      intuition.
      apply MethsEquiv_in; intros.
      repeat (apply in_app_or in H; destruct H);
        (apply dEquiv'; apply in_or_app; intuition auto).
      right; simpl in *; intuition auto.
      right; right; apply in_or_app; intuition auto.
      intros; apply HdmNoMeth; auto.
      rewrite sth2.
      repeat (try apply in_app_or in H; try apply in_or_app; try destruct H; intuition auto).
      right; apply in_or_app; right; auto.
      rewrite Hdm in HnoDupMeths.
      clear - HnoDupMeths HDmsInR2.
      unfold namesOf in *.
      rewrite map_app in *; simpl in *.
      apply NoDup_app_2 in HnoDupMeths; simpl in *.
      pose proof HnoDupMeths as sth.
      dependent destruction sth.
      clear HnoDupMeths.
      rewrite map_app in *; simpl in *.
      assert (sth2: ~ In (attrName a) (map (@attrName _) l)).
      { unfold not; intros.
        assert (In (attrName a) (map (@attrName _) l ++ map (@attrName _) sufDm))
          by (apply in_or_app; intuition auto).
        intuition auto.
      }
      destruct a as [n nt]; simpl in *.
      clear - sth2 HDmsInR2.
      apply inlineDmsCalls; auto.
  Qed.
End PartialMultiDm.

Section PartialMultiR.
  Variable m: Modules.

  Variable dm: DefMethT. (* a method to be inlined *)
  Variable preDm sufDm: list DefMethT.
  Variable Hdm: getDefsBodies m = preDm ++ dm :: sufDm.
  Hypotheses HnoDupMeths: NoDup (namesOf (getDefsBodies m)).
  Hypothesis HnoDupRules: NoDup (namesOf (getRules m)).
  Variable rs: list (Attribute (Action Void)). (* a rule calling dm *)
  Variable prefix suffix: list (Attribute (Action Void)).
  Hypothesis Hrule: getRules m = prefix ++ rs ++ suffix.
  
  Lemma inlineDmToRules_traceRefines_NoFilt:
    m <<==
      (Mod (getRegInits m)
           (prefix ++ map (fun r => inlineDmToRule r dm) rs ++ suffix)
           (getDefsBodies m)).
  Proof.
    generalize rs prefix suffix Hrule.
    clear rs prefix suffix Hrule.
    induction rs; simpl in *; intros.
    - rewrite <- Hrule.
      apply flatten_traceRefines.
    - assert (sth: (prefix ++ [a]) ++ l ++ suffix = prefix ++ a :: l ++ suffix) by
          (rewrite <- app_assoc; reflexivity).
      assert (sth2: getRules m = (prefix ++ [a]) ++ l ++ suffix) by
          (rewrite sth, Hrule; reflexivity).
      specialize (IHl (prefix ++ [a]) suffix sth2).
      rewrite idElementwiseId in *.
      match goal with
        | [H: traceRefines id m ?P |- _] => apply traceRefines_trans with (mb := P); auto
      end.
      rewrite <- idElementwiseId.
      rewrite <- app_assoc with (m := [a]); simpl.
      match goal with
        | |- ?m2 <<== _ =>
          assert (sth1: getRegInits m = getRegInits m2) by reflexivity;
            rewrite sth1 at 2; clear sth1
      end.
      match goal with
        | [|- ?m <<== _] =>
          pose proof (@inlineDmToRule_traceRefines_NoFilt
                        m dm preDm sufDm Hdm HnoDupMeths prefix
                        (map (fun r => inlineDmToRule r dm) l ++
                             suffix) a eq_refl) as sth3; simpl in *
      end.
      apply sth3.
      rewrite Hrule in HnoDupRules; clear - HnoDupRules.
      unfold namesOf in *; repeat rewrite map_app in *; simpl in *.
      assert (sth: map (@attrName _)
                       (map (fun r => inlineDmToRule r dm) l)
                   = map (@attrName _) l).
      { clear.
        induction l; simpl in *; intros.
        - reflexivity.
        - f_equal; auto.
      }
      rewrite map_app in *; simpl in *.
      rewrite sth.
      assumption.
  Qed.
End PartialMultiR.

Lemma inlineDmToRule_preserveName r l:
  attrName
    (fold_right
       (fun dm' r' =>
          inlineDmToRule r' dm') r l) = attrName r.
Proof.
  induction l; simpl in *; auto.
Qed.

Section PartialMultiR2.
  Variable m: Modules.
  Variable mEquiv: forall ty, ModEquiv ty typeUT m.

  Variable dm: DefMethT. (* a method to be inlined *)
  Variable preDm sufDm: list DefMethT.
  Variable Hdm: getDefsBodies m = preDm ++ dm :: sufDm.
  Hypotheses HnoDupMeths: NoDup (namesOf (getDefsBodies m)).
  Hypothesis HnoDupRules: NoDup (namesOf (getRules m)).
  Variable rs: list (Attribute (Action Void)). (* a rule calling dm *)
  Variable prefix suffix: list (Attribute (Action Void)).
  Hypothesis Hrule: getRules m = prefix ++ rs ++ suffix.
  
  Hypothesis HdmNoRule: forall r,
                          In r (prefix ++ suffix) ->
                          noCallDmSigA (attrType r typeUT) (attrName dm)
                                       (projT1 (attrType dm)) = true.

  Hypothesis HdmNoMeth:
    forall d,
      In d (getDefsBodies m) ->
      noCallDmSigA (projT2 (attrType d) typeUT tt)
                   (attrName dm) (projT1 (attrType dm)) = true.

  Hypothesis HDmsInRs: exists r, In r rs /\
                                 In (attrName dm) (getCallsA (attrType r typeUT)).

  Lemma inlineDmToRules_traceRefines_Filt:
    m <<==
      (Mod (getRegInits m)
           (prefix ++ map (fun r => inlineDmToRule r dm) rs ++ suffix)
           (preDm ++ sufDm)).
  Proof.
    destruct HDmsInRs as [r [InRRs InDmCallsR]]; clear HDmsInRs.
    generalize rs prefix Hrule r InRRs InDmCallsR HdmNoRule.
    clear rs prefix Hrule HdmNoRule r InRRs InDmCallsR.
    induction rs; simpl in *; intros; [intuition auto | ].
    destruct (in_dec string_dec (attrName dm) (getCallsA (attrType a typeUT))) as [isIn| notIn].
    - match goal with
        | |- _ <<== Mod ?regs (?pre ++ inlineDmToRule ?r dm :: ?rest) _ =>
          apply traceRefines_trans with (mb := Mod regs ((pre ++ [r]) ++ rest)
                                                   (getDefsBodies m))
      end.
      assert (sth: (fun f: MethsT => f) = id) by (extensionality f; reflexivity); rewrite sth.
      unfold MethsT; rewrite <- idElementwiseId.
      apply inlineDmToRules_traceRefines_NoFilt with (preDm := preDm) (sufDm := sufDm); auto.
      rewrite <- app_assoc; simpl; auto.
      rewrite <- app_assoc; simpl.
      match goal with
        | |- ?m2 <<== _ =>
          assert (sth1: getRegInits m = getRegInits m2) by reflexivity;
            rewrite sth1 at 2; clear sth1
      end.
      apply inlineDmToRule_traceRefines_Filt; auto; simpl in *.
      rewrite Hrule in HnoDupRules; clear - HnoDupRules.
      unfold namesOf in *; repeat rewrite map_app in *; simpl in *.
      assert (sth: map (@attrName _)
                       (map (fun r => inlineDmToRule r dm) l)
                   = map (@attrName _) l).
      { clear.
        induction l; simpl in *; intros.
        - reflexivity.
        - f_equal; auto.
      }
      rewrite map_app in *; simpl in *.
      rewrite sth.
      assumption.
      destruct (mEquiv type).
      constructor; simpl in *; auto.
      pose proof ((proj1 (RulesEquiv_in _ _ (getRules m))) H) as rEquiv; clear H.
      apply RulesEquiv_in; simpl in *; intros.
      rewrite Hrule in rEquiv.
      apply in_app_or in H; simpl in *; destruct H;[
        apply rEquiv; apply in_or_app; simpl; intuition auto|].
      destruct H; [subst; apply rEquiv; apply in_or_app; simpl; intuition auto|].
      apply in_app_or in H; destruct H;
      [|
       apply rEquiv; apply in_or_app; simpl; right; right; apply in_or_app; intuition auto].
      assert (forall r0, In r0 l -> RuleEquiv type typeUT r0) by
          (intros; apply rEquiv; apply in_or_app; right; right;
           apply in_or_app; left; intuition auto).
      apply in_map_iff in H; dest; subst.
      specialize (H1 x H2).
      pose proof ((proj1 (MethsEquiv_in _ _ (getDefsBodies m))) H0) as dEquiv; clear H0.
      rewrite Hdm in dEquiv.
      assert (MethEquiv type typeUT dm) by (apply dEquiv; apply in_or_app; right; left;
                                            intuition auto).
      apply inlineDm_ActionEquiv; auto.

      intros.
      apply in_app_or in H.
      destruct H; [apply HdmNoRule; apply in_or_app; intuition auto|].
      apply in_app_or in H.
      destruct H; [|apply HdmNoRule; apply in_or_app; intuition auto].
      apply in_map_iff in H; dest; subst.
      apply inlineDmToRule_noCallDmSigA; auto.
      apply HdmNoMeth; auto.
      rewrite Hdm; apply in_or_app; simpl; intuition auto.
    - destruct InRRs; subst.
      match goal with
        | |- _ <<== Mod ?regs (?pre ++ inlineDmToRule ?r dm :: ?rest) _ =>
          apply traceRefines_trans with (mb := Mod regs ((pre ++ [r]) ++ rest)
                                                   (getDefsBodies m))
      end.
      assert (sth: (fun f: MethsT => f) = id) by (extensionality f; reflexivity); rewrite sth.
      unfold MethsT; rewrite <- idElementwiseId.
      apply inlineDmToRules_traceRefines_NoFilt with (preDm := preDm) (sufDm := sufDm); auto.
      rewrite <- app_assoc; simpl; auto.
      rewrite <- app_assoc; simpl.
      match goal with
        | |- ?m2 <<== _ =>
          assert (sth1: getRegInits m = getRegInits m2) by reflexivity;
            rewrite sth1 at 2; clear sth1
      end.
      apply inlineDmToRule_traceRefines_Filt; auto; simpl in *.
      rewrite Hrule in HnoDupRules; clear - HnoDupRules.
      unfold namesOf in *; repeat rewrite map_app in *; simpl in *.
      assert (sth: map (@attrName _)
                       (map (fun r => inlineDmToRule r dm) l)
                   = map (@attrName _) l).
      { clear.
        induction l; simpl in *; intros.
        - reflexivity.
        - f_equal; auto.
      }
      rewrite map_app in *; simpl in *.
      rewrite sth.
      assumption.
      destruct (mEquiv type).
      constructor; simpl in *; auto.
      pose proof ((proj1 (RulesEquiv_in _ _ (getRules m))) H) as rEquiv; clear H.
      apply RulesEquiv_in; simpl in *; intros.
      rewrite Hrule in rEquiv.
      apply in_app_or in H; simpl in *; destruct H;[
        apply rEquiv; apply in_or_app; simpl; intuition auto|].
      destruct H; [subst; apply rEquiv; apply in_or_app; simpl; intuition auto|].
      apply in_app_or in H; destruct H;
      [|
       apply rEquiv; apply in_or_app; simpl; right; right; apply in_or_app; intuition auto].
      assert (forall r0, In r0 l -> RuleEquiv type typeUT r0) by
          (intros; apply rEquiv; apply in_or_app; right; right;
           apply in_or_app; left; intuition auto).
      apply in_map_iff in H; dest; subst.
      specialize (H1 x H2).
      pose proof ((proj1 (MethsEquiv_in _ _ (getDefsBodies m))) H0) as dEquiv; clear H0.
      rewrite Hdm in dEquiv.
      assert (MethEquiv type typeUT dm) by (apply dEquiv; apply in_or_app; right; left;
                                            intuition auto).
      apply inlineDm_ActionEquiv; auto.


      assert (sth: (prefix ++ [a]) ++ l ++ suffix = prefix ++ a :: l ++ suffix) by
          (rewrite <- app_assoc; reflexivity).
      rewrite <- sth in Hrule.
      specialize (IHl _ Hrule _ H InDmCallsR).
      repeat rewrite <- app_assoc in IHl; simpl in IHl.
      assert (forall r, In r (prefix ++ a :: suffix) ->
                        noCallDmSigA (attrType r typeUT) (attrName dm) (projT1 (attrType dm)) =
                        true).
      { intros.
        apply in_app_or in H0; simpl in *.
        destruct H0.
        - apply HdmNoRule.
          apply in_or_app; intuition auto.
        - destruct H0; subst.
          * apply noCalls_noCallDmSigATrue; auto.
          * apply HdmNoRule.
            apply in_or_app; intuition auto.
      }
      specialize (IHl H0).
      apply traceRefines_trans with (mb := Mod (getRegInits m)
                                               (prefix ++
                                                       a :: map (fun r => inlineDmToRule r dm) l
                                                       ++ suffix) (preDm ++ sufDm)).
      assert (sth2: (fun f: MethsT => f) = id) by (extensionality f; reflexivity); rewrite sth2.
      unfold MethsT; rewrite <- idElementwiseId; auto.
      assert (sth2: inlineDmToRule a dm = a).
      { unfold inlineDmToRule.
        assert (sth1: In a (getRules m)) by
            (rewrite Hrule; apply in_or_app; left; apply in_or_app;
             right; simpl; intuition auto).
        destruct a; simpl in *; f_equal.
        extensionality ty; simpl in *.
        destruct (mEquiv ty).
        pose proof (proj1 (RulesEquiv_in _ _ (getRules m)) H1 (attrName :: attrType)%struct
                          sth1) as sth2.
        unfold RuleEquiv in sth2; simpl in sth2.
        apply inlineNoCallAction_matches with (aUT := attrType typeUT); auto.
      }
      rewrite idElementwiseId.
      rewrite sth2.
      apply traceRefines_refl.
  Qed.
End PartialMultiR2.

Section inlineDmToRule_hasInCalls.
  Variable a: DefMethT.
  Variable r: Attribute (Action Void).
  Variable inaR: In (attrName a) (getCallsA (attrType r typeUT)).
  Variable l: list DefMethT.
  Variable notAL: ~ In (attrName a) (namesOf l).
  
  Lemma inlineDmToRule_hasInCalls:
    In (attrName a)
       (getCallsA
          (attrType
             (fold_right
                (fun dm' r' =>
                   inlineDmToRule r' dm') r l) typeUT)).
  Proof.
    induction l; simpl in *; auto.
    assert (attrName a0 <> attrName a) by intuition.
    assert (~ In (attrName a) (namesOf l0)) by intuition.
    specialize (IHl0 H0).
    apply inlineDmCalls; auto.
  Qed.
End inlineDmToRule_hasInCalls.

Section rEquivAfterInline.
  Variable ty: Kind -> Type.
  Variable ls: list DefMethT.

  Lemma inlineDmsToRule_Equiv r:
    RuleEquiv ty typeUT r ->
    (forall d, In d ls -> MethEquiv ty typeUT d) ->
    RuleEquiv ty typeUT
              (fold_right
                 (fun dm' r' => inlineDmToRule r' dm') r ls).
  Proof.
    intro rEquiv; induction ls; simpl in *; auto; intros.
    assert (sth1: MethEquiv ty typeUT a) by (apply H; auto).
    assert (sth2: forall d, In d l -> MethEquiv ty typeUT d) by (intros; apply H; auto).
    specialize (IHl sth2).
    apply inlineDm_ActionEquiv; auto.
  Qed.
End rEquivAfterInline.
  
Section PartialMultiDmMultiR.
  Variable m: Modules.

  Variable dms: list DefMethT. (* a method to be inlined *)
  Variable preDm sufDm: list DefMethT.
  Variable Hdm: getDefsBodies m = preDm ++ dms ++ sufDm.
  Hypotheses HnoDupMeths: NoDup (namesOf (getDefsBodies m)).
  Hypothesis HnoDupRules: NoDup (namesOf (getRules m)).
  Variable rs: list (Attribute (Action Void)). (* a rule calling dm *)
  Variable prefix suffix: list (Attribute (Action Void)).
  Hypothesis Hrule: getRules m = prefix ++ rs ++ suffix.
  
  Lemma inlineDmsToRules_traceRefines_NoFilt:
    m <<==
      (Mod (getRegInits m)
           (prefix ++ map (fun r => fold_right (fun dm' r' => inlineDmToRule r' dm') r dms) rs ++ suffix)
           (getDefsBodies m)).
  Proof.
    generalize rs prefix suffix Hrule.
    clear rs prefix suffix Hrule.
    induction rs; simpl in *; intros.
    - rewrite <- Hrule.
      apply flatten_traceRefines.
    - assert (sth: (prefix ++ [a]) ++ l ++ suffix = prefix ++ a :: l ++ suffix) by
          (rewrite <- app_assoc; reflexivity).
      assert (sth2: getRules m = (prefix ++ [a]) ++ l ++ suffix) by
          (rewrite sth, Hrule; reflexivity).
      specialize (IHl (prefix ++ [a]) suffix sth2).
      rewrite idElementwiseId in *.
      match goal with
        | [H: traceRefines id m ?P |- _] => apply traceRefines_trans with (mb := P); auto
      end.
      rewrite <- idElementwiseId.
      match goal with
        | [|- ?m <<== _] =>
          pose proof (@inlineDmsToRule_traceRefines_NoFilt
                        m dms preDm sufDm Hdm HnoDupMeths prefix
                        (map (fun r =>
                                fold_right (fun dm' r' => inlineDmToRule r' dm') r dms) l ++
                             suffix) a) as sth3; simpl in *
      end.
      apply sth3.
      rewrite <- app_assoc.
      f_equal.
      rewrite sth2 in HnoDupRules; clear - HnoDupRules.
      unfold namesOf in *; repeat rewrite map_app in *; simpl in *.
      assert (sth: map (@attrName _)
                       (map (fun r => fold_right (fun dm' r' =>
                                                    inlineDmToRule r' dm') r dms) l)
                   = map (@attrName _) l).
      { clear.
        induction l; simpl in *; intros.
        - reflexivity.
        - f_equal.
          + clear.
            induction dms; simpl in *; intros.
            * reflexivity.
            * assumption.
          + assumption.
      }
      rewrite sth.
      assumption.
  Qed.

  Hypothesis mEquiv: forall t, ModEquiv t typeUT m.

  Hypothesis HdmNoRule: forall r,
                          In r (prefix ++ suffix) ->
                          forall dm, In dm dms ->
                                     noCallDmSigA (attrType r typeUT) (attrName dm)
                                                  (projT1 (attrType dm)) = true.

  Hypothesis HdmNoMeth:
    forall d,
      In d (getDefsBodies m) ->
      forall dm, In dm dms ->
                 noCallDmSigA (projT2 (attrType d) typeUT tt)
                              (attrName dm) (projT1 (attrType dm)) = true.

  Hypothesis HDmsInRs: forall dm,
                         In dm dms ->
                         exists r, In r rs /\
                                   In (attrName dm) (getCallsA (attrType r typeUT)).

  Lemma inlineDmsToRules_traceRefines_Filt:
    m <<==
      (Mod (getRegInits m)
           (prefix ++ map (fun r => fold_right (fun dm' r' => inlineDmToRule r' dm') r dms) rs ++ suffix)
           (preDm ++ sufDm)).
  Proof.
    generalize dms preDm Hdm HdmNoMeth HdmNoRule HDmsInRs.
    clear dms preDm Hdm HdmNoMeth HdmNoRule HDmsInRs.
    induction dms; simpl in *; intros.
    - assert (sth: (fun r: Attribute (Action Void) => r) = id) by
          (extensionality r; reflexivity).
      rewrite sth.
      rewrite map_id.
      rewrite <- Hrule.
      rewrite <- Hdm.
      apply flatten_traceRefines.
    - assert (HdmNoMeth1:
                forall d,
                  In d (getDefsBodies m) ->
                  forall dm,
                    In dm l ->
                    noCallDmSigA (projT2 (attrType d) typeUT tt)
                                 (attrName dm) (projT1 (attrType dm)) = true)
        by (intros; apply HdmNoMeth; auto).
      assert (HdmNoMeth2: forall d, In d (getDefsBodies m) ->
                                    noCallDmSigA (projT2 (attrType d) typeUT tt)
                                                 (attrName a) (projT1 (attrType a)) = true)
        by (intros; apply HdmNoMeth; auto).
      clear HdmNoMeth.
      assert (HdmNoRule1:
                forall r : Attribute (Action Void),
                  In r (prefix ++ suffix) ->
                  forall dm : DefMethT,
                    In dm l ->
                    noCallDmSigA (attrType r typeUT) (attrName dm)
                                 (projT1 (attrType dm)) = true)
        by (intros; apply HdmNoRule; auto).
      assert (HdmNoRule2:
                forall r : Attribute (Action Void),
                  In r (prefix ++ suffix) ->
                  noCallDmSigA (attrType r typeUT) (attrName a)
                               (projT1 (attrType a)) = true)
        by (intros; apply HdmNoRule; auto).
      clear HdmNoRule.
      assert (HDmsInRs1:
                forall dm,
                  In dm l ->
                  exists r, In r rs /\ In (attrName dm) (getCallsA (attrType r typeUT)))
        by (intros; apply HDmsInRs; auto).
      assert (HDmsInRs2:
                exists r, In r rs /\ In (attrName a) (getCallsA (attrType r typeUT)))
        by (intros; apply HDmsInRs; auto).
      clear HDmsInRs.
      assert (sth: (preDm ++ [a]) ++ l ++ sufDm = preDm ++ a :: l ++ sufDm)
        by (rewrite <- app_assoc; simpl; reflexivity).
      rewrite <- sth in *.
      specialize (IHl _ Hdm HdmNoMeth1 HdmNoRule1 HDmsInRs1).
      rewrite <- app_assoc in IHl; simpl in IHl.
      match goal with
        | H: m <<== ?m2 |- _ => apply traceRefines_trans with (mb := m2)
      end.
      assert (sth2: (fun f: MethsT => f) = id) by (extensionality f; reflexivity).
      rewrite sth2.
      unfold MethsT; rewrite <- idElementwiseId.
      auto.
      match goal with
        | |- ?m2 <<== _ => assert (sth2: getRegInits m = getRegInits m2) by reflexivity;
            rewrite sth2 at 2
      end.
      rewrite <- map_map with (g := fun r => inlineDmToRule r a).
      apply inlineDmToRules_traceRefines_Filt; simpl in *; auto.
      + intros.
        specialize (mEquiv ty).
        destruct mEquiv as [rEquiv dEquiv].
        rewrite sth in Hdm.
        rewrite Hrule in rEquiv.
        rewrite Hdm in dEquiv.
        pose proof (proj1 (RulesEquiv_in _ _ _) rEquiv) as rEquiv'; clear rEquiv.
        pose proof (proj1 (MethsEquiv_in _ _ _) dEquiv) as dEquiv'; clear dEquiv.
        constructor; simpl in *.
        * apply RulesEquiv_in; intros.
          apply in_app_or in H.
          destruct H; [apply rEquiv'; apply in_or_app; left; intuition auto|].
          apply in_app_or in H.
          destruct H;
            [| apply rEquiv'; apply in_or_app; right; apply in_or_app; right; intuition auto].
          assert (sth4: forall r, In r rs -> RuleEquiv ty typeUT r)
            by (intros; apply rEquiv'; apply in_or_app; right; apply in_or_app; left;
                intuition auto).
          apply in_map_iff in H; dest; subst.
          specialize (sth4 _ H0).
          assert (sth5: forall m, In m l -> MethEquiv ty typeUT m)
            by (intros; apply dEquiv'; apply in_or_app; simpl; right; right; apply in_or_app;
                left; intuition auto).
          apply inlineDmsToRule_Equiv; auto.
        * apply MethsEquiv_in; intros.
          apply dEquiv'.
          apply in_or_app.
          apply in_app_or in H.
          destruct H; [left; intuition auto|].
          right; simpl in *.
          destruct H; [left; intuition auto|].
          right; apply in_or_app.
          intuition auto.
      + rewrite Hdm in HnoDupMeths; clear - HnoDupMeths.
        unfold namesOf in *.
        repeat (rewrite map_app in *; simpl in *).
        rewrite <- app_nil_r in HnoDupMeths.
        rewrite <- app_assoc with (n := nil) in HnoDupMeths.
        apply NoDup_app_comm_ext in HnoDupMeths.
        rewrite app_nil_r in HnoDupMeths.
        rewrite app_assoc in HnoDupMeths.
        apply NoDup_app_1 in HnoDupMeths.
        rewrite <- app_assoc in HnoDupMeths; simpl in *.
        assumption.
      + rewrite Hrule in HnoDupRules; clear - HnoDupRules.
        unfold namesOf in *; repeat (rewrite map_app in *; simpl in *).
        rewrite map_map.
        match goal with
          | H: NoDup (_ ++ ?l ++ _) |- NoDup (_ ++ ?x ++ _) =>
            assert (sth: x = l)
        end.
        (f_equal;
         extensionality x;
         apply inlineDmToRule_preserveName).
        rewrite sth; auto.
      + intros.
        rewrite sth in Hdm.
        rewrite Hdm in HdmNoMeth2.
        apply in_app_or in H; simpl in *.
        apply HdmNoMeth2; auto.
        apply in_or_app; simpl in *.
        intuition auto.
        right; right; apply in_or_app; auto.
      + destruct HDmsInRs2 as [r [inR inaR]].
        remember (fun x => fold_right (fun dm' r' => inlineDmToRule r' dm') x l) as f.
        exists (f r).
        constructor.
        apply in_map; auto.
        rewrite Heqf.
        apply inlineDmToRule_hasInCalls; auto.
        rewrite sth in Hdm.
        rewrite Hdm in HnoDupMeths.
        clear - HnoDupMeths.
        unfold namesOf in *.
        rewrite map_app in *.
        apply NoDup_app_2 in HnoDupMeths; simpl in *.
        rewrite map_app in *.
        pose proof HnoDupMeths as sth; clear HnoDupMeths.
        dependent destruction sth; clear sth.
        unfold not; intros.
        assert (In (attrName a) (map (@attrName _) l ++ map (@attrName _) sufDm))
          by (apply in_or_app; left; auto).
        intuition auto.
  Qed.
End PartialMultiDmMultiR.

Section rsEquivAfterInline.
  Variable ty: Kind -> Type.
  
  Lemma inlineDmsToRules_Equiv rs ls:
    RulesEquiv ty typeUT rs ->
    MethsEquiv ty typeUT ls ->
    RulesEquiv ty typeUT 
               (map (fun r => (fold_right
                                 (fun dm' r' => inlineDmToRule r' dm') r ls)) rs).
  Proof.
    induction rs; simpl in *; auto; intros.
    dependent destruction H.
    apply IHrs in H0; auto.
    constructor; auto.
    apply inlineDmsToRule_Equiv; auto.
    apply MethsEquiv_in; auto.
  Qed.
End rsEquivAfterInline.
  
