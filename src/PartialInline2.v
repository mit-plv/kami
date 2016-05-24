Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq.
Require Import Syntax Semantics SemFacts Equiv Inline InlineFacts_1 InlineFacts_2 Tactics.
Require Import Refinement PartialInline Program.Equality.

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

  Lemma filter_equiv: filter (filterA _ a) ls = prefix ++ suffix.
  Proof.
    subst.
    rewrite filter_app.
    f_equal.
    apply filterA_eq.
    apply aNotInPrefix.
    simpl.
    unfold filterA.
    destruct (string_dec (attrName a) (attrName a)); auto.
    apply filterA_eq.
    apply aNotInSuffix.
    intuition.
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
    assert (sth: inlineDmToRule r dm = attrF _ (fun a type => inlineDm (a type) dm) r) by
        (unfold inlineDmToRule; reflexivity).
    rewrite sth.
    rewrite <- map_equiv with (ls := getRules m); auto.
    apply inlineDmToRule_traceRefines_1.
    apply inDmGetDefsBodies; auto.
    auto.
  Qed.

  Hypothesis HdmNoRule: forall r, In r (prefix ++ suffix) ->
                                  ~ In (attrName dm) (getCallsA (attrType r typeUT)).
  Hypothesis HdmNoMeth: forall d, In d (getDefsBodies m) ->
                                  ~ In (attrName dm) (getCallsA (projT2 (attrType d) typeUT tt)).
  Hypothesis HDmInR: In (attrName dm) (getCallsA (attrType r typeUT)).
  Hypothesis HnoCall: noCallDm dm dm = true.
  
  Lemma inlineDmToRule_traceRefines_Filt:
    m <<== (Mod (getRegInits m)
                (prefix ++ inlineDmToRule r dm :: suffix)
                (preDm ++ sufDm)).
  Proof.
    assert (sth: inlineDmToRule r dm = attrF _ (fun a type => inlineDm (a type) dm) r) by
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
    apply HdmNoRule with (r := rule); auto.
    rewrite Hrule in H.
    apply in_app_or in H;
      apply in_or_app; intuition auto.
    simpl in H2.
    destruct H2.
    subst; intuition auto.
    intuition auto.
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
        | [|- ?m <<== _] => pose proof (inlineDmToRule_traceRefines_NoFilt m a preDm (l ++ sufDm) Hdm HnoDupMeths prefix suffix (fold_right (fun dm' r' => inlineDmToRule r' dm') r l) eq_refl) as sth3; simpl in *
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

  Hypothesis HdmNoRule: forall r,
                          In r (prefix ++ suffix) ->
                          forall dm, In dm dms ->
                                     ~ In (attrName dm) (getCallsA (attrType r typeUT)).
  Hypothesis HdmNoMeth:
    forall d,
      In d (getDefsBodies m) ->
      forall dm, In dm dms ->
                 ~ In (attrName dm) (getCallsA (projT2 (attrType d) typeUT tt)).

  Hypothesis HDmsInR: forall dm, In dm dms -> In (attrName dm) (getCallsA (attrType r typeUT)).
  Hypothesis HnoCall: forall dm, In dm dms -> noCallDm dm dm = true.

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
    generalize dms preDm Hdm HdmNoRule HdmNoMeth HDmsInR HnoCall.
    clear dms preDm Hdm HdmNoRule HdmNoMeth HDmsInR HnoCall.
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
                               forall dm, In dm l -> ~ In (attrName dm)
                                                       (getCallsA (attrType r0 typeUT)))
        by (intros; apply HdmNoRule; auto).
      assert (HDmsInR1: forall dm, In dm l -> In (attrName dm) (getCallsA (attrType r typeUT)))
        by (intros; apply HDmsInR; auto).
      assert (HDmsInR2: In (attrName a) (getCallsA (attrType r typeUT)))
        by (intros; apply HDmsInR; auto).
      assert (HnoCall1: forall dm, In dm l -> noCallDm dm dm = true) by
          (intros; apply HnoCall; auto).
      assert (HnoCall2: noCallDm a a = true) by
          (intros; apply HnoCall; auto).
      assert (sth4:
                forall d, In d (getDefsBodies m) ->
                          forall dm, In dm l -> ~ In (attrName dm)
                                                  (getCallsA (projT2 (attrType d) typeUT tt)))
        by (intros; apply HdmNoMeth; auto).
      specialize (IHl (preDm ++ [a]) sth2 sth3 sth4 HDmsInR1 HnoCall1); clear sth3 sth4.
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
          pose proof (inlineDmToRule_traceRefines_Filt
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
      intros; apply HdmNoMeth; auto.
      rewrite sth2.
      repeat (try apply in_app_or in H; try apply in_or_app; try destruct H; intuition auto).
      right; apply in_or_app; right; auto.
      apply cheat.
  Qed.
End PartialMultiDm.

(*
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
          pose proof (inlineDmsToRule_traceRefines_NoFilt
                        m dms preDm sufDm Hdm prefix
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

  Hypothesis HdmNoRule: forall r,
                          In r (prefix ++ suffix) ->
                          forall dm, In dm dms ->
                                     ~ In (attrName dm) (getCallsA (attrType r typeUT)).
  Hypothesis HdmNoMeth:
    forall d,
      In d (getDefsBodies m) ->
      forall dm, In dm dms ->
                 ~ In (attrName dm) (getCallsA (projT2 (attrType d) typeUT tt)).

  Lemma inlineDmsToRules_traceRefines_Filt:
    m <<==
      (Mod (getRegInits m)
           (prefix ++ map (fun r => fold_right (fun dm' r' => inlineDmToRule r' dm') r dms) rs ++ suffix)
           (preDm ++ sufDm)).
  Proof.
    admit.
  Qed.
End PartialMultiDmMultiR.
*)