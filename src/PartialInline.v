Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq.
Require Import Syntax Semantics SemFacts Equiv Inline InlineFacts_1 InlineFacts_2 Tactics.
Require Import Refinement.

Set Implicit Arguments.

Fixpoint ValidCall (dm: DefMethT) {retT} (a: ActionT typeUT retT) :=
  match a with
  | MCall m sig _ c =>
    if string_eq m (attrName dm) then
      if SignatureT_dec (projT1 (attrType dm)) sig then
        ValidCall dm (c tt)
      else false
    else false
  | Let_ fk e c => ValidCall dm
                             (c match fk as fk' return fullType typeUT fk' with
                                | SyntaxKind _ => tt
                                | NativeKind _ c' => c'
                                end)
  | ReadReg _ fk c => ValidCall dm
                                (c match fk as fk' return fullType typeUT fk' with
                                   | SyntaxKind _ => tt
                                   | NativeKind _ c' => c'
                                   end)
  | WriteReg _ _ _ c => ValidCall dm c
  | IfElse _ _ aT aF c => (ValidCall dm aT) && (ValidCall dm aF) && (ValidCall dm (c tt))
  | Assert_ _ c => ValidCall dm c
  | Return _ => true
  end.

Lemma inlineDm_not_in_calls:
  forall dm {retK} (a: ActionT typeUT retK),
    ValidCall dm a = true ->
    noCallDm dm dm = true ->
    ~ In (attrName dm) (getCallsA (inlineDm a dm)).
Proof.
  intros; induction a; auto.
  - simpl in *.
    unfold getBody.
    destruct (string_eq meth (attrName dm)); [|inv H].
    destruct (SignatureT_dec _ _); [|inv H].
    simpl; rewrite getCallsA_appendAction.

    intro Hx; apply in_app_or in Hx; destruct Hx;
      [|generalize H2; apply H1; auto].

    rewrite <-e0 in H2; simpl in H2.
    clear -H0 H2.
    unfold noCallDm in H0.
    apply eq_sym, isLeaf_implies_disj in H0.
    specialize (H0 (attrName dm)); destruct H0; auto.
    elim H; simpl; tauto.
    
  - apply H1; auto.
  - apply H1; auto.
  - simpl in H.
    apply andb_true_iff in H; dest.
    apply andb_true_iff in H; dest.
    simpl; intro Hx.
    apply in_app_or in Hx; destruct Hx.
    + apply IHa1; auto.
    + apply in_app_or in H4; destruct H4.
      * apply IHa2; auto.
      * generalize H4; apply H1; auto.
Qed.

Lemma inlineDmToRule_not_in_calls:
  forall (r: Attribute (Action Void))
         dm regs (rules: list (Attribute (Action Void)))
         (Hrule: In r rules)
         (HnoDupRules: NoDup (namesOf rules))
         (dms: list DefMethT),
    ValidCall dm (attrType r typeUT) = true ->
    noCallDm dm dm = true ->
    (forall rule,
        In rule rules ->
        attrName rule <> attrName r -> ~ In (attrName dm) (getCallsA (attrType rule typeUT))) ->
    (forall meth,
        In meth dms ->
        ~ In (attrName dm) (getCallsA (projT2 (attrType meth) typeUT tt))) ->
    ~ In (attrName dm)
      (getCalls
        (Mod regs
             (map (fun newr =>
                     if string_dec (attrName r) (attrName newr)
                     then inlineDmToRule newr dm
                     else newr) rules) dms)).
Proof.
  intros; intro Hx.
  apply in_app_or in Hx; destruct Hx.

  - simpl in *; clear H2.
    induction rules; simpl; intros; auto.
    simpl in H3.
    apply in_app_or in H3; destruct H3.
    + destruct (string_dec (attrName r) (attrName a)); [subst|].
      * assert (r = a); subst.
        { eapply in_NoDup_attr; eauto.
          left; auto.
        }
        simpl in H2; generalize H2.
        apply inlineDm_not_in_calls; auto.
      * generalize H2; apply H1; intuition.
    + destruct (string_dec (attrName r) (attrName a)); [subst|].
      * assert (r = a); subst.
        { eapply in_NoDup_attr; eauto.
          left; auto.
        }
        clear IHrules.
        replace (map
                   (fun newr =>
                      if string_dec (attrName a) (attrName newr)
                      then inlineDmToRule newr dm else newr)
                   rules) with rules in H2.
        { inv HnoDupRules. clear -H1 H2 H5.
          induction rules; [auto|].
          simpl in H2; apply in_app_or in H2; destruct H2.
          { generalize H; apply H1.
            { simpl; tauto. }
            { intro Hx; elim H5; left; auto. }
          }
          { apply IHrules; auto.
            { intros; apply H1; auto.
              inv H0; simpl; tauto.
            }
            { intro Hx; elim H5; simpl; tauto. }
          }
        }
        { inv HnoDupRules; clear -H5.
          induction rules; [auto|].
          simpl; f_equal.
          { destruct (string_dec (attrName a) (attrName a0)).
            { elim H5; simpl; left; auto. }
            { auto. }
          }
          { apply IHrules; intro Hx; elim H5.
            simpl; tauto.
          }
        }
      * generalize H2; apply IHrules; auto.
        { destruct Hrule; auto.
          subst; elim n; reflexivity.
        }
        { inv HnoDupRules; auto. }
        { intros; apply H1; auto.
          simpl; tauto.
        }

  - simpl in *; clear H1.
    induction dms; simpl; intros; auto.
    simpl in H3.
    apply in_app_or in H3; destruct H3.
    + generalize H1; apply H2; intuition.
    + generalize H1; apply IHdms; auto.
      intros; apply H2; intuition.
Qed.

(* Partial inlining interfaces *)
Section Partial.
  Variable m: Modules.

  Variable dm: DefMethT. (* a method to be inlined *)
  Hypotheses (Hdm: In dm (getDefsBodies m))
             (HnoDupMeths: NoDup (namesOf (getDefsBodies m))).
  Variable r: Attribute (Action Void). (* a rule calling dm *)
  Hypothesis Hrule: In r (getRules m).

  Lemma inlineDmToRule_substepsInd_intact_1:
    forall o u l,
      SubstepsInd m o u l ->
      ~ (annot l = Some (Some (attrName r)) /\ M.find (attrName dm) (calls l) <> None) ->
      SubstepsInd
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm
                   else newr) (getRules m)) (getDefsBodies m)) o u l.
  Proof.
    induction 1; intros; [constructor|].
    subst; econstructor.

    - apply IHSubstepsInd.
      intro Hx; elim H4; clear H4; dest; split.
      + clear -H1 H2.
        inv H1; dest.
        destruct l as [ann ds cs], sul as [|];
          simpl in *; subst; intuition idtac.
      + intro Hx; elim H3; clear H3.
        destruct l as [ann ds cs]; simpl in *; findeq.

    - instantiate (1:= scs); instantiate (1:= sul); instantiate (1:= su).
      clear -H0 H4.
      inv H0; try constructor.

      + destruct (string_dec (attrName r) k); subst.
        * remember (M.find (attrName dm) scs) as ods; destruct ods.
          { elim H4; clear H4; split.
            { destruct l as [ann ds cs]; simpl; destruct ann; reflexivity. }
            { destruct l as [ann ds cs]; simpl.
              rewrite M.find_union, <-Heqods; discriminate.
            }
          }
          { econstructor.
            { simpl.
              apply in_map with (f:= fun newr =>
                                       if string_dec (attrName r) (attrName newr)
                                       then inlineDmToRule newr dm
                                       else newr) in HInRules.
              simpl in HInRules.
              destruct (string_dec (attrName r) (attrName r)); [clear e|elim n; reflexivity].
              eauto.
            }
            { simpl; destruct dm as [dmn dmb].
              apply inlineDm_SemAction_intact; auto.
            }
          }
        * econstructor.
          { simpl.
            apply in_map with (f:= fun newr =>
                                     if string_dec (attrName r) (attrName newr)
                                     then inlineDmToRule newr dm
                                     else newr) in HInRules.
            simpl in HInRules.
            destruct (string_dec (attrName r) k); [elim n; auto|].
            eauto.
          }
          { auto. }

      + econstructor; eauto.

    - auto.
    - auto.
    - auto.

  Qed.

  Lemma inlineDmToRule_substepsInd_intact_2:
    forall o pu pds pcs,
      SubstepsInd m o pu {| annot := None; defs := pds; calls := pcs |} ->
      forall ru rcs,
        Substep m o ru (Rle (Some (attrName r))) rcs ->
        None = M.find (elt:=sigT SignT) (attrName dm) rcs ->
        (* Some s = M.find (elt:=sigT SignT) (attrName dm) pcs -> *)
        M.Disj ru pu -> M.Disj rcs pcs ->
        SubstepsInd
          (Mod (getRegInits m)
               (map
                  (fun newr =>
                     if string_dec (attrName r) (attrName newr)
                     then inlineDmToRule newr dm else newr)
                  (getRules m)) (getDefsBodies m)) o (M.union pu ru)
          {| annot := Some (Some (attrName r)); defs := pds; calls := M.union rcs pcs |}.
  Proof.
    intros; econstructor.

    - apply inlineDmToRule_substepsInd_intact_1.
      + eassumption.
      + simpl; intro Hx; dest; discriminate.

    - instantiate (1:= rcs).
      instantiate (1:= Rle (Some (attrName r))).
      instantiate (1:= ru).
      inv H0.

      econstructor.
      + simpl.
        apply in_map with (f:= fun newr =>
                                 if string_dec (attrName r) (attrName newr)
                                 then inlineDmToRule newr dm
                                 else newr) in HInRules.
        simpl in HInRules.
        destruct (string_dec (attrName r) (attrName r)); [clear e|elim n; reflexivity].
        eauto.
      + simpl; destruct dm as [dmn dmb].
        apply inlineDm_SemAction_intact; auto.

    - repeat split; auto.
    - reflexivity.
    - reflexivity.

  Qed.

  Lemma inlineDmToRule_substepsInd_sub:
    forall o u su scs s l,
      Substep m o su (Rle (Some (attrName r))) scs ->
      M.find (elt:=sigT SignT) (attrName dm) scs = Some s ->
      SubstepsInd m o u l ->
      forall ds cs,
        l = {| annot := None; defs:= ds; calls := cs |} ->
        M.Disj su u -> M.Disj scs cs ->
        M.find (elt:=sigT SignT) (attrName dm) ds = Some s ->
        SubstepsInd
          (Mod (getRegInits m)
               (map
                  (fun newr =>
                     if string_dec (attrName r) (attrName newr)
                     then inlineDmToRule newr dm else newr)
                  (getRules m)) (getDefsBodies m)) o (M.union u su)
          (hideMeth 
             {| annot := Some (Some (attrName r));
                defs := ds;
                calls := M.union scs cs |} (attrName dm)).
  Proof.
    induction 3; simpl; intros; [exfalso; inv H1; mred|].

    subst; destruct l as [pann pds pcs].
    destruct pann as [|]; [exfalso; destruct sul; inv H6|].
    specialize (IHSubstepsInd _ _ eq_refl).

    remember (M.find (attrName dm) pds) as odp; destruct odp.

    - assert (s = s0); subst.
      { clear -Heqodp H3 H6 H9.
        inv H3; dest; simpl in *.
        inv H6.
        destruct sul as [|[[dmn dmb]|]]; simpl in *; findeq.
        destruct (string_dec (attrName dm) dmn).
        { subst; exfalso; mcontra. }
        { mred. }
      }

      econstructor.
      + apply IHSubstepsInd; auto.
        inv H6; auto.
      + instantiate (1:= scs0); instantiate (1:= sul); instantiate (1:= su0).
        destruct sul as [|]; [exfalso; inv H6|].
        clear -H2.
        inv H2; [constructor|].
        econstructor; eauto.
      + inv H6; inv H3; dest; simpl in *.
        unfold hideMeth; simpl.
        rewrite <-Heqodp.
        rewrite M.find_union, H0.
        destruct (signIsEq _ _); [|elim n; reflexivity].
        repeat split; simpl; auto.
        destruct sul as [|[|]]; auto.
        * inv H5.
        * findeq; auto.
      + meq.
      + unfold hideMeth at 1; simpl.
        rewrite H9.
        rewrite M.find_union, H0.
        destruct (signIsEq _ _); [clear e|elim n; reflexivity].
        unfold hideMeth; simpl.
        rewrite <-Heqodp.
        rewrite M.find_union, H0.
        destruct (signIsEq _ _); [clear e|elim n; reflexivity].
        f_equal.
        * inv H6; destruct sul as [|[|]]; auto; inv H5.
        * inv H6; inv H3; dest; simpl in *.
          destruct sul as [|[[dmn dmb]|]]; auto.
          destruct (string_dec (attrName dm) dmn); auto.
          subst; meq.
          simpl in H6; mcontra.
        * inv H6; inv H3; dest; simpl in *.
          apply eq_sym in H0; meq.
          
    - clear IHSubstepsInd.
      assert (sul = Meth (Some (attrName dm :: s)%struct)); subst.
      { destruct sul as [|]; inv H6.
        destruct o0 as [[dmn dmb]|]; [|mred].
        destruct (string_dec (attrName dm) dmn); subst; mred.
      }
      inv H3; inv H6; dest; simpl in *; clear H5 H9.

      econstructor.
      + apply inlineDmToRule_substepsInd_intact_1.
        * eassumption.
        * simpl; intro Hx; dest; discriminate.
      + instantiate (1:= M.remove (attrName dm) (M.union scs scs0)).
        instantiate (1:= Rle (Some (attrName r))).
        instantiate (1:= M.union su su0).

        inv H; inv H2.
        econstructor.
        * simpl.
          apply in_map with (f:= fun newr =>
                                   if string_dec (attrName r) (attrName newr)
                                   then inlineDmToRule newr dm
                                   else newr) in HInRules.
          simpl in HInRules.
          destruct (string_dec _ _); [|elim n; reflexivity].
          eauto.
        * simpl; inv Hsig.
          assert (dm = f) by (eapply in_NoDup_attr; eauto); subst.
          rewrite M.union_comm with (m1:= su) by auto.
          replace (M.remove (attrName f) (M.union scs scs0)) with
          (M.union scs0 (M.remove (attrName f) scs))
            by (meq; apply eq_sym in H0; mcontra).
          eapply inlineDm_correct_SemAction; eauto.

      + repeat split; auto.
      + meq.
      + unfold hideMeth; simpl; mred.
        simpl; f_equal; meq.

  Qed.

  Lemma wellHidden_weakening:
    forall l m1 m2,
      SubList (getCalls m1) (getCalls m2) ->
      SubList (getDefs m1) (getDefs m2) ->
      wellHidden m2 l ->
      wellHidden m1 l.
  Proof.
    unfold wellHidden; intros.
    dest; split.
    - eapply M.KeysDisj_SubList; eauto.
    - eapply M.KeysDisj_SubList; eauto.
  Qed.

  Lemma inlineDmToRule_wellHidden:
    forall l,
      wellHidden m l ->
      wellHidden
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m)) (getDefsBodies m)) l.
  Proof.
    intros; apply wellHidden_weakening with (m2:= m); auto.
    - unfold getCalls; simpl.
      apply SubList_app_3; [|apply SubList_app_2, SubList_refl].
      clear -Hdm.
      induction (getRules m); [apply SubList_nil|].
      apply SubList_app_3.
      + destruct (string_dec _ _).
        * simpl.
          pose proof (inlineDm_calls _ _ Hdm (attrType a typeUT)).
          apply SubList_trans with (l2:= getCallsA (attrType a typeUT)
                                                   ++ getCallsM (getDefsBodies m)); auto.
          apply SubList_app_3.
          { apply SubList_app_1, SubList_app_1, SubList_refl. }
          { apply SubList_app_2, SubList_refl. }
        * simpl.
          apply SubList_app_1, SubList_app_1, SubList_refl.
      + fold getCallsR.
        apply SubList_trans with (l2:= getCallsR l ++ getCallsM (getDefsBodies m)); auto.
        apply SubList_app_3.
        * apply SubList_app_1, SubList_app_2, SubList_refl.
        * apply SubList_app_2, SubList_refl.
    - apply SubList_refl.
  Qed.

  Lemma inlineDmToRule_stepInd:
    forall o u l,
      StepInd m o u l ->
      StepInd
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m)) (getDefsBodies m)) o u l.
  Proof.
    intros; inv H.

    destruct l0 as [ann ds cs].
    assert (ann = Some (Some (attrName r)) \/ ~ ann = Some (Some (attrName r))).
    { destruct ann; [|right; discriminate].
      destruct o0; [|right; discriminate].
      destruct (string_dec s (attrName r)).
      { subst; left; reflexivity. }
      { right; intro Hx; inv Hx; elim n; reflexivity. }
    }

    destruct H.

    - subst.
      pose proof (substepsInd_rule_split HSubSteps) as Hsp.
      clear HSubSteps.
      specialize (Hsp _ eq_refl).
      destruct Hsp as [ru [rcs [pu [pl ?]]]]; dest; subst.

      remember (M.find (attrName dm) rcs) as odr; destruct odr.

      + rewrite <-hideMeth_preserves_hide with (dm:= attrName dm).
        constructor.
        * destruct pl as [pann pds pcs]; inv H3.
          inv H1; dest; simpl in *; mred.
          destruct pann; [inv H3|].
          eapply inlineDmToRule_substepsInd_sub; eauto.

          clear -Hdm Heqodr HWellHidden.
          apply wellHidden_find_1 with (a:= attrName dm) in HWellHidden.
          { simpl in *; destruct HWellHidden; mred. }
          { apply in_map; auto. }
          
        * rewrite hideMeth_preserves_hide.
          apply inlineDmToRule_wellHidden; auto.

      + destruct pl as [pann pds pcs]; simpl in *.
        remember (M.find (attrName dm) pcs) as odp; destruct odp.

        * econstructor.
          { mred; inv H3; clear H4.
            inv H1; dest; simpl in *.
            destruct pann; [inv H3|].
            apply inlineDmToRule_substepsInd_intact_2; auto.
          }
          { apply inlineDmToRule_wellHidden; auto. }

        * econstructor.
          { apply inlineDmToRule_substepsInd_intact_1; auto.
            { econstructor; eauto. }
            { simpl; intro Hx; dest.
              elim H4; clear H4.
              inv H3; findeq.
            }
          }
          { apply inlineDmToRule_wellHidden; auto. }

    - econstructor.
      + apply inlineDmToRule_substepsInd_intact_1; auto.
        simpl; intro Hx; dest; elim H; auto.
      + apply inlineDmToRule_wellHidden; auto.

  Qed.

  Lemma inlineDmToRule_traceRefines_1:
    m <<== (Mod (getRegInits m)
                (map (fun newr =>
                        if string_dec (attrName r) (attrName newr)
                        then inlineDmToRule newr dm
                        else newr) (getRules m))
                (getDefsBodies m)).
  Proof.
    apply stepRefinement with (ruleMap:= fun _ s => Some s) (theta:= id); auto.
    intros; exists u; split; auto.

    rewrite idElementwiseId.
    replace (liftPLabel _ _ _ _) with l; [|destruct l as [[[|]|] ? ?]; simpl; f_equal].
    unfold id.

    clear H.
    apply step_consistent; apply step_consistent in H0.
    apply inlineDmToRule_stepInd; auto.
  Qed.

  Hypotheses (Hequiv: ModEquiv type typeUT m)
             (HvCalls: ValidCall dm (attrType r typeUT) = true)
             (HrCalls: In (attrName dm) (getCallsA (attrType r typeUT)))
             (HnoDupRules: NoDup (namesOf (getRules m)))
             (HnoCallDm: noCallDm dm dm = true)
             (HnoRuleCalls: forall rule,
                 In rule (getRules m) ->
                 attrName rule <> attrName r ->
                 ~ In (attrName dm) (getCallsA (attrType rule typeUT)))
             (HnoMethCalls: forall meth,
                 In meth (getDefsBodies m) ->
                 ~ In (attrName dm) (getCallsA (projT2 (attrType meth) typeUT tt))).

  Lemma getCallsA_getCalls_In:
    In (attrName dm) (getCalls m).
  Proof.
    unfold getCalls.
    apply in_or_app; left.
    clear -Hrule HrCalls.
    induction (getRules m); auto.
    destruct Hrule; [subst|].
    - simpl; apply in_or_app; left; auto.
    - simpl; apply in_or_app; right; auto.
  Qed.

  Lemma inlineDmToRule_filtered_wellHidden:
    forall l,
      wellHidden
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m))
             (getDefsBodies m)) l ->
      wellHidden
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m))
             (filterDm (getDefsBodies m) (attrName dm))) l.
  Proof.
    intros.
    intros; eapply wellHidden_weakening; eauto.
    - apply SubList_app_3.
      + apply SubList_app_1, SubList_refl.
      + apply SubList_app_2; simpl.
        clear; induction (getDefsBodies m); simpl; [apply SubList_nil|].
        destruct (string_dec _ _).
        * apply SubList_app_2; auto.
        * simpl; apply SubList_app_3.
          { apply SubList_app_1, SubList_refl. }
          { apply SubList_app_2; auto. }
    - unfold getDefs; simpl.
      apply SubList_map.
      unfold SubList; intros.
      unfold filterDm in H0; apply filter_In in H0; dest; auto.
  Qed.

  Lemma inlineDmToRule_ModEquiv:
    ModEquiv type typeUT (Mod (getRegInits m)
                              (map (fun newr =>
                                      if string_dec (attrName r) (attrName newr)
                                      then inlineDmToRule newr dm
                                      else newr) (getRules m))
                              (getDefsBodies m)).
  Proof.
    clear -Hequiv Hdm.
    assert (MethEquiv type typeUT dm).
    { inv Hequiv.
      rewrite MethsEquiv_in in H0.
      apply H0; auto.
    }
    inv Hequiv.
    constructor; simpl; auto; clear H1.
    induction H0; simpl; [constructor|].
    constructor; auto.
    destruct (string_dec _ _); auto.
    apply inlineDm_ActionEquiv; auto.
  Qed.

  Lemma inlineDmToRule_traceRefines_2:
    m <<== (Mod (getRegInits m)
                (map (fun newr =>
                        if string_dec (attrName r) (attrName newr)
                        then inlineDmToRule newr dm
                        else newr) (getRules m))
                (filterDm (getDefsBodies m) (attrName dm))).
  Proof.
    apply stepRefinement with (ruleMap:= fun _ s => Some s) (theta:= id); auto.
    intros; exists u; split; auto.

    rewrite idElementwiseId.
    replace (liftPLabel _ _ _ _) with l; [|destruct l as [[[|]|] ? ?]; simpl; f_equal].
    unfold id.

    clear H.
    apply step_consistent; apply step_consistent in H0.

    pose proof (inlineDmToRule_stepInd H0).

    inv H; constructor.

    - match goal with
      | [H: SubstepsInd ?im _ _ _ |- _] =>
        assert (~ In (attrName dm) (getCalls im))
      end.
      { apply inlineDmToRule_not_in_calls; auto. }

      assert (M.find (attrName dm) (calls l0) = None).
      { pose proof (substepsInd_calls_in inlineDmToRule_ModEquiv HSubSteps).
        remember (M.find (attrName dm) (calls l0)) as odc; destruct odc; auto.
        elim H; apply H1; findeq.
      }

      assert (M.find (attrName dm) (defs l0) = None).
      { rewrite <-H1.
        clear HWellHidden; inv H0.
        apply wellHidden_find_2 with (m:= m); auto.
        { simpl; apply in_map; auto. }
        { apply getCallsA_getCalls_In. }
        { unfold wellHidden, hide; simpl.
          rewrite <-H5, <-H6; auto.
        }
      }

      apply substepsInd_filterDm; auto.

    - apply inlineDmToRule_filtered_wellHidden; auto.
    
  Qed.

End Partial.

