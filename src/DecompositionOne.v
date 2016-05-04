Require Import Bool List String Structures.Equalities FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax Semantics SemFacts Refinement Equiv.

Set Implicit Arguments.

Section Decomposition.
  Variable imp spec: Modules.
  Hypothesis HimpEquiv: ModEquiv type typeUT imp.

  Variable specRegName: string.
  Variable eta: RegsT -> option (sigT (fullType type)).

  Definition theta (r: RegsT): RegsT :=
    match eta r with
    | Some er => M.add specRegName er (M.empty _)
    | None => M.empty _
    end.
  
  Variable ruleMap: RegsT -> string -> option string.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).
  Hypothesis HthetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).
  
  Hypothesis HdefSubset: forall f, In f (getDefs spec) -> In f (getDefs imp).
  Hypothesis HcallSubset: forall f, In f (getCalls spec) -> In f (getCalls imp).

  Hypothesis HsubstepRuleMap:
    forall oImp uImp rule csImp,
      reachable oImp imp ->
      Substep imp oImp uImp (Rle (Some rule)) csImp ->
      exists uSpec,
        Substep spec (theta oImp) uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
        (* M.find specRegName uSpec <> M.find specRegName (theta oImp) /\ *)
        M.union uSpec (theta oImp) = theta (M.union uImp oImp).

  Definition liftP meth :=
    match meth with
    | (n :: t)%struct => match p n t with
                         | None => None
                         | Some v => Some (n :: v)%struct
                         end
    end.

  Hypothesis HsubstepMethMap:
    forall oImp uImp meth csImp,
      reachable oImp imp ->
      Substep imp oImp uImp (Meth (Some meth)) csImp ->
      exists uSpec,
        Substep spec (theta oImp) uSpec (Meth (liftP meth)) (liftToMap1 p csImp) /\
        (* M.find specRegName uSpec <> M.find specRegName (theta oImp) /\ *)
        M.union uSpec (theta oImp) = theta (M.union uImp oImp).

  Definition liftUnitLabel o ul :=
    match ul with
    | Rle (Some r) => Rle (ruleMap o r)
    | Rle None => Rle None
    | Meth (Some dm) => Meth (liftP dm)
    | Meth None => Meth None
    end.

  Hypothesis HcanCombine:
    forall oi ui1 ui2 uli1 uli2 csi1 csi2,
      reachable oi imp ->
      Substep imp oi ui1 uli1 csi1 ->
      Substep imp oi ui2 uli2 csi2 ->
      CanCombineUL ui1 ui2 (getLabel uli1 csi1) (getLabel uli2 csi2) ->
      forall os us1 us2 uls1 uls2 css1 css2,
        os = theta oi ->
        uls1 = liftUnitLabel oi uli1 ->
        uls2 = liftUnitLabel oi uli2 ->
        Substep spec os us1 uls1 css1 ->
        Substep spec os us2 uls2 css2 ->
        M.union us1 os = theta (M.union ui1 oi) ->
        M.union us2 os = theta (M.union ui2 oi) ->
        CanCombineUL us1 us2 (getLabel uls1 css1) (getLabel uls2 css2).

  Lemma canCombine_substepsInd:
    forall oi ui1 ui2 li1 uli2 csi2,
      reachable oi imp ->
      SubstepsInd imp oi ui1 li1 ->
      Substep imp oi ui2 uli2 csi2 ->
      CanCombineUUL ui1 li1 ui2 csi2 uli2 ->
      forall os us1 us2 ls1 uls2 css2,
        os = theta oi ->
        ls1 = liftPLabel (liftToMap1 p) ruleMap oi li1 ->
        uls2 = liftUnitLabel oi uli2 ->
        SubstepsInd spec os us1 ls1 ->
        Substep spec os us2 uls2 css2 ->
        M.union us1 os = theta (M.union ui1 oi) ->
        M.union us2 os = theta (M.union ui2 oi) ->
        CanCombineUUL us1 ls1 us2 css2 uls2.
  Proof.
    induction 2; simpl; intros; subst.
    
    - admit.
      
    - specialize (IHSubstepsInd H5).
      assert (CanCombineUUL u l ui2 csi2 uli2).
      { eapply unionCanCombineUUL.
        instantiate (1:= {| substep:= H1 |}); auto.
      }
      specialize (IHSubstepsInd H3); clear H3.
      admit.
  Qed.

  Lemma decomposition_substepsInd:
    forall oImp uImp lImp,
      reachable oImp imp ->
      SubstepsInd imp oImp uImp lImp ->
      exists uSpec,
        SubstepsInd spec (theta oImp) uSpec (liftPLabel (liftToMap1 p) ruleMap oImp lImp) /\
        M.union uSpec (theta oImp) = theta (M.union uImp oImp).
  Proof.
    induction 2; [exists (M.empty _); split; [constructor|auto]|subst].

    destruct sul as [[r|]|[dm|]].

    - destruct IHSubstepsInd as [uspecs ?]; dest.
      destruct (HsubstepRuleMap H H1) as [uspec ?]; dest.
      exists (M.union uspecs uspec); split.
      + eapply SubstepsCons; eauto.
        * eapply canCombine_substepsInd; eauto.
        * unfold liftPLabel; destruct l as [a d c]; simpl; f_equal.
          { destruct a as [[|]|]; auto. }
          { inv H2; dest; simpl in *.
            apply liftToMap1_union; auto.
          }
      + admit. (* update consistency by singleton property *)

    - destruct IHSubstepsInd as [uspecs ?]; dest.
      inv H1.
      exists uspecs; split.
      + eapply SubstepsCons.
        * exact H3.
        * apply EmptyRule.
        * clear -H2; inv H2; dest.
          repeat split; auto.
          destruct l as [[[|]|] d c]; simpl in *; auto.
        * auto.
        * unfold liftPLabel; destruct l as [a d c]; simpl; f_equal.
          destruct a as [[|]|]; auto.
      + mred.

    - destruct IHSubstepsInd as [uspecs ?]; dest.
      destruct (HsubstepMethMap H H1) as [uspec ?]; dest.
      exists (M.union uspecs uspec); split.
      + eapply SubstepsCons; eauto.
        * eapply canCombine_substepsInd; eauto.
        * inv H2; dest.
          destruct l as [a d c]; simpl in *; f_equal.
          { rewrite liftToMap1_union.
            { f_equal.
              destruct dm as [dmn dmb]; simpl.
              rewrite liftToMap1AddOne.
              destruct (p dmn dmb); auto.
            }
            { destruct dm as [dmn dmb]; simpl.
              apply M.Disj_add_1; auto.
              destruct a; auto.
            }
          }
          { apply liftToMap1_union; auto. }
      + admit. (* update consistency *)

    - destruct IHSubstepsInd as [uspecs ?]; dest.
      inv H1.
      exists uspecs; split.
      + p_equal H3; f_equal.
        destruct l as [a d c]; auto.
      + mred.

  Qed.

  Lemma liftPLabel_hide:
    forall o l,
      M.KeysSubset (defs l) (getDefs imp) ->
      M.KeysSubset (calls l) (getCalls imp) ->
      wellHidden imp (hide l) ->
      liftPLabel (liftToMap1 p) ruleMap o (hide l) =
      hide (liftPLabel (liftToMap1 p) ruleMap o l).
  Proof.
    intros; destruct l as [a d c].
    unfold hide in *; simpl in *.
    f_equal; auto.
    - apply eq_sym, liftToMap1_subtractKV_2.
      intros; unfold wellHidden in H1; dest; simpl in *.
      apply M.subtractKV_not_In_find with (deceqA:= signIsEq) (m2:= c) in H2.
      + rewrite H2 in H3; inv H3; reflexivity.
      + apply H1, H0.
        apply M.F.P.F.in_find_iff; rewrite H3; discriminate.
    - apply eq_sym, liftToMap1_subtractKV_2.
      intros; unfold wellHidden in H1; dest; simpl in *.
      apply M.subtractKV_not_In_find with (deceqA:= signIsEq) (m2:= c) in H3.
      + rewrite H2 in H3; inv H3; reflexivity.
      + apply H1, H0.
        apply M.F.P.F.in_find_iff; rewrite H2; discriminate.
  Qed.

  Lemma liftPLabel_wellHidden:
    forall o l,
      wellHidden imp l ->
      wellHidden spec (liftPLabel (liftToMap1 p) ruleMap o l).
  Proof.
    intros; unfold wellHidden in *.
    destruct l; simpl in *; dest; split.
    - clear -H HcallSubset.
      unfold M.KeysDisj in *; intros.
      specialize (H k (HcallSubset _ H0)).
      clear -H; findeq.
      rewrite liftToMap1_find, H; auto.
    - clear -H0 HdefSubset.
      unfold M.KeysDisj in *; intros.
      specialize (H0 k (HdefSubset _ H)).
      clear -H0; findeq.
      rewrite liftToMap1_find, H0; auto.
  Qed.

  Lemma liftPLabel_hide_wellHidden:
    forall o l,
      M.KeysSubset (defs l) (getDefs imp) ->
      M.KeysSubset (calls l) (getCalls imp) ->
      wellHidden imp (hide l) ->
      wellHidden spec (hide (liftPLabel (liftToMap1 p) ruleMap o l)).
  Proof.
    intros; rewrite <-liftPLabel_hide; auto.
    apply liftPLabel_wellHidden; auto.
  Qed.
    
  Theorem decomposition_singleton:
    traceRefines (liftToMap1 p) imp spec.
  Proof.
    apply stepRefinement with (theta:= theta) (ruleMap:= ruleMap); auto.
    intros.

    apply step_consistent in H0; inv H0.
    pose proof (decomposition_substepsInd H HSubSteps) as Hdecompose.
    destruct Hdecompose as [uspec ?]; dest.
    exists uspec; split; auto.

    apply step_consistent.
    rewrite liftPLabel_hide; auto.
    - constructor; auto.
      apply liftPLabel_hide_wellHidden; auto.
      + eapply substepsInd_defs_in; eauto.
      + eapply substepsInd_calls_in; eauto.
    - eapply substepsInd_defs_in; eauto.
    - eapply substepsInd_calls_in; eauto.
  Qed.
  
End Decomposition.

