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

  Definition ConsistentUpdate (oImp oSpec: RegsT) (uImp uSpec: UpdatesT) :=
    (uImp = M.empty _ -> uSpec = M.empty _) /\
    (uSpec = M.empty _ -> uImp = M.empty _) /\
    M.union uSpec (theta oImp) = theta (M.union uImp oImp).

  Hypothesis HsubstepRuleMap:
    forall oImp uImp rule csImp,
      reachable oImp imp ->
      Substep imp oImp uImp (Rle (Some rule)) csImp ->
      exists uSpec,
        Substep spec (theta oImp) uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
        ConsistentUpdate oImp (theta oImp) uImp uSpec.
  
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
        ConsistentUpdate oImp (theta oImp) uImp uSpec.

  Definition mapUnitLabel o ul :=
    match ul with
    | Rle (Some r) => Rle (ruleMap o r)
    | Rle None => Rle None
    | Meth (Some dm) => Meth (liftP dm)
    | Meth None => Meth None
    end.

  Lemma substepMap:
    forall oi ui uli csi,
      reachable oi imp ->
      Substep imp oi ui uli csi ->
      exists us,
        Substep spec (theta oi) us (mapUnitLabel oi uli) (liftToMap1 p csi) /\
        ConsistentUpdate oi (theta oi) ui us.
  Proof.
    intros; destruct uli as [[r|]|[dm|]].

    - apply HsubstepRuleMap; auto.
    - inv H0; exists (M.empty _); split.
      + apply EmptyRule.
      + unfold ConsistentUpdate; repeat split; auto.
    - apply HsubstepMethMap; auto.
    - inv H0; exists (M.empty _); split.
      + apply EmptyMeth.
      + unfold ConsistentUpdate; repeat split; auto.
  Qed.

  Record SubstepRel oImp :=
    { uImp: UpdatesT;
      ulImp: UnitLabel;
      csImp: MethsT;
      HssImp: Substep imp oImp uImp ulImp csImp;
      uSpec: UpdatesT;
      HssSpec: Substep spec (theta oImp) uSpec
                       (mapUnitLabel oImp ulImp) (liftToMap1 p csImp);
      Hcu: ConsistentUpdate oImp (theta oImp) uImp uSpec
    }.

  Definition toSubstepRecImp {oImp} (sr: SubstepRel oImp) :=
    {| upd := uImp sr;
       unitAnnot := ulImp sr;
       cms := csImp sr;
       substep := HssImp sr
    |}.

  Definition toSubstepRecSpec {oImp} (sr: SubstepRel oImp) :=
    {| upd := uSpec sr;
       unitAnnot := mapUnitLabel oImp (ulImp sr);
       cms := liftToMap1 p (csImp sr);
       substep := HssSpec sr
    |}.

  Inductive SubstepRels {oImp}: list (SubstepRel oImp) -> Prop :=
  | SubstepMapNil: SubstepRels nil
  | SubstepMapCons:
      forall srs sr,
        SubstepRels srs ->
        (forall sr', In sr' srs -> canCombine (toSubstepRecImp sr)
                                              (toSubstepRecImp sr')) ->
        SubstepRels (sr :: srs).

  Hypothesis HcanCombine:
    forall oi ui1 ui2 uli1 uli2 csi1 csi2,
      reachable oi imp ->
      Substep imp oi ui1 uli1 csi1 ->
      Substep imp oi ui2 uli2 csi2 ->
      CanCombineUL ui1 ui2 (getLabel uli1 csi1) (getLabel uli2 csi2) ->
      forall us1 us2 css1 css2,
        Substep spec (theta oi) us1 (mapUnitLabel oi uli1) css1 ->
        Substep spec (theta oi) us2 (mapUnitLabel oi uli2) css2 ->
        CanCombineUL us1 us2
                     (getLabel (mapUnitLabel oi uli1) css1)
                     (getLabel (mapUnitLabel oi uli2) css2).

  Lemma substeps_substepRels_imp:
    forall {oImp} (Hreach: reachable oImp imp)
           (ss: Substeps imp oImp) (Hcomb: substepsComb ss),
    exists (srs: list (SubstepRel oImp)),
      map toSubstepRecImp srs = ss /\ SubstepRels srs.
  Proof.
    induction ss; simpl; intros; [exists nil; split; auto; constructor|].
    inv Hcomb; specialize (IHss H1).
    destruct IHss as [psrs ?]; dest.
    destruct a as [su sul scs Hss].
    destruct (substepMap Hreach Hss) as [sus ?]; dest.
    exists ({| HssImp := Hss; HssSpec := H3; Hcu:= H4 |} :: psrs); split.
    - simpl; f_equal; auto.
    - constructor; auto.
      unfold toSubstepRecImp; simpl.
      clear -H2 H.
      intros; apply in_map with (f:= toSubstepRecImp) in H0.
      rewrite H in H0; auto.
  Qed.

  Lemma substepRels_canCombine:
    forall {oi} (Hreach: reachable oi imp)
           (srs: list (SubstepRel oi))
           sui suli scsi sus Hssi Hsss
           (Hcombi : forall sr' : SubstepRel oi,
               In sr' srs ->
               canCombine {| upd := sui; unitAnnot := suli; cms := scsi; substep := Hssi |}
                          {| upd := uImp sr'; unitAnnot := ulImp sr'; cms := csImp sr';
                             substep := HssImp sr' |}),
    forall s': SubstepRec spec (theta oi),
      In s' (map toSubstepRecSpec srs) ->
      canCombine
        {| upd := sus;
           unitAnnot := mapUnitLabel oi suli;
           cms := liftToMap1 p scsi;
           substep := Hsss |} s'.
  Proof.
    intros.
    apply in_map_iff in H.
    destruct H as [nsr ?]; dest; subst.
    specialize (Hcombi _ H0); clear H0.
    destruct nsr as [nui nuli ncsi Hnssi nus ncss Hnsss]; simpl in *.
    unfold toSubstepRecSpec; simpl.

    apply canCombine_CanCombineUL.
    apply canCombine_CanCombineUL in Hcombi.
    eapply HcanCombine; eauto.
  Qed.

  Lemma substepRels_substeps_spec:
    forall {oi} (Hreach: reachable oi imp)
           (srs: list (SubstepRel oi)),
      SubstepRels srs ->
      exists (ss: Substeps spec (theta oi)),
        map toSubstepRecSpec srs = ss /\ substepsComb ss.
  Proof.
    induction srs; simpl; intros; [exists nil; split; auto; constructor|].
    inv H; specialize (IHsrs H2).
    destruct IHsrs as [pss ?]; dest.
    destruct a as [sui suli scsi Hssi sus Hsss].
    exists ({| substep := Hsss |} :: pss); split.
    - simpl; f_equal; auto.
    - constructor; auto.
      subst; unfold toSubstepRecImp in H3; simpl in H3.

      clear -H3 Hreach HcanCombine.
      eapply substepRels_canCombine; eauto.
  Qed.

  Lemma liftPLabel_mergeLabel:
    forall o l1 l2,
      CanCombineLabel l1 l2 ->
      liftPLabel (liftToMap1 p) ruleMap o (mergeLabel l1 l2) =
      mergeLabel (liftPLabel (liftToMap1 p) ruleMap o l1)
                 (liftPLabel (liftToMap1 p) ruleMap o l2).
  Proof.
    intros; destruct l1 as [a1 d1 c1], l2 as [a2 d2 c2]; simpl in *; f_equal.

    - destruct a1 as [[|]|], a2 as [[|]|]; reflexivity.
    - inv H; dest; simpl in *.
      apply liftToMap1_union; auto.
    - inv H; dest; simpl in *.
      apply liftToMap1_union; auto.
  Qed.

  Lemma liftPLabel_substepRels:
    forall {oi} (srs: list (SubstepRel oi)),
      SubstepRels srs ->
      liftPLabel (liftToMap1 p) ruleMap oi (foldSSLabel (map toSubstepRecImp srs)) =
      foldSSLabel (map toSubstepRecSpec srs).
  Proof.
    induction srs; simpl; intros; [reflexivity|].
    inv H. specialize (IHsrs H2).
    rewrite <-IHsrs; clear IHsrs H2.
    unfold addLabelLeft; rewrite liftPLabel_mergeLabel.
    f_equal.
    - destruct a as [ui uli csi Hssi us Hsss Hcuis].
      unfold toSubstepRecImp, toSubstepRecSpec in *; simpl in *.
      unfold getSLabel, getLabel; f_equal; simpl; auto.
      + destruct uli as [[|]|[|]]; auto.
      + unfold mapUnitLabel, liftP.
        destruct uli as [[|]|[|]]; auto.
        destruct a as [an ab]; simpl.
        rewrite liftToMap1AddOne.
        destruct (p an ab); auto.
      
    - assert (forall ss: SubstepRec imp oi,
                 In ss (map toSubstepRecImp srs) -> canCombine (toSubstepRecImp a) ss).
      { intros; apply in_map_iff in H; dest; subst; auto. }
      clear H3.
      apply canCombine_consistent_1 in H; clear -H.
      generalize dependent (foldSSLabel (map toSubstepRecImp srs)); intros.
      inv H; dest; clear H0.
      repeat split; auto.
      + destruct a; simpl in *.
        destruct ulImp0 as [|[|]]; auto.
        destruct a as [an ab]; simpl in *.
        destruct (annot l); auto.
      + destruct a; simpl in *.
        destruct ulImp0 as [|[|]]; auto.
  Qed.

  Lemma consistentUpdate_update_spec:
    forall (oi os: RegsT) (ui us: UpdatesT),
      ConsistentUpdate oi os ui us ->
      us = M.empty _ \/ exists v, us = M.add specRegName v (M.empty _).
  Proof.
    intros; inv H; dest.
    remember (M.find specRegName us) as uv; destruct uv.

    - right; exists s; meq.
      assert (M.find y (M.union us (theta oi)) =
              M.find y (theta (M.union ui oi))) by (rewrite H1; reflexivity).
      unfold theta in H2; destruct (eta (M.union ui oi)); findeq.

    - left; meq.
      exfalso; M.cmp y specRegName.
      + findeq.
      + assert (M.find y (M.union us (theta oi)) =
                M.find y (theta (M.union ui oi))) by (rewrite H1; reflexivity).
        unfold theta in H2; destruct (eta (M.union ui oi)); findeq.
  Qed.

  Lemma substepRels_consistentUpdate:
    forall oi,
      reachable oi imp ->
      forall (srs: list (SubstepRel oi)),
        SubstepRels srs ->
        ConsistentUpdate oi (theta oi) (foldSSUpds (map toSubstepRecImp srs))
                         (foldSSUpds (map toSubstepRecSpec srs)).
  Proof.
    induction 2; simpl; intros;
      [unfold ConsistentUpdate; repeat split; auto|].

    pose proof (consistentUpdate_update_spec IHSubstepRels).
    unfold ConsistentUpdate in *; dest; repeat split.
    - intros.
      destruct sr as [ui uli csi Hssi us Hsss [? [? ?]]]; simpl in *.
      apply M.union_empty in H6; dest.
      unfold toSubstepRecImp in H1; simpl in H1; subst.
      specialize (e eq_refl); subst.
      mred.
    - intros.
      destruct sr as [ui uli csi Hssi us Hsss [? [? ?]]]; simpl in *.
      apply M.union_empty in H6; dest.
      unfold toSubstepRecImp in H1; simpl in H1; subst.
      specialize (e0 eq_refl); subst.
      mred.
    - destruct H2.
      + rewrite H2 in *.
        specialize (H4 eq_refl); rewrite H4 in *.
        mred.
        clear; destruct sr; simpl in *.
        inv Hcu0; dest; auto.
      + destruct sr as [ui uli csi Hssi us Hsss Hcuis]; simpl in *.
        pose proof (consistentUpdate_update_spec Hcuis).
        unfold toSubstepRecImp in H1; simpl in H1.
        inv Hcuis; dest.
        destruct H6.

        * subst.
          specialize (H8 eq_refl); subst.
          mred.
        * exfalso.
          pose proof (substepRels_canCombine (sui:= ui) (Hssi:= Hssi) H srs Hsss H1).
          apply canCombine_consistent_1 in H10.
          dest; subst.
          rewrite H2 in H10; clear -H10.
          inv H10; dest; clear -H.
          specialize (H specRegName); destruct H; findeq.
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

  Lemma substepRels_wellHidden:
    forall o,
      reachable o imp ->
      forall (srs: list (SubstepRel o)),
        SubstepRels srs ->
        wellHidden imp (hide (foldSSLabel (map toSubstepRecImp srs))) ->
        wellHidden spec (hide (foldSSLabel (map toSubstepRecSpec srs))).
  Proof.
    intros.
    pose proof (liftPLabel_wellHidden o H1).
    rewrite liftPLabel_hide in H2; auto.
    - rewrite liftPLabel_substepRels in H2; auto.
    - unfold M.KeysSubset; apply staticDynDefsSubsteps.
    - unfold M.KeysSubset; apply staticDynCallsSubsteps; auto.
  Qed.

  Theorem decompositionOne:
    traceRefines (liftToMap1 p) imp spec.
  Proof.
    apply stepRefinement with (theta:= theta) (ruleMap:= ruleMap); auto.
    intros.

    inv H0.
    apply substeps_substepRels_imp in HSubsteps; auto.
    destruct HSubsteps as [srs ?]; dest.
    pose proof (substepRels_consistentUpdate H H1).
    pose proof (substepRels_substeps_spec H H1).
    destruct H3 as [sss ?]; dest.
    exists (foldSSUpds sss); split.

    - rewrite liftPLabel_hide; auto.
      + subst; rewrite liftPLabel_substepRels; auto.
        constructor; auto.
        apply substepRels_wellHidden; auto.
      + unfold M.KeysSubset; apply staticDynDefsSubsteps.
      + unfold M.KeysSubset; apply staticDynCallsSubsteps; auto.

    - subst; unfold ConsistentUpdate in H2; dest; auto.
  Qed.
      
End Decomposition.

