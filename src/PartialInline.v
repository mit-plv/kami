Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq.
Require Import Syntax Semantics SemFacts Equiv Inline InlineFacts_1 InlineFacts_2 Tactics.
Require Import Refinement.

Lemma filterDm_filterDms_singleton:
  forall dms s, filterDm dms s = filterDms dms [s].
Proof.
  induction dms; simpl; intros; auto.
  remember (string_eq s (attrName a)) as sa; destruct sa.
  - apply string_eq_dec_eq in Heqsa; subst.
    destruct (string_dec _ _); [|elim n; reflexivity].
    simpl; auto.
  - apply string_eq_dec_neq in Heqsa.
    destruct (string_dec _ _); [elim Heqsa; auto|].
    simpl; f_equal; auto.
Qed.

(* Partial inlining interfaces *)
Section Partial.
  Variable m: Modules.

  Variable dm: DefMethT. (* a method to be inlined *)
  Hypotheses (Hdm: In dm (getDefsBodies m))
             (* (HnoCallDm: noCallDm dm dm = true) *)
             (HnoDupMeths: NoDup (namesOf (getDefsBodies m))).
  Variable r: Attribute (Action Void). (* a rule calling dm *)
  Hypothesis Hrule: In r (getRules m).

  Lemma inlineDmToRule_substepsInd_intact:
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

  Lemma inlineDmToRule_substepsInd_sub_1:
    forall o u ds cs su scs s l,
      l = {| annot := None; defs:= ds; calls := cs |} ->
      SubstepsInd m o u l ->
      M.Disj su u -> M.Disj scs cs ->
      M.find (elt:=sigT SignT) (attrName dm) scs = Some s ->
      M.find (elt:=sigT SignT) (attrName dm) ds = Some s ->
      Substep m o su (Rle (Some (attrName r))) scs ->
      SubstepsInd
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m)) (getDefsBodies m)) o (M.union u su)
        {| annot := Some (Some (attrName r)); defs := ds; calls := M.union scs cs |}.
  Proof.
    induction 2; simpl; intros; [exfalso; inv H; mred|].
    admit.
  Qed.

  Lemma inlineDmToRule_substepsInd_sub_2:
    forall o u ds cs su scs s l,
      l = {| annot := Some (Some (attrName r)); defs := ds; calls := cs |} ->
      SubstepsInd m o u l ->
      M.find (elt:=sigT SignT) (attrName dm) cs = Some s ->
      Substep m o su (Meth (Some (attrName dm :: s)%struct)) scs ->
      M.Disj su u -> M.Disj scs cs ->
      ~ M.In (elt:=sigT SignT) (attrName dm) ds ->
      SubstepsInd
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm else newr)
                (getRules m)) (getDefsBodies m)) o (M.union u su)
        {| annot := Some (Some (attrName r));
           defs := M.union (M.add (attrName dm) s (M.empty (sigT SignT))) ds;
           calls := M.union scs cs |}.
  Proof.
    induction 2; simpl; intros; [exfalso; inv H; mred|].
    admit.
  Qed.

  Lemma inlineDmToRule_substepsInd:
    forall o u l,
      SubstepsInd m o u l ->
      M.find (attrName dm) (calls l) = None \/
      M.find (attrName dm) (defs l) = M.find (attrName dm) (calls l) ->
      SubstepsInd
        (Mod (getRegInits m)
             (map
                (fun newr =>
                   if string_dec (attrName r) (attrName newr)
                   then inlineDmToRule newr dm
                   else newr) (getRules m)) (getDefsBodies m)) o u l.
  Proof.
    intros.
    assert ((annot l = Some (Some (attrName r)) /\ M.find (attrName dm) (calls l) <> None) \/
            ~ (annot l = Some (Some (attrName r)) /\ M.find (attrName dm) (calls l) <> None)).
    { clear; destruct l as [a d c]; simpl.
      destruct a; [|right; intro Hx; dest; discriminate].
      destruct o; [|right; intro Hx; dest; discriminate].
      destruct (string_dec s (attrName r));
        [subst|right; intro Hx; dest; inv H; elim n; reflexivity].
      destruct (M.find (attrName dm) c).
      { left; split; [auto|discriminate]. }
      { right; intro Hx; dest; elim H0; reflexivity. }
    }

    destruct H1; [|apply inlineDmToRule_substepsInd_intact; auto].

    dest; destruct H0; [elim H2; auto|].
    remember (M.find (attrName dm) (calls l)) as odml; destruct odml; [|elim H2; reflexivity].
    apply eq_sym in Heqodml; clear H2.

    induction H; [constructor|subst].

    destruct sul as [or|odm].

    - destruct l as [ann ds cs]; simpl in *.
      assert (or = Some (attrName r)) by (destruct ann; inv H1; auto).
      subst; clear H1.
      inv H3; dest; simpl in *.
      destruct ann; [inv H4|clear H4].

      clear IHSubstepsInd.

      remember (M.find (attrName dm) scs) as ods; destruct ods.

      + mred; eapply inlineDmToRule_substepsInd_sub_1; eauto.

      + mred.
        econstructor.
        * apply inlineDmToRule_substepsInd_intact.
          { eassumption. }
          { simpl; intro Hx; dest; inv H4. }
        * inv H2; eapply SingleRule.
          { simpl.
            apply in_map with (f:= fun newr =>
                                     if string_dec (attrName r) (attrName newr)
                                     then inlineDmToRule newr dm
                                     else newr) in HInRules.
            simpl in HInRules.
            destruct (string_dec (attrName r) (attrName r)); [|elim n; reflexivity].
            unfold inlineDmToRule in HInRules; simpl in HInRules.
            eauto.
          }
          { simpl; destruct dm as [dmn dmb].
            eapply inlineDm_SemAction_intact; eauto.
          }
        * repeat split; auto.
        * reflexivity.
        * reflexivity.

    - destruct l as [ann ds cs]; simpl in *; subst.
      assert ((odm = Some ((attrName dm) :: s)%struct /\ M.find (attrName dm) cs = Some s) \/
              ~ (odm = Some ((attrName dm) :: s)%struct /\ M.find (attrName dm) cs = Some s)).
      { destruct odm; [|right; intro Hx; dest; discriminate].
        destruct a as [dmn dmb].
        destruct (string_dec (attrName dm) dmn);
          [|right; intro Hx; dest; inv H1; elim n; reflexivity].
        subst.
        rewrite M.find_union, M.find_add_1 in H0; inv H0.
        remember (M.find (attrName dm) cs) as odc; destruct odc;
          [|right; intro Hx; dest; discriminate].
        rewrite M.find_union in Heqodml.
        remember (M.find (attrName dm) scs) as odsc; destruct odsc;
          [inv H3; dest; simpl in *; mcontra|].
        rewrite Heqodml in Heqodc; inv Heqodc.
        left; split; auto.
      }
      destruct H1.

      + dest; subst; simpl in *.
        clear IHSubstepsInd.
        clear Heqodml; mred.
        inv H3; dest; simpl in *.
        eapply inlineDmToRule_substepsInd_sub_2; eauto.

      + remember (M.find (attrName dm) cs) as odc; destruct odc.

        * assert (s = s0); subst.
          { mred; remember (M.find (attrName dm) scs) as odsc; destruct odsc.
            { exfalso; inv H3; dest; simpl in *; mcontra. }
            { inv Heqodml; reflexivity. }
          }
          econstructor.
          { apply IHSubstepsInd; auto.
            destruct odm as [|]; auto.
            destruct a as [dmn dmb].
            destruct (string_dec (attrName dm) dmn).
            { exfalso; subst.
              elim H1; clear H1; split; auto.
              repeat f_equal.
              findeq.
            }
            { findeq. }
          }
          { instantiate (1:= scs); instantiate (1:= Meth odm); instantiate (1:= su).
            inv H2.
            { eapply EmptyMeth. }
            { eapply SingleMeth; eauto. }
          }
          { inv H3; dest; simpl in *.
            repeat split; auto.
          }
          { reflexivity. }
          { reflexivity. }

        * clear IHSubstepsInd.
          econstructor.
          { apply inlineDmToRule_substepsInd_intact.
            { eassumption. }
            { simpl; intro Hx; dest.
              rewrite <-Heqodc in H5; elim H5; reflexivity.
            }
          }
          { instantiate (1:= scs); instantiate (1:= Meth odm); instantiate (1:= su).
            inv H2.
            { eapply EmptyMeth. }
            { eapply SingleMeth; eauto. }
          }
          { inv H3; dest; simpl in *.
            repeat split; auto.
          }
          { reflexivity. }
          { reflexivity. }
            
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
    unfold wellHidden; intros.
    dest; split.

    - apply M.KeysDisj_SubList with (d1:= getCalls m); auto.
      unfold getCalls; simpl.
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

    - unfold getDefs; simpl; auto.
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
    intros; inv H; constructor.

    - apply wellHidden_find with (a:= attrName dm) in HWellHidden;
        [|apply in_map; auto].
      apply inlineDmToRule_substepsInd; auto.
      
    - apply inlineDmToRule_wellHidden; auto.
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

  Hypothesis (HnoDupRules: NoDup (namesOf (getRules m))).
  Hypothesis (HnoRuleCalls: forall rule,
                 In rule (getRules m) ->
                 attrName rule <> attrName r ->
                 ~ In (attrName dm) (getCallsA (attrType rule typeUT))).
  Hypothesis (HnoMethCalls: forall meth,
                 In meth (getDefsBodies m) ->
                 ~ In (attrName dm) (getCallsA (projT2 (attrType meth) typeUT tt))).

  Lemma inlineDmToRule_traceRefines_2:
    m <<== (Mod (getRegInits m)
                (map (fun newr =>
                        if string_dec (attrName r) (attrName newr)
                        then inlineDmToRule newr dm
                        else newr) (getRules m))
                (filterDm (getDefsBodies m) (attrName dm))).
  Proof.
    (* rewrite filterDm_filterDms_singleton. *)
    
    apply stepRefinement with (ruleMap:= fun _ s => Some s) (theta:= id); auto.
    intros; exists u; split; auto.

    rewrite idElementwiseId.
    replace (liftPLabel _ _ _ _) with l; [|destruct l as [[[|]|] ? ?]; simpl; f_equal].
    unfold id.

    clear H.
    apply step_consistent; apply step_consistent in H0.

    pose proof (inlineDmToRule_stepInd _ _ _ H0).

    admit.
    
  Qed.

End Partial.

