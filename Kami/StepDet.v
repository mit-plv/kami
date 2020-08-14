Require Import Bool List String Lia.
Require Import Lib.CommonTactics Lib.Struct Lib.Reflection Lib.FMap Lib.Struct Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.

Set Implicit Arguments.

Set Asymmetric Patterns.

Section NoCalls.
  Fixpoint actionNoCalls {retT} (a: ActionT typeUT retT) :=
    match a with
    | MCall name _ _ cont => false
    | Let_ _ ar cont => actionNoCalls (cont (getUT _))
    | ReadNondet k cont => actionNoCalls (cont (getUT _))
    | ReadReg reg k cont => actionNoCalls (cont (getUT _))
    | WriteReg reg _ e cont => actionNoCalls cont
    | IfElse ce _ ta fa cont =>
      (actionNoCalls ta) && (actionNoCalls fa) && (actionNoCalls (cont tt))
    | Assert_ ae cont => actionNoCalls cont
    | Displ ls cont => actionNoCalls cont
    | Return e => true
    end.

  Definition dmNoCalls (dm: DefMethT) :=
    actionNoCalls (projT2 (attrType dm) typeUT tt).

  Lemma actionNoCalls_SemAction:
    forall {retT} (aU: ActionT type retT) (aT: ActionT typeUT retT),
      ActionEquiv aU aT ->
      actionNoCalls aT = true ->
      forall o u cs ret,
        SemAction o aU u cs ret ->
        cs = M.empty _.
  Proof.
    induction 1; simpl; intros; try (inv H2; destruct_existT; eauto; fail).
    - inv H1; destruct_existT; eauto.
    - do 2 (apply andb_true_iff in H3; dest).
      inv H4; destruct_existT.
      + apply IHActionEquiv1 in HAction; auto; subst.
        eapply H2 in HSemAction; eauto.
      + apply IHActionEquiv2 in HAction; auto; subst.
        eapply H2 in HSemAction; eauto.
    - inv H1; destruct_existT; eauto.
    - inv H0; auto.
  Qed.

  Corollary dmNoCalls_Substep:
    forall f,
      MethEquiv type typeUT f ->
      dmNoCalls f = true ->
      forall o u mcs argV retV,
        SemAction o (projT2 (attrType f) type argV) u mcs retV ->
        mcs = M.empty _.
  Proof.
    intros; eapply actionNoCalls_SemAction; eauto.
  Qed.

  Corollary dmNoCalls_SubstepsInd:
    forall m (Hequiv: ModEquiv type typeUT m)
           (Hdms: Forall (fun dm => dmNoCalls dm = true) (getDefsBodies m))
           o u l,
      SubstepsInd m o u l ->
      forall ds cs,
        l = {| annot := None; defs := ds; calls := cs |} ->
        cs = M.empty _.
  Proof.
    induction 3; simpl; intros; subst; [inv H; reflexivity|].

    destruct l as [pann pds pcs]; simpl in *; inv H4.
    destruct sul as [|]; destruct pann; try discriminate.
    specialize (IHSubstepsInd _ _ eq_refl); subst.

    inv H0; auto.
    apply dmNoCalls_Substep in HAction; subst; auto.
    - unfold ModEquiv in Hequiv; destruct Hequiv.
      eapply MethsEquiv_in in HIn; eauto.
    - eapply Forall_forall in Hdms; eauto.
  Qed.

End NoCalls.

Section OneDepth.
  Variable m : Modules.
  Hypotheses (Hequiv: ModEquiv type typeUT m)
             (Hdms: Forall (fun dm => dmNoCalls dm = true) (getDefsBodies m))
             (Hedms: getExtDefs m = nil).

  Section GivenOldRegs.
    Variable o : RegsT.

    (* Note that [SubstepMeths] doesn't need to collect labels 
     * since by an assumption there're no calls in methods! 
     *)
    Inductive SubstepMeths : list (string * {x : SignatureT & SignT x}) -> UpdatesT -> Prop :=
    | SmsNil: SubstepMeths nil (M.empty _)
    | SmsCons:
        forall mn mar u cs,
          Substep m o u (Meth (Some (mn :: mar)%struct)) cs ->
          forall pms pu,
            SubstepMeths pms pu ->
            M.Disj u pu ->
            SubstepMeths ((mn, mar) :: pms) (M.union u pu).

    Inductive StepDet : UpdatesT -> LabelT -> Prop :=
    | SbEmptyRule:
        StepDet (M.empty _) {| annot := Some None; defs := M.empty _; calls := M.empty _ |}
    | SbEmptyMeth:
        StepDet (M.empty _) {| annot := None; defs := M.empty _; calls := M.empty _ |}
    | SbRule:
        forall ru rcs rn,
          Substep m o ru (Rle (Some rn)) rcs ->
          forall mu,
            SubstepMeths (M.elements (M.restrict rcs (getDefs m))) mu ->
            M.Disj ru mu ->
            forall u cs,
              u = M.union ru mu ->
              cs = M.complement rcs (getDefs m) ->
              StepDet u {| annot := Some (Some rn);
                           defs := M.empty _;
                           calls := cs |}.

  End GivenOldRegs.

  (** [StepDet] implies [Step] *)
  Section FromDet.

    Lemma substepMeths_implies_substepsInd:
      forall o mu meths,
        SubstepMeths o meths mu ->
        forall ms,
          M.KeysSubset ms (getDefs m) ->
          meths = M.elements ms ->
          SubstepsInd m o mu {| annot := None;
                                defs := ms;
                                calls := M.empty _ |}.
    Proof.
      induction 1; simpl; intros.
      - apply eq_sym, M.F.P.elements_Empty in H0.
        apply M.empty_canon in H0; subst.
        constructor.
      - assert (cs = M.empty _).
        { inv H; inv Hsig.
          eapply dmNoCalls_Substep; eauto.
          { unfold ModEquiv in Hequiv; destruct Hequiv.
            eapply MethsEquiv_in in H4; eauto.
          }
          { eapply Forall_forall in Hdms; eauto. }
        }
        subst.
        apply elements_cons in H3; dest; subst.

        econstructor.
        + eapply IHSubstepMeths; try reflexivity.
          eapply M.KeysSubset_add_1; eauto.
        + eassumption.
        + unfold CanCombineUUL; cbn; repeat split; [mdisj|mdisj|findeq].
        + meq.
        + reflexivity.
    Qed.

    Theorem stepDet_implies_step:
      forall o u l, StepDet o u l -> Step m o u l.
    Proof.
      intros; inv H; try (apply step_empty; auto).

      - assert (Hl: {| annot := Some (Some rn);
                       defs := M.empty _;
                       calls := M.complement rcs (getDefs m) |} =
                    hide {| annot := Some (Some rn);
                            defs := M.restrict rcs (getDefs m);
                            calls := rcs |}).
        { unfold hide; cbn; f_equal.
          { (* TODO: better to have a lemma in FMap.v *)
            M.ext y.
            rewrite M.subtractKV_find.
            rewrite M.restrict_find.
            destruct (in_dec M.F.P.F.eq_dec y (getDefs m)); auto.
            destruct (M.find y rcs); auto.
            destruct (signIsEq s s); auto.
            elim n; auto.
          }
          { (* TODO: better to have a lemma in FMap.v *)
            M.ext y.
            rewrite M.subtractKV_find, M.complement_find, M.restrict_find.
            destruct (in_dec M.F.P.F.eq_dec y (getDefs m)).
            { destruct (M.find y rcs); auto.
              destruct (signIsEq s s); auto.
              elim n; auto.
            }
            { destruct (M.find y rcs); auto. }
          }
        }
        rewrite Hl.

        apply step_consistent.
        constructor.
        + econstructor 2 with
          (u:= mu) (l:= {| annot := None;
                           defs := M.restrict rcs (getDefs m);
                           calls := M.empty _ |}); try eassumption.
          * eapply substepMeths_implies_substepsInd; eauto.
            (* TODO: better to have a lemma in FMap.v *)
            unfold M.KeysSubset; intros.
            apply M.F.P.F.in_find_iff in H.
            rewrite M.restrict_find in H.
            destruct (in_dec M.F.P.F.eq_dec k (getDefs m)); auto.
            elim H; auto.
          * unfold CanCombineUUL; cbn; auto.
          * apply M.union_comm; auto.
          * unfold mergeLabel; cbn.
            f_equal; meq.
        + rewrite <-Hl.
          unfold wellHidden; cbn; split.
          * apply M.KeysDisj_empty.
          * (* TODO: better to have a lemma in FMap.v *)
            unfold M.KeysDisj; intros.
            findeq.
            rewrite M.complement_find.
            destruct (in_dec _ k (getDefs m)); auto.
            elim n; auto.
    Qed.

  End FromDet.

  (** [Step] implies [StepDet] *)
  Section ToDet.

    Lemma getExtDefs_nil_step_ds:
      forall o u a ds cs,
        Step m o u {| annot := a; defs := ds; calls := cs |} ->
        ds = M.empty _.
    Proof.
      intros.
      apply step_defs_extDefs_in in H; auto.
      rewrite Hedms in H; simpl in H.
      apply M.KeysSubset_nil; auto.
    Qed.

    Lemma getExtDefs_nil_substepsInd_cs:
      forall o u l,
        SubstepsInd m o u l ->
        forall a ds cs,
          l = {| annot := a; defs := ds; calls := cs |} ->
          (a = Some None \/ a = None) ->
          cs = M.empty _.
    Proof.
      induction 1; simpl; intros.
      - inv H; auto.
      - subst.
        destruct l as [pa pds pcs].
        assert (pa = Some None \/ pa = None).
        { destruct pa as [orn|]; auto.
          destruct orn as [rn|]; auto.
          inv H4.
          destruct H5.
          { destruct sul as [|]; [|inv H2].
            inv H1; dest; simpl in *; elim H4.
          }
          { destruct sul as [|]; inv H2. }
        }
        specialize (IHSubstepsInd _ _ _ eq_refl H2); clear H2.
        dest; subst.

        inv H0.
        + inv H4; auto.
        + inv H4; auto.
        + inv H4; dest.
          destruct H5, pa; discriminate.
        + eapply dmNoCalls_Substep in HAction; subst.
          { inv H4; auto. }
          { unfold ModEquiv in Hequiv; destruct Hequiv.
            eapply MethsEquiv_in in H2; eauto.
          }
          { eapply Forall_forall in Hdms; eauto. }
    Qed.

    Lemma substepsInd_update_empty:
      forall o u l,
        SubstepsInd m o u l ->
        forall a,
          l = {| annot := a; defs := M.empty _; calls := M.empty _ |} ->
          (a = Some None \/ a = None) ->
          u = M.empty _.
    Proof.
      induction 1; simpl; intros; auto.

      subst.
      destruct l as [pa ds cs].
      assert (pa = Some None \/ pa = None).
      { destruct pa as [orn|]; auto.
        destruct orn as [rn|]; auto.
        inv H4.
        destruct H5.
        { destruct sul as [|]; [|inv H2].
          inv H1; dest; simpl in *; elim H4.
        }
        { destruct sul as [|]; inv H2. }
      }
        
      inv H0.
      - inv H4.
        mred; subst.
        eapply IHSubstepsInd; eauto.
      - inv H4.
        mred; subst.
        eapply IHSubstepsInd; eauto.
      - inv H4.
        destruct H5, pa; discriminate.
      - simpl in H4.
        exfalso; clear -H4.
        match goal with
        | [H: {| defs := ?m |} = _ |- _] =>
          assert (m <> M.empty _)
        end.
        { intro Hx.
          apply M.union_empty in Hx; dest.
          eapply M.add_empty_neq; eauto.
        }
        remember (M.union _ _) as m; clear Heqm.
        inv H4; auto.
    Qed.
    
    Lemma getExtDefs_nil_step_empty:
      forall o u a cs,
        Step m o u {| annot := a; defs := []%fmap; calls := cs |} ->
        (a = Some None \/ a = None) ->
        u = M.empty _ /\ cs = M.empty _.
    Proof.
      intros.
      apply step_consistent in H.
      remember {| annot := a; defs := M.empty _; calls := cs |} as l.
      inv H.
      destruct l0 as [a0 ds0 cs0].
      unfold hide in H2; simpl in H2; inv H2.

      pose proof (getExtDefs_nil_substepsInd_cs HSubSteps eq_refl H0); subst.
      rewrite M.subtractKV_empty_2 in H3; subst.
      split; auto.
      eapply substepsInd_update_empty; eauto.
    Qed.

    Lemma substepMeths_pull_hd:
      forall o ms1 ms2 m u,
        SubstepMeths o (m :: (ms1 ++ ms2)) u ->
        SubstepMeths o (ms1 ++ m :: ms2) u.
    Proof.
      induction ms1; simpl; intros; auto.
      inv H.
      inv H3.
      assert (SubstepMeths o ((mn, mar) :: (ms1 ++ ms2)) (M.union u0 pu0))
        by (econstructor; eauto).
      specialize (IHms1 _ _ _ H).
      replace (M.union u0 (M.union u pu0)) with (M.union u (M.union u0 pu0)) by meq.
      econstructor; eauto.
    Qed.
    
    Lemma substepsInd_implies_substepMeths:
      forall o u l,
        SubstepsInd m o u l ->
        forall ds,
          l = {| annot := None; defs := ds; calls := M.empty _ |} ->
          SubstepMeths o (M.elements ds) u.
    Proof.
      induction 1; simpl; intros; subst; [inv H; constructor|].

      destruct l as [pann pds pcs]; simpl in *.
      destruct pann; [inv H4; destruct sul; discriminate|].
      destruct sul as [|om]; [inv H4|].

      eapply dmNoCalls_SubstepsInd in H; eauto; subst.
      specialize (IHSubstepsInd _ eq_refl).

      destruct om as [[mn mar]|]; [|inv H4; inv H0; mred].
      inv H4; mred; subst.

      replace (M.union (M.add mn mar (M.empty _)) pds)
      with (M.add mn mar pds) by meq.

      assert (SubstepMeths o ((mn, mar) :: (M.elements pds)) (M.union su u)).
      { econstructor; eauto.
        inv H1; auto.
      }

      assert (M.F.P.Add mn mar pds (M.add mn mar pds)) by (unfold M.F.P.Add; auto).
      apply M.F.elements_Add in H2; [|inv H1; simpl in *; dest; auto].

      replace (M.Map.elements (M.add mn mar pds))
      with ((M.F.elements_lt (mn, mar) pds)
              ++ (mn, mar) :: M.F.elements_ge (mn, mar) pds).
      - apply substepMeths_pull_hd.
        rewrite <-M.F.elements_split.
        replace (M.union u su) with (M.union su u) by (inv H1; dest; meq).
        auto.
      - apply eq_sym, M.eq_leibniz_list.
        apply eqlistA_eqke_eq_compat; auto.
    Qed.

    Theorem step_implies_stepDet:
      forall o u l ,
        Step m o u l ->
        StepDet o u l.
    Proof.
      intros.
      destruct l as [ann ds cs].
      pose proof (getExtDefs_nil_step_ds H); subst.

      destruct ann as [orn|];
        [|pose proof (getExtDefs_nil_step_empty H (or_intror eq_refl)); dest; subst;
          econstructor].
      destruct orn as [rn|];
        [|pose proof (getExtDefs_nil_step_empty H (or_introl eq_refl)); dest; subst;
          econstructor].

      assert (M.restrict cs (getDefs m) = M.empty _).
      { pose proof (step_calls_extCalls_in Hequiv H); simpl in H0.
        eapply M.restrict_DisjList; eauto.
        apply extCalls_defs_disj.
      }
        
      remember {| annot := Some (Some rn); defs := M.empty _; calls := cs |}.
      apply step_consistent in H.
      inv H.

      assert (exists ms,
                 l0 = {| annot := Some (Some rn);
                         defs := ms;
                         calls := M.union ms cs |}).
      { clear -H2.
        destruct l0 as [ann0 ds0 cs0]; unfold hide in H2; simpl in *.
        inv H2.
        exists ds0; f_equal.

        M.ext y.
        apply M.Equal_val with (k:= y) in H1.
        rewrite M.subtractKV_find in H1.
        rewrite M.find_union, M.subtractKV_find.
        destruct (M.find y ds0), (M.find y cs0); auto.
        destruct (signIsEq s s0); subst; auto.
        inv H1.
      }
      
      dest; subst.
      rewrite H2; clear H2 HWellHidden.
      apply substepsInd_rule_split with (or := Some rn) in HSubSteps; [|subst; reflexivity].
      dest; subst.

      destruct x3 as [mann mds mcs]; simpl in *.
      destruct mann; [inv H2; dest; inv H5|].
      pose proof (dmNoCalls_SubstepsInd Hequiv Hdms H1 eq_refl); subst; mred.
      inv H4.

      eapply SbRule.
      - eassumption.
      - instantiate (1:= x2).
        pose proof (substepsInd_defs_in H1); simpl in H3.
        rewrite M.restrict_union; rewrite H0; mred.
        rewrite M.restrict_KeysSubset by assumption.
        eapply substepsInd_implies_substepMeths; eauto.
      - inv H2; auto.
      - inv H2; apply M.union_comm; auto.
      - rewrite M.complement_union.
        pose proof (substepsInd_defs_in H1); simpl in H3.
        rewrite M.complement_KeysSubset by assumption; mred.
        rewrite M.restrict_complement_union with (d:= getDefs m) at 1.
        rewrite H0; mred.
    Qed.

  End ToDet.

End OneDepth.

Lemma substepMeths_inv:
  forall m o ms u,
    SubstepMeths m o ms u ->
    match ms with
    | nil => u = M.empty _
    | (mn, mar) :: pms =>
      exists mu pu cs, Substep m o mu (Meth (Some (mn :: mar)%struct)) cs /\
                       SubstepMeths m o pms pu /\
                       u = M.union mu pu
    end.
Proof.
  destruct 1; simpl; intros; auto.
  do 3 eexists; split; eauto.
Qed.

Definition dummyDefMeth: {x: SignatureT & MethodT x} :=
  existT (fun x => MethodT x) {| arg := Void; ret := Void |}
         (fun ty _ => Return (Const ty (getDefaultConst Void))).

Fixpoint getMeth_default (mn: string) (ms: list DefMethT): {x: SignatureT & MethodT x} :=
  match ms with
  | nil => dummyDefMeth
  | (mn' :: meth)%struct :: ms' =>
    if string_dec mn mn' then meth else getMeth_default mn ms'
  end.

Lemma getMeth_default_In:
  forall ms mn msig mb,
    In mn (Struct.namesOf ms) ->
    getMeth_default mn ms = existT (fun x : SignatureT => MethodT x) msig mb ->
    In (mn :: (existT (fun x : SignatureT => MethodT x) msig mb))%struct ms.
Proof.
  induction ms; simpl; intros; auto.
  destruct a as [an ab].
  destruct (string_dec mn an); subst; auto.
  right; apply IHms; auto.
  destruct H; auto.
  elim n; auto.
Qed.

Lemma getMeth_default_NoDup_In:
  forall ms (Hms: NoDup (Struct.namesOf ms)) mn mb,
    In (mn :: mb)%struct ms ->
    forall mb',
      getMeth_default mn ms = existT (fun x : SignatureT => MethodT x) (projT1 mb) mb' ->
      projT2 mb = mb'.
Proof.
  intros.
  apply getMeth_default_In in H0.
  - apply in_NoDup_attr with (a1:= (mn :: mb)%struct) in H0; auto.
    apply attribute_inv in H0; dest.
    destruct mb; simpl in *.
    destruct_existT; reflexivity.
  - apply in_map with (f:= @attrName _) in H; auto.
Qed.
  
Lemma substep_meth_inv:
  forall m (Hdefs: NoDup (getDefs m))
         o u mn (mar: {x : SignatureT & SignT x}) cs,
    Substep m o u (Meth (Some (mn :: mar)%struct)) cs ->
    forall (Haeq: projT1 mar = projT1 (getMeth_default mn (getDefsBodies m))),
      SemAction o (projT2 (getMeth_default mn (getDefsBodies m)) type
                          (match Haeq with
                           | eq_refl => fst (projT2 mar)
                           end))
                u cs (match Haeq with
                      | eq_refl => snd (projT2 mar)
                      end).
Proof.
  intros; inv H; inv Hsig.
  simpl in *.
  destruct f as [fsig fb]; simpl in *.
  remember (getMeth_default fsig (getDefsBodies m)) as f'.
  destruct f' as [fsig' fb']; simpl in *; subst.
  eapply getMeth_default_NoDup_In in HIn; eauto; subst; auto.
Qed.

