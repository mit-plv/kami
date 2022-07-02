Require Import Bool List String.
Require Import Structures.Equalities FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.ilist Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf Kami.RefinementFacts.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section GivenLabelMap.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).

  Definition liftP meth :=
    match meth with
    | (n :: t)%struct => match p n t with
                         | None => None
                         | Some v => Some (n :: v)%struct
                         end
    end.
  
  Section DecompositionZero.
    Variable imp spec: Modules.

    Section ThetaFunc.
      Variable theta: RegsT -> RegsT.
      Variable ruleMap: RegsT -> string -> option string.
      Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).
      Variable defsImpZero: getDefsBodies imp = nil.
      Variable defsSpecZero: getDefsBodies spec = nil.
    
      Variable substepRuleMap:
        forall oImp uImp rule csImp,
          reachable oImp imp ->
          Substep imp oImp uImp (Rle (Some rule)) csImp ->
          exists uSpec,
            Substep spec (theta oImp) uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
            M.union uSpec (theta oImp) = theta (M.union uImp oImp) .

      Definition ruleMapEmptyZero o u cs (s: Substep imp o u (Rle None) cs):
        exists uSpec,
          Substep spec (theta o) uSpec (Rle None) (liftToMap1 p cs) /\
          M.union uSpec (theta o) = theta (M.union u o).
      Proof.
        refine (ex_intro _ (M.empty _) _);
          abstract (
              inversion s; subst; rewrite liftToMap1_empty;
              constructor;
              [ constructor |
                repeat rewrite M.union_empty_L; intuition]).
      Defined.

      Definition methMapEmptyZero o u cs (s: Substep imp o u (Meth None) cs):
        exists uSpec,
          Substep spec (theta o) uSpec (Meth None) (liftToMap1 p cs) /\
          M.union uSpec (theta o) = theta (M.union u o).
      Proof.
        refine (ex_intro _ (M.empty _) _);
          abstract (
              inversion s; subst; rewrite liftToMap1_empty;
              constructor;
              [ constructor |
                repeat rewrite M.union_empty_L; intuition]).
      Defined.

      Theorem substepMethEmptyZero o u f cs (s: Substep imp o u (Meth f) cs):
        u = M.empty _ /\ cs = M.empty _ /\ f = None.
      Proof.
        inversion s; eauto; exfalso.
        rewrite defsImpZero in HIn.
        intuition.
      Qed.

      Definition substepMethMapZero o u f cs (s: Substep imp o u (Meth (Some f)) cs):
        exists uSpec,
          Substep spec (theta o) uSpec (Meth (liftP f)) (liftToMap1 p cs) /\
          M.union uSpec (theta o) = theta (M.union u o).
      Proof.
        refine (ex_intro _ (M.empty _) _).
        abstract (apply substepMethEmptyZero in s; dest; subst; discriminate).
      Defined.

      Definition xformUnitAnnotZero o rm :=
        match rm with
        | Rle (Some rule) => Rle (ruleMap o rule)
        | Meth (Some meth) => Meth (liftP meth)
        | Rle None => Rle None
        | Meth None => Meth None
        end.

      Definition substepMapZero o u rm cs reachO (s: Substep imp o u rm cs) :=
        match rm return Substep imp o u rm cs ->
                        exists uSpec,
                          Substep spec (theta o) uSpec (xformUnitAnnotZero o rm)
                                  (liftToMap1 p cs) /\
                          M.union uSpec (theta o) = theta (M.union u o) with
        | Rle (Some rule) => fun s => substepRuleMap reachO s
        | Meth (Some meth) => fun s => substepMethMapZero s
        | Rle None => fun s => ruleMapEmptyZero s
        | Meth None => fun s => methMapEmptyZero s
        end s.

      Definition xformLabelZero o l :=
        match l with
        | {| annot := a; defs := dfs; calls := clls |} =>
          {| annot := match a with
                      | Some (Some r) => Some (ruleMap o r)
                      | Some None => Some None
                      | None => None
                      end;
             defs := liftToMap1 p dfs;
             calls := liftToMap1 p clls |}
        end.

      Theorem stepMapZero o (reachO: reachable o imp) u l (s: Step imp o u l):
        exists uSpec,
          Step spec (theta o) uSpec (xformLabelZero o l) /\
          M.union uSpec (theta o) = theta (M.union u o).
      Proof.
        apply step_zero in s; auto; dest.
        destruct l; simpl in *.
        pose proof (substepMapZero reachO H0); dest.
        exists x.
        apply substepZero_imp_step in H1; auto.
        repeat (try constructor; auto).
        rewrite H.
        rewrite liftToMap1_empty.
        unfold xformUnitAnnotZero, getLabel; simpl in *.
        destruct annot; auto.
        destruct o0; auto.
      Qed.

      Lemma rleEmptyZero m o u cs:
        Substep m o u (Rle None) cs -> u = M.empty _ /\ cs = M.empty _.
      Proof.
        clear;
          intros.
        inversion H; intuition.
      Qed.

      Lemma methEmptyZero m o u cs:
        Substep m o u (Meth None) cs -> u = M.empty _ /\ cs = M.empty _.
      Proof.
        clear;
          intros.
        inversion H; intuition.
      Qed.

      Theorem decompositionZero':
        forall s sig, Behavior imp s sig ->
                      exists sigSpec, Behavior spec (theta s) sigSpec /\
                                      equivalentLabelSeq (liftToMap1 p) sig sigSpec.
      Proof.
        intros.
        dependent induction H.
        dependent induction HMultistepBeh; subst.
        - exists nil; rewrite thetaInit; repeat constructor.
        - specialize (IHHMultistepBeh thetaInit defsSpecZero substepRuleMap eq_refl).
          assert(reachO: reachable n imp) by (eexists; econstructor; eauto).
          pose proof (stepMapZero reachO HStep) as [uSpec [stepSpec upd]].
          destruct IHHMultistepBeh as [sigSpec [behSpec eqv]].
          inversion behSpec; subst.
          pose proof (BehaviorIntro (Multi HMultistepBeh0 stepSpec)) as sth.
          rewrite upd in sth.
          exists (xformLabelZero n l :: sigSpec).
          constructor.
          + intuition.
          + constructor.
            * unfold equivalentLabel, xformLabelZero; simpl.
              destruct l; destruct annot; simpl; intuition.
              destruct o; simpl; intuition.
            * intuition.
      Qed.

      Theorem decompositionZero:
        traceRefines (liftToMap1 p) imp spec.
      Proof.
        unfold traceRefines; intros.
        pose proof (decompositionZero' H) as [sigSpec beh].
        exists (theta s1); exists sigSpec.
        intuition.
      Qed.

    End ThetaFunc.

    Section ThetaFuncNoRuleMap.
      Variable theta: RegsT -> RegsT.
      Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).
      Variable defsImpZero: getDefsBodies imp = nil.
      Variable defsSpecZero: getDefsBodies spec = nil.

      Variable substepRuleMap:
        forall oImp uImp rule csImp (Hreach: reachable oImp imp),
          Substep imp oImp uImp (Rle (Some rule)) csImp ->
          exists srule uSpec,
            Substep spec (theta oImp) uSpec (Rle srule) (liftToMap1 p csImp) /\
            M.union uSpec (theta oImp) = theta (M.union uImp oImp).

      Lemma stepMapZero_NoRuleMap:
        forall o (reachO: reachable o imp) u l
               (s: Step imp o u l),
        exists sl uSpec,
          Step spec (theta o) uSpec sl /\
          equivalentLabel (liftToMap1 p) l sl /\
          M.union uSpec (theta o) = theta (M.union u o).
      Proof.
        intros; apply step_zero in s; auto; dest.
        destruct l as [ann ds cs]; simpl in *; subst.

        destruct ann as [[r|]|].

        - pose proof (substepRuleMap reachO H0).
          destruct H as [srule [uSpec ?]]; dest.
          exists {| annot := Some srule;
                    defs := M.empty _;
                    calls := liftToMap1 p cs |}.
          exists uSpec; repeat split.
          + apply substepZero_imp_step in H; auto.
          + auto.

        - inv H0; exists emptyRuleLabel, (M.empty _); repeat split.
          match goal with
          | [ |- Step _ _ _ ?l ] =>
            change l with (getLabel (Rle None) (M.empty _))
          end.
          apply substepZero_imp_step; auto.
          constructor.

        - inv H0; exists emptyMethLabel, (M.empty _); repeat split.
          match goal with
          | [ |- Step _ _ _ ?l ] =>
              change l with (getLabel (Meth None) (M.empty _))
          end.
          apply substepZero_imp_step; auto.
          constructor.
      Qed.

      Lemma multistepMapZero_NoRuleMap:
        forall o u l,
          o = initRegs (getRegInits imp) ->
          Multistep imp o u l ->
          exists ll,
            equivalentLabelSeq (liftToMap1 p) l ll /\
            Multistep spec (initRegs (getRegInits spec)) (theta u) ll.
      Proof.
        induction 2; simpl; intros; repeat subst.

        - eexists; repeat split.
          + instantiate (1:= nil); constructor.
          + constructor; auto.

        - specialize (IHMultistep eq_refl).
          destruct IHMultistep as [pll ?]; dest.
          apply stepMapZero_NoRuleMap in HStep;
            [|eexists; constructor; eauto].
          destruct HStep as [sl [uSpec ?]]; dest.

          exists (sl :: pll).
          repeat split; auto.
          + constructor; auto.
          + rewrite <-H4; constructor; auto.
      Qed.

      Theorem decompositionZero_NoRuleMap:
        traceRefines (liftToMap1 p) imp spec.
      Proof.
        unfold traceRefines; intros.
        inv H.
        apply multistepMapZero_NoRuleMap in HMultistepBeh; auto.
        destruct HMultistepBeh as [ll ?]; dest.
        exists (theta s1), ll.
        split; auto.
        constructor; auto.
      Qed.

    End ThetaFuncNoRuleMap.
    
    Section ThetaRel.
      Variable thetaR: RegsT -> RegsT -> Prop.
      Variable ruleMap: RegsT -> string -> option string.
      Variable thetaInit: thetaR (initRegs (getRegInits imp)) (initRegs (getRegInits spec)).
      Variable defsImpZero: getDefsBodies imp = nil.
      Variable defsSpecZero: getDefsBodies spec = nil.

      Variable substepRuleMap:
        forall oImp uImp rule csImp (Hreach: reachable oImp imp),
          Substep imp oImp uImp (Rle (Some rule)) csImp ->
          forall oSpec,
            thetaR oImp oSpec ->
            exists uSpec,
              Substep spec oSpec uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
              thetaR (M.union uImp oImp) (M.union uSpec oSpec).
      
      Definition xformLabelZeroR l oImp :=
        match l with
        | {| annot := a; defs := dfs; calls := clls |} =>
          {| annot := match a with
                      | Some (Some r) => Some (ruleMap oImp r) 
                      | Some None => Some None
                      | None => None
                      end;
             defs := liftToMap1 p dfs;
             calls := liftToMap1 p clls |}
        end.

      Lemma stepMapZeroR:
        forall o (reachO: reachable o imp) u l (s: Step imp o u l) oSpec,
          thetaR o oSpec ->
          exists uSpec,
            Step spec oSpec uSpec (xformLabelZeroR l o) /\
            thetaR (M.union u o) (M.union uSpec oSpec).
      Proof.
        intros; apply step_zero in s; auto; dest.
        destruct l as [ann ds cs]; simpl in *; subst.

        destruct ann as [[r|]|].

        - pose proof (substepRuleMap reachO H1 H).
          destruct H0 as [uSpec ?]; dest.
          exists uSpec; split.
          + apply substepZero_imp_step in H0; auto.
          + auto.

        - inv H1; exists (M.empty _); split.
          + match goal with
            | [ |- Step _ _ _ ?l ] =>
              change l with (getLabel (Rle None) (M.empty _))
            end.
            apply substepZero_imp_step; auto.
            constructor.
          + mred; eauto.

        - inv H1; exists (M.empty _); split.
          + match goal with
            | [ |- Step _ _ _ ?l ] =>
              change l with (getLabel (Meth None) (M.empty _))
            end.
            apply substepZero_imp_step; auto.
            constructor.
          + mred; eauto.
      Qed.

      Lemma multistepMapZeroR:
        forall o u l,
          o = initRegs (getRegInits imp) ->
          Multistep imp o u l ->
          exists uSpec ll,
            thetaR u uSpec /\
            equivalentLabelSeq (liftToMap1 p) l ll /\
            Multistep spec (initRegs (getRegInits spec)) uSpec ll.
      Proof.
        induction 2; simpl; intros; repeat subst.

        - do 2 eexists; repeat split.
          + instantiate (1:= initRegs (getRegInits spec)); auto.
          + instantiate (1:= nil); constructor.
          + constructor; auto.

        - specialize (IHMultistep eq_refl).
          destruct IHMultistep as [puSpec [pll ?]]; dest.
          apply stepMapZeroR with (oSpec:= puSpec) in HStep; auto;
            [|eexists; constructor; eauto].
          destruct HStep as [uSpec ?]; dest.

          exists (M.union uSpec puSpec), (xformLabelZeroR l n :: pll).
          repeat split; auto.
          + constructor; auto.
            unfold equivalentLabel, xformLabelZero; simpl.
            destruct l; destruct annot; simpl; intuition.
            destruct o; simpl; intuition.
          + constructor; auto.
      Qed.

      Theorem decompositionZeroR:
        traceRefines (liftToMap1 p) imp spec.
      Proof.
        unfold traceRefines; intros.
        inv H.
        apply multistepMapZeroR in HMultistepBeh; auto.
        destruct HMultistepBeh as [uSpec [ll ?]]; dest.
        exists uSpec, ll.
        split; auto.
        constructor; auto.
      Qed.

    End ThetaRel.

    Section ThetaRelNoRuleMap.
      Variable thetaR: RegsT -> RegsT -> Prop.
      Variable thetaInit: thetaR (initRegs (getRegInits imp)) (initRegs (getRegInits spec)).
      Variable defsImpZero: getDefsBodies imp = nil.
      Variable defsSpecZero: getDefsBodies spec = nil.

      Variable substepRuleMap:
        forall oImp uImp rule csImp (Hreach: reachable oImp imp),
          Substep imp oImp uImp (Rle (Some rule)) csImp ->
          forall oSpec,
            thetaR oImp oSpec ->
            exists srule uSpec,
              Substep spec oSpec uSpec (Rle srule) (liftToMap1 p csImp) /\
              thetaR (M.union uImp oImp) (M.union uSpec oSpec).
      
      Lemma stepMapZeroR_NoRuleMap:
        forall o (reachO: reachable o imp) u l (s: Step imp o u l) oSpec,
          thetaR o oSpec ->
          exists sl uSpec,
            Step spec oSpec uSpec sl /\
            equivalentLabel (liftToMap1 p) l sl /\
            thetaR (M.union u o) (M.union uSpec oSpec).
      Proof.
        intros; apply step_zero in s; auto; dest.
        destruct l as [ann ds cs]; simpl in *; subst.

        destruct ann as [[r|]|].

        - pose proof (substepRuleMap reachO H1 H).
          destruct H0 as [srule [uSpec ?]]; dest.
          exists {| annot := Some srule;
                    defs := M.empty _;
                    calls := liftToMap1 p cs |}.
          exists uSpec; repeat split.
          + apply substepZero_imp_step in H0; auto.
          + auto.

        - inv H1; exists emptyRuleLabel, (M.empty _); repeat split.
          + match goal with
            | [ |- Step _ _ _ ?l ] =>
              change l with (getLabel (Rle None) (M.empty _))
            end.
            apply substepZero_imp_step; auto.
            constructor.
          + mred.

        - inv H1; exists emptyMethLabel, (M.empty _); repeat split.
          + match goal with
            | [ |- Step _ _ _ ?l ] =>
              change l with (getLabel (Meth None) (M.empty _))
            end.
            apply substepZero_imp_step; auto.
            constructor.
          + mred.
      Qed.

      Lemma multistepMapZeroR_NoRuleMap:
        forall o u l,
          o = initRegs (getRegInits imp) ->
          Multistep imp o u l ->
          exists uSpec ll,
            thetaR u uSpec /\
            equivalentLabelSeq (liftToMap1 p) l ll /\
            Multistep spec (initRegs (getRegInits spec)) uSpec ll.
      Proof.
        induction 2; simpl; intros; repeat subst.

        - do 2 eexists; repeat split.
          + instantiate (1:= initRegs (getRegInits spec)); auto.
          + instantiate (1:= nil); constructor.
          + constructor; auto.

        - specialize (IHMultistep eq_refl).
          destruct IHMultistep as [puSpec [pll ?]]; dest.
          apply stepMapZeroR_NoRuleMap with (oSpec:= puSpec) in HStep; auto;
            [|eexists; constructor; eauto].
          destruct HStep as [sl [uSpec ?]]; dest.

          exists (M.union uSpec puSpec), (sl :: pll).
          repeat split; auto.
          + constructor; auto.
          + constructor; auto.
      Qed.

      Theorem decompositionZeroR_NoRuleMap:
        traceRefines (liftToMap1 p) imp spec.
      Proof.
        unfold traceRefines; intros.
        inv H.
        apply multistepMapZeroR_NoRuleMap in HMultistepBeh; auto.
        destruct HMultistepBeh as [uSpec [ll ?]]; dest.
        exists uSpec, ll.
        split; auto.
        constructor; auto.
      Qed.

    End ThetaRelNoRuleMap.
    
  End DecompositionZero.

  Section DecompositionOne.
    Variable imp spec: Modules.
    
    Section EtaFunc.
      Hypothesis HimpEquiv: ModEquiv type typeUT imp.

      Variable specRegName: string.
      Variable eta: RegsT -> option (sigT (fullType type)).
      Definition theta (r: RegsT): RegsT :=
        match eta r with
        | Some er => M.add specRegName er (M.empty _)
        | None => M.empty _
        end.
  
      Variable ruleMap: RegsT -> string -> option string.
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
      
      Hypothesis HsubstepMethMap:
        forall oImp uImp meth csImp,
          reachable oImp imp ->
          Substep imp oImp uImp (Meth (Some meth)) csImp ->
          exists uSpec,
            Substep spec (theta oImp) uSpec (Meth (liftP meth)) (liftToMap1 p csImp) /\
            ConsistentUpdate oImp (theta oImp) uImp uSpec.

      Definition mapUnitLabelOne o ul :=
        match ul with
        | Rle (Some r) => Rle (ruleMap o r)
        | Rle None => Rle None
        | Meth (Some dm) => Meth (liftP dm)
        | Meth None => Meth None
        end.

      Lemma substepMapOne:
        forall oi ui uli csi,
          reachable oi imp ->
          Substep imp oi ui uli csi ->
          exists us,
            Substep spec (theta oi) us (mapUnitLabelOne oi uli) (liftToMap1 p csi) /\
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
                           (mapUnitLabelOne oImp ulImp) (liftToMap1 p csImp);
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
           unitAnnot := mapUnitLabelOne oImp (ulImp sr);
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
            Substep spec (theta oi) us1 (mapUnitLabelOne oi uli1) css1 ->
            Substep spec (theta oi) us2 (mapUnitLabelOne oi uli2) css2 ->
            CanCombineUL us1 us2
                         (getLabel (mapUnitLabelOne oi uli1) css1)
                         (getLabel (mapUnitLabelOne oi uli2) css2).

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
        destruct (substepMapOne Hreach Hss) as [sus ?]; dest.
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
               unitAnnot := mapUnitLabelOne oi suli;
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
          + unfold mapUnitLabelOne, liftP.
            destruct uli as [[|]|[|]]; auto.
            destruct a as [an ab]; simpl.
            rewrite liftToMap1_add_one.
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

      Lemma substepRels_wellHidden:
        forall o,
          reachable o imp ->
          forall (srs: list (SubstepRel o)),
            SubstepRels srs ->
            wellHidden imp (hide (foldSSLabel (map toSubstepRecImp srs))) ->
            wellHidden spec (hide (foldSSLabel (map toSubstepRecSpec srs))).
      Proof.
        intros.
        pose proof (liftPLabel_wellHidden spec ruleMap o p HdefSubset HcallSubset H1).
        rewrite liftPLabel_hide with (imp:= imp) in H2; auto.
        - rewrite liftPLabel_substepRels in H2; auto.
        - unfold M.KeysSubset; apply getDefs_substeps.
        - unfold M.KeysSubset; apply getCalls_substeps; auto.
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

        - rewrite liftPLabel_hide with (imp:= imp); auto.
          + subst; rewrite liftPLabel_substepRels; auto.
            constructor; auto.
            apply substepRels_wellHidden; auto.
          + unfold M.KeysSubset; apply getDefs_substeps.
          + unfold M.KeysSubset; apply getCalls_substeps; auto.

        - subst; unfold ConsistentUpdate in H2; dest; auto.
      Qed.
      
    End EtaFunc.

    Section EtaRel.
      Hypothesis HimpEquiv: ModEquiv type typeUT imp.

      Variable specRegName: string.
      Variable etaR: RegsT -> option (sigT (fullType type)) -> Prop.

      Definition etaRState (v: option (sigT (fullType type))) :=
        match v with
        | Some ev => M.add specRegName ev (M.empty _)
        | _ => M.empty _
        end.
      Definition thetaR (ir sr: RegsT): Prop := exists sv, etaR ir sv /\ etaRState sv = sr.
      
      Variable ruleMap: RegsT -> string -> option string.
      Hypothesis HthetaRRInit: thetaR (initRegs (getRegInits imp)) (initRegs (getRegInits spec)).
      
      Hypothesis HdefSubset: forall f, In f (getDefs spec) -> In f (getDefs imp).
      Hypothesis HcallSubset: forall f, In f (getCalls spec) -> In f (getCalls imp).

      Definition ConsistentUpdateR (oImp oSpec: RegsT) (uImp uSpec: UpdatesT) :=
        (uImp = M.empty _ -> uSpec = M.empty _) /\
        (uSpec = M.empty _ -> uImp = M.empty _) /\
        (thetaR oImp oSpec -> thetaR (M.union uImp oImp) (M.union uSpec oSpec)).

      Hypothesis HsubstepRuleRel:
        forall oImp uImp rule csImp,
          reachable oImp imp ->
          Substep imp oImp uImp (Rle (Some rule)) csImp ->
          forall oSpec,
            thetaR oImp oSpec ->
            exists uSpec,
              Substep spec oSpec uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
              ConsistentUpdateR oImp oSpec uImp uSpec.

      Hypothesis HsubstepMethRel:
        forall oImp uImp meth csImp,
          reachable oImp imp ->
          Substep imp oImp uImp (Meth (Some meth)) csImp ->
          forall oSpec,
            thetaR oImp oSpec ->
            exists uSpec,
              Substep spec oSpec uSpec (Meth (liftP meth)) (liftToMap1 p csImp) /\
              ConsistentUpdateR oImp oSpec uImp uSpec.

      Definition mapUnitLabelR o ul :=
        match ul with
        | Rle (Some r) => Rle (ruleMap o r)
        | Rle None => Rle None
        | Meth (Some dm) => Meth (liftP dm)
        | Meth None => Meth None
        end.

      Lemma substepRel:
        forall oi ui uli csi,
          reachable oi imp ->
          Substep imp oi ui uli csi ->
          forall os,
            thetaR oi os ->
            exists us,
              Substep spec os us (mapUnitLabelR oi uli) (liftToMap1 p csi) /\
              ConsistentUpdateR oi os ui us.
      Proof.
        intros; destruct uli as [[r|]|[dm|]].

        - apply HsubstepRuleRel; auto.
        - inv H0; exists (M.empty _); split.
          + apply EmptyRule.
          + unfold ConsistentUpdate; repeat split; auto.
        - apply HsubstepMethRel; auto.
        - inv H0; exists (M.empty _); split.
          + apply EmptyMeth.
          + unfold ConsistentUpdate; repeat split; auto.
      Qed.

      Record SubstepRelR oImp oSpec :=
        { uImpR: UpdatesT;
          ulImpR: UnitLabel;
          csImpR: MethsT;
          HssImpR: Substep imp oImp uImpR ulImpR csImpR;
          uSpecR: UpdatesT;
          HssSpecR: Substep spec oSpec uSpecR
                            (mapUnitLabelR oImp ulImpR) (liftToMap1 p csImpR);
          HthetaR: thetaR oImp oSpec;
          HcuR: ConsistentUpdateR oImp oSpec uImpR uSpecR
        }.

      Definition toSubstepRecImpR {oImp oSpec} (sr: SubstepRelR oImp oSpec) :=
        {| upd := uImpR sr;
           unitAnnot := ulImpR sr;
           cms := csImpR sr;
           substep := HssImpR sr
        |}.

      Definition toSubstepRecSpecR {oImp oSpec} (sr: SubstepRelR oImp oSpec) :=
        {| upd := uSpecR sr;
           unitAnnot := mapUnitLabelR oImp (ulImpR sr);
           cms := liftToMap1 p (csImpR sr);
           substep := HssSpecR sr
        |}.

      Inductive SubstepRelsR {oImp oSpec}: list (SubstepRelR oImp oSpec) -> Prop :=
      | SubstepMapNilR: SubstepRelsR nil
      | SubstepMapConsR:
          forall srs sr,
            SubstepRelsR srs ->
            (forall sr', In sr' srs -> canCombine (toSubstepRecImpR sr)
                                                  (toSubstepRecImpR sr')) ->
            SubstepRelsR (sr :: srs).

      Hypothesis HcanCombine:
        forall oi ui1 ui2 uli1 uli2 csi1 csi2,
          reachable oi imp ->
          Substep imp oi ui1 uli1 csi1 ->
          Substep imp oi ui2 uli2 csi2 ->
          CanCombineUL ui1 ui2 (getLabel uli1 csi1) (getLabel uli2 csi2) ->
          forall us1 us2 css1 css2 os,
            thetaR oi os ->
            Substep spec os us1 (mapUnitLabelR oi uli1) css1 ->
            Substep spec os us2 (mapUnitLabelR oi uli2) css2 ->
            CanCombineUL us1 us2
                         (getLabel (mapUnitLabelR oi uli1) css1)
                         (getLabel (mapUnitLabelR oi uli2) css2).

      Lemma substeps_substepRels_impR:
        forall {oImp oSpec} (HthetaR: thetaR oImp oSpec)
               (Hreach: reachable oImp imp)
               (ss: Substeps imp oImp) (Hcomb: substepsComb ss),
        exists (srs: list (SubstepRelR oImp oSpec)),
          map toSubstepRecImpR srs = ss /\ SubstepRelsR srs.
      Proof.
        induction ss; simpl; intros; [exists nil; split; auto; constructor|].
        inv Hcomb; specialize (IHss H1).
        destruct IHss as [psrs ?]; dest.
        destruct a as [su sul scs Hss].
        pose proof (substepRel Hreach Hss HthetaR0) as [sus ?]; dest.
        exists ({| HthetaR:= HthetaR0; HssImpR := Hss; HssSpecR := H3; HcuR:= H4 |} :: psrs); split.
        - simpl; f_equal; auto.
        - constructor; auto.
          unfold toSubstepRecImp; simpl.
          clear -H2 H.
          intros; apply in_map with (f:= toSubstepRecImpR) in H0.
          rewrite H in H0; auto.
      Qed.

      Lemma substepRels_canCombineR:
        forall {oi os} (Hreach: reachable oi imp)
               (srs: list (SubstepRelR oi os))
               sui suli scsi sus Hssi Hsss
               (Hcombi : forall sr' : SubstepRelR oi os,
                   In sr' srs ->
                   canCombine {| upd := sui; unitAnnot := suli; cms := scsi; substep := Hssi |}
                              {| upd := uImpR sr'; unitAnnot := ulImpR sr'; cms := csImpR sr';
                                 substep := HssImpR sr' |}),
        forall s': SubstepRec spec os,
          In s' (map toSubstepRecSpecR srs) ->
          canCombine
            {| upd := sus;
               unitAnnot := mapUnitLabelR oi suli;
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

      Lemma substepRels_substeps_specR:
        forall {oi os} (Hreach: reachable oi imp)
               (srs: list (SubstepRelR oi os)),
          SubstepRelsR srs ->
          exists (ss: Substeps spec os),
            map toSubstepRecSpecR srs = ss /\ substepsComb ss.
      Proof.
        induction srs; simpl; intros; [exists nil; split; auto; constructor|].
        inv H; specialize (IHsrs H2).
        destruct IHsrs as [pss ?]; dest.
        destruct a as [sui suli scsi Hssi sus Hsss].
        exists ({| substep := Hsss |} :: pss); split.
        - simpl; f_equal; auto.
        - constructor; auto.
          subst; unfold toSubstepRecImp in H3; simpl in H3.

          clear -H3 HthetaR0 Hreach HcanCombine.
          eapply substepRels_canCombineR; eauto.
      Qed.

      Lemma liftPLabel_substepRelsR:
        forall {oi os} (srs: list (SubstepRelR oi os)),
          SubstepRelsR srs ->
          liftPLabel (liftToMap1 p) ruleMap oi (foldSSLabel (map toSubstepRecImpR srs)) =
          foldSSLabel (map toSubstepRecSpecR srs).
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
          + unfold mapUnitLabelR, liftP.
            destruct uli as [[|]|[|]]; auto.
            destruct a as [an ab]; simpl.
            rewrite liftToMap1_add_one.
            destruct (p an ab); auto.
            
        - assert (forall ss: SubstepRec imp oi,
                     In ss (map toSubstepRecImpR srs) -> canCombine (toSubstepRecImpR a) ss).
          { intros; apply in_map_iff in H; dest; subst; auto. }
          clear H3.
          apply canCombine_consistent_1 in H; clear -H.
          generalize dependent (foldSSLabel (map toSubstepRecImpR srs)); intros.
          inv H; dest; clear H0.
          repeat split; auto.
          + destruct a; simpl in *.
            destruct ulImpR0 as [|[|]]; auto.
            destruct a as [an ab]; simpl in *.
            destruct (annot l); auto.
          + destruct a; simpl in *.
            destruct ulImpR0 as [|[|]]; auto.
      Qed.

      Lemma consistentUpdate_update_specR:
        forall (oi os: RegsT) (HthetaR: thetaR oi os)
               (ui us: UpdatesT),
          ConsistentUpdateR oi os ui us ->
          us = M.empty _ \/ exists v, us = M.add specRegName v (M.empty _).
      Proof.
        intros; inv H; dest.
        remember (M.find specRegName us) as uv; destruct uv.

        - right; exists s; meq; exfalso.
          unfold thetaR in H2; destruct H2 as [sv ?]; dest.
          destruct sv.
          + simpl in H2; apply M.Equal_val with (k:= y) in H2; mred.
          + simpl in H2; apply M.Equal_val with (k:= y) in H2; mred.

        - left; meq.
          exfalso; M.cmp y specRegName.
          + findeq.
          + unfold thetaR in H2; destruct H2 as [sv ?]; dest.
            destruct sv.
            * simpl in H2; apply M.Equal_val with (k:= y) in H2; mred.
            * simpl in H2; apply M.Equal_val with (k:= y) in H2; mred.
      Qed.

      Lemma substepRels_consistentUpdateR:
        forall oi os,
          reachable oi imp ->
          forall (srs: list (SubstepRelR oi os)),
            SubstepRelsR srs ->
            ConsistentUpdateR oi os (foldSSUpds (map toSubstepRecImpR srs))
                              (foldSSUpds (map toSubstepRecSpecR srs)).
      Proof.
        induction 2; simpl; intros;
          [unfold ConsistentUpdateR; repeat split; auto|].

        destruct sr as [ui uli csi Hssi us Hsss HthetaR Hcu]; simpl in *.
        pose proof (consistentUpdate_update_specR HthetaR IHSubstepRelsR).
        repeat split.
        - intros; unfold ConsistentUpdateR in *; dest; simpl in *.
          apply M.union_empty in H3; dest.
          unfold toSubstepRecImpR in H1; simpl in H1; subst.
          specialize (e eq_refl); subst.
          mred.
        - intros; unfold ConsistentUpdateR in *; dest; simpl in *.
          apply M.union_empty in H3; dest.
          unfold toSubstepRecImpR in H1; simpl in H1; subst.
          specialize (e0 eq_refl); subst.
          mred.
        - destruct H2.
          + rewrite H2 in *.
            unfold ConsistentUpdateR in *; dest; simpl in *.
            specialize (H4 eq_refl); rewrite H4 in *.
            intros; mred; auto.
          + pose proof (consistentUpdate_update_specR HthetaR Hcu).
            unfold toSubstepRecImpR in H1; simpl in H1.
            inv Hcu; dest.
            destruct H3.

            * subst.
              specialize (H5 eq_refl); subst.
              inv IHSubstepRelsR; dest.
              mred.
            * exfalso.
              pose proof (substepRels_canCombineR (sui:= ui) (Hssi:= Hssi) H srs Hsss H1).
              apply canCombine_consistent_1 in H7.
              dest; subst.
              rewrite H2 in H7; clear -H7.
              inv H7; dest; clear -H.
              specialize (H specRegName); destruct H; findeq.
      Qed.

      Lemma substepRels_wellHiddenR:
        forall o s,
          reachable o imp ->
          forall (srs: list (SubstepRelR o s)),
            SubstepRelsR srs ->
            wellHidden imp (hide (foldSSLabel (map toSubstepRecImpR srs))) ->
            wellHidden spec (hide (foldSSLabel (map toSubstepRecSpecR srs))).
      Proof.
        intros.
        pose proof (liftPLabel_wellHidden spec ruleMap o p HdefSubset HcallSubset H1).
        rewrite liftPLabel_hide with (imp:= imp) in H2; auto.
        - rewrite liftPLabel_substepRelsR in H2; auto.
        - unfold M.KeysSubset; apply getDefs_substeps.
        - unfold M.KeysSubset; apply getCalls_substeps; auto.
      Qed.

      Lemma stepMapOne:
        forall o (reachO: reachable o imp)
               u l (s: Step imp o u l) oSpec,
          thetaR o oSpec ->
          exists uSpec ul,
            Step spec oSpec uSpec ul /\
            thetaR (M.union u o) (M.union uSpec oSpec) /\
            equivalentLabel (liftToMap1 p) l ul.
      Proof.
        intros; inv s.
        pose proof (substeps_substepRels_impR H reachO HSubsteps) as Hsrs.
        destruct Hsrs as [srs ?]; dest; subst.
        exists (foldSSUpds (map toSubstepRecSpecR srs)).
        exists (hide (foldSSLabel (map toSubstepRecSpecR srs))); split; [|split].
        - constructor; auto.
          + pose proof (substepRels_substeps_specR reachO H1) as Hsss.
            dest; subst; auto.
          + apply substepRels_wellHiddenR; auto.
        - apply substepRels_consistentUpdateR; auto.
        - pose proof (liftPLabel_substepRelsR H1).
          rewrite <-H0.
          rewrite <-liftPLabel_hide with (imp:= imp); auto.
          + generalize (hide (foldSSLabel (map toSubstepRecImpR srs))) as l; intros.
            destruct l as [a d c].
            repeat split; simpl; destruct a as [[|]|]; auto.
          + unfold M.KeysSubset; apply getDefs_substeps.
          + unfold M.KeysSubset; apply getCalls_substeps; auto.
      Qed.

      Lemma multistepMapOne:
        forall o u l,
          o = initRegs (getRegInits imp) ->
          Multistep imp o u l ->
          exists uSpec ll,
            thetaR u uSpec /\
            equivalentLabelSeq (liftToMap1 p) l ll /\
            Multistep spec (initRegs (getRegInits spec)) uSpec ll.
      Proof.
        induction 2; simpl; intros; repeat subst.

        - do 2 eexists; repeat split.
          + instantiate (1:= initRegs (getRegInits spec)); auto.
          + instantiate (1:= nil); constructor.
          + constructor; auto.

        - specialize (IHMultistep eq_refl).
          destruct IHMultistep as [puSpec [pll ?]]; dest.
          apply stepMapOne with (oSpec:= puSpec) in HStep; auto;
            [|eexists; constructor; eauto].
          destruct HStep as [uSpec [ul ?]]; dest.

          eexists (M.union uSpec puSpec), (ul :: pll).
          repeat split; auto.
          + constructor; auto.
          + constructor; auto.
      Qed.

      Theorem decompositionOneR:
        traceRefines (liftToMap1 p) imp spec.
      Proof.
        unfold traceRefines; intros.
        inv H.
        apply multistepMapOne in HMultistepBeh; auto.
        destruct HMultistepBeh as [uSpec [ll ?]]; dest.
        exists uSpec, ll.
        split; auto.
        constructor; auto.
      Qed.
      
    End EtaRel.

  End DecompositionOne.

  Section DecompositionDrop.
    Variable imp spec: Modules.
    Hypothesis HimpEquiv: ModEquiv type typeUT imp.

    Hypothesis HdefSubset: forall f, In f (getDefs spec) -> In f (getDefs imp).
    Hypothesis HcallSubset: forall f, In f (getCalls spec) -> In f (getCalls imp).

    Hypothesis (Hp: forall c1 c2, M.Disj c1 c2 -> M.Disj (liftToMap1 p c1) (liftToMap1 p c2)).

    Variable theta: RegsT -> RegsT.
    Hypotheses
      (HthetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec))
      (Htheta1: theta (M.empty _) = M.empty _)
      (Htheta2: forall s1 s2,
          theta (M.union s1 s2) = M.union (theta s1) (theta s2))
      (Htheta3: forall s1 s2, M.Disj s1 s2 -> M.Disj (theta s1) (theta s2)).
    
    Variable ruleMap: RegsT -> string -> option string.
    
    Variable substepRuleMap:
      forall oImp uImp rule csImp,
        reachable oImp imp ->
        Substep imp oImp uImp (Rle (Some rule)) csImp ->
        Substep spec (theta oImp) (theta uImp) (Rle (ruleMap oImp rule)) (liftToMap1 p csImp).

    Variable substepMethMap:
      forall oImp uImp meth csImp,
        reachable oImp imp ->
        Substep imp oImp uImp (Meth (Some meth)) csImp ->
        Substep spec (theta oImp) (theta uImp) (Meth (liftP meth)) (liftToMap1 p csImp).

    Definition liftPUnitLabel o ul :=
      match ul with
      | Rle (Some r) => Rle (ruleMap o r)
      | Rle None => Rle None
      | Meth (Some dm) => Meth (liftP dm)
      | Meth None => Meth None
      end.

    Lemma decompositionDrop_substep:
      forall o u ul cs,
        reachable o imp ->
        Substep imp o u ul cs ->
        Substep spec (theta o) (theta u) (liftPUnitLabel o ul) (liftToMap1 p cs).
    Proof.
      intros; destruct ul as [[|]|[|]].
      - apply substepRuleMap in H0; auto.
      - inv H0; simpl; rewrite Htheta1; constructor.
      - apply substepMethMap in H0; auto.
      - inv H0; simpl; rewrite Htheta1; constructor.
    Qed.

    Lemma p_disj_unitLabel:
      forall n d,
        ~ M.In n d ->
        ~ M.In n (liftToMap1 p d).
    Proof.
      intros; findeq.
      rewrite liftToMap1_find.
      rewrite H; auto.
    Qed.

    Lemma decompositionDrop_substepsInd:
      forall o u l,
        reachable o imp ->
        SubstepsInd imp o u l ->
        SubstepsInd spec (theta o) (theta u) (liftPLabel (liftToMap1 p) ruleMap o l).
    Proof.
      induction 2; [simpl; rewrite Htheta1; constructor|].
      subst.
      rewrite Htheta2.
      rewrite liftPLabel_mergeLabel.
      - econstructor.
        + apply IHSubstepsInd.
        + apply decompositionDrop_substep; auto.
          eassumption.
        + unfold CanCombineUUL in *; dest; simpl in *.
          repeat split; auto.
          * destruct l as [a d c]; simpl in *; auto.
          * destruct l as [a d c]; simpl in *.
            destruct a as [[|]|]; destruct sul as [[|]|[|]]; simpl in *; auto;
              try (destruct a as [n t]; simpl in *;
                   case_eq (p n t); simpl; intros; auto;
                   apply p_disj_unitLabel; auto).
        + reflexivity.
        + f_equal.
          unfold getLabel; cbn; f_equal.
          * unfold liftPUnitLabel.
            destruct sul as [[|]|[|]]; try reflexivity.
          * unfold liftToMap1, liftPUnitLabel; simpl.
            destruct sul as [[|]|[|]]; try reflexivity.
            destruct a; cbn.
            unfold rmModify.
            destruct (p attrName attrType); try reflexivity.
      - clear -H2.
        unfold CanCombineUUL in H2; unfold CanCombineLabel.
        destruct l as [a d c]; simpl in *; dest.
        repeat split; auto;
          try (destruct a as [|]; destruct sul as [[|]|[|]]; auto;
               destruct a; simpl in *; auto).
    Qed.

    Lemma decompositionDrop_stepInd:
      forall o u l,
        reachable o imp ->
        StepInd imp o u l ->
        StepInd spec (theta o) (theta u) (liftPLabel (liftToMap1 p) ruleMap o l).
    Proof.
      intros; inv H0.
      rewrite liftPLabel_hide with (imp:= imp); auto.
      - constructor.
        + apply decompositionDrop_substepsInd; auto.
        + rewrite <-liftPLabel_hide with (imp:= imp); auto.
          * eapply liftPLabel_wellHidden; eauto.
          * eapply substepsInd_defs_in; eauto.
          * eapply substepsInd_calls_in; eauto.
      - eapply substepsInd_defs_in; eauto.
      - eapply substepsInd_calls_in; eauto.
    Qed.

    Lemma decompositionDrop_step:
      forall o u l,
        reachable o imp ->
        Step imp o u l ->
        Step spec (theta o) (theta u) (liftPLabel (liftToMap1 p) ruleMap o l).
    Proof.
      intros.
      apply step_consistent in H0.
      apply step_consistent.
      apply decompositionDrop_stepInd; auto.
    Qed.

    Theorem decompositionDrop:
      traceRefines (liftToMap1 p) imp spec.
    Proof.
      unfold traceRefines; intros.
      eapply stepRefinement with (ruleMap:= ruleMap); eauto.
      intros.
      exists (theta u); split; auto.
      apply decompositionDrop_step; auto.
    Qed.
    
  End DecompositionDrop.

End GivenLabelMap.

#[global] Hint Unfold theta etaRState thetaR: MethDefs.

Section DecompositionInv.
  Variable m: Modules.
  Variable P: RegsT -> Prop.
  Hypothesis HinitP: P (initRegs (getRegInits m)).

  Hypothesis HruleP:
    forall o u rule cs,
      P o ->
      Substep m o u (Rle (Some rule)) cs ->
      P (M.union u o).

  Hypothesis HmethP:
    forall o u meth cs,
      P o ->
      Substep m o u (Meth (Some meth)) cs ->
      P (M.union u o).

  Lemma substep_P:
    forall o u ul cs,
      P o ->
      Substep m o u ul cs ->
      P (M.union u o).
  Proof.
    intros; destruct ul as [[r|]|[dm|]].
    - eapply HruleP; eauto.
    - inv H0; mred.
    - eapply HmethP; eauto.
    - inv H0; mred.
  Qed.

  Hypothesis HcanCombine:
    forall o u1 u2 ul1 ul2 cs1 cs2,
      Substep m o u1 ul1 cs1 ->
      Substep m o u2 ul2 cs2 ->
      CanCombineUL u1 u2 (getLabel ul1 cs1) (getLabel ul2 cs2) ->
      u1 = M.empty _ \/ u2 = M.empty _.

  Lemma substeps_updates:
    forall o (s: SubstepRec m o)
           (ss: Substeps m o),
      (forall s' : SubstepRec m o, In s' ss -> canCombine s s') ->
      foldSSUpds ss = M.empty _ \/ upd s = M.empty _.
  Proof.
    induction ss; simpl; intros; [auto|].
    assert (forall s' : SubstepRec m o, In s' ss -> canCombine s s').
    { intros; apply H; auto. }
    specialize (IHss H0); clear H0.
    destruct IHss; auto.
    rewrite H0; mred.
    specialize (H a (or_introl eq_refl)).
    apply or_comm.
    destruct s, a; simpl in *.
    eapply HcanCombine; eauto.
    eapply canCombine_CanCombineUL; eauto.
  Qed.

  Lemma substeps_P:
    forall o,
      P o ->
      forall (ss: Substeps m o),
        substepsComb ss ->
        P (M.union (foldSSUpds ss) o).
  Proof.
    induction 2; simpl; intros; [mred|].
    apply substeps_updates in H1; destruct H1; rewrite H1.
    - mred.
      destruct s; simpl in *.
      eapply substep_P; eauto.
    - mred.
  Qed.

  Lemma multistep_P:
    forall init n ll,
      init = initRegs (getRegInits m) ->
      Multistep m init n ll ->
      P n.
  Proof.
    induction 2; [repeat subst; auto|].
    specialize (IHMultistep H); subst; clear H0.
    inv HStep; clear HWellHidden.
    apply substeps_P; auto.
  Qed.

  Lemma decompositionInv:
    forall o,
      reachable o m ->
      P o.
  Proof.
    intros; inv H; inv H0.
    eapply multistep_P; eauto.
  Qed.
      
End DecompositionInv.

