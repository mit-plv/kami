Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap.
Require Import Syntax.
Require Export SemanticsExprAction Semantics SemFacts.

Set Implicit Arguments.

Section GivenModule.
  Variable m: Modules.
  Variable o: RegsT.

  (* Inductive SubstepComb: UpdatesT -> UnitLabel -> MethsT -> Prop := *)
  (* | SSCStart *)
  (*     u l cs *)
  (*     (HSubstep: Substep m o u l cs): *)
  (*     SubstepComb u l cs *)
  (* | SSCComb *)
  (*     u l cs *)
  (*     (HSSC: SubstepComb o l cs) *)
  (*     meth ar *)
  (*     (HInDynCalls: M.In meth cs) *)
  (*     (HFind: M.find meth cs = Some ar) *)
  (*     u' cs' *)
  (*     (HSubstep: Substep m o u' (Meth (Some (meth :: ar)%struct)) cs') *)
  (*     (HDisjRegs: M.Disj u u') *)
  (*     (HDisjCalls: M.Disj cs cs') *)
  (*     u'' cs'' *)
  (*     (HUEq: u'' = M.union u u') *)
  (*     (HCsEq: cs'' = M.union (M.remove meth cs) cs'): *)
  (*     SubstepComb u'' l cs''. *)

  (* Inductive SubstepFull: UpdatesT -> UnitLabel -> MethsT -> Prop := *)
  (* | SSF u l cs *)
  (*       (HSubstepComb: SubstepComb u l cs) *)
  (*       (HNoInternalCalls: forall x, M.In x cs -> In x (getDefs m) -> False): *)
  (*     SubstepFull u l cs. *)

  Inductive SubstepFull: UpdatesT -> UnitLabel -> MethsT -> Prop :=
  | SSFStart
      u l cs
      (HSubstep: Substep m o u l cs)
      meth ar
      (HInDynCalls: M.In meth cs)
      (HFind: M.find meth cs = Some ar)
      u' cs'
      (HSubstepFull: SubstepFull u' (Meth (Some (meth :: ar)%struct)) cs')
      (HDisjRegs: M.Disj u u')
      (HDisjCalls: M.Disj (M.remove meth cs) cs')
      u'' cs''
      (HUEq: u'' = M.union u u')
      (HCsEq: cs'' = M.union (M.remove meth cs) cs'):
      SubstepFull u'' l cs''
  | SSFDone:
      SubstepFull (M.empty _) (Meth None) (M.empty _).
  
  Inductive StepComb: UpdatesT -> LabelT -> Prop :=
  | SCNil:
      StepComb (M.empty _) {| annot := None; defs := M.empty _; calls := M.empty _ |}
  | SCAdd
      u l
      (HStepComb: StepComb u l)
      u' l' cs'
      (HSubstepFull: SubstepFull u' l' cs')
      (HRegsDisj: M.Disj u u')
      (HLabelsComb: CanCombineLabel l (getLabel l' cs'))
      u'' l''
      (HUEq: u'' = M.union u u')
      (HLEq: l'' = mergeLabel l (getLabel l' cs')):
      StepComb u'' l''.
End GivenModule.

(*
Section decomposition.
  Variable imp spec: Modules.
  Variable theta: RegsT -> RegsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).
  Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).
  Variable defSubset: forall f, In f (getDefs spec) -> In f (getDefs imp).
  Variable callSubset: forall f, In f (getCalls spec) -> In f (getCalls imp).

  Definition liftP meth :=
    match meth with
      | (n :: t)%struct => match p n t with
                             | None => None
                             | Some v => Some (n :: v)%struct
                           end
    end.

  Variable substepMap:
    forall oImp uImp rmImp csImp,
      SubstepFull imp oImp uImp rmImp csImp ->
      { uSpec |
        SubstepFull spec (theta oImp) uSpec match rmImp with
                                            | Rle None => Rle None
                                            | Meth None => Meth None
                                            | Rle (Some x) => Rle (ruleMap oImp x)
                                            | Meth (Some y) => Meth (liftP y)
                                            end (liftToMap1 p csImp) /\
        forall o, M.union uSpec (theta o) = theta (M.union uImp o) }.

  Definition xformUnitAnnot o rm :=
    match rm with
      | Rle (Some rule) => Rle (ruleMap o rule)
      | Meth (Some meth) => Meth (liftP meth)
      | Rle None => Rle None
      | Meth None => Meth None
    end.

  Definition xformSubstepRec o (s': SubstepRec imp o) :=
    match s' with
      | {| upd := u; unitAnnot := rm; cms := cs; substep := s |} =>
        match substepMap s with
          | exist uSpec (conj sSpec _) =>
            {| upd := uSpec; unitAnnot := xformUnitAnnot o rm;
               cms := liftToMap1 p cs; substep := sSpec |}
        end
    end.

  Variable specRegsCanCombine:
    forall o (s1 s2: SubstepRec imp o),
      M.Disj (upd s1) (upd s2) -> M.Disj (upd (xformSubstepRec s1)) (upd (xformSubstepRec s2)).

  Definition specCanCombine:
    forall o (s1 s2: SubstepRec imp o),
      canCombine s1 s2 -> canCombine (xformSubstepRec s1) (xformSubstepRec s2).
  Proof.
    intros.
    unfold canCombine in *.
    dest.
    constructor.
    intuition.
    - constructor.
      clear - H0; intros.
      unfold xformSubstepRec in *.
      destruct s1, s2; simpl in *.
      destruct (substepMap substep), (substepMap substep0); simpl in *.
      destruct a, a0; simpl in *.
      unfold xformUnitAnnot in *.
      destruct unitAnnot, unitAnnot0.
      destruct o0, o1; try discriminate.
      destruct o0, o1; try discriminate.
      destruct o0, o1; try discriminate.
      destruct o0, o1; try discriminate.
      unfold liftP in *.
      destruct a, a0.
      unfold not; intros.
      destruct x, y; simpl in *.
      rewrite <- H2 in *.
      case_eq (p attrName attrType);
      case_eq (p attrName0 attrType0).
      intros.
      rewrite H3, H4 in *.
      subst.
      inversion H; inversion H1; subst.
      specialize (H0 (attrName2 :: attrType)%struct (attrName2 :: attrType0)%struct eq_refl
                     eq_refl); simpl in *.
      intuition.
      intros; subst.
      rewrite H3 in *.
      inversion H1; discriminate.
      intros; subst.
      rewrite H4 in *.
      inversion H; discriminate.
      intros; subst.
      rewrite H3 in *.
      inversion H1; discriminate.

      + constructor.
        clear -H1.
        unfold xformSubstepRec.
        destruct s1, s2; simpl in *.
        destruct (substepMap substep), (substepMap substep0).
        destruct a, a0; simpl in *.
        unfold xformUnitAnnot.
        destruct unitAnnot, unitAnnot0; destruct o0, o1; destruct H1; try discriminate;
          unfold liftP; try destruct a; try destruct (p attrName attrType); eexists; eauto.

        clear -H2.
        unfold xformSubstepRec.
        destruct s1, s2; simpl in *.
        destruct (substepMap substep), (substepMap substep0).
        destruct a, a0; simpl in *.
        { clear - H2.
          unfold M.Disj in *; intros.
          specialize (H2 k).
          destruct H2; unfold not.
          - left; intros.
            apply M.MapsToIn2 in H0; dest.
            apply liftToMap1MapsTo in H0; dest; subst.
            apply M.MapsToIn1 in H1; intuition.
          - right; intros.
            apply M.MapsToIn2 in H0; dest.
            apply liftToMap1MapsTo in H0; dest; subst.
            apply M.MapsToIn1 in H1; intuition.
        }
  Qed.

  Theorem substepsSpecComb o:
    forall (ss: Substeps imp o), substepsComb ss ->
                                 substepsComb (map (@xformSubstepRec o) ss).
  Proof.
    induction ss; intros; simpl in *; constructor; intros.
    - dependent destruction H; intuition.
    - dependent destruction H.
      pose proof (proj1 (in_map_iff (@xformSubstepRec o) ss s') H1) as [sImp [eqS inS]].
      specialize (H0 _ inS); subst.
      apply specCanCombine; intuition.
  Qed.

  Definition xformLabel o l :=
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

  Lemma wellHiddenSpec o l:
    wellHidden imp l ->
    wellHidden spec (xformLabel o l).
  Proof.
    intros [dHid cHid].
    unfold wellHidden in *.
    unfold xformLabel; destruct l; simpl in *.
    clear - defSubset callSubset dHid cHid.
    pose proof (liftToMap1Subset p defs) as dH.
    pose proof (liftToMap1Subset p calls) as cH.
    unfold M.DomainSubset, M.KeysDisj in *.
    constructor; unfold not; intros.
    - specialize (dH _ H0).
      specialize (callSubset _ H).
      specialize (dHid _ callSubset dH).
      intuition.
    - specialize (cH _ H0).
      specialize (defSubset _ H).
      specialize (cHid _ defSubset cH).
      intuition.
  Qed.

  Lemma subtractKVMapSet l1:
    forall l2,
      (forall x v1 v2, M.find x l1 = Some v1 -> M.find x l2 = Some v2 -> v1 = v2) ->
      liftToMap1 p (M.subtractKV signIsEq l1 l2) =
      M.subtractKV signIsEq (liftToMap1 p l1) (liftToMap1 p l2).
  Proof.
    clear; intros.
    assert (sth: forall x v1 v2, M.MapsTo x v1 l1 -> M.MapsTo x v2 l2 -> v1 = v2) by
        (intros;
         apply M.F.P.F.find_mapsto_iff in H0;
         apply M.F.P.F.find_mapsto_iff in H1; apply (H x); intuition); clear H.
    apply M.leibniz.
    apply M.F.P.F.Equal_mapsto_iff; intros.
    constructor; intros.
    - apply M.subtractKV_mapsto.
      apply liftToMap1MapsTo in H; dest.
      apply M.subtractKV_mapsto in H0; dest.
      constructor.
      apply liftToMap1MapsTo.
      eexists; eauto.
      unfold not; intros.
      apply liftToMap1MapsTo in H2; dest.
      specialize (sth _ _ _ H0 H3).
      subst.
      intuition.
    - apply liftToMap1MapsTo.
      apply M.subtractKV_mapsto in H; dest.
      apply liftToMap1MapsTo in H; dest.
      exists x.
      intuition.
      apply M.subtractKV_mapsto.
      constructor; intuition.
      assert (sth2: exists x, p k x = Some e /\ M.MapsTo k x l2) by (eexists; eauto).
      apply liftToMap1MapsTo in sth2.
      intuition.
  Qed.
  
  Theorem wellHiddenEq1 m l:
    M.KeysSubset (defs l) (getDefs m) ->
    M.KeysSubset (calls l) (getCalls m) ->
    wellHidden m (hide l) ->
    forall x v1 v2, M.find x (defs l) = Some v1 ->
                    M.find x (calls l) = Some v2 ->
                    v1 = v2.
  Proof.
    intros; unfold M.KeysSubset, wellHidden, M.KeysDisj in *.
    destruct l; unfold hide; simpl in *.
    destruct H1 as [d c].
    destruct (signIsEq v1 v2).
    - assumption.
    - exfalso.
      pose proof (M.subtractKV_in_find signIsEq H2 H3 n) as sthSub.
      elim (d x); auto.
      apply H0.
      apply M.F.P.F.in_find_iff.
      rewrite H3; discriminate.
  Qed.
    
  Theorem xformLabelHideCommute o l:
    (forall x v1 v2, M.find x (defs l) = Some v1 -> M.find x (calls l) = Some v2 -> v1 = v2) ->
    xformLabel o (hide l) = hide (xformLabel o l).
  Proof.
    intros Hyp.
    unfold xformLabel, hide.
    destruct l as [ann ds cs]; simpl in *; f_equal.
    - apply subtractKVMapSet; auto.
    - apply subtractKVMapSet.
      intros; apply eq_sym.
      eapply Hyp; eauto.
  Qed.

  Theorem liftToMap1UnionCommute l1 l2:
    M.Disj l1 l2 ->
    liftToMap1 p (M.union l1 l2) = M.union (liftToMap1 p l1) (liftToMap1 p l2).
  Proof.
    clear; intros disj.
    apply M.leibniz.
    apply M.F.P.F.Equal_mapsto_iff; intros.
    constructor; intros.
    - apply liftToMap1MapsTo in H; dest.
      apply M.mapsto_union in H0.
      apply M.mapsto_union.
      destruct H0; dest; subst.
      + left.
        apply liftToMap1MapsTo.
        eexists; eauto.
      + right.
        constructor; unfold not; intros.
        apply M.MapsToIn2 in H2; dest.
        apply liftToMap1MapsTo in H2; dest; subst.
        apply M.MapsToIn1 in H3; intuition.
        apply liftToMap1MapsTo.
        exists x; intuition.
    - apply M.mapsto_union in H.
      apply liftToMap1MapsTo.
      destruct H; dest; subst.
      + apply liftToMap1MapsTo in H; dest; subst.
        exists x; intuition.
        apply M.mapsto_union; intuition.
      + apply liftToMap1MapsTo in H0; dest; subst.
        unfold M.Disj in disj.
        pose proof H1 as sth.
        apply M.MapsToIn1 in H1.
        destruct (disj k); clear disj; intuition.
        exists x; intuition.
        apply M.mapsto_union; intuition.
  Qed.

  Theorem xformLabelAddLabelCommute l1 l2:
    M.Disj (defs l1) (defs l2) ->
    M.Disj (calls l1) (calls l2) ->
    forall o,
      xformLabel o (mergeLabel l1 l2) = mergeLabel (xformLabel o l1) (xformLabel o l2).
  Proof.
    intros.
    unfold mergeLabel, xformLabel; simpl in *.
    destruct l1, l2; simpl in *.
    destruct annot, annot0;
      repeat (try destruct o0; try destruct o1; simpl in *;
              repeat rewrite liftToMap1UnionCommute; intuition).
  Qed.

  Lemma xformLabelGetSLabelCommute o a:
    xformLabel o (getSLabel (o := o) a) = getSLabel (xformSubstepRec a).
  Proof.
    destruct a; simpl in *.
    destruct (substepMap substep).
    destruct a.
    simpl.
    unfold xformLabel, xformUnitAnnot.
    destruct unitAnnot; destruct o0; try rewrite liftToMap1Empty; intuition.
    destruct a.
    unfold liftP.
    rewrite liftToMap1AddOne.
    unfold getSLabel; simpl.
    destruct (p attrName attrType); intuition.
  Qed.
    
  Lemma defsDisjSs' m o u n ar cms
        (s: Substep m o u (Meth (Some (n :: ar)%struct)) cms) ss:
    (forall s', In s' ss -> canCombine {| substep := s |} s') ->
    M.Disj (M.add n ar (M.empty _)) (defs (foldSSLabel ss)).
  Proof.
    clear.
    dependent induction ss; intros; simpl in *.
    - apply M.Disj_empty_2.
    - assert (sth: forall s', In s' ss ->
                              canCombine {| substep := s |} s') by
          (intros; specialize (H s'); intuition).
      specialize (IHss sth); clear sth.
      assert (sth2: canCombine {| substep := s |} a) by (specialize (H a); intuition).
      clear H; unfold canCombine in *.
      dest.
      clear H x H1 H2; simpl in *.
      destruct a.
      unfold addLabelLeft, mergeLabel, getSLabel, getLabel; simpl in *.
      destruct (foldSSLabel ss); simpl in *.
      destruct unitAnnot; simpl in *.
      + rewrite M.union_empty_L.
        intuition.
      + destruct o0.
        * destruct a.
          { apply M.Disj_union.
            - specialize (H0 (n :: ar)%struct (attrName :: attrType)%struct eq_refl eq_refl).
              apply M.Disj_add_1.
              apply M.Disj_empty_1.
              unfold not; intros.
              simpl in *.
              apply M.F.P.F.add_in_iff in H.
              destruct H; intuition.
              apply M.F.P.F.empty_in_iff in H.
              intuition.
            - intuition.
          } 
        * rewrite M.union_empty_L.
          intuition.
  Qed.
  
  Lemma defsDisjSs m o (ss: list (SubstepRec m o)):
    forall b,
      substepsComb (b :: ss) ->
      M.Disj (defs (getSLabel b)) (defs (foldSSLabel ss)).
  Proof.
    clear.
    dependent induction ss; intros; simpl in *.
    - unfold M.Disj; unfold not; intros.
      right; intros.
      apply M.F.P.F.empty_in_iff in H0; intuition.
    - dependent destruction H.
      specialize (IHss _ H).
      destruct a, b; simpl in *.
      unfold addLabelLeft, mergeLabel, getSLabel; simpl in *.
      destruct unitAnnot0, unitAnnot; try apply M.Disj_empty_1;
        try destruct o0; try destruct a; try apply M.Disj_empty_1.
      case_eq (foldSSLabel ss); intros; simpl.
      rewrite M.union_empty_L.
      rewrite H1 in *; simpl in *.
      assert (sth: forall s', In s' ss ->
                              canCombine {| substep := substep0 |} s') by
          (intros; specialize (H0 s'); intuition); clear - sth H1.
      assert (sth3: defs = Semantics.defs (foldSSLabel ss)) by (rewrite H1; reflexivity).
      rewrite sth3.
      eapply defsDisjSs'; eauto.
      case_eq (foldSSLabel ss); intros; simpl.
      destruct o1.
      + destruct a.
        rewrite H1 in *; simpl in *.
        assert (sth3: defs = Semantics.defs (foldSSLabel ss)) by (rewrite H1; reflexivity).
        assert (sth2: M.union (M.add attrName0 attrType0 (M.empty _)) defs =
                      Semantics.defs (foldSSLabel ({| substep := substep |} :: ss))) by
            (simpl;
             unfold addLabelLeft, mergeLabel, getSLabel, getLabel;
             destruct (foldSSLabel ss); simpl in *; subst; reflexivity).
        rewrite sth2.
        eapply defsDisjSs'; eauto.
      + rewrite M.union_empty_L.
        rewrite H1 in *; simpl in *.
        assert (sth: forall s', In s' ss ->
                                canCombine {| substep := substep0 |} s') by
            (intros; specialize (H0 s'); intuition); clear - sth H1.
        assert (sth3: defs = Semantics.defs (foldSSLabel ss)) by (rewrite H1; reflexivity).
        rewrite sth3.
        eapply defsDisjSs'; eauto.
  Qed.

  Lemma callsDisjSs' m o u a cms (sr: Substep m o u a cms): forall ss,
      (forall s', In s' ss -> canCombine {| substep := sr|} s') ->
      M.Disj cms (calls (foldSSLabel ss)).
  Proof.    
    clear.
    dependent induction ss; intros.
    - apply M.Disj_empty_2.
    - assert (sth: forall s', In s' ss ->
                              canCombine {| substep := sr |} s') by
          (intros; specialize (H s'); intuition).
      specialize (IHss sth); clear sth.
      assert (sth2: canCombine {| substep := sr |} a0) by (specialize (H a0); intuition).
      clear H; unfold canCombine in *.
      dest.
      clear H x H0 H1; simpl in *.
      destruct a0.
      unfold addLabelLeft, mergeLabel, getSLabel, getLabel; simpl in *.
      destruct (foldSSLabel ss); simpl in *.
      apply M.Disj_union; intuition.
  Qed.
  
  Lemma callsDisjSs m o (ss: list (SubstepRec m o)):
    forall b,
      substepsComb (b :: ss) ->
      M.Disj (calls (getSLabel b)) (calls (foldSSLabel ss)).
  Proof.
    clear.
    intros.
    destruct b; simpl in *.
    unfold addLabelLeft, mergeLabel, getSLabel; simpl in *.
    case_eq (foldSSLabel ss); intros; simpl in *.
    assert (sth: Semantics.calls (foldSSLabel ss) = calls) by (rewrite H0; reflexivity).
    rewrite <- sth.
    dependent destruction H.
    eapply callsDisjSs'; eauto.
  Qed.
  
  Theorem xformLabelFoldCommute o ss:
    substepsComb ss ->
    xformLabel o (foldSSLabel (o := o) ss) = foldSSLabel (map (@xformSubstepRec _) ss).
  Proof.
    induction ss; simpl in *; try rewrite liftToMap1Empty; intros.
    - reflexivity.
    - pose proof H as sth.
      dependent destruction H.
      specialize (IHss H).
      unfold addLabelLeft in *.
      rewrite xformLabelAddLabelCommute.
      f_equal; intuition.
      apply xformLabelGetSLabelCommute.
      apply defsDisjSs; intuition.
      apply callsDisjSs; intuition.
  Qed.

  Variable impEquiv: ModEquiv type typeUT imp.

  Theorem xformLabelHide o:
    forall(ss: Substeps imp o) (ssGd: wellHidden imp (hide (foldSSLabel ss))),
      substepsComb ss ->
      hide (foldSSLabel (map (@xformSubstepRec _) ss)) =
      xformLabel o (hide (foldSSLabel ss)).
  Proof.
    intros.
    rewrite xformLabelHideCommute.
    f_equal.
    apply eq_sym; apply xformLabelFoldCommute; intuition.
    apply (wellHiddenEq1 (m := imp)).
    - unfold M.KeysSubset; apply (staticDynDefsSubsteps ss).
    - unfold M.KeysSubset; apply (staticDynCallsSubsteps impEquiv ss).
    - intuition.
  Qed.

  Lemma unionCommute' o a state:
    M.union (upd (xformSubstepRec (o := o) a)) (theta state) = theta (M.union (upd a) state).
  Proof.
    destruct a; simpl in *.
    destruct (substepMap substep).
    destruct a; simpl in *.
    intuition.
  Qed.

  Lemma unionCommute o ss:
    forall state,
      M.union (foldSSUpds (map (xformSubstepRec (o:=o)) ss)) (theta state) =
      theta (M.union (foldSSUpds ss) state).
  Proof.
    induction ss; intros; simpl in *.
    - repeat rewrite M.union_empty_L; reflexivity.
    - rewrite <- M.union_assoc.
      rewrite <- M.union_assoc.
      rewrite unionCommute'.
      apply (IHss (M.union (upd a) state)).
  Qed.

  Theorem stepMap o u l (s: Step imp o u l):
    exists uSpec,
      Step spec (theta o) uSpec (xformLabel o l) /\
      M.union uSpec (theta o) = theta (M.union u o).
  Proof.
    destruct s as [ss ssGd].
    exists (foldSSUpds (map (@xformSubstepRec _) ss)).
    pose proof (wellHiddenSpec o HWellHidden) as sth.
    pose proof (StepIntro (substepsSpecComb ssGd)) as final.
    rewrite xformLabelHide in *.
    specialize (final sth); clear sth.
    constructor.
    - intuition.
    - apply unionCommute; intuition.
    - intuition.
    - intuition.
  Qed.

  Lemma rleEmpty m o u cs:
    Substep m o u (Rle None) cs -> u = M.empty _ /\ cs = M.empty _.
  Proof.
    clear;
    intros.
    inversion H; intuition.
  Qed.

  Lemma methEmpty m o u cs:
    Substep m o u (Meth None) cs -> u = M.empty _ /\ cs = M.empty _.
  Proof.
    clear;
    intros.
    inversion H; intuition.
  Qed.

  Theorem decomposition':
    forall s sig, Behavior imp s sig ->
                  exists sigSpec, Behavior spec (theta s) sigSpec /\
                                  equivalentLabelSeq (liftToMap1 p) sig sigSpec.
  Proof.
    intros.
    dependent induction H.
    dependent induction HMultistepBeh; subst.
    - exists nil; rewrite thetaInit; repeat constructor.
    - specialize (IHHMultistepBeh specRegsCanCombine substepMethMap substepRuleMap
                                  callSubset defSubset thetaInit eq_refl).
      clear defSubset0 callSubset0 thetaInit0
            substepRuleMap0 substepMethMap0 specRegsCanCombine0.
      pose proof (stepMap HStep) as [uSpec [stepSpec upd]].
      destruct IHHMultistepBeh as [sigSpec [behSpec eqv]].
      inversion behSpec; subst.
      pose proof (BehaviorIntro (Multi HMultistepBeh0 stepSpec)) as sth.
      rewrite upd in sth.
      exists (xformLabel n l :: sigSpec).
      constructor.
      + intuition.
      + constructor.
        * unfold equivalentLabel, xformLabel; simpl.
          destruct l; destruct annot; simpl; intuition.
          destruct o; simpl; intuition.
        * intuition.
  Qed.

  Theorem decomposition:
    traceRefines (liftToMap1 p) imp spec.
  Proof.
    unfold traceRefines; intros.
    pose proof (decomposition' H) as [sigSpec beh].
    exists (theta s1); exists sigSpec.
    intuition.
  Qed.
End Decomposition.


Ltac decomposeT t r Hrm Hmm :=
  eapply decomposition with (theta:= t)
                              (ruleMap:= r)
                              (substepRuleMap:= Hrm)
                              (substepMethMap:= Hmm); auto; intros.
    


Definition fbCm := MethodSig "fb"() : Bool.

(* Test below after implementing alpha-renaming *)
(* Definition fbCm := MethodSig ("fb"__ i)() : Bool. *)

Definition ma := MODULE {
                     Register "a" : Bool <- Default

                     with Rule "ra" :=
                       Call vb <- fbCm();
                     Write "a" <- #vb;
                     Retv
                   }.

Definition mb := MODULE {
                     Register "b" : Bool <- true

                     with Method "fb"() : Bool :=
                       (* with Method ("fb"__ i)() : Bool := *)
                       Write "b" <- $$true;
                     Read rb <- "b";
                     Ret #rb
                   }.

Definition mc := MODULE {
                     Register "a" : Bool <- Default
                     with Register "b" : Bool <- true

                     with Rule "ra" :=                           
                       Write "b" <- $$true;
                     Read rb : Bool <- "b";
                     Write "a" <- #rb;
                     Retv
                   }.

Require Import Program.Equality.

Goal forall o u l cs, SubstepFull (ConcatMod ma mb) o u l cs -> Substep mc o u l cs.
Proof.
  intros; simpl in *.
  inversion H; subst; clear H.
  simpl in *.
  inversion HSubstepComb; subst; clear HSubstepComb; simpl in *.
  - inversion HSubstep; subst; clear HSubstep; simpl in *.
    + admit.
    + admit.
    + inversion HInRules; subst; clear HInRules.
      * inversion H; subst; clear H; simpl in *.
        invertActionRep.
        admit.
      * admit.
    + inversion HIn; subst; clear HIn; simpl in *.
      invertActionRep.
      apply SingleMeth.
      constructor.
      simpl in *.
      * repeat invertAction HAction.
        inv HAction.
        inversion HAction.
        destruct HAction.
      simpl in *.
      dependent induction HAction; subst.
    inversion HAction.
  inversion 
  
  
  Inductive 
    :
      StepComb u (getLabel l cs)
  | SCComb
      u1 l1 u2 l2
      (HSC1: StepComb u1 l1)
      (HSC2: StepComb u2 l2)
      (HRegsDisj: M.Disj u1 u2)
      (HLabelsComb: CanCombineLabel l1 l2):
      StepComb (M.union u1 u2) (mergeLabel l1 l2).

  Inductive SubstepOp: UpdatesT -> UnitLabel -> MethsT -> Prop :=
  | SSSEmptyRule:
      SubstepOp (M.empty _) (Rle None) (M.empty _)
  | SSSEmptyMeth:
      SubstepOp (M.empty _) (Meth None) (M.empty _)
  | SSSRule:
      forall k (a: Action Void)
             (HInRules: List.In {| attrName := k; attrType := a |} (getRules m))
             u cs (HAction: SemActionOp (a type) u cs WO),
        SubstepOp u (Rle (Some k)) cs
  | SSSMeth:
      forall (f: DefMethT)
             (HIn: In f (getDefsBodies m))
             (HNotIn: ~ In (attrName f) (getCalls m))
             u cs argV retV
             (HAction: SemActionOp ((projT2 (attrType f)) type argV) u cs retV),
        SubstepOp u (Meth (Some (f :: (existT _ _ (argV, retV)))%struct)) cs.

  Inductive SubstepsOp: UpdatesT -> LabelT -> Prop :=
  | SSSNil:
      SubstepsOp (M.empty _) emptyMethLabel
  | SSSCons:
      forall pu pl,
        SubstepsOp pu pl ->
        forall nu nl,
          CanCombineUL pu nu pl nl ->
          SubstepOp nu nl ->
          SubstepsOp (M.union pu nu) (mergeLabel nl pl).

  Inductive StepOp: UpdatesT -> LabelT -> Prop :=
  | StepOpIntro: forall u l (HSubSteps: SubstepsOp u l),
      StepOp u l.

End GivenModule.

Ltac invertActionOp H := apply inversionSemActionOp in H; simpl in H; dest; try subst.
Ltac invertActionOpFirst :=
  match goal with
  | [H: SemActionOp _ _ _ _ _ _ |- _] => invertActionOp H
  end.
Ltac invertActionOpRep :=
  repeat
    match goal with
    | [H: SemActionOp _ _ _ _ _ _ |- _] => invertActionOp H
    | [H: if ?c
          then
            SemActionOp _ _ _ _ _ _ /\ _ /\ _ /\ _
          else
            SemActionOp _ _ _ _ _ _ /\ _ /\ _ /\ _ |- _] =>
      let ic := fresh "ic" in
      (remember c as ic; destruct ic; dest; subst)
    end.

Section Facts.
  Variable m: Modules.

  Lemma semActionOp_calls:
    forall o {retK} (a: ActionT type retK) u cs retv,
      SemActionOp m o a u cs retv ->
      M.KeysDisj cs (getDefs m).
  Proof.
    induction 1; simpl; intros; subst; auto.
    - apply M.KeysDisj_add; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_union; auto.
    - apply M.KeysDisj_empty.
  Qed.

  Lemma substepOp_calls:
    forall o u l,
      SubstepOp m o u l ->
      M.KeysDisj (calls l) (getDefs m).
  Proof.
    induction 1; simpl; intros.
    - apply M.KeysDisj_empty.
    - apply M.KeysDisj_empty.
    - eapply semActionOp_calls; exact HAction.
    - eapply semActionOp_calls; exact HAction.
  Qed.

  Lemma substepsOp_calls:
    forall o u l,
      SubstepsOp m o u l ->
      M.KeysDisj (calls l) (getDefs m).
  Proof.
    induction 1; simpl; intros.
    - apply M.KeysDisj_empty.
    - apply substepOp_calls in H1.
      destruct nl, pl; simpl in *.
      apply M.KeysDisj_union; auto.
  Qed.

  Lemma stepOp_calls:
    forall o u l,
      StepOp m o u l ->
      M.KeysDisj (calls l) (getDefs m).
  Proof. induction 1; eapply substepsOp_calls; eauto. Qed.

End Facts.

Require Import Wf.

Section Consistency.
  Variable m: Modules.

  Hypothesis (Hwfm: WfModules type m).

  Lemma substepsInd_implies_substepOp:
    forall o u l,
      SubstepsInd m o u l ->
      wellHidden m (hide l) ->
      SubstepsOp m o u (hide l).
  Proof.
    induction 1; simpl; intros; subst; [apply SSSNil|].
    admit.
  Qed.

  Lemma step_implies_StepOp:
    forall o u l,
      Step m o u l -> StepOp m o u l.
  Proof.
    intros; apply step_consistent in H; inv H.
    constructor.
    apply substepsInd_implies_substepOp; auto.
  Qed.
    
End Consistency.

*)