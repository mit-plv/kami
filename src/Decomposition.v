Require Import Bool List String Structures.Equalities FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax Semantics SemFacts.

Set Implicit Arguments.

Section Decomposition.
  Variable imp spec: Modules.
  Variable theta: RegsT -> RegsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).
  Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).
  Variable defSubset: forall f, In f (getDefs spec) -> In f (getDefs imp).
  Variable callSubset: forall f, In f (getCalls spec) -> In f (getCalls imp).

  Variable substepRuleMap:
    forall oImp uImp rule csImp,
      Substep imp oImp uImp (Rle (Some rule)) csImp ->
      { uSpec |
        Substep spec (theta oImp) uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
        forall o, M.union uSpec (theta o) = theta (M.union uImp o) }.

  Definition liftP meth :=
    match meth with
      | (n :: t)%struct => match p n t with
                             | None => None
                             | Some v => Some (n :: v)%struct
                           end
    end.

  Variable substepMethMap:
    forall oImp uImp meth csImp,
      Substep imp oImp uImp (Meth (Some meth)) csImp ->
      { uSpec |
        Substep spec (theta oImp) uSpec (Meth (liftP meth)) (liftToMap1 p csImp) /\
        forall o, M.union uSpec (theta o) = theta (M.union uImp o) }.

  Definition ruleMapEmpty o u cs (s: Substep imp o u (Rle None) cs):
    { uSpec |
      Substep spec (theta o) uSpec (Rle None) (liftToMap1 p cs) /\
      forall o', M.union uSpec (theta o') = theta (M.union u o') }.
  Proof.
    refine (exist _ (M.empty _) _);
    abstract (
        inversion s; subst; rewrite liftToMap1Empty;
        constructor;
        [ constructor |
          repeat rewrite M.union_empty_L; intuition]).
  Defined.

  Definition methMapEmpty o u cs (s: Substep imp o u (Meth None) cs):
    { uSpec |
      Substep spec (theta o) uSpec (Meth None) (liftToMap1 p cs) /\
      forall o', M.union uSpec (theta o') = theta (M.union u o') }.
  Proof.
    refine (exist _ (M.empty _) _);
    abstract (
        inversion s; subst; rewrite liftToMap1Empty;
        constructor;
        [ constructor |
          repeat rewrite M.union_empty_L; intuition]).
  Defined.

  Definition xformUnitAnnot o rm :=
    match rm with
      | Rle (Some rule) => Rle (ruleMap o rule)
      | Meth (Some meth) => Meth (liftP meth)
      | Rle None => Rle None
      | Meth None => Meth None
    end.

  Definition substepMap o u rm cs (s: Substep imp o u rm cs) :=
    match rm return Substep imp o u rm cs ->
                    { uSpec |
                      Substep spec (theta o) uSpec (xformUnitAnnot o rm) (liftToMap1 p cs) /\
                      forall o', M.union uSpec (theta o') = theta (M.union u o') } with
      | Rle (Some rule) => fun s => substepRuleMap s
      | Meth (Some meth) => fun s => substepMethMap s
      | Rle None => fun s => ruleMapEmpty s
      | Meth None => fun s => methMapEmpty s
    end s.

  Definition xformSubstepRec o (s': SubstepRec imp o) :=
    match s' with
      | {| upd := u; unitAnnot := rm; cms := cs; substep := s |} =>
        match substepMap s with
          | exist uSpec (conj sSpec _) =>
            {| upd := uSpec; unitAnnot := xformUnitAnnot o rm;
               cms := liftToMap1 p cs; substep := sSpec |}
        end
    end.

  Variable specCanCombine:
    forall o (s1 s2: SubstepRec imp o),
      canCombine s1 s2 -> canCombine (xformSubstepRec s1) (xformSubstepRec s2).

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
    intros; M.mind l1.
    - rewrite M.subtractKV_empty_1.
      rewrite liftToMap1Empty.
      rewrite M.subtractKV_empty_1.
      reflexivity.
    - admit.
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
    liftToMap1 p (M.union l1 l2) = M.union (liftToMap1 p l1) (liftToMap1 p l2).
  Proof.
    admit.
  Qed.      
  
  Theorem xformLabelAddLabelCommute l1 l2:
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
    
  Theorem xformLabelFoldCommute o ss:
    xformLabel o (foldSSLabel (o := o) ss) = foldSSLabel (map (@xformSubstepRec _) ss).
  Proof.
    induction ss; simpl in *; try rewrite liftToMap1Empty.
    - reflexivity.
    - unfold addLabelLeft in *.
      rewrite xformLabelAddLabelCommute.
      f_equal; intuition.
      apply xformLabelGetSLabelCommute.
  Qed.    
  
  Theorem xformLabelHide o:
    forall(ss: Substeps imp o) (ssGd: wellHidden imp (hide (foldSSLabel ss))),
      hide (foldSSLabel (map (@xformSubstepRec _) ss)) =
      xformLabel o (hide (foldSSLabel ss)).
  Proof.
    intros.
    rewrite xformLabelHideCommute.
    f_equal.
    apply eq_sym; apply xformLabelFoldCommute.
    apply (wellHiddenEq1 (m := imp)).
    - unfold M.KeysSubset; apply (staticDynDefsSubsteps ss).
    - unfold M.KeysSubset; apply (staticDynCallsSubsteps ss).
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
    - specialize (IHHMultistepBeh specCanCombine substepMethMap substepRuleMap
                                  callSubset defSubset thetaInit eq_refl).
      clear defSubset0 callSubset0 thetaInit0
            substepRuleMap0 substepMethMap0 specCanCombine0.
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

