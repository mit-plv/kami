Require Import Bool List String Structures.Equalities FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax Semantics SemFacts Equiv.

Set Implicit Arguments.

Section EmptyDefs.
  Variable m: Modules.
  Variable o: RegsT.
  Variable defsZero: getDefsBodies m = nil.
  
  Theorem substepsIndZero u l:
    SubstepsInd m o u l ->
    defs l = M.empty _ /\
    Substep m o u match annot l with
                    | None => Meth None
                    | Some r => Rle r
                  end (calls l).
  Proof.
    intros si.
    dependent induction si.
    - constructor; econstructor; eauto.
    - dest; destruct l; subst.
      inv H; simpl in *; repeat rewrite M.union_empty_L; constructor; auto;
      repeat rewrite M.union_empty_R; unfold CanCombineUUL in *; simpl in *; dest.
      + destruct annot; intuition.
        inversion H4.
        econstructor; eauto.
      + destruct annot; auto.
      + destruct annot.
        * intuition.
        * inversion H4.
          rewrite M.union_empty_L, M.union_empty_R.
          econstructor; eauto.
      + rewrite defsZero in *.
        intuition.
      + rewrite defsZero in *.
        intuition.
  Qed.

  Theorem substepsIndZeroHide u l:
    SubstepsInd m o u l ->
    hide l = l.
  Proof.
    intros si.
    apply substepsIndZero in si; dest.
    unfold hide; destruct l; simpl in *; subst.
    rewrite M.subtractKV_empty_1.
    rewrite M.subtractKV_empty_2.
    reflexivity.
  Qed.

  Theorem stepZero u l:
    Step m o u l ->
    defs l = M.empty _ /\
    Substep m o u match annot l with
                    | None => Meth None
                    | Some r => Rle r
                  end (calls l).
  Proof.
    intros si.
    apply step_consistent in si.
    inv si.
    apply substepsIndZero.
    rewrite substepsIndZeroHide with (u := u); auto.
  Qed.

  Theorem substepZero_imp_step u a cs:
    Substep m o u a cs ->
    Step m o u (getLabel a cs).
  Proof.
    intros si.
    assert (sth: substepsComb ({| substep := si |} :: nil)).
    { constructor 2.
      constructor.
      intuition.
    }
    pose proof (StepIntro sth); simpl in *.
    unfold addLabelLeft in H;
      unfold getSLabel in H.
    assert (ua: unitAnnot
                  {| upd := u; unitAnnot := a; cms := cs; substep := si |} = a) by reflexivity.
    rewrite ua in H.
    assert (ub: cms
                  {| upd := u; unitAnnot := a; cms := cs; substep := si |} = cs) by reflexivity.
    rewrite ub in H.
    clear ua ub.
    assert (st: mergeLabel (getLabel a cs) {| annot := None;
                                          defs := M.empty _;
                                          calls := M.empty _ |} = getLabel a cs).
    { simpl.
      destruct a.
      - repeat rewrite M.union_empty_L, M.union_empty_R.
        reflexivity.
      - destruct o0;
        try destruct a; repeat rewrite M.union_empty_L; repeat rewrite M.union_empty_R;
        try reflexivity.
    }
    rewrite st in H; clear st.
    rewrite M.union_empty_L in H.
    assert (s: hide (getLabel a cs) = getLabel a cs).
    { clear H sth.
      unfold hide.
      simpl.
      destruct a; destruct o0; try destruct a; repeat rewrite M.subtractKV_empty_1;
      repeat rewrite M.subtractKV_empty_2; try reflexivity.
      inv si.
      rewrite defsZero in HIn.
      intuition.
    }
    rewrite s in *; clear s.
    assert (t: wellHidden m (getLabel a cs)).
    { clear sth H.
      unfold wellHidden.
      simpl in *.
      unfold getDefs.
      rewrite defsZero.
      simpl in *.
      destruct a;
      constructor;
      destruct o0; try destruct a;
      try apply M.KeysDisj_empty; try apply M.KeysDisj_nil.
      inversion si.
      rewrite defsZero in HIn.
      intuition.
    }
    apply H; intuition.
  Qed.
End EmptyDefs.

Section Decomposition.
  Variable imp spec: Modules.
  Variable theta: RegsT -> RegsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).
  Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).
  Variable defsImpZero: getDefsBodies imp = nil.
  Variable defsSpecZero: getDefsBodies spec = nil.

  Definition reachable o m := exists sigma, Behavior m o sigma.
  
  Variable substepRuleMap:
    forall oImp uImp rule csImp,
      reachable oImp imp ->
      Substep imp oImp uImp (Rle (Some rule)) csImp ->
      { uSpec |
        Substep spec (theta oImp) uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
        M.union uSpec (theta oImp) = theta (M.union uImp oImp) }.

  Definition liftP meth :=
    match meth with
      | (n :: t)%struct => match p n t with
                             | None => None
                             | Some v => Some (n :: v)%struct
                           end
    end.

  Definition ruleMapEmpty o u cs (s: Substep imp o u (Rle None) cs):
    { uSpec |
      Substep spec (theta o) uSpec (Rle None) (liftToMap1 p cs) /\
      M.union uSpec (theta o) = theta (M.union u o) }.
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
      M.union uSpec (theta o) = theta (M.union u o) }.
  Proof.
    refine (exist _ (M.empty _) _);
    abstract (
        inversion s; subst; rewrite liftToMap1Empty;
        constructor;
        [ constructor |
          repeat rewrite M.union_empty_L; intuition]).
  Defined.

  Theorem substepMethEmpty o u f cs (s: Substep imp o u (Meth f) cs):
    u = M.empty _ /\ cs = M.empty _ /\ f = None.
  Proof.
    inversion s; eauto; exfalso.
    rewrite defsImpZero in HIn.
    intuition.
  Qed.

  Definition substepMethMap o u f cs (s: Substep imp o u (Meth (Some f)) cs):
    { uSpec |
      Substep spec (theta o) uSpec (Meth (liftP f)) (liftToMap1 p cs) /\
      M.union uSpec (theta o) = theta (M.union u o) }.
  Proof.
    refine (exist _ (M.empty _) _).
    abstract (apply substepMethEmpty in s; dest; subst; discriminate).
  Defined.

  Definition xformUnitAnnot o rm :=
    match rm with
      | Rle (Some rule) => Rle (ruleMap o rule)
      | Meth (Some meth) => Meth (liftP meth)
      | Rle None => Rle None
      | Meth None => Meth None
    end.

  Definition substepMap o u rm cs reachO (s: Substep imp o u rm cs) :=
    match rm return Substep imp o u rm cs ->
                    { uSpec |
                      Substep spec (theta o) uSpec (xformUnitAnnot o rm) (liftToMap1 p cs) /\
                      M.union uSpec (theta o) = theta (M.union u o) } with
      | Rle (Some rule) => fun s => substepRuleMap reachO s
      | Meth (Some meth) => fun s => substepMethMap s
      | Rle None => fun s => ruleMapEmpty s
      | Meth None => fun s => methMapEmpty s
    end s.

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

  Theorem stepMap o (reachO: reachable o imp) u l (s: Step imp o u l):
    exists uSpec,
      Step spec (theta o) uSpec (xformLabel o l) /\
      M.union uSpec (theta o) = theta (M.union u o).
  Proof.
    apply stepZero in s; auto; dest.
    destruct l; simpl in *.
    pose proof (substepMap reachO H0); dest.
    destruct X; dest.
    exists x.
    apply substepZero_imp_step in H1; auto.
    repeat (try constructor; auto).
    rewrite H.
    rewrite liftToMap1Empty.
    unfold xformUnitAnnot, getLabel; simpl in *.
    destruct annot; auto.
    destruct o0; auto.
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
    - specialize (IHHMultistepBeh thetaInit defsSpecZero substepRuleMap eq_refl).
      assert(reachO: reachable n imp) by (eexists; econstructor; eauto).
      pose proof (stepMap reachO HStep) as [uSpec [stepSpec upd]].
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

Ltac kdecompose t r Hrm Hmm :=
  eapply decomposition with (theta:= t)
                              (ruleMap:= r)
                              (substepRuleMap:= Hrm); auto; intros.
(*
Ltac kdecompose_nodefs t r :=
  apply decomposition_nodefs with (theta:= t) (ruleMap:= r).
*)