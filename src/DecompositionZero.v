Require Import Bool List String Structures.Equalities FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax Semantics SemFacts Equiv.

Set Implicit Arguments.

Section Decomposition.
  Variable imp spec: Modules.
  Variable theta: RegsT -> RegsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).
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

  Definition liftP meth :=
    match meth with
      | (n :: t)%struct => match p n t with
                             | None => None
                             | Some v => Some (n :: v)%struct
                           end
    end.

  Definition ruleMapEmpty o u cs (s: Substep imp o u (Rle None) cs):
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

  Definition methMapEmpty o u cs (s: Substep imp o u (Meth None) cs):
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

  Theorem substepMethEmpty o u f cs (s: Substep imp o u (Meth f) cs):
    u = M.empty _ /\ cs = M.empty _ /\ f = None.
  Proof.
    inversion s; eauto; exfalso.
    rewrite defsImpZero in HIn.
    intuition.
  Qed.

  Definition substepMethMap o u f cs (s: Substep imp o u (Meth (Some f)) cs):
    exists uSpec,
      Substep spec (theta o) uSpec (Meth (liftP f)) (liftToMap1 p cs) /\
      M.union uSpec (theta o) = theta (M.union u o).
  Proof.
    refine (ex_intro _ (M.empty _) _).
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
                    exists uSpec,
                      Substep spec (theta o) uSpec (xformUnitAnnot o rm) (liftToMap1 p cs) /\
                      M.union uSpec (theta o) = theta (M.union u o) with
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
    apply step_zero in s; auto; dest.
    destruct l; simpl in *.
    pose proof (substepMap reachO H0); dest.
    exists x.
    apply substepZero_imp_step in H1; auto.
    repeat (try constructor; auto).
    rewrite H.
    rewrite liftToMap1_empty.
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

  Theorem decompositionZero:
    traceRefines (liftToMap1 p) imp spec.
  Proof.
    unfold traceRefines; intros.
    pose proof (decompositionZero' H) as [sigSpec beh].
    exists (theta s1); exists sigSpec.
    intuition.
  Qed.
End Decomposition.

Section ThetaRel.
  Variable imp spec: Modules.
  Variable thetaR: RegsT -> RegsT -> Prop.
  Variable ruleMap: RegsT -> string -> option string.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).
  Variable thetaInit: thetaR (initRegs (getRegInits imp)) (initRegs (getRegInits spec)).
  Variable defsImpZero: getDefsBodies imp = nil.
  Variable defsSpecZero: getDefsBodies spec = nil.

  Variable substepRuleMap:
    forall oImp uImp rule csImp
           (Hreach: reachable oImp imp),
      Substep imp oImp uImp (Rle (Some rule)) csImp ->
      forall oSpec,
        thetaR oImp oSpec ->
        exists uSpec,
          Substep spec oSpec uSpec (Rle (ruleMap oImp rule)) (liftToMap1 p csImp) /\
          thetaR (M.union uImp oImp) (M.union uSpec oSpec).

  Definition liftPR meth :=
    match meth with
    | (n :: t)%struct => match p n t with
                         | None => None
                         | Some v => Some (n :: v)%struct
                         end
    end.

  Definition xformLabelR o l :=
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

  Lemma stepMapR:
    forall o (reachO: reachable o imp)
           u l (s: Step imp o u l) oSpec,
      thetaR o oSpec ->
      exists uSpec,
        Step spec oSpec uSpec (xformLabelR o l) /\
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

  Lemma multistepMapR:
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
      apply stepMapR with (oSpec:= puSpec) in HStep; auto;
        [|eexists; constructor; eauto].
      destruct HStep as [uSpec ?]; dest.

      exists (M.union uSpec puSpec), (xformLabelR n l :: pll).
      repeat split; auto.
      + constructor; auto.
        unfold equivalentLabel, xformLabel; simpl.
        destruct l; destruct annot; simpl; intuition.
        destruct o; simpl; intuition.
      + constructor; auto.
  Qed.

  Theorem decompositionZeroR:
    traceRefines (liftToMap1 p) imp spec.
  Proof.
    unfold traceRefines; intros.
    inv H.
    apply multistepMapR in HMultistepBeh; auto.
    destruct HMultistepBeh as [uSpec [ll ?]]; dest.
    exists uSpec, ll.
    split; auto.
    constructor; auto.
  Qed.

End ThetaRel.

