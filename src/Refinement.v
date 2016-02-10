Require Import Syntax Semantics String Lib.FMap Program.Equality List.

Set Implicit Arguments.

Section StepToRefinement.
  Variable imp spec: Modules.
  Variable p: MethsT -> MethsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable theta: RegsT -> RegsT.
  Variable thetaInit: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).

  Definition liftPLabel o l :=
    match l with
    | {| annot := a; defs := dfs; calls := clls |} =>
      {| annot := match a with
                  | Some (Some r) => Some (ruleMap o r)
                  | Some None => Some None
                  | None => None
                  end;
         defs := p dfs;
         calls := p clls |}
    end.

  Variable stepMap:
    forall o u l, Step imp o u l ->
             exists uspec, Step spec (theta o) uspec (liftPLabel o l) /\
                      theta (M.union u o) = M.union uspec (theta o).

  Theorem stepRefinement':
    forall s sig, Behavior imp s sig ->
                  exists sigSpec, Behavior spec (theta s) sigSpec /\
                                  equivalentLabelSeq p sig sigSpec.
  Proof.
    intros.
    dependent induction H.
    dependent induction HMultistepBeh; subst.
    - exists nil; rewrite thetaInit; repeat constructor.
    - specialize (IHHMultistepBeh thetaInit stepMap eq_refl).
      pose proof (stepMap HStep) as [uSpec [stepSpec upd]].
      destruct IHHMultistepBeh as [sigSpec [behSpec eqv]].
      inversion behSpec; subst.
      pose proof (BehaviorIntro (Multi HMultistepBeh0 stepSpec)) as sth.
      rewrite <- upd in sth.
      exists (liftPLabel n l :: sigSpec).
      constructor.
      + intuition.
      + constructor.
        * unfold equivalentLabel, liftPLabel; simpl.
          destruct l; destruct annot; simpl; intuition.
          destruct o; simpl; intuition.
        * intuition.
  Qed.

  Theorem stepRefinement: traceRefines p imp spec.
  Proof.
    unfold traceRefines; intros.
    pose proof (stepRefinement' H) as [sigSpec beh].
    exists (theta s1); exists sigSpec.
    intuition.
  Qed.
End StepToRefinement.

Section Facts.

  Lemma traceRefines_trans:
    forall ma mb mc p q,
      traceRefines p ma mb ->
      traceRefines q mb mc ->
      traceRefines (fun f => q (p f)) ma mc.
  Proof.
    admit.
  Qed.
  
End Facts.

