Require Import List String.
Require Import Program.Equality.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Syntax Semantics Wf Split.

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

  Lemma equivalentLabelSeq_length:
    forall l1 l2 p,
      equivalentLabelSeq p l1 l2 ->
      List.length l1 = List.length l2.
  Proof. induction 1; simpl; intros; auto. Qed.

  Lemma traceRefines_modular:
    forall ma mb mc md p
           (Hacdisj: DisjList (namesOf (getRegInits ma))
                              (namesOf (getRegInits mc)))
           (Hacval: ValidRegsModules type (ConcatMod ma mc))
           (Hbddisj: DisjList (namesOf (getRegInits mb))
                              (namesOf (getRegInits md)))
           (Hbdval: ValidRegsModules type (ConcatMod mb md))
           (Hpunion: forall m1 m2, M.union (p m1) (p m2) =
                                   p (M.union m1 m2))
           (Hpsub: forall m1 m2, M.subtractKV signIsEq (p m1) (p m2) =
                                 p (M.subtractKV signIsEq m1 m2)),
      traceRefines p ma mb ->
      traceRefines p mc md ->
      traceRefines p (ConcatMod ma mc) (ConcatMod mb md).
  Proof.
    unfold traceRefines; intros.
    apply behavior_split in H1; auto.
    destruct H1 as [sa [lsa [sc [lsc ?]]]]; dest; subst.
    specialize (H _ _ H1).
    destruct H as [sb [lsb [? ?]]].
    specialize (H0 _ _ H2).
    destruct H0 as [sd [lsd [? ?]]].

    exists (M.union sb sd).
    exists (composeLabels lsb lsd).
    split; auto.
    - apply behavior_modular; auto.
      apply equivalentLabelSeq_length in H3.
      apply equivalentLabelSeq_length in H4.
      intuition.
    - apply composeLabels_modular; auto.
  Qed.
  
End Facts.

