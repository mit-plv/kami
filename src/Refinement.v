Require Import List String.
Require Import Program.Equality Program.Basics Classes.Morphisms.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Syntax Semantics SemFacts Wf Split.

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

  Section Modularity.
    Variables (ma mb mc md: Modules)
              (p: MethsT -> MethsT).

    Hypotheses (Hacdisj: DisjList (namesOf (getRegInits ma))
                                  (namesOf (getRegInits mc)))
               (Hacval: ValidRegsModules type (ConcatMod ma mc))
               (Hdisjregs: DisjList (namesOf (getRegInits mb))
                                    (namesOf (getRegInits md)))
               (Hdisjdefs: DisjList (getDefs mb) (getDefs md))
               (Hdisjcalls: DisjList (getCalls mb) (getCalls md))
               (Hbdval: ValidRegsModules type (ConcatMod mb md)).

    Hypotheses (Hpunion: forall m1 m2, M.union (p m1) (p m2) = p (M.union m1 m2))
               (Hpsub: forall m1 m2, M.subtractKV signIsEq (p m1) (p m2) =
                                     p (M.subtractKV signIsEq m1 m2))
               (Hpcomb: Proper (equivalentLabel p ==> equivalentLabel p ==> impl)
                               CanCombineLabel).

    Definition NonInteracting (m1 m2: Modules) :=
      DisjList (getDefs m1) (getCalls m2) /\
      DisjList (getCalls m1) (getDefs m2).

    Lemma nonInteracting_implies_wellHiddenModular:
      forall m1 m2,
        NonInteracting m1 m2 ->
        WellHiddenModular m1 m2.
    Proof.
      admit.
    Qed.

    Lemma traceRefines_modular_noninteracting:
      NonInteracting mb md ->
      traceRefines p ma mb ->
      traceRefines p mc md ->
      traceRefines p (ConcatMod ma mc) (ConcatMod mb md).
    Proof.
      unfold traceRefines; intros.
      apply behavior_split in H2; auto.
      destruct H2 as [sa [lsa [sc [lsc ?]]]]; dest; subst.
      specialize (H0 _ _ H2).
      destruct H0 as [sb [lsb [? ?]]].
      specialize (H1 _ _ H3).
      destruct H1 as [sd [lsd [? ?]]].

      exists (M.union sb sd).
      exists (composeLabels lsb lsd).
      split; auto.
      - apply behavior_modular; auto.
        + apply nonInteracting_implies_wellHiddenModular; auto.
        + eapply equivalentLabelSeq_CanCombineLabelSeq; eauto.
      - apply composeLabels_modular; auto.
    Qed.

  End Modularity.
  
End Facts.

