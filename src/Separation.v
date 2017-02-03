Require Import Bool List String Omega.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.
Require Import Kami.ModularFacts Kami.RefinementFacts.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** Extension of the complement notion *)

Definition complementLabel (l: LabelT) (d: list string): LabelT :=
  {| defs := M.complement (defs l) d;
     calls := M.complement (calls l) d;
     annot := annot l |}.

Definition complementLabelSeq (ll: LabelSeqT) (d: list string): LabelSeqT :=
  map (fun l => complementLabel l d) ll.

(** The notion of dual *)

Definition Dual (l1 l2: LabelT): Prop :=
  defs l1 = calls l2 /\ calls l1 = defs l2.

Inductive DualSeq: LabelSeqT -> LabelSeqT -> Prop :=
| DualSeqNil: DualSeq nil nil
| DualSeqCons:
    forall ll1 ll2,
      DualSeq ll1 ll2 ->
      forall l1 l2,
        Dual l1 l2 -> DualSeq (l1 :: ll1) (l2 :: ll2).

Definition DualComm (q: LabelSeqT -> LabelSeqT) :=
  forall ll1 ll2,
    DualSeq ll1 ll2 ->
    DualSeq (q ll1) (q ll2).

Section AboutCertainMethods.
  Variable p: MethsT -> MethsT.
  Variable fs: list string.

  Definition EquivalentLabelWithout l1 l2 :=
    p (defs l1) = defs l2 /\
    p (M.complement (calls l1) fs) = M.complement (calls l2) fs /\
    match annot l1, annot l2 with
    | Some _, Some _ => True
    | None, None => True
    | _, _ => False
    end.

  Inductive EquivalentLabelSeqWithout: LabelSeqT -> LabelSeqT -> Prop :=
  | ELSWNil: EquivalentLabelSeqWithout nil nil
  | ELSWCons:
      forall ll1 ll2,
        EquivalentLabelSeqWithout ll1 ll2 ->
        forall l1 l2,
          EquivalentLabelWithout l1 l2 ->
          EquivalentLabelSeqWithout (l1 :: ll1) (l2 :: ll2).

  Definition traceRefinesSep q m1 m2 :=
    forall s1 sig1,
      Behavior m1 s1 sig1 ->
      exists s2 sig2, Behavior m2 s2 sig2 /\
                      EquivalentLabelSeqWithout sig1 sig2 /\
                      q (complementLabelSeq sig1 fs) = complementLabelSeq sig2 fs.

End AboutCertainMethods.

Lemma equivalentLabelSeqWithout_CanCombineLabelSeq:
  forall m1 m2
         (Hwf1: ModEquiv type typeUT m1)
         (Hwf2: ModEquiv type typeUT m2),
    DisjList (getDefs m1) (getDefs m2) ->
    DisjList (getCalls m1) (getCalls m2) ->
    forall p fs ll1 ll2 lsa lsb,
      CanCombineLabelSeq lsa lsb ->
      EquivalentLabelSeqWithout p fs lsa ll1 ->
      EquivalentLabelSeqWithout p fs lsb ll2 ->
      forall s1 s2,
        Multistep m1 (initRegs (getRegInits m1)) s1 ll1 ->
        Multistep m2 (initRegs (getRegInits m2)) s2 ll2 ->
        CanCombineLabelSeq ll1 ll2.
Proof.
  induction ll1 as [|l1 ll1]; simpl; intros;
    [inv H4; inv H2; destruct lsb; inv H1; inv H3; auto|].

  destruct lsa as [|la lsa]; inv H2.
  destruct lsb as [|lb lsb]; inv H1.
  destruct ll2 as [|l2 ll2]; inv H3.
  inv H4; inv H5.
  specialize (IHll1 _ _ _ H6 H9 H10 _ _ HMultistep HMultistep0);
    clear H6 H9 H10 HMultistep HMultistep0.
  split; auto.

  repeat split.
  - eapply M.DisjList_KeysSubset_Disj.
    + exact H.
    + eapply step_defs_in; eauto.
    + eapply step_defs_in; eauto.
  - eapply M.DisjList_KeysSubset_Disj.
    + exact H0.
    + eapply step_calls_in; eauto.
    + eapply step_calls_in; eauto.
  - inv H2; inv H11; inv H13; dest.
    destruct (annot l1), (annot l2), (annot la), (annot lb); auto.
Qed.

Section Modularity.
  
  Variables (m1 m2 m3 m4: Modules).
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hwf3: ModEquiv type typeUT m3)
             (Hwf4: ModEquiv type typeUT m4)
             (Hrdisj12: DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2)))
             (Hrdisj34: DisjList (namesOf (getRegInits m3)) (namesOf (getRegInits m4)))
             (Hddisj12: DisjList (getDefs m1) (getDefs m2))
             (Hcdisj12: DisjList (getCalls m1) (getCalls m2))
             (Hddisj34: DisjList (getDefs m3) (getDefs m4))
             (Hcdisj34: DisjList (getCalls m3) (getCalls m4))
             (Hvr12: ValidRegsModules type (m1 ++ m2)%kami)
             (Hvr34: ValidRegsModules type (m3 ++ m4)%kami).

  Section PartiallyNonInteracting.
    Variable fs: list string.
    Hypothesis (Hni1: forall f, In f (getCalls m1) -> In f (getDefs m2) -> In f fs)
               (Hni2: forall f, In f (getDefs m1) -> In f (getCalls m2) -> In f fs).

    Theorem traceRefinesSep_modular:
      forall vp q,
        DualComm q ->
        traceRefinesSep (liftToMap1 vp) fs q m1 m3 ->
        traceRefinesSep (liftToMap1 vp) fs q m2 m4 ->
        DisjList (getExtMeths (m1 ++ m2)%kami) fs ->
        (m1 ++ m2)%kami <<=[vp] (m3 ++ m4)%kami.
    Proof.
      unfold traceRefines; intros.
      
      apply behavior_split in H3; auto.
      destruct H3 as [sa [lsa [sb [lsb ?]]]]; dest; subst.

      specialize (H0 _ _ H3); clear H3; destruct H0 as [s3 [ll3 ?]]; dest.
      specialize (H1 _ _ H4); clear H4; destruct H1 as [s4 [ll4 ?]]; dest.

      exists (M.union s3 s4).
      exists (composeLabels ll3 ll4).

      split.
      - apply behavior_modular; auto.
        + inv H0; inv H1; eauto using equivalentLabelSeqWithout_CanCombineLabelSeq.
        + admit.
      - admit.
    Admitted.

  End PartiallyNonInteracting.

End Modularity.

