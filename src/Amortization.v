Require Import Bool List String Omega.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.
Require Import Kami.ModularFacts Kami.RefinementFacts.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** Extension of the restrict notion *)

Definition restrictLabel (l: LabelT) (d: list string): LabelT :=
  {| defs := M.restrict (defs l) d;
     calls := M.restrict (calls l) d;
     annot := annot l |}.

Definition restrictLabelSeq (ll: LabelSeqT) (d: list string): LabelSeqT :=
  map (fun l => restrictLabel l d) ll.

Lemma restrictLabelSeq_nil:
  forall ll d, restrictLabelSeq ll d = nil -> ll = nil.
Proof.
  induction ll; simpl; intros; auto; inv H.
Qed.

(** * Notion of amortization *)

Inductive AmortizedSeq: LabelSeqT (* amortization *) -> LabelSeqT -> LabelSeqT -> Prop :=
| AmortizedNil: AmortizedSeq nil nil nil
| AmortizedPrd:
    forall amt ll1 ll2,
      AmortizedSeq amt ll1 ll2 ->
      forall l1, AmortizedSeq (amt ++ [l1]) (l1 :: ll1) (emptyMethLabel :: ll2)
| AmortizedCsm:
    forall amt l2 ll1 ll2,
      AmortizedSeq (l2 :: amt) ll1 ll2 ->
      AmortizedSeq amt (emptyMethLabel :: ll1) (l2 :: ll2)
| AmortizedBoth:
    forall amt l2 ll1 ll2,
      AmortizedSeq (l2 :: amt) ll1 ll2 ->
      forall l1, AmortizedSeq (amt ++ [l1]) (l1 :: ll1) (l2 :: ll2)
| AmortizedNone:
    forall ll1 ll2,
      AmortizedSeq nil ll1 ll2 ->
      forall l, AmortizedSeq nil (l :: ll1) (l :: ll2).

Section AboutCertainMethods.
  Variable p: MethsT -> MethsT.
  Variable fs: list string.

  Definition EquivalentLabelWithout l1 l2 :=
    p (defs l1) = defs l2 /\
    p (M.restrict (calls l1) fs) = M.restrict (calls l2) fs /\
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

  Definition traceRefinesAmort m1 m2 :=
    forall s1 sig1,
      Behavior m1 s1 sig1 ->
      exists s2 sig2,
        Behavior m2 s2 sig2 /\
        EquivalentLabelSeqWithout sig1 sig2 /\
        exists amt, AmortizedSeq amt (restrictLabelSeq sig1 fs) (restrictLabelSeq sig2 fs).

End AboutCertainMethods.

Notation "ma <<~[ p ]{ fs } mb" :=
  (traceRefinesAmort (liftToMap1 p) fs ma mb)
    (at level 100, format "ma  <<~[  p  ]{  fs  }  mb").

Section TwoModuleFacts.
  Variables (m1 m2: Modules).
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hddisj: DisjList (getDefs m1) (getDefs m2))
             (Hcdisj: DisjList (getCalls m1) (getCalls m2)).

  Lemma equivalentLabelSeqWithout_CanCombineLabelSeq:
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
      [inv H2; inv H0; destruct lsb; inv H; inv H1; auto|].

    destruct lsa as [|la lsa]; inv H0.
    destruct lsb as [|lb lsb]; inv H.
    destruct ll2 as [|l2 ll2]; inv H1.
    inv H2; inv H3.
    specialize (IHll1 _ _ _ H4 H7 H8 _ _ HMultistep HMultistep0);
      clear H4 H7 H8 HMultistep HMultistep0.
    split; auto.

    repeat split.
    - eapply M.DisjList_KeysSubset_Disj.
      + exact Hddisj.
      + eapply step_defs_in; eauto.
      + eapply step_defs_in; eauto.
    - eapply M.DisjList_KeysSubset_Disj.
      + exact Hcdisj.
      + eapply step_calls_in; eauto.
      + eapply step_calls_in; eauto.
    - inv H0; inv H9; inv H11; dest.
      destruct (annot l1), (annot l2), (annot la), (annot lb); auto.
  Qed.

End TwoModuleFacts.
  
Section Modularity.
  Variables (m1 m2 ctxt: Modules).
  Variable fs: list string.
  
  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hwfc: ModEquiv type typeUT ctxt)

             (Hrdisj: DisjList (namesOf (getRegInits m1)) (namesOf (getRegInits m2)))
             (Hddisj: DisjList (getDefs m1) (getDefs m2))
             (Hcdisj: DisjList (getCalls m1) (getCalls m2))
             (Hvr1: ValidRegsModules type m1)
             (Hvr2: ValidRegsModules type m2)

             (Hemc: getExtMeths ctxt = fs)
             (Hvrc: ValidRegsModules type ctxt).

  Theorem traceRefinesAmort_modular:
    forall vp,
      traceRefinesAmort (liftToMap1 vp) fs m1 m2 ->
      (m1 ++ ctxt)%kami <<=[vp] (m2 ++ ctxt)%kami.
  Proof.
  Admitted.

End Modularity.

