Require Import Bool List String Structures.Equalities FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap.
Require Import Syntax.
Require Export SemanticsExprAction.

Set Implicit Arguments.

(*
 * underscore to separate names only for lemmas and theorems
 * Propositions start with upper case and no underscore
 * Computable definitions start with lower case
 *)

Inductive UnitLabel :=
| Rle: option string -> UnitLabel
| Meth: option (Attribute (sigT SignT)) -> UnitLabel.

Record LabelT := { annot: option (option string);
                   defs: MethsT;
                   calls: MethsT }.

Section GivenModule.
  Variable m: Modules.

  Section GivenOldregs.
    Variable o: RegsT.
    Definition UpdatesT := RegsT.

    Inductive Substep: UpdatesT -> UnitLabel -> MethsT -> Prop :=
    | EmptyRule (HDomainEq: M.KeysEq o (map (@attrName _) (getRegInits m))):
        Substep (M.empty _) (Rle None) (M.empty _)
    | EmptyMeth (HDomainEq: M.KeysEq o (map (@attrName _) (getRegInits m))):
        Substep (M.empty _) (Meth None) (M.empty _)
    | SingleRule k (a: Action Void)
                 (HInRules: List.In {| attrName := k; attrType := a |} (getRules m))
                 (HOldRegs: M.KeysSubset o (map (@attrName _) (getRegInits m)))
                 u cs (HAction: SemAction o (a type) u cs WO):
        Substep u (Rle (Some k)) cs
    | SingleMeth (f: DefMethT)
                 (HIn: In f (getDefsBodies m))
                 u cs argV retV
                 (HOldRegs: M.KeysSubset o (map (@attrName _) (getRegInits m)))
                 (HAction: SemAction o ((projT2 (attrType f)) type argV) u cs retV):
        Substep u
                (Meth (Some {| attrName := attrName f;
                               attrType := (existT _ _ (argV, retV)) |})) cs.

    Record SubstepRec :=
      { upd: UpdatesT;
        unitAnnot: UnitLabel;
        cms: MethsT;
        substep: Substep upd unitAnnot cms }.

    Definition Substeps := list SubstepRec.

    Definition canCombine (s1 s2: SubstepRec) :=
      M.Disj (upd s1) (upd s2) /\
      (forall x y, unitAnnot s1 = Meth (Some x) ->
                   unitAnnot s2 = Meth (Some y) -> attrName x <> attrName y) /\
      (exists x, unitAnnot s1 = Meth x \/ unitAnnot s2 = Meth x) /\
      M.Disj (cms s1) (cms s2).

    Inductive substepsComb: Substeps -> Prop :=
    | NilSubsteps: substepsComb nil
    | AddSubstep (s: SubstepRec) (ss: Substeps):
        substepsComb ss -> (forall s', In s' ss -> canCombine s s') ->
        substepsComb (s :: ss).

    Fixpoint foldSSUpds (ss: Substeps) :=
      match ss with
        | x :: xs => M.union (foldSSUpds xs) (upd x)
        | nil => M.empty _
      end.

    Definition getSLabel (s: SubstepRec) :=
      match s with
        | {| unitAnnot := a; cms := cs |} =>
          match a with
            | Rle x => {| annot := Some x; defs := M.empty _; calls := cs |}
            | Meth None => {| annot := None; defs := M.empty _; calls := cs |}
            | Meth (Some {| attrName := n; attrType := t |}) =>
              {| annot := None; defs := M.add n t (M.empty _); calls := cs |}
          end
      end.

    Definition addLabelLeft' lnew lold :=
      match lnew, lold with
        | {| annot := a'; defs := d'; calls := c' |},
          {| annot := a; defs := d; calls := c |} =>
          {| annot := match a', a with
                        | None, x => x
                        | x, None => x
                        | _, _ => None
                      end; defs := M.union d' d; calls := M.union c' c |}
      end.
    
    Definition addLabelLeft lold s := addLabelLeft' (getSLabel s) lold.

    Fixpoint foldSSLabel (ss: Substeps) :=
      match ss with
        | x :: xs => addLabelLeft (foldSSLabel xs) x
        | nil => {| annot := None; defs := M.empty _; calls := M.empty _ |}
      end.

(*
    Definition getSSLabel (ss: Substeps) :=
      fold_left addLabelLeft ss
                {| annot := None; defs := M.empty _; calls := M.empty _ |}.
*)

    Lemma sigT_eq:
      forall {A} (a: A) (B: A -> Type) (v1 v2: B a),
        existT _ a v1 = existT _ a v2 ->
        v1 = v2.
    Proof. intros; inv H; apply Eqdep.EqdepTheory.inj_pair2 in H1; assumption. Qed.

    Theorem signIsEq :
      forall (l1 l2 : sigT SignT), {l1 = l2} + {l1 <> l2}.
    Proof.
      intros. destruct l1, l2.
      destruct (SignatureT_dec x x0).
      - induction e. destruct x, s, s0.
        destruct (isEq arg t t1). induction e.
        destruct (isEq ret t0 t2). induction e. left. reflexivity.
        right. unfold not. intros. apply sigT_eq in H.
        inversion H. apply n in H1. assumption.
        right. unfold not. intros. apply sigT_eq in H.
        inversion H. apply n in H1. assumption.
      - right. unfold not. intros. inversion H. apply n in H1.
        assumption.
    Qed.

    Definition hide (l: LabelT) :=
      Build_LabelT (annot l) (M.subtractKV signIsEq (defs l) (calls l))
                   (M.subtractKV signIsEq (calls l) (defs l)).

    Definition wellHidden (l: LabelT) := M.KeysDisj (defs l) (getCalls m) /\
                                         M.KeysDisj (calls l) (getDefs m).

    Inductive Step: UpdatesT -> LabelT -> Prop :=
      StepIntro ss (HSubsteps: substepsComb ss)
                (HWellHidden: wellHidden (hide (foldSSLabel ss))) :
        Step (foldSSUpds ss) (hide (foldSSLabel ss)).

    (* Another step semantics based on inductive definitions for Substeps *)
    Definition CanCombineLabel u (l: LabelT) (s: SubstepRec) :=
      M.Disj u (upd s) /\
      M.Disj (calls l) (cms s) /\
      match annot l, unitAnnot s with
        | Some _, Rle (Some _) => False
        | _, Meth (Some a) => ~ M.In (attrName a) (defs l)
        | _, _ => True
      end.

    Inductive SubstepsInd: UpdatesT -> LabelT -> Prop :=
    | SubstepsNil: SubstepsInd (M.empty _)
                               {| annot:= None; defs:= M.empty _; calls:= M.empty _ |}
    | SubstepsCons:
        forall (s: SubstepRec) u l,
          SubstepsInd u l ->
          CanCombineLabel u l s ->
          SubstepsInd (M.union u (upd s)) (addLabelLeft l s).

    Inductive SubstepsIndAnnot: UpdatesT -> LabelT -> list SubstepRec -> Prop :=
    | SubstepsAnnotNil:
        SubstepsIndAnnot (M.empty _)
                         {| annot:= None; defs:= M.empty _; calls:= M.empty _ |} nil
    | SubstepsAnnotCons:
        forall (s: SubstepRec) u l ss,
          SubstepsIndAnnot u l ss ->
          CanCombineLabel u l s ->
          SubstepsIndAnnot (M.union u (upd s)) (addLabelLeft l s) (s :: ss).

    Lemma canCombine_consistent:
      forall s ss,
        (forall s' : SubstepRec, In s' ss -> canCombine s s') <->
        CanCombineLabel (foldSSUpds ss) (foldSSLabel ss) s.
    Proof.
      admit.
    Qed.

    Lemma substeps_annot:
      forall u l,
        SubstepsInd u l ->
        exists ss, SubstepsIndAnnot u l ss /\
                   substepsComb ss /\
                   u = foldSSUpds ss /\ l = foldSSLabel ss.
    Proof.
      induction 1.
      - eexists; repeat split; constructor.
      - destruct IHSubstepsInd as [ss [? [? [? ?]]]]; subst.
        exists (s :: ss); split.
        + constructor; auto.
        + repeat split.
          constructor; auto.
          apply canCombine_consistent; auto.
    Qed.

    Inductive StepInd: UpdatesT -> LabelT -> Prop :=
    | StepIndIntro: forall u l (HSubSteps: SubstepsInd u l)
                           (HWellHidden: wellHidden (hide l)),
                      StepInd u (hide l).

    Lemma step_consistent:
      forall u l, Step u l <-> StepInd u l.
    Proof.
      split; intros.
      - inv H; constructor; auto.
        clear HWellHidden.
        induction HSubsteps; simpl in *; [constructor|].
        constructor; auto.
        apply canCombine_consistent; auto.
      - inv H.
        apply substeps_annot in HSubSteps.
        destruct HSubSteps as [ss [? [? [? ?]]]]; subst.
        constructor; auto.
    Qed.

  End GivenOldregs.

  Inductive Multistep: RegsT -> UpdatesT -> list LabelT -> Prop :=
  | NilMultistep o: Multistep o o nil
  | Multi o a n (HMultistep: Multistep o n a)
          u l (HStep: Step n u l):
      Multistep o (M.union u n) (l :: a).

  Definition initRegs (init: list RegInitT): RegsT :=
    makeMap (fullType type) evalConstFullT init.
  Hint Unfold initRegs.

  Definition LabelSeqT := list LabelT.

  Inductive Behavior: UpdatesT -> LabelSeqT -> Prop :=
  | BehaviorIntro a n (HMultistepBeh: Multistep (initRegs (getRegInits m)) n a):
      Behavior n a.
End GivenModule.

Definition equivalentLabel p l1 l2 :=
  p (defs l1) = defs l2 /\
  p (calls l1) = calls l2 /\
  match annot l1, annot l2 with
    | Some _, Some _ => True
    | None, None => True
    | _, _ => False
  end.

Inductive equivalentLabelSeq p: LabelSeqT -> LabelSeqT -> Prop :=
| NilEquivalentSeq: equivalentLabelSeq p nil nil
| EquivalentSeq x xs y ys: equivalentLabel p x y -> equivalentLabelSeq p xs ys ->
                           equivalentLabelSeq p (x :: xs) (y :: ys).

Definition traceRefines p m1 m2 :=
  forall s1 sig1, Behavior m1 s1 sig1 ->
                  exists s2 sig2, Behavior m2 s2 sig2 /\
                                  equivalentLabelSeq p sig1 sig2.

Theorem staticDynCallsSubstep m o u rm cs:
  Substep m o u rm cs ->
  forall f, M.In f cs -> List.In f (getCalls m).
Proof.
  admit.
Qed.

Theorem staticDynDefsSubstep m o u far cs:
  Substep m o u (Meth (Some far)) cs ->
  List.In (attrName far) (getDefs m).
Proof.
  intros.
  dependent induction H; simpl in *.
  unfold getDefs in *.
  clear - HIn.
  induction (getDefsBodies m).
  - intuition.
  - simpl in *.
    destruct HIn.
    + subst.
      left; intuition.
    + right; intuition.
Qed.

Theorem staticDynCallsSubsteps m o ss:
  forall f, M.In f (calls (foldSSLabel (m := m) (o := o) ss)) -> In f (getCalls m).
Proof.
  intros.
  induction ss; simpl in *.
  - exfalso.
    apply (proj1 (M.F.P.F.empty_in_iff _ _) H).
  - unfold addLabelLeft, addLabelLeft' in *.
    destruct a.
    simpl in *.
    destruct unitAnnot0.
    + destruct (foldSSLabel ss); simpl in *.
      pose proof (M.union_In H) as sth.
      destruct sth.
      * apply (staticDynCallsSubstep substep0); intuition.
      * intuition.
    + destruct (foldSSLabel ss); simpl in *.
      dependent destruction o0; simpl in *.
      * dependent destruction a; simpl in *.
        pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply (staticDynCallsSubstep substep0); intuition.
          - intuition.
        }
      * pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply (staticDynCallsSubstep substep0); intuition.
          - intuition.
        }
Qed.

Theorem staticDynDefsSubsteps m o ss:
  forall f, M.In f (defs (foldSSLabel (m := m) (o := o) ss)) -> In f (getDefs m).
Proof.
  intros.
  induction ss; simpl in *.
  - exfalso.
    apply (proj1 (M.F.P.F.empty_in_iff _ _) H).
  - unfold addLabelLeft, addLabelLeft' in *.
    destruct a.
    simpl in *.
    destruct unitAnnot0.
    + destruct (foldSSLabel ss); simpl in *.
      rewrite M.union_empty_L in H.
      intuition.
    + destruct (foldSSLabel ss); simpl in *.
      dependent destruction o0; simpl in *.
      * dependent destruction a; simpl in *.
        pose proof (M.union_In H) as sth.
        { destruct sth.
          - apply M.F.P.F.add_in_iff in H0.
            destruct H0.
            + subst.
              apply (staticDynDefsSubstep substep0).
            + exfalso; apply ((proj1 (M.F.P.F.empty_in_iff _ _)) H0).
          - intuition.
        }
      * rewrite M.union_empty_L in H.
        intuition.
Qed.

Definition reachable m o := exists sig, Behavior m o sig.
