Require Import Bool List String.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.FMap.
Require Import Syntax Semantics SemFacts SemOp Refinement Equiv.

Set Implicit Arguments.

Section Decomposition.
  Variable imp spec: Modules.
  Variable theta: RegsT -> RegsT.
  Variable ruleMap: RegsT -> string -> option string.
  Variable p: string -> (sigT SignT) -> option (sigT SignT).

  Hypothesis Htheta: theta (initRegs (getRegInits imp)) = initRegs (getRegInits spec).
  Hypothesis HspecNoCalls: DisjList (getDefs spec) (getCalls spec).

  Hypothesis Hsso2ssr:
    forall o u rule cs ics,
      SubstepOp imp o u (getLabel (Rle (Some rule)) cs) ics ->
      exists uspec, Substep spec (theta o) uspec (Rle (ruleMap o rule)) (liftToMap1 p cs) /\
                    forall o, M.union uspec (theta o) = theta (M.union u o).
  
  Definition liftP meth :=
    match meth with
    | (n :: t)%struct => match p n t with
                         | None => None
                         | Some v => Some (n :: v)%struct
                         end
    end.

  Hypothesis Hsso2ssm:
    forall o u meth msig cs ics,
      SubstepOp imp o u (getLabel (Meth (Some (meth :: msig)%struct)) cs) ics ->
      exists uspec, Substep spec (theta o) uspec (Meth (liftP (meth :: msig)%struct))
                            (liftToMap1 p cs) /\
                    forall o, M.union uspec (theta o) = theta (M.union u o).

  Lemma substepsOp_step_decompose:
    forall o u l ics,
      SubstepsOp imp o u l ics ->
      exists uspec : UpdatesT,
        Step spec (theta o) uspec (liftPLabel (liftToMap1 p) ruleMap o l) /\
        theta (M.union u o) = M.union uspec (theta o).
  Proof.
    induction 1.
    - exists (M.empty _); split; auto.
      apply step_consistent.
      change (liftPLabel (liftToMap1 p) ruleMap o emptyMethLabel) with (hide emptyMethLabel).
      constructor.
      + econstructor.
      + unfold wellHidden, hide; simpl; split;
          rewrite M.subtractKV_empty_1; apply M.KeysDisj_empty.

    - destruct IHSubstepsOp as [uspec ?]; dest.
      pose proof H2. (* stupid; fix it *)
      inv H2.
      + exists uspec; split.
        * p_equal H3; f_equal.
          admit. (* easy with CanCombineUL *)
        * rewrite <-H4; meq.
      + exists uspec; split.
        * p_equal H3; f_equal.
          admit. (* easy with CanCombineUL *)
        * rewrite <-H4; meq.
      + specialize (Hsso2ssr H5).
        admit.
      + specialize (Hsso2ssm H5).
        admit.
  Qed.
    
  Theorem decomposition:
    traceRefines (liftToMap1 p) imp spec.
  Proof.
    apply stepRefinement with (ruleMap:= ruleMap) (theta:= theta); auto.
    intros; apply step_implies_StepOp in H; inv H.
    eapply substepsOp_step_decompose; eauto.
  Qed.

End Decomposition.

