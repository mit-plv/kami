Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.

Require Import Lts.Syntax Lts.Semantics Lts.SemOp Lts.Equiv Lts.Wf.
Require Import Lts.Inline Lts.InlineFacts_1 Lts.InlineFacts_2.
Require Import Lts.Refinement Lts.Decomposition.
(* Require Import Lts.Renaming *)

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Parameter i: nat.

Definition fbCm := MethodSig "fb"() : Bool.

(* Test below after implementing alpha-renaming *)
(* Definition fbCm := MethodSig ("fb"__ i)() : Bool. *)

Definition ma := MODULE {
  Register "a" : Bool <- Default

  with Rule "ra" :=
    Call vb <- fbCm();
    Write "a" <- #vb;
    Retv
}.

Definition mb := MODULE {
  Register "b" : Bool <- true

  with Method "fb"() : Bool :=
  (* with Method ("fb"__ i)() : Bool := *)
    Write "b" <- $$true;
    Read rb <- "b";
    Ret #rb
}.

Definition mc := MODULE {
  Register "a" : Bool <- Default
  with Register "b" : Bool <- true

  with Rule "ra" :=                           
    Write "b" <- $$true;
    Read rb : Bool <- "b";
    Write "a" <- #rb;
    Retv
}.

Require Import Program.Equality.

Section Tests.

  Definition theta : RegsT -> RegsT := id.
  Definition ruleMap : RegsT -> string -> option string :=
    fun _ r => Some r.

  Definition HssRuleMap:
    forall o u rule cs,
      Substep (fst (inlineF (ConcatMod ma mb))) o u (Rle (Some rule)) cs ->
      {uSpec : UpdatesT |
       Substep mc (id o) uSpec (Rle (Some rule))
               (liftToMap1 (idElementwise (A:=sigT SignT)) cs) /\
       forall o0 : RegsT, M.union uSpec (id o0) = id (M.union u o0)
      }.
  Proof.
    simpl; intros.
    exists u; split; auto.
    rewrite idElementwiseId; unfold id.
    inv H.
    inv HInRules.
    {
      inv H; invertActionRep.
      repeat (econstructor; eauto).
    }
    { inv H. }
  Defined.

  Definition HssMethMap:
    forall o u meth cs,
      Substep (fst (inlineF (ConcatMod ma mb))) o u (Meth (Some meth)) cs ->
      {uSpec : UpdatesT |
       Substep mc (id o) uSpec (Meth (liftP (idElementwise (A:=sigT SignT)) meth))
               (liftToMap1 (idElementwise (A:=sigT SignT)) cs) /\
       forall o0 : RegsT, M.union uSpec (id o0) = id (M.union u o0)
      }.
  Proof.
    simpl; intros.
    exists u; split; auto.
    rewrite idElementwiseId; unfold id.
    inv H.
    inv HIn.
  Defined.

  Lemma mab_mc: (ConcatMod ma mb) <<== mc.
  Proof.
    inlineL.
    equiv_tac.
    decomposeT (id (A:= RegsT))
               (fun (r: RegsT) (rl: string) => Some rl)
               HssRuleMap HssMethMap.
    admit. (* do we really have to prove this for each instance? *)
  Qed.
  
End Tests.

Section SemOpTest.

  Lemma mab_mc2: (ConcatMod ma mb) <<== mc.
  Proof.
    intros; apply stepRefinement with (ruleMap:= fun o r => Some r) (theta:= id); auto.
    intros; exists u; split; auto.

    apply step_implies_StepOp in H.

    (* decomposition condition like this? *)
    assert (forall o nu nl,
               SubstepOp (ConcatMod ma mb) o nu nl ->
               SubstepsInd mc o nu nl).
    { clear; intros.
      inv H; try (constructor; fail).

      - eapply SubstepsCons.
        + apply SubstepsNil.
        + apply EmptyRule.
        + repeat split; auto.
        + meq.
        + reflexivity.

      - inv HInRules; [|inv H].
        inv H.

        admit.
        
      - exfalso; simpl in *.
        inv HIn; simpl in *; intuition.
    }

    admit.
  Qed.

  Definition getNames m := namesOf (getRegInits m) ++ namesOf (getRules m) ++ getDefs m.
  Definition getPrepNames m s := map (fun x => (s ++ x)%string) (getNames m).

  Require Import Renaming.
  Definition makeBijective m s := bijective (getNames m) (getPrepNames m s).

  Definition bijMaMb (s: string) := makeBijective (ConcatMod ma mb) ("s" ++ "-").
  
  Ltac bijective :=
    apply bijectiveCorrect; auto;
    repeat unfold not, getNames, getPrepNames;
    repeat unfold getRegInits, getRules, getDefs, getDefsBodies;
    simpl in *;
    intros;
    dest;
    repeat match goal with
           | H: _ \/ _ |- _ => destruct H
           end; subst;
      try discriminate; intuition.

  Lemma bijMaMbCorrect x s: bijMaMb x (bijMaMb x s) = s.
    bijective.
  Qed.

  Definition bijMc (s: string) := makeBijective mc ("s" ++ "-").
  
  Lemma bijMcCorrect x s: bijMc x (bijMc x s) = s.
    bijective.
  Qed.

  Lemma renameTR x:
    traceRefines
      (liftPRename (bijMaMb x) (bijMc x) (liftToMap1 (@idElementwise _)))
      (renameModules (bijMaMb x) (ConcatMod ma mb)) (renameModules (bijMc x) mc).
  Proof.
    apply renameTheorem'.
    - apply bijMcCorrect.
    - apply bijMcCorrect.
    - apply mab_mc2.
  Qed.
End SemOpTest.
