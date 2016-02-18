Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.

Require Import Lts.Syntax Lts.Semantics Lts.SemSmall Lts.Equiv Lts.Wf.
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

Section SmallStepTest.

  Lemma mab_mc2: (ConcatMod ma mb) <<== mc.
  Proof.
    intros; apply stepRefinement with (ruleMap:= fun o r => Some r) (theta:= id); auto.
    intros; exists u; split; auto.

    apply stepSmall_consistent; auto; try (repeat constructor).
    apply stepSmall_consistent in H.

    inv H.
    inv HSubSteps; [do 2 constructor|].

    (* decomposition like this? *)
    assert (forall o nu nl,
               SubstepSmall (ConcatMod ma mb) o nu nl ->
               SubstepSmall mc o nu nl).
    { clear; intros.
      inv H; try (constructor; fail).

      - inv HInRules; [|inv H].
        inv H.

        eapply SSSRule; [left; reflexivity|].

        invertActionSmall HAction.
        inv HAction; [|dest; elim H; left; auto].
        inv H; dest.
        inv H; [|intuition].
        inv H5; simpl in *.
        invertActionSmallRep.

        assert (x5 = eq_refl) by apply UIP; subst; simpl.
        econstructor.
        + instantiate (1:= M.add "a"%string (existT (fullType type) (SyntaxKind Bool) x1)
                                 (M.empty (sigT (fullType type)))).
          meq.
        + econstructor; eauto.
          econstructor.
          * instantiate (1:= M.empty (sigT (fullType type))).
            meq.
          * econstructor; eauto.

      - exfalso; simpl in *.
        inv HIn; simpl in *; intuition.
    }

    admit.
  Qed.

End SmallStepTest.

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
    apply traceRefines_trans with (mb:= fst (inlineF (ConcatMod ma mb))).
    - apply inlineF_refines; auto.
      + repeat (constructor; intros).
      + repeat constructor; auto.
    - eapply decomposition with (theta:= id)
                                 (ruleMap:= fun _ r => Some r)
                                 (substepRuleMap:= HssRuleMap)
                                 (substepMethMap:= HssMethMap); auto.

      intros.
      admit. (* do we really have to prove this for each instance? *)
  Qed.
  
End Tests.

