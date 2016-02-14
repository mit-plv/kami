Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.

Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Wf.
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

  (* TODO: eq_rect incomputable *)
  (* Eval compute in (noCalls (fst (inline (ConcatMod ma mb)))). *)

  Lemma mab_mc: (ConcatMod ma mb) <<== mc.
  Proof.
    apply traceRefines_trans with (mb:= fst (inlineF (ConcatMod ma mb))).
    - apply inlineF_refines; auto.
      + repeat constructor.
      + repeat constructor; auto.
    - assert (HssRuleMap:
                (forall o u rule cs,
                    Substep (fst (inlineF (ConcatMod ma mb))) o u (Rle (Some rule)) cs ->
                    {uSpec : UpdatesT |
                     Substep mc (id o) uSpec (Rle (Some rule))
                             (liftToMap1 (idElementwise (A:=sigT SignT)) cs) /\
                     (forall o0 : RegsT, M.union uSpec (id o0) = id (M.union u o0))})).
      { simpl; intros.
        exists u; split; auto.
        rewrite idElementwiseId; unfold id.
        inv H.
        inv HInRules.
        { inv H; invertActionRep.
          repeat (econstructor; eauto).
        }
        { inv H. }
      }

      assert (HssMethMap:
                (forall o u meth cs,
                    Substep (fst (inlineF (ConcatMod ma mb))) o u (Meth (Some meth)) cs ->
                    {uSpec : UpdatesT |
                     Substep mc (id o) uSpec (Meth (liftP (idElementwise (A:=sigT SignT)) meth))
                             (liftToMap1 (idElementwise (A:=sigT SignT)) cs) /\
                     (forall o0 : RegsT, M.union uSpec (id o0) = id (M.union u o0))})).
      { simpl; intros.
        exists u; split; auto.
        rewrite idElementwiseId; unfold id.
        inv H.
        inv HIn.
      }

      apply decomposition with (theta:= id)
                                 (ruleMap:= fun _ r => Some r)
                                 (substepRuleMap:= HssRuleMap)
                                 (substepMethMap:= HssMethMap); auto.
      admit.
  Qed.

End Tests.

