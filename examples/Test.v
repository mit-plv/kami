Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.

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

Hint Unfold ma mb mc: ModuleDefs.
Hint Unfold fbCm: MethDefs.

(* Require Import Program.Equality. *)

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

  Ltac decompositionSimple :=
    repeat
      match goal with
      | s: SubstepRec _ _ |- _ => destruct s
      | s: Substep _ _ _ _ _ |- _ => destruct s; simpl in *
      | |- context [match ?P with
                    | _ => _
                    end] => destruct P
      | |- M.Disj (M.empty _) _ => apply M.Disj_empty_1
      | |- M.Disj _ (M.empty _) => apply M.Disj_empty_2
      | _ => eauto
      end.

  Lemma mab_mc: (ConcatMod ma mb) <<== mc.
  Proof.
    kinline_left; [equiv_tac|].
    (* kinline_compute. *)
    decomposeT (id (A:= RegsT))
               (fun (r: RegsT) (rl: string) => Some rl)
               HssRuleMap HssMethMap;
      decompositionSimple.
    equiv_tac.
  Qed.
  
End Tests.

