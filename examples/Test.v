Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.

Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Wf.
Require Import Lts.Inline Lts.InlineFacts_1 Lts.InlineFacts_2.
Require Import Lts.Refinement Lts.Decomposition.

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

Section Tests.

  Lemma mab_mc: (ConcatMod ma mb) <<== mc.
  Proof.
    apply traceRefines_trans with (mb:= fst (inline (ConcatMod ma mb))).
    - apply inline_refines; auto.
      + repeat constructor.
      + repeat constructor; auto.
    - (* TODO: constructing mapSet should be easy and automated *)
      assert (id (A:= MethsT) = mapSet (fun n v => Some v)).
      { extensionality k.
        unfold mapSet, rmModify, id; simpl.
        M.mind k.
        { rewrite M.F.P.fold_Empty; auto. }
        { rewrite M.F.P.fold_add; auto.
          { f_equal; auto. }
          { clear; M.proper_tac. }
          { unfold M.F.P.transpose_neqkey; intros.
            apply M.add_comm; auto.
          }
        }
      }
      rewrite H; clear H.

      eapply decomposition with (theta:= id) (ruleMap:= fun _ r => Some r); auto.
      + intuition.
      + intuition.
      + (* ??? *)

  Abort.

End Tests.

