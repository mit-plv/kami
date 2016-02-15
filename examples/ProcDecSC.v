Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement.
Require Import Lts.Decomposition Lts.Renaming Lts.Inline Lts.InlineFacts_2.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.

Section ProcDecSC.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition procDecM (n: nat) := procDecM fifoSize dec exec n.
  Definition sc (n: nat) := sc 2 _ _ _ dec exec opLd opSt opHt n.
  Hint Unfold procDecM sc : ModuleDefs.

  Section SingleCore.
    Variable i: nat. (* i-th core *)
    Notation "^ s" := (s __ i) (at level 0).

    Definition pdecfi := ProcDec.pdecfi fifoSize dec exec i.
    Definition pinsti := pinsti 2 _ _ _ dec exec opLd opSt opHt i.
    Hint Unfold pdecfi pinsti.

  End SingleCore.

End ProcDecSC.

Section Instantiation.
  Variable dec: DecT 2 1 1 1.
  Variable exec: ExecT 2 1 1 1. (* 1 *)

  Hypothesis Hdec: (* 2 *)
    forall G (st1: ft1 typeUT (StateK 1 1)) st2
           (a1: ft1 typeUT (SyntaxKind (Bit 1))) a2,
      In (vars (st1, st2)) G ->
      In (vars (a1, a2)) G ->
      Equiv.ExprEquiv G #(dec (fullType typeUT) st1 a1)%kami #(dec (fullType type) st2 a2)%kami.
  Hint Immediate Hdec.

  Ltac tequiv :=
    match goal with
    | [ |- 

  Lemma pdecf_pinst: (pdecfi _ 1 _ _ dec exec 0) <<== (pinsti _ _ _ dec exec 0).
  Proof.
    apply traceRefines_trans with (mb:= fst (inlineF (pdecfi _ 1 _ _ dec exec 0))).
    - apply inlineF_refines. (* TODO: automate all about inlining *)
      + constructor.
        * constructor.
          { repeat (constructor; auto).
          }
          { (* repeat (constructor; auto). *)
            admit.
          }
        * admit.
          (* simpl; tauto. (* hint extern 1 ... *) *)
            (* constructor. (* 4 *) *)
          
      + repeat constructor; intro Hx; in_tac_H; discriminate.
      + vm_compute; reflexivity.

    - eapply decomposition with (theta:= id) (ruleMap:= fun _ r => Some r).
      + rewrite <-inlineF_preserves_regInits.
        admit. (* TODO: theta shouldn't be an id (have to drain registers) *)
      + vm_compute; auto.
      + vm_compute; intuition.
      + (* 5 *)
  Abort.

End Ins.


