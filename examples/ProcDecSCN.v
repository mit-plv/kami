Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.
  Hypotheses (HdecEquiv: DecEquiv dec)
             (HexecEquiv_1: ExecEquiv_1 dec exec)
             (HexecEquiv_2: ExecEquiv_2 dec exec).

  (* Variable n: nat. *)
  Definition n := 2.
  
  Definition pdecN := procDecM fifoSize dec exec n.
  Definition scN := sc dec exec opLd opSt opHt n.

  Lemma DisjList_logic:
    forall (l1 l2: list string),
      (forall e, In e l1 -> In e l2 -> False) ->
      DisjList l1 l2.
  Proof.
    unfold DisjList; intros.
    specialize (H e).
    destruct (in_dec string_dec e l1); intuition.
  Qed.

  Ltac disjList_tac :=
    abstract (
        apply DisjList_logic; vm_compute; intros;
        repeat
          match goal with
          | [H: _ \/ _ |- _] => inv H
          | [H: False |- _] => inv H
          | [H: _ = _%string |- _] => vm_compute in H; inv H
          end).

  Lemma pdecN_refines_scN: traceRefines (liftToMap1 (@idElementwise _)) pdecN scN.
  Proof.
    apply traceRefines_modular_interacting with (vp:= (@idElementwise _)).
    - auto.
    - auto.
    - auto.
    - auto.
    - disjList_tac. (* TODO: add disjList_tac to Hint Extern *)
    - disjList_tac.
    - constructor.
      + apply duplicate_validRegsModules. (* TODO: add this tactic approach to kvalid_regs *)
        kvalid_regs.
      + kvalid_regs.
    - constructor.
      + apply duplicate_validRegsModules.
        kvalid_regs.
      + kvalid_regs.
    - disjList_tac.
    - disjList_tac.
    - disjList_tac.
    - disjList_tac.
    - apply duplicate_defCallSub; auto.
      vm_compute; split; intros; intuition idtac.
    - apply DefCallSub_refl.
    - repeat split.
    - kduplicated.
      apply pdec_refines_pinst.
    - rewrite idElementwiseId; apply traceRefines_refl.
  Qed.

End ProcDecSCN.

