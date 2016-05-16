Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.DuplicateMeta.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable execState: ExecStateT 2 addrSize valSize rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize valSize rfIdx.
  (* Hypotheses (HdecEquiv: DecEquiv dec) *)
  (*            (HexecEquiv_1: ExecEquiv_1 dec exec) *)
  (*            (HexecEquiv_2: ExecEquiv_2 dec exec). *)

  Variable n: nat.
  
  Definition pdecN := procDecM fifoSize dec execState execNextPc n.
  Definition scN := sc dec execState execNextPc opLd opSt opHt n.

  Lemma pdecN_refines_scN: traceRefines (liftToMap1 (@idElementwise _)) pdecN scN.
  Proof.
    kmodular.
    - kequiv.
    - kequiv.
    - kequiv.
    - kequiv.
    - apply duplicate_meta_disj_regs_one; auto.
    - apply duplicate_meta_disj_regs_one; auto.
    - split.
      + apply duplicate_validRegsModules; auto.
      + constructor; [constructor|].
        simpl; rewrite app_nil_r.
        induction n; simpl; [repeat constructor|].
        repeat constructor; auto.
    - split.
      + apply duplicate_validRegsModules; auto.
      + constructor; [constructor|].
        simpl; rewrite app_nil_r.
        induction n; simpl; [repeat constructor|].
        repeat constructor; auto.
    - apply duplicate_meta_disj_defs_rep; auto.
    - apply duplicate_meta_disj_meth_calls_rep with (mregso:= nil); auto.
    - apply duplicate_meta_disj_defs_rep; auto.
    - apply duplicate_meta_disj_meth_calls_rep with (mregso:= nil); auto.
    - kduplicated.
      + kequiv.
      + kequiv.
      + apply pdec_refines_pinst.
    - krefl.
  Qed.

End ProcDecSCN.

