Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Variable n: nat.
  
  Definition pdecN := procDecM fifoSize dec execState execNextPc n.
  Definition scN := sc dec execState execNextPc opLd opSt opHt n.

  Lemma pdecN_refines_scN: pdecN <<== scN.
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

  Definition procDecN := pdecs dec execState execNextPc n.
  Definition memAtomic := memAtomic addrSize fifoSize lgDataBytes n.
  Definition pdecAN := (procDecN ++ memAtomic)%kami.

  Lemma pdecN_memAtomic_refines_scN: pdecAN <<== scN.
  Proof.
    apply traceRefines_trans with (mb:= pdecN); [|apply pdecN_refines_scN].

    replace (fun f : MethsT => f) with (liftToMap1 (idElementwise (A:= sigT SignT)))
      by apply SemFacts.idElementwiseId.
    unfold pdecAN, procDecN, memAtomic, MemAtomic.memAtomic.
    
    apply traceRefines_trans with
    (mb:= ((pdecs dec execState execNextPc n ++ ioms addrSize fifoSize lgDataBytes n)
             ++ minst addrSize lgDataBytes n)%kami);
      [apply traceRefines_assoc_2|].

    unfold pdecN, procDecM.
    (* kmodular *)
    admit.
  Qed.
  
End ProcDecSCN.

