Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.SemFacts.
Require Import Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate Lts.ModuleBound.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables addrSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Variable n: nat.
  
  Definition pdecN := procDecM dec execState execNextPc n.
  Definition scN := sc dec execState execNextPc opLd opSt opHt n.

  Lemma pdecN_refines_scN: pdecN <<== scN.
  Proof. (* SKIP_PROOF_ON
    simple kmodular.
    - kequiv.
    - kequiv.
    - kequiv.
    - kequiv.
    - kdisj_list.
    - kdisj_list.
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
    - kdisj_list.
    - kdisj_list.
    - kdisj_list.
    - kdisj_list.
    - kdef_call_sub.
    - kdef_call_sub.
    - auto.
    - kduplicated.
      + kequiv.
      + kequiv.
      + apply pdec_refines_pinst.
    - krefl.
      END_SKIP_PROOF_ON *) admit.
  Qed.

  Definition procDecN := pdecs dec execState execNextPc n.
  Definition memAtomic := memAtomic addrSize lgDataBytes n.
  Definition pdecAN := (procDecN ++ memAtomic)%kami.

  Lemma pdecN_memAtomic_refines_scN: pdecAN <<== scN.
  Proof. (* SKIP_PROOF_ON
    ktrans pdecN; [|unfold MethsT; rewrite <-idElementwiseId; apply pdecN_refines_scN].
    ktrans ((pdecs dec execState execNextPc n ++ ioms addrSize lgDataBytes n)
              ++ minst addrSize lgDataBytes n)%kami; [apply traceRefines_assoc_2|].

    kmodular_sim_l.
    - simpl; unfold namesOf; rewrite map_app; apply NoDup_DisjList.
      + apply duplicate_regs_NoDup; auto.
      + apply duplicate_regs_NoDup; auto.
      + kdisj_list.
    - apply duplicate_regs_NoDup; auto.
    - auto.
    - kdisj_list.
    - kdisj_list.
    - apply duplicate_regs_ConcatMod_2; auto; kequiv.
    - apply duplicate_regs_ConcatMod_1; auto; kequiv.
    - apply duplicate_rules_ConcatMod_2; auto; kequiv.
    - apply duplicate_rules_ConcatMod_1; auto; kequiv.
    - apply duplicate_defs_ConcatMod_2; auto; kequiv.
    - apply duplicate_defs_ConcatMod_1; auto; kequiv.
      END_SKIP_PROOF_ON *) admit.
  Qed.
  
End ProcDecSCN.

