Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.SemFacts.
Require Import Lts.RefinementFacts Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate.
Require Import Lts.ModuleBound Lts.ModuleBoundEx.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables opIdx addrSize iaddrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize iaddrSize lgDataBytes rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).
  Hypotheses (HldSt: (if weq (evalConstT opLd) (evalConstT opSt) then true else false) = false).

  Variable n: nat.
  
  Definition pdecN := procDecM fifoSize dec execState execNextPc opLd opSt opHt n.
  Definition scN := sc dec execState execNextPc opLd opSt opHt n.

  Lemma pdecN_refines_scN: pdecN <<== scN.
  Proof. (* SKIP_PROOF_ON
    kmodular.
    - kdisj_edms_cms_ex n.
    - kdisj_ecms_dms_ex n.
    - kduplicated.
      apply pdec_refines_pinst; auto.
    - krefl.
      END_SKIP_PROOF_ON *) admit.
  Qed.

  Definition procDecN := pdecs dec execState execNextPc opLd opSt opHt n.
  Definition memAtomic := memAtomic addrSize fifoSize lgDataBytes n.
  Definition pdecAN := (procDecN ++ memAtomic)%kami.

  Lemma pdecN_memAtomic_refines_scN: pdecAN <<== scN.
  Proof. (* SKIP_PROOF_ON
    ketrans; [|apply pdecN_refines_scN; auto].
    krewrite assoc left.
    kmodular_sim_l.
    - apply duplicate_regs_ConcatMod; auto; kvr.
    - apply duplicate_rules_ConcatMod; auto; kvr.
    - apply duplicate_defs_ConcatMod; auto; kvr.
      END_SKIP_PROOF_ON *) admit.
  Qed.
  
End ProcDecSCN.

