Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming.
Require Import Lts.Decomposition Lts.Renaming Lts.Inline Lts.InlineFacts_2.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.

Set Implicit Arguments.

Section ProcDecSC.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Variable n: nat.

  Definition pdecN := procDecM fifoSize dec exec n.
  Definition scN := sc dec exec opLd opSt opHt n.
  Hint Unfold pdecN scN : ModuleDefs.

  Section SingleCore.
    Definition pdec := pdecf fifoSize dec exec.
    Definition pinst := pinst dec exec opLd opSt opHt.
    Hint Unfold pdec pinst.

    Lemma pdec_refines_pinst: pdec <<== pinst.
    Proof.
      admit.
    Qed.

  End SingleCore.

  Lemma pdecN_refines_scN: pdecN <<== scN.
  Proof.
    admit.
  Qed.

End ProcDecSC.

