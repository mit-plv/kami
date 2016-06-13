Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate.

Require Import Ex.SC Ex.ProcDec Ex.MemCache Ex.L1Cache.
Require Import Ex.MemCorrect Ex.ProcDecSCN Lts.ParametricSyntax.

Set Implicit Arguments.

Section ProcMem.
  Variable FifoSize: nat. (* fifo *)
  Variables RfIdx: nat. (* processor *)
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat. (* memory *)
  Variable Id: Kind.

  Definition AddrSize := L1Cache.AddrBits IdxBits TagBits LgNumDatas LgDataBytes.
  Hint Unfold AddrSize: MethDefs.
  
  Variable dec: DecT 2 AddrSize LgDataBytes RfIdx.
  Variable execState: ExecStateT 2 AddrSize LgDataBytes RfIdx.
  Variable execNextPc: ExecNextPcT 2 AddrSize LgDataBytes RfIdx.

  Variable n: nat.

  Definition pdecN := pdecs dec execState execNextPc n.
  Definition mcache := memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n. 
  Definition scN := sc dec execState execNextPc opLd opSt opHt n.

  Theorem pdecN_mcache_refines_scN: (pdecN ++ modFromMeta mcache)%kami <<== scN.
  Proof.
    ktrans (pdecN ++ memAtomic AddrSize LgDataBytes n)%kami.

    - admit.
    - unfold MethsT; rewrite <-idElementwiseId.
      apply pdecN_memAtomic_refines_scN.
  Qed.

End ProcMem.

