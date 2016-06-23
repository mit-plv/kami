Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate.

Require Import Ex.SC Ex.ProcDec Ex.MemAtomic Ex.MemCache Ex.L1Cache.
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

  Variable LgNumChildren: nat.
  Definition numChildren := (wordToNat (wones LgNumChildren)).

  Definition pdecN := pdecs dec execState execNextPc numChildren.
  Definition pmFifos :=
    modFromMeta
      ((nfifoRqFromProc IdxBits TagBits LgNumDatas LgDataBytes LgNumChildren)
         +++ (nfifoRsToProc LgDataBytes LgNumChildren)).
    
  Definition mcache := memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize LgNumChildren.
  Definition scN := sc dec execState execNextPc opLd opSt opHt numChildren.

  Theorem pdecN_mcache_refines_scN: (pdecN ++ pmFifos ++ modFromMeta mcache)%kami <<== scN.
  Proof.
    ketrans; [|apply pdecN_memAtomic_refines_scN].

    kmodular_light.
    - kdef_call_sub.
    - admit. (* TODO: kdef_call_sub automation *)
    - kinteracting.
    - krefl.
    - ketrans; [|apply ios_memAtomicWoQ_memAtomic].
      apply traceRefines_modular_interacting with (vp:= dropP);
        [kequiv|kequiv|kequiv|kequiv
         |kdisj_regs|kdisj_regs|kvr|kvr
         |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
         | | | | |].
      + admit. (* kdef_call_sub automation *)
      + admit. (* kdef_call_sub automation *)
      + admit. (* dropP satisfies Interacting *)
      + admit. (* fifos <= simpleFifos *)
      + apply memCache_refines_memAtomic.
  Qed.

End ProcMem.

