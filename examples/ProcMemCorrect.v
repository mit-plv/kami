Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate Lts.ParamDup.

Require Import Ex.SC Ex.ProcDec Ex.MemAtomic Ex.MemCache Ex.MemCacheSubst Ex.L1Cache.
Require Import Ex.FifoCorrect Ex.MemCorrect Ex.ProcDecSCN Lts.ParametricSyntax.

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
    - admit. (* kdef_call_sub automation *)
    - kinteracting.
    - krefl.
    - ketrans; [|apply ios_memAtomicWoQ_memAtomic].
      apply traceRefines_modular_interacting with (vp:= dropFirstElts LgNumChildren);
        [kequiv|kequiv|kequiv|kequiv
         |kdisj_regs|kdisj_regs|kvr|kvr
         |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
         | | | | |].
      + admit. (* kdef_call_sub automation *)
      + admit. (* kdef_call_sub automation *)
      + admit. (* dropFirstElts satisfies Interacting *)
      + ketrans_r; [apply modFromMeta_comm_1|].
        ketrans_l; [|apply duplicate_concatMod_comm_2; auto; [kvr|kvr|kequiv|kequiv]].
        replace (dropFirstElts LgNumChildren) with
        (compLabelMaps (dropFirstElts LgNumChildren) (@idElementwise _))
          by apply compLabelMaps_id_right.

        apply traceRefines_modular_noninteracting_p;
          [kequiv|kequiv|kequiv|kequiv
           |kdisj_regs|kdisj_regs|kvr|kvr
           |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
           | | |knoninteracting|knoninteracting| |].
        * admit. (* disjointness of label maps *)
        * admit. (* disjointness of label maps *)
        * ketrans_r;
            [apply sinModule_duplicate_1;
             [kequiv|kvr|knodup_regs|apply nativeFifoS_const_regs]|].
          apply duplicate_traceRefines_drop; auto.
          rewrite <-NativeFifo.nativeFifo_nativeFifoS.
          apply nfifo_refines_nsfifo.
        * apply sinModule_duplicate_1; [kequiv|kvr|knodup_regs|].
          apply nativeFifoS_const_regs with (default:= (getDefaultConst _)).
          
      + apply memCache_refines_memAtomic.
  Qed.

End ProcMem.

