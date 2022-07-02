Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct.
Require Import Kami.Syntax Kami.Notations.
Require Import Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Inline Kami.InlineFacts.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC.

Set Implicit Arguments.

Section Inlined.
  Variables (addrSize maddrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (procInit: ProcInit addrSize dataBytes rfIdx)
           (memInit: MemInit maddrSize).
  
  Definition scmm: Modules := scmm Hdb fetch dec exec ammio procInit memInit.
  #[local] Hint Unfold scmm: ModuleDefs. (* for kinline_compute *)

  Definition scmmInl: sigT (fun m: Modules => scmm <<== m).
  Proof.
    kinline_refine scmm.
  Defined.

End Inlined.

