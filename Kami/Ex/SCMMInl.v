Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct.
Require Import Kami.Syntax Kami.Notations.
Require Import Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Inline Kami.InlineFacts.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC.

Set Implicit Arguments.

Section Inlined.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec iaddrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).
  
  Definition scmm := scmm fetch dec exec ammio init.
  Hint Unfold scmm: ModuleDefs. (* for kinline_compute *)

  Definition scmmInl: sigT (fun m: Modules => scmm <<== m).
  Proof.
    kinline_refine scmm.
  Defined.

End Inlined.

