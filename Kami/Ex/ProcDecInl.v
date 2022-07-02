Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Inline Kami.InlineFacts Kami.Tactics.
Require Import Ex.SC Ex.ProcDec.

Set Implicit Arguments.

Section Inlined.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx).

  Variable (init: ProcInit addrSize dataBytes rfIdx).

  Definition pdec := pdecf fetch dec exec init.
  #[local] Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)

  Definition pdecInl: sigT (fun m: Modules => pdec <<== m).
  Proof.
    kinline_refine pdec.
  Defined.

End Inlined.

