Require Import Kami.
Require Import Lib.FinNotations Lib.Struct Lib.Indexer.
Require Import Ex.OneEltFifo Ex.ProcMemSpec Ex.PipelinedProc
        Ex.DecExec Ex.DecExecOk.

Require Import Kami.Tactics Kami.ModuleBoundEx.

Set Implicit Arguments.

Section PipelinedProc.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK).

  Variable (init: ProcInit instK dataK rfSize pgmSize).
  
  Definition procInterm :=
    ((decexec dec exec (pcInit init) (pgmInit init))
       ++ (regFile (rfInit init))
       ++ (e2w dataK rfSize)
       ++ (scoreboard rfSize)
       ++ (writeback dataK rfSize))%kami.
  Lemma procInterm_PhoasWf: ModPhoasWf procInterm.
  Proof. kequiv. Qed.
  Lemma procInterm_RegsWf: ModRegsWf procInterm.
  Proof. kvr. Qed.
  Hint Resolve procInterm_PhoasWf procInterm_RegsWf.

  Hint Unfold procInterm: ModuleDefs.
  
  Theorem procImpl_ok_1:
    procImpl dec exec init <<== procInterm.
  Proof.
    kmodular.
    - apply decexec_ok.
    - krefl.
  Qed.

  Definition procIntermInl: {m: Modules & procInterm <<== m}.
  Proof.
    kinline_refine procInterm.
  Defined.

End PipelinedProc.

