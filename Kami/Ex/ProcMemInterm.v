Require Import Kami.
Require Import Lib.FinNotations.
Require Import Ex.OneEltFifo Ex.ProcMemSpec Ex.PipelinedProc Ex.DecExec Ex.DecExecOk.

Require Import Kami.Tactics Kami.ModuleBoundEx.

Set Implicit Arguments.

(*! Specifying, implementing, and verifying a very simple processor !*)

(** You may want to take a look at the code in the following order:
 * - ProcMemSpec.v: the spec of processors and memory systems
 * - PipelinedProc.v: a 3-stage pipelined processor implementation
 * - DecExec.v: a pipeline stage that merges the first two stages,
 *   [decoder] and [executer].
 * - DecExecOk.v: correctness of [decexec] in DecExec.v
 * - ProcMemInterm.v (you are here!): an intermediate 2-stage pipelined 
 * - ProcMemOk.v: a complete refinement proof
 *)

(* After successfully merging the first two stages, now we have a 2-stage
 * pipelined processor as an intermediate implementation. Thanks to Kami's
 * modular-refinement theorem and related high-level tactics, it is quite
 * easy to prove a refinement from the 3-stage processor to the 2-stage one. *)
Section PipelinedProc.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK).

  Variable (init: ProcInit instK dataK rfSize pgmSize).

  (* [procInterm] is our intermediate processor implementation, which has two
   * stages, [decexec] and [writeback]. *)
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
    (* [kmodular] is used to apply the modular-refinement theorem.
     * Try [unfold procImpl, procInterm] to check how submodules are composed
     * for each module. *)
    kmodular.
    - (* We already proved the stage-merging 
       * between [decoder] and [executer]. *)
      apply decexec_ok.
    - krefl.
  Qed.

  (* We inline the 2-stage processor again to prove the final refinement.
   * See ProcMemOk.v for details. *)
  Definition procIntermInl: {m: Modules & procInterm <<== m}.
  Proof.
    kinline_refine procInterm.
  Defined.

End PipelinedProc.
