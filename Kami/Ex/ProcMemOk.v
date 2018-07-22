Require Import Kami.
Require Import Lib.FinNotations.
Require Import Ex.OneEltFifo Ex.ProcMemSpec Ex.PipelinedProc
        Ex.DecExec Ex.DecExecOk Ex.ProcMemInterm.

Set Implicit Arguments.

(*! Specifying, implementing, and verifying a very simple processor !*)

(** You may want to take a look at the code in the following order:
 * - ProcMemSpec.v: the spec of processors and memory systems
 * - PipelinedProc.v: a 3-stage pipelined processor implementation
 * - DecExec.v: a pipeline stage that merges the first two stages,
 *   [decoder] and [executer].
 * - DecExecOk.v: correctness of [decexec] in DecExec.v
 * - ProcMemInterm.v: an intermediate 2-stage pipelined 
 * - ProcMemOk.v (you are here!): a complete refinement proof
 *)

(* For the given 2-stage pipelined processor [procInterm], one more
 * stage-merging is required to prove the final refinement. This stage-merging is
 * quite different from the one we did in DecExecOk.v -- now
 * the pipelined system has a feedback mechanism. Between [decexec] and 
 * [writeback], we have a [scoreboard] to check whether a certain register value 
 * is up-to-date or not. Therefore, in order to merge the two stages, some 
 * additional invariants about [scoreboard] are required.
 *)
Section PipelinedProc.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK).

  Variable (init: ProcInit instK dataK rfSize pgmSize).

  Local Definition procIntermInl := procIntermInl dec exec init.
  Local Definition RfWrite := RfWrite dataK rfSize.

  (* Here is an invariant of [scoreboard]; it simply says that whenever 
   * [decexec] sends data to [writeback], [scoreboard] always says the
   * corresponding register value is not up-to-date. This very simple
   * invariant is enough to prove the stage-merging.
   * Can you guess why it is so simple?
   *)
  Definition procInterm_scoreboard_inv
             (sbFlagsv: fullType type (SyntaxKind (Vector Bool rfSize)))
             (e2wfullv: fullType type (SyntaxKind Bool))
             (e2weltv: fullType type (SyntaxKind (Struct RfWrite))) :=
    e2wfullv = true -> sbFlagsv (e2weltv F1) = true.

  Record procInterm_inv (o: RegsT): Prop :=
    { pcv: fullType type (SyntaxKind (Bit pgmSize));
      Hpcv: M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv: fullType type (SyntaxKind (Vector instK pgmSize));
      Hpgmv: M.find "pgm"%string o = Some (existT _ _ pgmv);
      rfv: fullType type (SyntaxKind (Vector dataK rfSize));
      Hrfv: M.find "rf"%string o = Some (existT _ _ rfv);
      e2wfullv: fullType type (SyntaxKind Bool);
      He2wfullv: M.find "full.e2w"%string o = Some (existT _ _ e2wfullv);
      e2weltv: fullType type (SyntaxKind (Struct RfWrite));
      He2weltv: M.find "elt.e2w"%string o = Some (existT _ _ e2weltv);
      sbFlagsv: fullType type (SyntaxKind (Vector Bool rfSize));
      HsbFlagsv: M.find "sbFlags"%string o = Some (existT _ _ sbFlagsv);

      HsbInv: procInterm_scoreboard_inv sbFlagsv e2wfullv e2weltv;
    }.
  Hint Unfold procInterm_scoreboard_inv : InvDefs.

  (* We prove the invariant as we did in DecExecOk.v. *)
  
  Ltac procInterm_inv_dest_tac :=
    unfold getRegInits, decexecSepInl, projT1;
    try match goal with
        | [H: procInterm_inv _ |- _] => destruct H
        end.

  Ltac procInterm_inv_constr_tac :=
    try econstructor; intros;
    repeat (kinv_eq; kinv_red; eauto).

  Ltac procInterm_inv_tac :=
    procInterm_inv_dest_tac; procInterm_inv_constr_tac.

  Lemma procInterm_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (projT1 procIntermInl)) ->
      Multistep (projT1 procIntermInl) init n ll ->
      procInterm_inv n.
  Proof.
    induction 2.
    - procInterm_inv_tac; cbn in *; kinv_simpl.
    - kinvert.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
      + kinv_dest_custom procInterm_inv_tac.
  Qed.

  Lemma procInterm_inv_ok:
    forall o,
      reachable o (projT1 procIntermInl) ->
      procInterm_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply procInterm_inv_ok'; eauto.
  Qed.

  (* Register and rule mapping are provided similarly. *)
  
  Definition procInterm_regMap (r: RegsT): RegsT :=
    (mlet pcv: (Bit pgmSize) <- r |> "pc";
       mlet pgmv: (Vector instK pgmSize) <- r |> "pgm";
       mlet rfv: (Vector dataK rfSize) <- r |> "rf";
       mlet e2wfullv: Bool <- r |> "e2w"--"full";
       mlet e2weltv: (Struct RfWrite) <- r |> "e2w"--"elt";
       mlet sbFlagsv: (Vector Bool rfSize) <- r |> "sbFlags";
       (["pgm" <- existT _ _ pgmv]
        +["rf" <- existT _ _
               (if e2wfullv
                then evalExpr (#rfv@[#e2weltv!RfWrite@."idx"
                               <- #e2weltv!RfWrite@."val"])%kami_expr
                else rfv)]
        +["pc" <- existT _ _ pcv])%fmap)%mapping.
  Hint Unfold procInterm_regMap: MethDefs.

  Definition procInterm_ruleMap (o: RegsT): string -> option string :=
    "decexecArith" |-> "doArith";
      "decexecLd" |-> "doLoad";
      "decexecSt" |-> "doStore";
      "decexecTh" |-> "doToHost"; ||.
  Hint Unfold procInterm_ruleMap: MethDefs.

  (* The refinement is proven by following the typical verification flow. *)
  Theorem procImpl_ok_2:
    procInterm dec exec init <<== procSpec dec exec init.
  Proof.
    (* 1) Inlining *)
    kinline_refine_left procIntermInl.

    (* 2) Decomposition *)
    kdecompose_nodefs procInterm_regMap procInterm_ruleMap.

    (* 3) Simulation *)
    kinv_add procInterm_inv_ok.
    kinv_add_end.
    kinvert.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
    - kinv_magic_with procInterm_inv_tac idtac.
  Qed.

  (* Putting all pieces together! Finally we can prove the refinement from
   * our 3-stage pipelined processor to the spec by using transitivity of the
   * refinement relation. *)
  Theorem procImpl_ok:
    procImpl dec exec init <<== procSpec dec exec init.
  Proof.
    ketrans.
    - apply procImpl_ok_1.
    - apply procImpl_ok_2.
  Qed.

  (* The very last theorem claims the refinement where the same memory is 
   * attached to each processor. *)
  Theorem procMemImpl_ok:
    procMemImpl dec exec init <<== procMemSpec dec exec init.
  Proof.
    kmodular.
    - apply procImpl_ok.
    - krefl.
  Qed.

End PipelinedProc.
