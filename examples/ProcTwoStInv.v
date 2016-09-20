Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcTwoStage Ex.ProcTwoStInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables addrSize lgDataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT lgDataBytes)
            (getLdDst: LdDstT lgDataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize lgDataBytes)
            (getLdSrc: LdSrcT lgDataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize lgDataBytes)
            (getStAddr: StAddrT addrSize lgDataBytes)
            (getStSrc: StSrcT lgDataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize lgDataBytes)
            (getStVSrc: StVSrcT lgDataBytes rfIdx)
            (getSrc1: Src1T lgDataBytes rfIdx)
            (getSrc2: Src2T lgDataBytes rfIdx)
            (execState: ExecStateT addrSize lgDataBytes rfIdx)
            (execNextPc: ExecNextPcT addrSize lgDataBytes rfIdx).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition p2stInl := p2stInl getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                getStAddr getStSrc calcStAddr getStVSrc
                                getSrc1 execState execNextPc.

  Definition p2st_pc_epochs_inv
             (fepochv eepochv d2efullv e2dfullv stallv: fullType type (SyntaxKind Bool))
             (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (d2eeltv stalledv: fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx))) :=
    (fepochv = eepochv -> e2dfullv = false) /\ (e2dfullv = false -> fepochv = eepochv) /\
    (fepochv <> eepochv -> e2dfullv = true) /\ (e2dfullv = true -> fepochv <> eepochv) /\

    (e2dfullv = true -> d2efullv = true -> d2eeltv ``"epoch" = fepochv) /\
    (d2efullv = true -> d2eeltv ``"epoch" = fepochv -> d2eeltv ``"nextPc" = pcv) /\
    (d2efullv = true -> d2eeltv ``"epoch" = eepochv -> e2dfullv = false) /\

    (stallv = true -> e2dfullv = false) /\

    (stallv = true -> d2efullv = true ->
     (stalledv ``"nextPc" = d2eeltv ``"curPc" /\ d2eeltv ``"epoch" = fepochv)) /\
    (stallv = true -> d2efullv = false -> e2dfullv = false ->
     stalledv ``"nextPc" = pcv).

  Definition p2st_decode_inv
             (pgmv: fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize)))
             (rfv: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2eeltv: fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx))) :=
    d2efullv = true ->
    let rawInst := d2eeltv ``"rawInst" in
    (rawInst = pgmv (d2eeltv ``"curPc") /\
     d2eeltv ``"opType" = evalExpr (getOptype _ rawInst) /\
     (d2eeltv ``"opType" = opLd ->
      (d2eeltv ``"dst" = evalExpr (getLdDst _ rawInst) /\
       d2eeltv ``"addr" =
       evalExpr (calcLdAddr _ (evalExpr (getLdAddr _ rawInst))
                            (rfv (evalExpr (getLdSrc _ rawInst)))))) /\
     (d2eeltv ``"opType" = opSt ->
      d2eeltv ``"addr" =
      evalExpr (calcStAddr _ (evalExpr (getStAddr _ rawInst))
                           (rfv (evalExpr (getStSrc _ rawInst)))) /\
      d2eeltv ``"val" = rfv (evalExpr (getStVSrc _ rawInst)))) /\
    (d2eeltv ``"opType" = opTh ->
     d2eeltv ``"val" = rfv (evalExpr (getSrc1 _ rawInst))).

  Definition p2st_raw_inv
             (d2efullv stallv: fullType type (SyntaxKind Bool))
             (d2eeltv stalledv: fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx))) :=
    d2efullv = true -> stallv = true -> stalledv ``"opType" = opLd ->
    (d2eeltv ``"opType" = opSt ->
     (stalledv ``"dst" <> evalExpr (getStSrc _ (d2eeltv ``"rawInst")) /\
      stalledv ``"dst" <> evalExpr (getStVSrc _ (d2eeltv ``"rawInst")))) /\
    (d2eeltv ``"opType" = opLd ->
     stalledv ``"dst" <> evalExpr (getLdSrc _ (d2eeltv ``"rawInst"))) /\
    (d2eeltv ``"opType" = opTh ->
     stalledv ``"dst" <> evalExpr (getSrc1 _ (d2eeltv ``"rawInst"))).

  Definition p2st_scoreboard_inv
             (d2efullv stallv sbvv: fullType type (SyntaxKind Bool))
             (sbv: fullType type (SyntaxKind (Bit rfIdx)))
             (d2eeltv stalledv: fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx))) :=
    (d2efullv = false -> stallv = true -> sbvv = true /\ stalledv ``"dst" = sbv) /\
    (d2efullv = true -> d2eeltv ``"opType" = opLd -> sbvv = true /\ d2eeltv ``"dst" = sbv).
  
  Record p2st_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Bit addrSize));
      Hpcv : M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv : M.find "pgm"%string o = Some (existT _ _ pgmv);
      fepochv : fullType type (SyntaxKind Bool);
      Hfepochv : M.find "fEpoch"%string o = Some (existT _ _ fepochv);

      rfv : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv : M.find "rf"%string o = Some (existT _ _ rfv);

      sbv : fullType type (SyntaxKind (Bit rfIdx));
      Hsbv : M.find "idx"%string o = Some (existT _ _ sbv);
      sbvv : fullType type (SyntaxKind Bool);
      Hsbvv : M.find "valid"%string o = Some (existT _ _ sbvv);

      d2eeltv : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hd2eeltv : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv);
      d2efullv : fullType type (SyntaxKind Bool);
      Hd2efullv : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv);

      e2deltv : fullType type (SyntaxKind (Bit addrSize));
      He2deltv : M.find "e2d"--"elt"%string o = Some (existT _ _ e2deltv);
      e2dfullv : fullType type (SyntaxKind Bool);
      He2dfullv : M.find "e2d"--"full"%string o = Some (existT _ _ e2dfullv);

      stallv : fullType type (SyntaxKind Bool);
      Hstallv : M.find "stall"%string o = Some (existT _ _ stallv);
      stalledv : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hstalledv : M.find "stalled"%string o = Some (existT _ _ stalledv);

      eepochv : fullType type (SyntaxKind Bool);
      Heepochv : M.find "eEpoch"%string o = Some (existT _ _ eepochv);

      Hinv :
        p2st_pc_epochs_inv fepochv eepochv d2efullv e2dfullv stallv pcv d2eeltv stalledv
        (* p2st_decode_inv pgmv rfv d2efullv d2eeltv /\ *)
        (* p2st_raw_inv d2efullv stallv d2eeltv stalledv /\ *)
        (* p2st_scoreboard_inv d2efullv stallv sbvv sbv d2eeltv stalledv *)
    }.
  Hint Unfold p2st_pc_epochs_inv p2st_decode_inv p2st_raw_inv p2st_scoreboard_inv: InvDefs.
  
  Ltac p2st_inv_old :=
    try match goal with
        | [H: p2st_inv _ |- _] => destruct H
        end;
    kinv_red.

  Ltac p2st_inv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kregmap_clear; (* for improving performance *)
    kinv_red; (* unfolding invariant definitions *)
    repeat (* cheaper than "intuition" *)
      (match goal with
       | [ |- _ /\ _ ] => split
       end);
    try eassumption; intros; try reflexivity;
    intuition kinv_simpl; intuition idtac.

  Ltac p2st_inv_tac := p2st_inv_old; p2st_inv_new.

  Lemma p2st_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst p2stInl)) ->
      Multistep (fst p2stInl) init n ll ->
      p2st_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - p2st_inv_old.
      unfold getRegInits, fst, p2stInl, ProcTwoStInl.p2stInl.
      p2st_inv_new; simpl in *; kinv_simpl.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p2st_inv_tac.
        * destruct x0, eepochv; intuition idtac.
        * destruct x0, eepochv; intuition idtac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac; intuition idtac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac; intuition idtac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.

        END_SKIP_PROOF_ON *) admit.
  Qed.
  
  Lemma p2st_inv_ok:
    forall o,
      reachable o (fst p2stInl) ->
      p2st_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply p2st_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold RqFromProc RsToProc: MethDefs.

