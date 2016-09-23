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

  Definition p2stInl := projT1 (p2stInl getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                        getStAddr getStSrc calcStAddr getStVSrc
                                        getSrc1 execState execNextPc).

  Definition p2st_pc_epochs_inv_body
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

  Record p2st_pc_epochs_inv (o: RegsT) : Prop :=
    { pcv0 : fullType type (SyntaxKind (Bit addrSize));
      Hpcv0 : M.find "pc"%string o = Some (existT _ _ pcv0);
      fepochv0 : fullType type (SyntaxKind Bool);
      Hfepochv0 : M.find "fEpoch"%string o = Some (existT _ _ fepochv0);

      d2eeltv0 : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hd2eeltv0 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv0);
      d2efullv0 : fullType type (SyntaxKind Bool);
      Hd2efullv0 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv0);

      (* NOTE: Don't remove e2dElt even if it's not used in the invariant body. *)
      e2deltv0 : fullType type (SyntaxKind (e2dElt addrSize));
      He2deltv0 : M.find "e2d"--"elt"%string o = Some (existT _ _ e2deltv0);
      e2dfullv0 : fullType type (SyntaxKind Bool);
      He2dfullv0 : M.find "e2d"--"full"%string o = Some (existT _ _ e2dfullv0);

      stallv0 : fullType type (SyntaxKind Bool);
      Hstallv0 : M.find "stall"%string o = Some (existT _ _ stallv0);
      stalledv0 : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hstalledv0 : M.find "stalled"%string o = Some (existT _ _ stalledv0);

      eepochv0 : fullType type (SyntaxKind Bool);
      Heepochv0 : M.find "eEpoch"%string o = Some (existT _ _ eepochv0);
    
      Hinv0 : p2st_pc_epochs_inv_body fepochv0 eepochv0 d2efullv0 e2dfullv0
                                      stallv0 pcv0 d2eeltv0 stalledv0 }.

  (* NOTE: this invariant requires p2st_raw_inv *)
  Definition p2st_decode_inv_body
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

  Record p2st_decode_inv (o: RegsT) : Prop :=
    { pgmv1 : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv1 : M.find "pgm"%string o = Some (existT _ _ pgmv1);

      rfv1 : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv1 : M.find "rf"%string o = Some (existT _ _ rfv1);

      d2eeltv1 : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hd2eeltv1 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv1);
      d2efullv1 : fullType type (SyntaxKind Bool);
      Hd2efullv1 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv1);

      Hinv1 : p2st_decode_inv_body pgmv1 rfv1 d2efullv1 d2eeltv1 }.

  (* NOTE: this invariant requires p2st_scoreboard_inv *)
  Definition p2st_raw_inv_body
             (d2efullv stallv: fullType type (SyntaxKind Bool))
             (d2eeltv stalledv: fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx))) :=
    d2efullv = true -> stallv = true -> stalledv ``"opType" = opLd ->
    ((d2eeltv ``"opType" = opSt ->
      (stalledv ``"dst" <> evalExpr (getStSrc _ (d2eeltv ``"rawInst")) /\
       stalledv ``"dst" <> evalExpr (getStVSrc _ (d2eeltv ``"rawInst")))) /\
     (d2eeltv ``"opType" = opLd ->
      stalledv ``"dst" <> evalExpr (getLdSrc _ (d2eeltv ``"rawInst"))) /\
     (d2eeltv ``"opType" = opTh ->
      stalledv ``"dst" <> evalExpr (getSrc1 _ (d2eeltv ``"rawInst")))).

  Record p2st_raw_inv (o: RegsT) : Prop :=
    { d2eeltv2 : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hd2eeltv2 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv2);
      d2efullv2 : fullType type (SyntaxKind Bool);
      Hd2efullv2 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv2);

      stallv2 : fullType type (SyntaxKind Bool);
      Hstallv2 : M.find "stall"%string o = Some (existT _ _ stallv2);
      stalledv2 : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hstalledv2 : M.find "stalled"%string o = Some (existT _ _ stalledv2);

      Hinv : p2st_raw_inv_body d2efullv2 stallv2 d2eeltv2 stalledv2 }.

  Definition p2st_scoreboard_inv_body
             (d2efullv stallv sbvv: fullType type (SyntaxKind Bool))
             (sbv: fullType type (SyntaxKind (Bit rfIdx)))
             (d2eeltv stalledv: fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx))) :=
    stallv = true -> stalledv ``"opType" = opLd -> (sbvv = true /\ stalledv ``"dst" = sbv).

  Record p2st_scoreboard_inv (o: RegsT) : Prop :=
    { sbv3 : fullType type (SyntaxKind (Bit rfIdx));
      Hsbv3 : M.find "idx"%string o = Some (existT _ _ sbv3);
      sbvv3 : fullType type (SyntaxKind Bool);
      Hsbvv3 : M.find "valid"%string o = Some (existT _ _ sbvv3);

      d2eeltv3 : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hd2eeltv3 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv3);
      d2efullv3 : fullType type (SyntaxKind Bool);
      Hd2efullv3 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv3);

      stallv3 : fullType type (SyntaxKind Bool);
      Hstallv3 : M.find "stall"%string o = Some (existT _ _ stallv3);
      stalledv3 : fullType type (SyntaxKind (d2eElt addrSize lgDataBytes rfIdx));
      Hstalledv3 : M.find "stalled"%string o = Some (existT _ _ stalledv3);

      Hinv : p2st_scoreboard_inv_body d2efullv3 stallv3 sbvv3 sbv3 d2eeltv3 stalledv3 }.

  Hint Unfold p2st_pc_epochs_inv_body p2st_decode_inv_body
       p2st_raw_inv_body p2st_scoreboard_inv_body : InvDefs.

  Ltac p2st_inv_old :=
    repeat match goal with
           | [H: p2st_pc_epochs_inv _ |- _] => destruct H
           | [H: p2st_decode_inv _ |- _] => destruct H
           | [H: p2st_raw_inv _ |- _] => destruct H
           | [H: p2st_scoreboard_inv _ |- _] => destruct H
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

  Lemma p2st_scoreboard_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p2stInl) ->
      Multistep p2stInl init n ll ->
      p2st_scoreboard_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - p2st_inv_old.
      unfold getRegInits, p2stInl, ProcTwoStInl.p2stInl, projT1.
      p2st_inv_new; simpl in *; kinv_simpl.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac;
          try (match goal with
               | [H1: ?x ?s1 = _, H2: ?x ?s2 = _ |- _] => change s1 with s2 in H1
               end; rewrite e in H2; inv H2).
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.

        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma p2st_raw_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p2stInl) ->
      Multistep p2stInl init n ll ->
      p2st_raw_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p2st_inv_old.
      unfold getRegInits, fst, p2stInl, ProcTwoStInl.p2stInl, projT1.
      p2st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p2st_scoreboard_inv_ok' H H0).
      kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H5; inv H5; fail).
        rewrite andb_true_l in H14; kinv_simpl; intuition idtac.
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H7; inv H7; fail).
        * rewrite andb_true_l in H4; kinv_simpl; intuition idtac.
        * rewrite andb_true_l in H11; kinv_simpl; intuition idtac.
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H5; inv H5; fail).
        rewrite andb_true_l in H14; kinv_simpl; intuition idtac.
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H7; inv H7; fail).
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.

        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma p2st_decode_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p2stInl) ->
      Multistep p2stInl init n ll ->
      p2st_decode_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p2st_inv_old.
      unfold getRegInits, fst, p2stInl, ProcTwoStInl.p2stInl, projT1.
      p2st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p2st_raw_inv_ok' H H0).
      kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p2st_inv_tac; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
        * find_if_inside; [elim H15; auto|auto].
        * find_if_inside; [elim H9; auto|auto].
        * find_if_inside; [elim H17; auto|auto].
        * find_if_inside; [elim H7; auto|auto].
        * find_if_inside; [elim H15; auto|auto].
        * find_if_inside; [elim H9; auto|auto].
        * find_if_inside; [elim H17; auto|auto].
        * find_if_inside; [elim H7; auto|auto].
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.

        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma p2st_pc_epochs_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p2stInl) ->
      Multistep p2stInl init n ll ->
      p2st_pc_epochs_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p2st_inv_old.
      unfold getRegInits, fst, p2stInl, ProcTwoStInl.p2stInl, projT1.
      p2st_inv_new; simpl in *; kinv_simpl.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p2st_inv_tac.
        * destruct x0, eepochv0; intuition idtac.
        * destruct x0, eepochv0; intuition idtac.
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
      reachable o p2stInl ->
      p2st_pc_epochs_inv o /\ p2st_decode_inv o /\
      p2st_raw_inv o /\ p2st_scoreboard_inv o.
  Proof.
    intros; inv H; inv H0.
    repeat split.
    - eapply p2st_pc_epochs_inv_ok'; eauto.
    - eapply p2st_decode_inv_ok'; eauto.
    - eapply p2st_raw_inv_ok'; eauto.
    - eapply p2st_scoreboard_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold RqFromProc RsToProc: MethDefs.
Hint Unfold p2st_pc_epochs_inv_body p2st_decode_inv_body
     p2st_raw_inv_body p2st_scoreboard_inv_body : InvDefs.

