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
            (getDst: DstT lgDataBytes rfIdx)
            (exec: ExecT addrSize lgDataBytes)
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eVal: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  Hypotheses (Hd2eOpType: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eOpType _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr opType)
             (Hd2eDst: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eDst _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr dst)
             (Hd2eAddr: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eAddr _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr addr)
             (Hd2eVal: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eVal _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr val)
             (Hd2eRawInst: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eRawInst _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr rawInst)
             (Hd2eCurPc: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eCurPc _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr curPc)
             (Hd2eNextPc: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eNextPc _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr nextPc)
             (Hd2eEpoch: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eEpoch _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr epoch).
  

  Definition p2stInl := projT1 (p2stInl getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                        getStAddr getStSrc calcStAddr getStVSrc
                                        getSrc1 getSrc2 getDst exec getNextPc predictNextPc
                                        d2ePack d2eOpType d2eDst d2eAddr d2eVal
                                        d2eRawInst d2eCurPc d2eNextPc d2eEpoch).

  Definition p2st_pc_epochs_inv_body
             (fepochv eepochv d2efullv e2dfullv stallv: fullType type (SyntaxKind Bool))
             (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (d2eeltv stalledv: fullType type (SyntaxKind d2eElt)) :=
    (fepochv = eepochv -> e2dfullv = false) /\ (e2dfullv = false -> fepochv = eepochv) /\
    (fepochv <> eepochv -> e2dfullv = true) /\ (e2dfullv = true -> fepochv <> eepochv) /\

    (e2dfullv = true -> d2efullv = true -> evalExpr (d2eEpoch _ d2eeltv) = fepochv) /\
    (d2efullv = true -> evalExpr (d2eEpoch _ d2eeltv) = fepochv ->
     evalExpr (d2eNextPc _ d2eeltv) = pcv) /\
    (d2efullv = true -> evalExpr (d2eEpoch _ d2eeltv) = eepochv -> e2dfullv = false) /\

    (stallv = true -> e2dfullv = false) /\

    (stallv = true -> d2efullv = true ->
     (evalExpr (d2eNextPc _ stalledv) = evalExpr (d2eCurPc _ d2eeltv) /\
      evalExpr (d2eEpoch _ d2eeltv) = fepochv)) /\
    (stallv = true -> d2efullv = false -> e2dfullv = false ->
     evalExpr (d2eNextPc _ stalledv) = pcv).

  Record p2st_pc_epochs_inv (o: RegsT) : Prop :=
    { pcv0 : fullType type (SyntaxKind (Bit addrSize));
      Hpcv0 : M.find "pc"%string o = Some (existT _ _ pcv0);
      fepochv0 : fullType type (SyntaxKind Bool);
      Hfepochv0 : M.find "fEpoch"%string o = Some (existT _ _ fepochv0);

      d2eeltv0 : fullType type (SyntaxKind d2eElt);
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
      stalledv0 : fullType type (SyntaxKind d2eElt);
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
             (d2eeltv: fullType type (SyntaxKind d2eElt)) :=
    d2efullv = true ->
    let rawInst := evalExpr (d2eRawInst _ d2eeltv) in
    (rawInst = pgmv (evalExpr (d2eCurPc _ d2eeltv)) /\
     evalExpr (d2eOpType _ d2eeltv) = evalExpr (getOptype _ rawInst) /\
     (evalExpr (d2eOpType _ d2eeltv) = opLd ->
      (evalExpr (d2eDst _ d2eeltv) = evalExpr (getLdDst _ rawInst) /\
       evalExpr (d2eAddr _ d2eeltv) =
       evalExpr (calcLdAddr _ (evalExpr (getLdAddr _ rawInst))
                            (rfv (evalExpr (getLdSrc _ rawInst)))))) /\
     (evalExpr (d2eOpType _ d2eeltv) = opSt ->
      evalExpr (d2eAddr _ d2eeltv) =
      evalExpr (calcStAddr _ (evalExpr (getStAddr _ rawInst))
                           (rfv (evalExpr (getStSrc _ rawInst)))) /\
      evalExpr (d2eVal _ d2eeltv) = rfv (evalExpr (getStVSrc _ rawInst)))) /\
    (evalExpr (d2eOpType _ d2eeltv) = opTh ->
     evalExpr (d2eVal _ d2eeltv) = rfv (evalExpr (getSrc1 _ rawInst))).

  Record p2st_decode_inv (o: RegsT) : Prop :=
    { pgmv1 : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv1 : M.find "pgm"%string o = Some (existT _ _ pgmv1);

      rfv1 : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv1 : M.find "rf"%string o = Some (existT _ _ rfv1);

      d2eeltv1 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv1 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv1);
      d2efullv1 : fullType type (SyntaxKind Bool);
      Hd2efullv1 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv1);

      Hinv1 : p2st_decode_inv_body pgmv1 rfv1 d2efullv1 d2eeltv1 }.

  (* NOTE: this invariant requires p2st_decode_inv *)
  Definition p2st_stalled_inv_body
             (pgmv: fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize)))
             (rfv: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (stallv: fullType type (SyntaxKind Bool))
             (stalledv: fullType type (SyntaxKind d2eElt)) :=
    stallv = true ->
    let rawInst := evalExpr (d2eRawInst _ stalledv) in
    evalExpr (d2eOpType _ stalledv) = evalExpr (getOptype _ rawInst) /\
    rawInst = pgmv (evalExpr (d2eCurPc _ stalledv)) /\
    (evalExpr (d2eOpType _ stalledv) = opLd ->
     evalExpr (d2eDst _ stalledv) = evalExpr (getLdDst _ rawInst)).

  Record p2st_stalled_inv (o: RegsT) : Prop :=
    { pgmv2 : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv2 : M.find "pgm"%string o = Some (existT _ _ pgmv2);

      rfv2 : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv2 : M.find "rf"%string o = Some (existT _ _ rfv2);

      stallv2 : fullType type (SyntaxKind Bool);
      Hstallv2 : M.find "stall"%string o = Some (existT _ _ stallv2);
      stalledv2 : fullType type (SyntaxKind d2eElt);
      Hstalledv2 : M.find "stalled"%string o = Some (existT _ _ stalledv2);

      Hinv2 : p2st_decode_inv_body pgmv2 rfv2 stallv2 stalledv2 }.
  
  (* NOTE: this invariant requires p2st_scoreboard_inv *)
  Definition p2st_raw_inv_body
             (d2efullv stallv: fullType type (SyntaxKind Bool))
             (d2eeltv stalledv: fullType type (SyntaxKind d2eElt)) :=
    d2efullv = true -> stallv = true -> evalExpr (d2eOpType _ stalledv) = opLd ->
    ((evalExpr (d2eOpType _ d2eeltv) = opSt ->
      (evalExpr (d2eDst _ stalledv) <> evalExpr (getStSrc _ (evalExpr (d2eRawInst _ d2eeltv))) /\
       evalExpr (d2eDst _ stalledv) <> evalExpr (getStVSrc _ (evalExpr (d2eRawInst _ d2eeltv))))) /\
     (evalExpr (d2eOpType _ d2eeltv) = opLd ->
      evalExpr (d2eDst _ stalledv) <> evalExpr (getLdSrc _ (evalExpr (d2eRawInst _ d2eeltv)))) /\
     (evalExpr (d2eOpType _ d2eeltv) = opTh ->
      evalExpr (d2eDst _ stalledv) <> evalExpr (getSrc1 _ (evalExpr (d2eRawInst _ d2eeltv))))).

  Record p2st_raw_inv (o: RegsT) : Prop :=
    { d2eeltv3 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv3 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv3);
      d2efullv3 : fullType type (SyntaxKind Bool);
      Hd2efullv3 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv3);

      stallv3 : fullType type (SyntaxKind Bool);
      Hstallv3 : M.find "stall"%string o = Some (existT _ _ stallv3);
      stalledv3 : fullType type (SyntaxKind d2eElt);
      Hstalledv3 : M.find "stalled"%string o = Some (existT _ _ stalledv3);

      Hinv : p2st_raw_inv_body d2efullv3 stallv3 d2eeltv3 stalledv3 }.

  Definition p2st_scoreboard_inv_body
             (d2efullv stallv sbvv: fullType type (SyntaxKind Bool))
             (sbv: fullType type (SyntaxKind (Bit rfIdx)))
             (d2eeltv stalledv: fullType type (SyntaxKind d2eElt)) :=
    stallv = true -> evalExpr (d2eOpType _ stalledv) = opLd ->
    (sbvv = true /\ evalExpr (d2eDst _ stalledv) = sbv).

  Record p2st_scoreboard_inv (o: RegsT) : Prop :=
    { sbv4 : fullType type (SyntaxKind (Bit rfIdx));
      Hsbv4 : M.find "idx"%string o = Some (existT _ _ sbv4);
      sbvv4 : fullType type (SyntaxKind Bool);
      Hsbvv4 : M.find "valid"%string o = Some (existT _ _ sbvv4);

      d2eeltv4 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv4 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv4);
      d2efullv4 : fullType type (SyntaxKind Bool);
      Hd2efullv4 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv4);

      stallv4 : fullType type (SyntaxKind Bool);
      Hstallv4 : M.find "stall"%string o = Some (existT _ _ stallv4);
      stalledv4 : fullType type (SyntaxKind d2eElt);
      Hstalledv4 : M.find "stalled"%string o = Some (existT _ _ stalledv4);

      Hinv : p2st_scoreboard_inv_body d2efullv4 stallv4 sbvv4 sbv4 d2eeltv4 stalledv4 }.

  Hint Unfold p2st_pc_epochs_inv_body p2st_decode_inv_body p2st_stalled_inv_body
       p2st_raw_inv_body p2st_scoreboard_inv_body : InvDefs.

  Ltac p2st_inv_old :=
    repeat match goal with
           | [H: p2st_pc_epochs_inv _ |- _] => destruct H
           | [H: p2st_decode_inv _ |- _] => destruct H
           | [H: p2st_stalled_inv _ |- _] => destruct H
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

  Ltac d2e_abs_tac :=
    try rewrite Hd2eOpType in *;
    try rewrite Hd2eDst in *;
    try rewrite Hd2eAddr in *;
    try rewrite Hd2eVal in *;
    try rewrite Hd2eRawInst in *;
    try rewrite Hd2eCurPc in *;
    try rewrite Hd2eNextPc in *;
    try rewrite Hd2eEpoch in *.

  Ltac p2st_inv_tac := p2st_inv_old; p2st_inv_new; d2e_abs_tac.

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
      + kinv_dest_custom p2st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p2st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p2st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p2st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
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

  Lemma p2st_stalled_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p2stInl) ->
      Multistep p2stInl init n ll ->
      p2st_stalled_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p2st_inv_old.
      unfold getRegInits, fst, p2stInl, ProcTwoStInl.p2stInl, projT1.
      p2st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p2st_decode_inv_ok' H H0).
      kinvert.
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
      + kinv_dest_custom p2st_inv_tac.
      + kinv_dest_custom p2st_inv_tac.
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
      + kinv_dest_custom p2st_inv_tac; try reflexivity.
      + kinv_dest_custom p2st_inv_tac; try reflexivity.
      + kinv_dest_custom p2st_inv_tac; try reflexivity.
      + kinv_dest_custom p2st_inv_tac; try reflexivity.
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
      p2st_pc_epochs_inv o /\ p2st_decode_inv o /\ p2st_stalled_inv o /\
      p2st_raw_inv o /\ p2st_scoreboard_inv o.
  Proof.
    intros; inv H; inv H0.
    repeat split.
    - eapply p2st_pc_epochs_inv_ok'; eauto.
    - eapply p2st_decode_inv_ok'; eauto.
    - eapply p2st_stalled_inv_ok'; eauto.
    - eapply p2st_raw_inv_ok'; eauto.
    - eapply p2st_scoreboard_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold p2st_pc_epochs_inv_body p2st_decode_inv_body p2st_stalled_inv_body
     p2st_raw_inv_body p2st_scoreboard_inv_body : InvDefs.

