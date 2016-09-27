Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcFetchDecode Ex.ProcFDInl.
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

  Definition fetchDecodeInl := projT1 (fetchDecodeInl
                                         getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                         getStAddr getStSrc calcStAddr getStVSrc
                                         getSrc1 predictNextPc).

  Definition fetchDecode_inv_body
             (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (pgmv: fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize)))
             (fepochv: fullType type (SyntaxKind Bool))
             (f2dfullv: fullType type (SyntaxKind Bool))
             (f2deltv: fullType type (SyntaxKind (f2dElt addrSize lgDataBytes))) :=
    f2dfullv = true ->
    let rawInst := f2deltv ``"rawInst" in
    (rawInst = pgmv (f2deltv ``"curPc") /\
     f2deltv ``"nextPc" = evalExpr (predictNextPc type (f2deltv ``"curPc")) /\
     f2deltv ``"nextPc" = pcv /\
     f2deltv ``"epoch" = fepochv).
                                                      
  Record fetchDecode_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Bit addrSize));
      Hpcv : M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv : M.find "pgm"%string o = Some (existT _ _ pgmv);
      fepochv : fullType type (SyntaxKind Bool);
      Hfepochv : M.find "fEpoch"%string o = Some (existT _ _ fepochv);

      f2dfullv : fullType type (SyntaxKind Bool);
      Hf2dfullv : M.find "full.f2d"%string o = Some (existT _ _ f2dfullv);
      f2deltv : fullType type (SyntaxKind (f2dElt addrSize lgDataBytes));
      Hf2deltv : M.find "elt.f2d"%string o = Some (existT _ _ f2deltv);

      Hinv : fetchDecode_inv_body pcv pgmv fepochv f2dfullv f2deltv
    }.

  Hint Unfold fetchDecode_inv_body : InvDefs.

  Ltac fetchDecode_inv_old :=
    repeat match goal with
           | [H: fetchDecode_inv _ |- _] => destruct H
           end;
    kinv_red.

  Ltac fetchDecode_inv_new :=
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

  Ltac fetchDecode_inv_tac := fetchDecode_inv_old; fetchDecode_inv_new.

  Lemma fetchDecode_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits fetchDecodeInl) ->
      Multistep fetchDecodeInl init n ll ->
      fetchDecode_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - fetchDecode_inv_old.
      unfold getRegInits, fetchDecodeInl, ProcFDInl.fetchDecodeInl, projT1.
      fetchDecode_inv_new; simpl in *; kinv_simpl.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.

        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma fetchDecode_inv_ok:
    forall o,
      reachable o fetchDecodeInl ->
      fetchDecode_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply fetchDecode_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold fetchDecode_inv_body : InvDefs.

