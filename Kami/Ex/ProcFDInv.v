Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcFetchDecode Ex.ProcFDInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
  Variables addrSize iaddrSize dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT dataBytes)
            (getLdDst: LdDstT dataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize dataBytes)
            (getLdSrc: LdSrcT dataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize dataBytes)
            (getStSrc: StSrcT dataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT dataBytes rfIdx)
            (getSrc1: Src1T dataBytes rfIdx)
            (getSrc2: Src2T dataBytes rfIdx)
            (getDst: DstT dataBytes rfIdx)
            (exec: ExecT addrSize dataBytes)
            (getNextPc: NextPcT addrSize dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data dataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data dataBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Hypotheses (Hf2dRawInst: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dRawInst _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr rawInst)
             (Hf2dCurPc: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dCurPc _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr curPc)
             (Hf2dNextPc: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dNextPc _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr nextPc)
             (Hf2dEpoch: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dEpoch _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr epoch).

  Variables (pcInit : ConstT (Bit addrSize))
            (pgmInit : ConstT (Vector (Data dataBytes) iaddrSize)).
  
  Definition fetchDecodeInl := projT1 (fetchDecodeInl
                                         getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                         getStAddr getStSrc calcStAddr getStVSrc
                                         getSrc1 getSrc2 getDst alignPc predictNextPc
                                         d2ePack f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                                         pcInit pgmInit).

  Definition fetchDecode_inv_body
             (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (pgmv: fullType type (SyntaxKind (Vector (Data dataBytes) iaddrSize)))
             (fepochv: fullType type (SyntaxKind Bool))
             (f2dfullv: fullType type (SyntaxKind Bool))
             (f2deltv: fullType type (SyntaxKind f2dElt)) :=
    f2dfullv = true ->
    let rawInst := evalExpr (f2dRawInst _ f2deltv) in
    (rawInst = pgmv (evalExpr (alignPc _ (evalExpr (f2dCurPc _ f2deltv)))) /\
     evalExpr (f2dNextPc _ f2deltv) =
     evalExpr (predictNextPc type (evalExpr (f2dCurPc _ f2deltv))) /\
     evalExpr (f2dNextPc _ f2deltv) = pcv /\
     evalExpr (f2dEpoch _ f2deltv) = fepochv).
                                                      
  Record fetchDecode_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Bit addrSize));
      Hpcv : M.find "pc"%string o = Some (existT _ _ pcv);
      pgmv : fullType type (SyntaxKind (Vector (Data dataBytes) iaddrSize));
      Hpgmv : M.find "pgm"%string o = Some (existT _ _ pgmv);
      fepochv : fullType type (SyntaxKind Bool);
      Hfepochv : M.find "fEpoch"%string o = Some (existT _ _ fepochv);

      f2dfullv : fullType type (SyntaxKind Bool);
      Hf2dfullv : M.find "full.f2d"%string o = Some (existT _ _ f2dfullv);
      f2deltv : fullType type (SyntaxKind f2dElt);
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

  Ltac f2d_abs_tac :=
    try rewrite Hf2dRawInst in *;
    try rewrite Hf2dCurPc in *;
    try rewrite Hf2dNextPc in *;
    try rewrite Hf2dEpoch in *.

  Ltac fetchDecode_inv_tac := fetchDecode_inv_old; fetchDecode_inv_new; f2d_abs_tac.

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
      + kinv_dest_custom fetchDecode_inv_tac; kinv_eq.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.
      + kinv_dest_custom fetchDecode_inv_tac.
        END_SKIP_PROOF_ON *) apply cheat.
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

