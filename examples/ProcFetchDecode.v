Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcTwoStage.

Set Implicit Arguments.

Section F2dInst.
  Variables addrSize lgDataBytes rfIdx: nat.

  Definition f2dEltI :=
    STRUCT { "rawInst" :: Data lgDataBytes;
             "curPc" :: Bit addrSize;
             "nextPc" :: Bit addrSize;
             "epoch" :: Bool }.

  Definition f2dPackI ty 
             (rawInst: Expr ty (SyntaxKind (Data lgDataBytes)))
             (curPc: Expr ty (SyntaxKind (Bit addrSize)))
             (nextPc: Expr ty (SyntaxKind (Bit addrSize)))
             (epoch: Expr ty (SyntaxKind Bool)): Expr ty (SyntaxKind f2dEltI) :=
    STRUCT { "rawInst" ::= rawInst;
             "curPc" ::= curPc;
             "nextPc" ::= nextPc;
             "epoch" ::= epoch }%kami_expr.

  Definition f2dRawInstI ty (f2d: fullType ty (SyntaxKind f2dEltI))
    : Expr ty (SyntaxKind (Data lgDataBytes)) := (#f2d@."rawInst")%kami_expr.
  Definition f2dCurPcI ty (f2d: fullType ty (SyntaxKind f2dEltI))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#f2d@."curPc")%kami_expr.
  Definition f2dNextPcI ty (f2d: fullType ty (SyntaxKind f2dEltI))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#f2d@."nextPc")%kami_expr.
  Definition f2dEpochI ty (f2d: fullType ty (SyntaxKind f2dEltI))
    : Expr ty (SyntaxKind Bool) := (#f2d@."epoch")%kami_expr.

  Lemma f2dElt_rawInst:
    forall rawInst curPc nextPc epoch,
      evalExpr (f2dRawInstI _ (evalExpr (f2dPackI rawInst curPc nextPc epoch)))
      = evalExpr rawInst.
  Proof. reflexivity. Qed.

  Lemma f2dElt_curPc:
    forall rawInst curPc nextPc epoch,
      evalExpr (f2dCurPcI _ (evalExpr (f2dPackI rawInst curPc nextPc epoch)))
      = evalExpr curPc.
  Proof. reflexivity. Qed.

  Lemma f2dElt_nextPc:
    forall rawInst curPc nextPc epoch,
      evalExpr (f2dNextPcI _ (evalExpr (f2dPackI rawInst curPc nextPc epoch)))
      = evalExpr nextPc.
  Proof. reflexivity. Qed.

  Lemma f2dElt_epoch:
    forall rawInst curPc nextPc epoch,
      evalExpr (f2dEpochI _ (evalExpr (f2dPackI rawInst curPc nextPc epoch)))
      = evalExpr epoch.
  Proof. reflexivity. Qed.

End F2dInst.

(* A pipelined "fetch" and "decode" modules. This module substitutes the {fetch, decode} stage
 * in two-staged processor (P2st).
 *)
Section FetchDecode.
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

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data lgDataBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Definition f2dFifoName := "f2d"%string.
  Definition f2dEnq := MethodSig (f2dFifoName -- "enq")(f2dElt) : Void.
  Definition f2dDeq := MethodSig (f2dFifoName -- "deq")() : f2dElt.
  Definition f2dFlush := MethodSig (f2dFifoName -- "flush")() : Void.

  Definition getRf := getRf lgDataBytes rfIdx.
  Definition d2eEnq := d2eEnq d2eElt.
  Definition e2dDeq := e2dDeq addrSize.
  Definition sbSearch1 := sbSearch1 rfIdx.
  Definition sbSearch2 := sbSearch2 rfIdx.
  
  Definition fetcher := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "pgm" : Vector (Data lgDataBytes) addrSize <- Default
    with Register "fEpoch" : Bool <- false

    with Rule "modifyPc" :=
      Call correctPc <- e2dDeq();
      Write "pc" <- #correctPc;
      Read pEpoch <- "fEpoch";
      Write "fEpoch" <- !#pEpoch;
      Call f2dFlush();
      Retv

    with Rule "instFetch" :=
      Read pc <- "pc";
      Read pgm <- "pgm";
      Read epoch <- "fEpoch";
      LET npc <- predictNextPc _ pc;
      Call f2dEnq(f2dPack #pgm@[#pc] #pc #npc #epoch);
      Write "pc" <- #npc;
      Retv
  }.

  Definition decoder := MODULE {
    Rule "decodeLd" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- f2dRawInst _ f2d;

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opLd);

      LET srcIdx <- getLdSrc _ rawInst;
      Call stall1 <- sbSearch1(#srcIdx);
      Assert !#stall1;
      LET addr <- getLdAddr _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      LET curPc <- f2dCurPc _ f2d;
      LET nextPc <- f2dNextPc _ f2d;
      LET epoch <- f2dEpoch _ f2d;
      Call d2eEnq(d2ePack #opType (getLdDst _ rawInst) #laddr $$Default
                          #rawInst #curPc #nextPc #epoch);
      Retv

    with Rule "decodeSt" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- f2dRawInst _ f2d;

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opSt);

      LET srcIdx <- getStSrc _ rawInst;
      LET vsrcIdx <- getStVSrc _ rawInst;
      Call stall1 <- sbSearch1(#srcIdx);
      Call stall2 <- sbSearch2(#vsrcIdx);
      Assert !(#stall1 || #stall2);

      LET addr <- getStAddr _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET stVal <- #rf@[#vsrcIdx];
      LET saddr <- calcStAddr _ addr srcVal;
      LET curPc <- f2dCurPc _ f2d;
      LET nextPc <- f2dNextPc _ f2d;
      LET epoch <- f2dEpoch _ f2d;
      Call d2eEnq(d2ePack #opType $$Default #saddr #stVal
                          #rawInst #curPc #nextPc #epoch);
      Retv

    with Rule "decodeTh" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- f2dRawInst _ f2d;

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opTh);

      LET srcIdx <- getSrc1 _ rawInst;
      Call stall1 <- sbSearch1(#srcIdx);
      Assert !#stall1;

      LET srcVal <- #rf@[#srcIdx];
      LET curPc <- f2dCurPc _ f2d;
      LET nextPc <- f2dNextPc _ f2d;
      LET epoch <- f2dEpoch _ f2d;
      Call d2eEnq(d2ePack #opType $$Default $$Default #srcVal
                          #rawInst #curPc #nextPc #epoch);
      Retv

    with Rule "decodeNm" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- f2dRawInst _ f2d;

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opNm);

      LET curPc <- f2dCurPc _ f2d;
      LET nextPc <- f2dNextPc _ f2d;
      LET epoch <- f2dEpoch _ f2d;
      Call d2eEnq(d2ePack #opType $$Default $$Default $$Default
                          #rawInst #curPc #nextPc #epoch);
      Retv
  }.

  Definition fetchDecode := (fetcher
                               ++ oneEltFifoEx2 f2dFifoName f2dElt
                               ++ decoder)%kami.
  
End FetchDecode.

Hint Unfold fetcher decoder fetchDecode : ModuleDefs.
Hint Unfold f2dFifoName f2dEnq f2dDeq f2dFlush
     getRf d2eEnq e2dDeq sbSearch1 sbSearch2 : MethDefs.

(* TODO: Hint Unfold flush should be moved to ProcTwoStage.v *)
Hint Unfold f2dFlush flush : MethDefs.

Section Facts.
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

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data lgDataBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Lemma fetcher_ModEquiv:
    ModPhoasWf (fetcher predictNextPc f2dPack).
  Proof. kequiv. Qed.
  Hint Resolve fetcher_ModEquiv.

  Lemma decoder_ModEquiv:
    ModPhoasWf (decoder getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                        getStAddr getStSrc calcStAddr getStVSrc getSrc1
                        d2ePack f2dRawInst f2dCurPc f2dNextPc f2dEpoch).
  Proof. (* SKIP_PROOF_ON
    kequiv.
    END_SKIP_PROOF_ON *) admit.
  Qed.
  Hint Resolve decoder_ModEquiv.

  Lemma fetchDecode_ModEquiv:
    ModPhoasWf (fetchDecode getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                            getStAddr getStSrc calcStAddr getStVSrc
                            getSrc1 predictNextPc d2ePack
                            f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve fetcher_ModEquiv decoder_ModEquiv fetchDecode_ModEquiv.

