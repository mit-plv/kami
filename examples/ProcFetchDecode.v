Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcThreeStage.

Set Implicit Arguments.

Section F2dInst.
  Variables addrSize iaddrSize lgDataBytes rfIdx: nat.

  Definition f2dEltI :=
    STRUCT { "rawInst" :: Data lgDataBytes;
             "curPc" :: Bit addrSize;
             "nextPc" :: Bit addrSize;
             "epoch" :: Bool }.

  Definition f2dPackI ty 
             (rawInst: Expr ty (SyntaxKind (Data lgDataBytes)))
             (curPc: Expr ty (SyntaxKind (Bit addrSize)))
             (nextPc: Expr ty (SyntaxKind (Bit addrSize)))
             (epoch: Expr ty (SyntaxKind Bool)): Expr ty (SyntaxKind (Struct f2dEltI)) :=
    STRUCT { "rawInst" ::= rawInst;
             "curPc" ::= curPc;
             "nextPc" ::= nextPc;
             "epoch" ::= epoch }%kami_expr.

  Definition f2dRawInstI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind (Data lgDataBytes)) := (#f2d!f2dEltI@."rawInst")%kami_expr.
  Definition f2dCurPcI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#f2d!f2dEltI@."curPc")%kami_expr.
  Definition f2dNextPcI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#f2d!f2dEltI@."nextPc")%kami_expr.
  Definition f2dEpochI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind Bool) := (#f2d!f2dEltI@."epoch")%kami_expr.

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
 * in three-staged processor (P3st).
 *)
Section FetchAndDecode.
  Variables addrSize iaddrSize lgDataBytes rfIdx: nat.

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
            (alignPc: AlignPcT addrSize iaddrSize)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val2 *)
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

  Definition getRf1 := getRf1 lgDataBytes rfIdx.
  Definition d2eEnq := d2eEnq d2eElt.
  Definition w2dDeq := w2dDeq addrSize.
  Definition sbSearch1 := sbSearch1 rfIdx.
  Definition sbSearch2 := sbSearch2 rfIdx.
  Definition sbSearch3 := sbSearch3 rfIdx.
  Definition sbInsert := sbInsert rfIdx.
  
  Definition fetcher := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "pgm" : Vector (Data lgDataBytes) iaddrSize <- Default
    with Register "fEpoch" : Bool <- false

    with Rule "modifyPc" :=
      Call correctPc <- w2dDeq();
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
      LET apc <- alignPc _ pc;
      Call f2dEnq(f2dPack #pgm@[#apc] #pc #npc #epoch);
      Write "pc" <- #npc;
      Retv
  }.

  Definition decoder := MODULE {
    Rule "decodeLd" :=
      Call w2dFull <- w2dFull();
      Assert !#w2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf1();

      LET rawInst <- f2dRawInst _ f2d;

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opLd);

      LET srcIdx <- getLdSrc _ rawInst;
      LET dst <- getLdDst _ rawInst;
      Call stall1 <- sbSearch1(#srcIdx);
      Call stall2 <- sbSearch2(#dst);
      Assert !(#stall1 || #stall2);
      LET addr <- getLdAddr _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      LET curPc <- f2dCurPc _ f2d;
      LET nextPc <- f2dNextPc _ f2d;
      LET epoch <- f2dEpoch _ f2d;
      Call d2eEnq(d2ePack #opType #dst #laddr $$Default $$Default
                          #rawInst #curPc #nextPc #epoch);
      Call sbInsert(#dst);
      Retv

    with Rule "decodeSt" :=
      Call w2dFull <- w2dFull();
      Assert !#w2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf1();

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
      Call d2eEnq(d2ePack #opType $$Default #saddr #stVal $$Default
                          #rawInst #curPc #nextPc #epoch);
      Retv

    with Rule "decodeTh" :=
      Call w2dFull <- w2dFull();
      Assert !#w2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf1();

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
      Call d2eEnq(d2ePack #opType $$Default $$Default #srcVal $$Default
                          #rawInst #curPc #nextPc #epoch);
      Retv

    with Rule "decodeNm" :=
      Call w2dFull <- w2dFull();
      Assert !#w2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf1();

      LET rawInst <- f2dRawInst _ f2d;

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opNm);

      LET dst <- getDst _ rawInst;
      LET idx1 <- getSrc1 _ rawInst;
      LET idx2 <- getSrc2 _ rawInst;
      Call stall1 <- sbSearch1(#idx1);
      Call stall2 <- sbSearch2(#idx2);
      Call stall3 <- sbSearch3(#dst);
      Assert !(#stall1 || #stall2 || #stall3);

      LET val1 <- #rf@[#idx1];
      LET val2 <- #rf@[#idx2];

      LET curPc <- f2dCurPc _ f2d;
      LET nextPc <- f2dNextPc _ f2d;
      LET epoch <- f2dEpoch _ f2d;
      Call d2eEnq(d2ePack #opType #dst $$Default #val1 #val2
                          #rawInst #curPc #nextPc #epoch);
      Call sbInsert(#dst);
      Retv
  }.

  Definition fetchDecode := (fetcher
                               ++ oneEltFifoEx2 f2dFifoName f2dElt
                               ++ decoder)%kami.

End FetchAndDecode.

Hint Unfold fetcher decoder fetchDecode : ModuleDefs.
Hint Unfold f2dFifoName f2dEnq f2dDeq f2dFlush
     getRf1 d2eEnq w2dDeq sbSearch1 sbSearch2 sbSearch3 sbInsert : MethDefs.
  
Section Facts.
  Variables addrSize iaddrSize lgDataBytes rfIdx: nat.

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
            (alignPc: AlignPcT addrSize iaddrSize)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val2 *)
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
    ModPhoasWf (fetcher alignPc predictNextPc f2dPack).
  Proof. kequiv. Qed.
  Hint Resolve fetcher_ModEquiv.

  Lemma decoder_ModEquiv:
    ModPhoasWf (decoder getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                        getStAddr getStSrc calcStAddr getStVSrc getSrc1 getSrc2 getDst
                        d2ePack f2dRawInst f2dCurPc f2dNextPc f2dEpoch).
  Proof.
    kequiv.
  Qed.
  Hint Resolve decoder_ModEquiv.

  Lemma fetchDecode_ModEquiv:
    ModPhoasWf (fetchDecode getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                            getStAddr getStSrc calcStAddr getStVSrc
                            getSrc1 getSrc2 getDst alignPc predictNextPc d2ePack
                            f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve fetcher_ModEquiv decoder_ModEquiv fetchDecode_ModEquiv.

