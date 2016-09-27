Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcTwoStage.

Set Implicit Arguments.

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

  Definition f2dElt :=
    STRUCT { "rawInst" :: Data lgDataBytes;
             "curPc" :: Bit addrSize;
             "nextPc" :: Bit addrSize;
             "epoch" :: Bool }.
  Definition f2dFifoName := "f2d"%string.
  Definition f2dEnq := MethodSig (f2dFifoName -- "enq")(f2dElt) : Void.
  Definition f2dDeq := MethodSig (f2dFifoName -- "deq")() : f2dElt.
  Definition f2dFlush := MethodSig (f2dFifoName -- "flush")() : Void.

  Definition getRf := getRf lgDataBytes rfIdx.
  Definition d2eEnq := d2eEnq addrSize lgDataBytes rfIdx.
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
      Call f2dEnq(STRUCT { "rawInst" ::= #pgm@[#pc];
                           "curPc" ::= #pc;
                           "nextPc" ::= #npc;
                           "epoch" ::= #epoch });
      Write "pc" <- #npc;
      Retv
  }.

  Definition decoder := MODULE {
    Rule "decodeLd" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- #f2d@."rawInst";

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opLd);

      LET srcIdx <- getLdSrc _ rawInst;
      Call stall1 <- sbSearch1(#srcIdx);
      Assert !#stall1;
      LET addr <- getLdAddr _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      Call d2eEnq(STRUCT { "opType" ::= #opType;
                           "dst" ::= getLdDst _ rawInst;
                           "addr" ::= #laddr;
                           "val" ::= $$Default;
                           "rawInst" ::= #rawInst;
                           "curPc" ::= #f2d@."curPc";
                           "nextPc" ::= #f2d@."nextPc";
                           "epoch" ::= #f2d@."epoch" });
      Retv

    with Rule "decodeSt" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- #f2d@."rawInst";

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
      Call d2eEnq(STRUCT { "opType" ::= #opType;
                           "dst" ::= $$Default;
                           "addr" ::= #saddr;
                           "val" ::= #stVal;
                           "rawInst" ::= #rawInst;
                           "curPc" ::= #f2d@."curPc";
                           "nextPc" ::= #f2d@."nextPc";
                           "epoch" ::= #f2d@."epoch" });
      Retv

    with Rule "decodeTh" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- #f2d@."rawInst";

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opTh);

      LET srcIdx <- getSrc1 _ rawInst;
      Call stall1 <- sbSearch1(#srcIdx);
      Assert !#stall1;

      LET srcVal <- #rf@[#srcIdx];
      Call d2eEnq(STRUCT { "opType" ::= #opType;
                           "dst" ::= $$Default;
                           "addr" ::= $$Default;
                           "val" ::= #srcVal;
                           "rawInst" ::= #rawInst;
                           "curPc" ::= #f2d@."curPc";
                           "nextPc" ::= #f2d@."nextPc";
                           "epoch" ::= #f2d@."epoch" });
      Retv

    with Rule "decodeNm" :=
      Call e2dFull <- e2dFull();
      Assert !#e2dFull;
      Call f2d <- f2dDeq();
      Call rf <- getRf();

      LET rawInst <- #f2d@."rawInst";

      LET opType <- getOptype _ rawInst;
      Assert (#opType == $$opNm);

      Call d2eEnq(STRUCT { "opType" ::= #opType;
                           "dst" ::= $$Default;
                           "addr" ::= $$Default;
                           "val" ::= $$Default;
                           "rawInst" ::= #rawInst;
                           "curPc" ::= #f2d@."curPc";
                           "nextPc" ::= #f2d@."nextPc";
                           "epoch" ::= #f2d@."epoch" });
      Retv
  }.

  Definition fetchDecode := (fetcher
                               ++ oneEltFifoEx2 f2dFifoName f2dElt
                               ++ decoder)%kami.
  
End FetchDecode.

Hint Unfold fetcher decoder fetchDecode : ModuleDefs.
Hint Unfold f2dElt f2dFifoName f2dEnq f2dDeq f2dFlush
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

  Lemma fetcher_ModEquiv:
    ModPhoasWf (fetcher lgDataBytes predictNextPc).
  Proof. kequiv. Qed.
  Hint Resolve fetcher_ModEquiv.

  Lemma decoder_ModEquiv:
    ModPhoasWf (decoder getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                        getStAddr getStSrc calcStAddr getStVSrc
                        getSrc1).
  Proof. (* SKIP_PROOF_ON
    kequiv.
    END_SKIP_PROOF_ON *) admit.
  Qed.
  Hint Resolve decoder_ModEquiv.

  Lemma fetchDecode_ModEquiv:
    ModPhoasWf (fetchDecode getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                            getStAddr getStSrc calcStAddr getStVSrc
                            getSrc1 predictNextPc).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve fetcher_ModEquiv decoder_ModEquiv fetchDecode_ModEquiv.

