Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.OneEltFifo Ex.Fifo Ex.MemAsync Ex.ProcThreeStage.

Set Implicit Arguments.

Section F2dInst.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Definition f2dEltI :=
    STRUCT { "rawInst" :: Data instBytes;
             "curPc" :: Pc iaddrSize;
             "nextPc" :: Pc iaddrSize;
             "epoch" :: Bool }.

  Definition f2dPackI ty 
             (rawInst: Expr ty (SyntaxKind (Data instBytes)))
             (curPc: Expr ty (SyntaxKind (Pc iaddrSize)))
             (nextPc: Expr ty (SyntaxKind (Pc iaddrSize)))
             (epoch: Expr ty (SyntaxKind Bool)): Expr ty (SyntaxKind (Struct f2dEltI)) :=
    STRUCT { "rawInst" ::= rawInst;
             "curPc" ::= curPc;
             "nextPc" ::= nextPc;
             "epoch" ::= epoch }%kami_expr.

  Definition f2dRawInstI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind (Data instBytes)) := (#f2d!f2dEltI@."rawInst")%kami_expr.
  Definition f2dCurPcI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind (Pc iaddrSize)) := (#f2d!f2dEltI@."curPc")%kami_expr.
  Definition f2dNextPcI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind (Pc iaddrSize)) := (#f2d!f2dEltI@."nextPc")%kami_expr.
  Definition f2dEpochI ty (f2d: fullType ty (SyntaxKind (Struct f2dEltI)))
    : Expr ty (SyntaxKind Bool) := (#f2d!f2dEltI@."epoch")%kami_expr.

End F2dInst.

(* A pipelined "fetch" and "decode" modules. This module substitutes the {fetch, decode} stage
 * in three-staged processor (P3st).
 *)
Section FetchAndDecode.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx).

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Pc iaddrSize)).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Definition f2dFifoName := "f2d"%string.
  Definition f2dEnq := MethodSig (f2dFifoName -- "enq")(f2dElt) : Void.
  Definition f2dDeq := MethodSig (f2dFifoName -- "deq")() : f2dElt.
  Definition f2dFlush := MethodSig (f2dFifoName -- "flush")() : Void.

  Definition getRf1 := getRf1 dataBytes rfIdx.
  Definition d2eEnq := d2eEnq d2eElt.
  Definition w2dDeq := w2dDeq iaddrSize.
  Definition sbSearch1_Ld := sbSearch1_Ld rfIdx.
  Definition sbSearch2_Ld := sbSearch2_Ld rfIdx.
  Definition sbSearch1_St := sbSearch1_St rfIdx.
  Definition sbSearch2_St := sbSearch2_St rfIdx.
  Definition sbSearch1_Nm := sbSearch1_Nm rfIdx.
  Definition sbSearch2_Nm := sbSearch2_Nm rfIdx.
  Definition sbSearch3_Nm := sbSearch3_Nm rfIdx.
  Definition sbInsert := sbInsert rfIdx.

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Definition memReq := memReq addrSize dataBytes.
  Definition memRep := memRep dataBytes.

  Variables (pcInit : ConstT (Pc iaddrSize)).

  Definition fetcher := MODULE {
    Register "pc" : Pc iaddrSize <- pcInit
    with Register "pinit" : Bool <- Default
    with Register "pinitRqOfs" : Bit iaddrSize <- Default
    with Register "pinitRsOfs" : Bit iaddrSize <- Default
    with Register "pgm" : Vector (Data instBytes) iaddrSize <- Default
    with Register "fEpoch" : Bool <- false

    (** Phase 1: initialize the program [pinit == false] *)

    with Rule "pgmInitRq" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
      Assert ((UniBit (Inv _) #pinitRqOfs) != $0);

      Call memReq(STRUCT { "addr" ::= (_zeroExtend_ #pinitRqOfs) << $$(natToWord 2 2);
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Write "pinitRqOfs" <- #pinitRqOfs + $1;
      Retv

    with Rule "pgmInitRqEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
      Assert ((UniBit (Inv _) #pinitRqOfs) == $0);
      Call memReq(STRUCT { "addr" ::= (_zeroExtend_ #pinitRqOfs) << $$(natToWord 2 2);
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Retv
        
    with Rule "pgmInitRs" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRsOfs : Bit iaddrSize <- "pinitRsOfs";
      Assert ((UniBit (Inv _) #pinitRsOfs) != $0);

      Call ldData <- memRep();
      LET ldVal <- #ldData!RsToProc@."data";
      LET inst <- alignInst _ ldVal;
      Read pgm <- "pgm";
      Write "pgm" <- #pgm@[#pinitRsOfs <- #inst];
      Write "pinitRsOfs" <- #pinitRsOfs + $1;
      Retv

    with Rule "pgmInitRsEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRsOfs : Bit iaddrSize <- "pinitRsOfs";
      Assert ((UniBit (Inv _) #pinitRsOfs) == $0);

      Call ldData <- memRep();
      LET ldVal <- #ldData!RsToProc@."data";
      LET inst <- alignInst _ ldVal;
      Read pgm <- "pgm";
      Write "pgm" <- #pgm@[#pinitRsOfs <- #inst];
      Write "pinit" <- !#pinit;
      Retv

    (** Phase 2: execute the program [pinit == true] *)
                                  
    with Rule "modifyPc" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Call correctPc <- w2dDeq();
      Write "pc" <- #correctPc;
      Read pEpoch <- "fEpoch";
      Write "fEpoch" <- !#pEpoch;
      Call f2dFlush();
      Retv

    with Rule "instFetch" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Read pc : Pc iaddrSize <- "pc";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Read epoch <- "fEpoch";
      LET npc <- predictNextPc _ pc;
      Call f2dEnq(f2dPack #pgm@[_truncLsb_ #pc] #pc #npc #epoch);
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
      Call stall1 <- sbSearch1_Ld(#srcIdx);
      Call stall2 <- sbSearch2_Ld(#dst);
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
      Call stall1 <- sbSearch1_St(#srcIdx);
      Call stall2 <- sbSearch2_St(#vsrcIdx);
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
      Call stall1 <- sbSearch1_Nm(#idx1);
      Call stall2 <- sbSearch2_Nm(#idx2);
      Call stall3 <- sbSearch3_Nm(#dst);
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
     getRf1 d2eEnq w2dDeq sbSearch1_Ld sbSearch2_Ld
     sbSearch1_St sbSearch2_St sbSearch1_Nm
     sbSearch2_Nm sbSearch3_Nm sbInsert : MethDefs.
  
Section Facts.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx).

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Pc iaddrSize)).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Lemma fetcher_ModEquiv:
    forall pcInit, ModPhoasWf (fetcher addrSize fetch predictNextPc f2dPack pcInit).
  Proof. kequiv. Qed.
  Hint Resolve fetcher_ModEquiv.

  Lemma decoder_ModEquiv:
    ModPhoasWf (decoder dec d2ePack f2dRawInst f2dCurPc f2dNextPc f2dEpoch).
  Proof.
    kequiv.
  Qed.
  Hint Resolve decoder_ModEquiv.

  Lemma fetchDecode_ModEquiv:
    forall pcInit,
      ModPhoasWf (fetchDecode fetch dec predictNextPc
                              d2ePack f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                              pcInit).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve fetcher_ModEquiv decoder_ModEquiv fetchDecode_ModEquiv.

