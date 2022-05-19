Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.Tactics.
Require Import Kami.PrimFifo.
Require Import Ex.MemTypes Ex.SC Ex.MemAsync Ex.ProcDec.

Set Implicit Arguments.

Section D2eInst.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Definition d2eEltI :=
    STRUCT { "opType" :: Bit 2;
             "dst" :: Bit rfIdx;
             "addr" :: Bit addrSize;
             "byteEn" :: Array Bool dataBytes;
             "val1" :: Data dataBytes;
             "val2" :: Data dataBytes;
             "rawInst" :: Data instBytes;
             "curPc" :: Pc iaddrSize;
             "nextPc" :: Pc iaddrSize;
             "epoch" :: Bool }.

  Definition d2ePackI ty 
             (opTy: Expr ty (SyntaxKind (Bit 2)))
             (dst: Expr ty (SyntaxKind (Bit rfIdx)))
             (addr: Expr ty (SyntaxKind (Bit addrSize)))
             (byteEn: Expr ty (SyntaxKind (Array Bool dataBytes)))
             (val1 val2: Expr ty (SyntaxKind (Data dataBytes)))
             (rawInst: Expr ty (SyntaxKind (Data instBytes)))
             (curPc: Expr ty (SyntaxKind (Pc iaddrSize)))
             (nextPc: Expr ty (SyntaxKind (Pc iaddrSize)))
             (epoch: Expr ty (SyntaxKind Bool)): Expr ty (SyntaxKind (Struct d2eEltI)) :=
    STRUCT { "opType" ::= opTy;
             "dst" ::= dst;
             "addr" ::= addr;
             "byteEn" ::= byteEn;
             "val1" ::= val1;
             "val2" ::= val2;
             "rawInst" ::= rawInst;
             "curPc" ::= curPc;
             "nextPc" ::= nextPc;
             "epoch" ::= epoch }%kami_expr.

  Definition d2eOpTypeI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Bit 2)) := (#d2e!d2eEltI@."opType")%kami_expr.
  Definition d2eDstI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Bit rfIdx)) := (#d2e!d2eEltI@."dst")%kami_expr.
  Definition d2eAddrI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#d2e!d2eEltI@."addr")%kami_expr.
  Definition d2eByteEnI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Array Bool dataBytes)) := (#d2e!d2eEltI@."byteEn")%kami_expr.
  Definition d2eVal1I ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Data dataBytes)) := (#d2e!d2eEltI@."val1")%kami_expr.
  Definition d2eVal2I ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Data dataBytes)) := (#d2e!d2eEltI@."val2")%kami_expr.
  Definition d2eRawInstI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Data instBytes)) := (#d2e!d2eEltI@."rawInst")%kami_expr.
  Definition d2eCurPcI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Pc iaddrSize)) := (#d2e!d2eEltI@."curPc")%kami_expr.
  Definition d2eNextPcI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Pc iaddrSize)) := (#d2e!d2eEltI@."nextPc")%kami_expr.
  Definition d2eEpochI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind Bool) := (#d2e!d2eEltI@."epoch")%kami_expr.

End D2eInst.

Section E2wInst.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Definition e2wEltI :=
    STRUCT { "decInst" :: Struct (d2eEltI addrSize iaddrSize instBytes dataBytes rfIdx);
             "val" :: Data dataBytes }.

  Definition e2wPackI ty
             (decInst: Expr ty (SyntaxKind (Struct (d2eEltI addrSize iaddrSize instBytes dataBytes rfIdx))))
             (val: Expr ty (SyntaxKind (Data dataBytes))) : Expr ty (SyntaxKind (Struct e2wEltI))
    := STRUCT { "decInst" ::= decInst;
                "val" ::= val }%kami_expr.

  Definition e2wDecInstI ty (e2w: fullType ty (SyntaxKind (Struct e2wEltI)))
    : Expr ty (SyntaxKind (Struct (d2eEltI addrSize iaddrSize instBytes dataBytes rfIdx))) :=
    (#e2w!e2wEltI@."decInst")%kami_expr.
  Definition e2wValI ty (e2w: fullType ty (SyntaxKind (Struct e2wEltI)))
    : Expr ty (SyntaxKind (Data dataBytes)) := (#e2w!e2wEltI@."val")%kami_expr.

End E2wInst.
  
(* A three-staged processor, where three sets -- {fetch, decode}, {execute}, and 
 * {mem, write-back} -- are modularly separated to form each stage. "epoch" registers are
 * used to handle incorrect branch prediction. Like a decoupled processor, memory operations are
 * stalled until getting the response.
 *)
Section ProcThreeStage.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Definition memReq := memReq addrSize dataBytes.
  Definition memRep := memRep dataBytes.

  (* Abstract d2eElt *)
  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Array Bool dataBytes)) -> (* byteEn *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eByteEn: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Array Bool dataBytes)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data dataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Pc addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Pc addrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  (* Abstract e2wElt *)
  Variable (e2wElt: Kind).
  Variable (e2wPack:
              forall ty,
                Expr ty (SyntaxKind d2eElt) -> (* decInst *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* execVal *)
                Expr ty (SyntaxKind e2wElt)).
  Variables
    (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                            Expr ty (SyntaxKind d2eElt))
    (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Data dataBytes))).
  
  Definition d2eFifoName := "d2e"%string.
  Definition d2eEnq := MethodSig (d2eFifoName -- "enq")(d2eElt) : Void.
  Definition d2eDeq := MethodSig (d2eFifoName -- "deq")() : d2eElt.

  (** For redirecting a correct pc: a previous pc is sent as well to train
   * the branch predictor. *)
  Definition W2DStr := STRUCT { "prevPc" :: Pc addrSize; "nextPc" :: Pc addrSize }.
  Definition w2dElt := Struct W2DStr.
  Definition w2dFifoName := "w2d"%string.
  Definition w2dEnq := MethodSig (w2dFifoName -- "enq")(w2dElt) : Void.
  Definition w2dDeq := MethodSig (w2dFifoName -- "deq")() : w2dElt.
  Definition w2dFull := MethodSig (w2dFifoName -- "isFull")() : Bool.

  Definition e2wFifoName := "e2w"%string.
  Definition e2wEnq := MethodSig (e2wFifoName -- "enq")(e2wElt) : Void.
  Definition e2wDeq := MethodSig (e2wFifoName -- "deq")() : e2wElt.
  
  Section RegFile.
    Variable rfInit: ConstT (Vector (Data dataBytes) rfIdx).

    Definition regFile := MODULE {
      Register "rf" : Vector (Data dataBytes) rfIdx <- rfInit

      with Method "getRf1" () : Vector (Data dataBytes) rfIdx :=
        Read rf <- "rf";
        Ret #rf

      with Method "getRf2" () : Vector (Data dataBytes) rfIdx :=
        Read rf <- "rf";
        Ret #rf

      with Method "setRf" (rf: Vector (Data dataBytes) rfIdx) : Void :=
        Write "rf" <- #rf;
        Retv
    }.
      
    Definition getRf1 := MethodSig "getRf1"() : Vector (Data dataBytes) rfIdx.
    Definition getRf2 := MethodSig "getRf2"() : Vector (Data dataBytes) rfIdx.
    Definition setRf := MethodSig "setRf"(Vector (Data dataBytes) rfIdx) : Void.

  End RegFile.

  Section Epoch.
    
    Definition epoch := MODULE {
      Register "eEpoch" : Bool <- false

      with Method "getEpoch" () : Bool :=
        Read epoch <- "eEpoch";
        Ret #epoch

      with Method "toggleEpoch" () : Void :=
        Read epoch <- "eEpoch";
        Write "eEpoch" <- !#epoch;
        Retv
    }.

    Definition getEpoch := MethodSig "getEpoch"() : Bool.
    Definition toggleEpoch := MethodSig "toggleEpoch"() : Void.

  End Epoch.

  Section ScoreBoard.

    Definition scoreBoard := MODULE {
      Register "sbFlags" : Vector Bool rfIdx <- Default
                                 
      with Method "sbSearch1_Ld" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch2_Ld" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch1_St" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]
            
      with Method "sbSearch2_St" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch1_Nm" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]
            
      with Method "sbSearch2_Nm" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch3_Nm" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]
            
      with Method "sbInsert" (nidx: Bit rfIdx) : Void :=
        Read flags <- "sbFlags";
        Write "sbFlags" <- #flags@[#nidx <- $$true];
        Retv

      with Method "sbRemove" (nidx: Bit rfIdx) : Void :=
        Read flags <- "sbFlags";
        Write "sbFlags" <- #flags@[#nidx <- $$false];
        Retv
    }.

    Definition sbSearch1_Ld := MethodSig "sbSearch1_Ld"(Bit rfIdx) : Bool.
    Definition sbSearch2_Ld := MethodSig "sbSearch2_Ld"(Bit rfIdx) : Bool.
    Definition sbSearch1_St := MethodSig "sbSearch1_St"(Bit rfIdx) : Bool.
    Definition sbSearch2_St := MethodSig "sbSearch2_St"(Bit rfIdx) : Bool.
    Definition sbSearch1_Nm := MethodSig "sbSearch1_Nm"(Bit rfIdx) : Bool.
    Definition sbSearch2_Nm := MethodSig "sbSearch2_Nm"(Bit rfIdx) : Bool.
    Definition sbSearch3_Nm := MethodSig "sbSearch3_Nm"(Bit rfIdx) : Bool.
    Definition sbInsert := MethodSig "sbInsert"(Bit rfIdx) : Void.
    Definition sbRemove := MethodSig "sbRemove"(Bit rfIdx) : Void.
    
  End ScoreBoard.

  Section FetchDecode.
    Variable (pcInit : ConstT (Pc addrSize)).

    Definition fetchDecode := MODULE {
      Register "pc" : Pc addrSize <- pcInit
      with Register "pinit" : Bool <- Default
      with Register "pinitRq" : Bool <- Default
      with Register "pinitRqOfs" : Bit iaddrSize <- Default
      with Register "pinitRsOfs" : Bit iaddrSize <- Default
      with Register "pgm" : Vector (Data instBytes) iaddrSize <- Default
      with Register "fEpoch" : Bool <- false

      (** Phase 1: initialize the program [pinit == false] *)

      with Rule "pgmInitRq" :=
        Read pinit <- "pinit";
        Assert !#pinit;
        Read pinitRq <- "pinitRq";
        Assert !#pinitRq;
        Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
        Assert ((UniBit (Inv _) #pinitRqOfs) != $0);

        Call memReq(STRUCT { "addr" ::= toAddr _ pinitRqOfs;
                             "op" ::= $$false;
                             "byteEn" ::= $$Default;
                             "data" ::= $$Default });
        Write "pinitRqOfs" <- #pinitRqOfs + $1;
        Retv

      with Rule "pgmInitRqEnd" :=
        Read pinit <- "pinit";
        Assert !#pinit;
        Read pinitRq <- "pinitRq";
        Assert !#pinitRq;
        Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
        Assert ((UniBit (Inv _) #pinitRqOfs) == $0);
        Call memReq(STRUCT { "addr" ::= toAddr _ pinitRqOfs;
                             "op" ::= $$false;
                             "byteEn" ::= $$Default;
                             "data" ::= $$Default });
        Write "pinitRq" <- $$true;
        Write "pinitRqOfs" : Bit iaddrSize <- $0;
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
        Write "pinitRsOfs" : Bit iaddrSize <- $0;
        Retv

      (** Phase 2: fetch/decode the program [pinit == true] *)
          
      with Rule "modifyPc" :=
        Read pinit <- "pinit";
        Assert #pinit;
        Call correctPc <- w2dDeq();
        Write "pc" <- #correctPc!W2DStr@."nextPc";
        Read pEpoch <- "fEpoch";
        Write "fEpoch" <- !#pEpoch;
        Retv
          
      with Rule "instFetchLd" :=
        Read pinit <- "pinit";
        Call w2dFull <- w2dFull();
        Assert !#w2dFull;
        Read ppc : Pc addrSize <- "pc";
        Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
        Assert #pinit;
        LET rawInst <- #pgm@[toIAddr _ ppc];
        Call rf <- getRf1();

        Nondet npc : SyntaxKind (Pc addrSize);
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

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
        Call d2eEnq(d2ePack #opType #dst #laddr $$Default $$Default $$Default
                            #rawInst #ppc #npc #epoch);
        Call sbInsert(#dst);
        Retv

      with Rule "instFetchSt" :=
        Read pinit <- "pinit";
        Call w2dFull <- w2dFull();
        Assert !#w2dFull;
        Read ppc : Pc addrSize <- "pc";
        Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
        Assert #pinit;
        LET rawInst <- #pgm@[toIAddr _ ppc];
        Call rf <- getRf1();

        Nondet npc: SyntaxKind (Pc addrSize);
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

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
        LET byteEn <- calcStByteEn _ rawInst;
        Call d2eEnq(d2ePack #opType $$Default #saddr #byteEn #stVal $$Default
                            #rawInst #ppc #npc #epoch);
        Retv

      with Rule "instFetchNm" :=
        Read pinit <- "pinit";
        Call w2dFull <- w2dFull();
        Assert !#w2dFull;
        Read ppc : Pc addrSize <- "pc";
        Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
        Assert #pinit;
        LET rawInst <- #pgm@[toIAddr _ ppc];
        Call rf <- getRf1();

        Nondet npc: SyntaxKind (Pc addrSize);
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

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
        
        Call d2eEnq(d2ePack #opType #dst $$Default $$Default #val1 #val2
                            #rawInst #ppc #npc #epoch);
        Call sbInsert(#dst);
        Retv
    }.

  End FetchDecode.

  Section Execute.

    Definition executer := MODULE {
      Rule "execNm" :=
        Call rf <- getRf2();
        Call d2e <- d2eDeq();
        LET ppc <- d2eCurPc _ d2e;
        Assert d2eOpType _ d2e == $$opNm;
        
        LET rawInst <- d2eRawInst _ d2e;
        LET val1 <- d2eVal1 _ d2e;
        LET val2 <- d2eVal2 _ d2e;
        LET execVal <- doExec _ val1 val2 ppc rawInst;
        Call e2wEnq (e2wPack #d2e #execVal);
        Retv

      with Rule "execBypass" :=
        Call rf <- getRf2();
        Call d2e <- d2eDeq();
        Assert d2eOpType _ d2e != $$opNm;
        Call e2wEnq (e2wPack #d2e $$Default);
        Retv
    }.

  End Execute.

  Section WriteBack.
    
    Definition commitPc {ty} ppc npcp st rawInst :=
      (Write "lastPc" <- #ppc;
       LET npc <- getNextPc ty st ppc rawInst;
       If (#npc != #npcp)
       then
         Call toggleEpoch();
         Call w2dEnq(STRUCT { "prevPc" ::= #ppc;
                              "nextPc" ::= #npc });
         Retv
       else
         Retv
        as _;
         Retv)%kami_action.

    Definition wb := MODULE {
      Register "stall" : Bool <- false
      with Register "stalled" : d2eElt <- Default
      with Register "lastPc" : Pc addrSize <- Default
                                       
      with Rule "wrongEpoch" :=
        Read stall <- "stall";
        Assert !#stall;
        Call e2w <- e2wDeq();
        LET d2e <- e2wDecInst _ e2w;
        LET fEpoch <- d2eEpoch _ d2e;
        Call eEpoch <- getEpoch();
        Assert (#fEpoch != #eEpoch);

        If (d2eOpType _ d2e == $$opLd || d2eOpType _ d2e == $$opNm)
        then
          LET dst <- d2eDst _ d2e;
          Call sbRemove(#dst);
          Retv
        else
          Retv
        as _;
        Retv

      with Rule "reqLd" :=
        Read stall <- "stall";
        Assert !#stall;
        Call e2w <- e2wDeq();
        LET d2e <- e2wDecInst _ e2w;

        LET fEpoch <- d2eEpoch _ d2e;
        Call eEpoch <- getEpoch();
        Assert (#fEpoch == #eEpoch);

        Assert d2eOpType _ d2e == $$opLd;
        LET laddr <- d2eAddr _ d2e;
        Call memReq(STRUCT { "addr" ::= #laddr;
                             "op" ::= $$false;
                             "byteEn" ::= $$Default;
                             "data" ::= $$Default });
        Write "stall" <- $$true;
        Write "stalled" <- #d2e;
        Retv
                        
      with Rule "reqSt" :=
        Read stall <- "stall";
        Assert !#stall;
        Call e2w <- e2wDeq();
        LET d2e <- e2wDecInst _ e2w;

        LET fEpoch <- d2eEpoch _ d2e;
        Call eEpoch <- getEpoch();
        Assert (#fEpoch == #eEpoch);

        Assert d2eOpType _ d2e == $$opSt;
        LET saddr <- d2eAddr _ d2e;
        LET byteEn <- d2eByteEn _ d2e;
        Call memReq(STRUCT { "addr" ::= #saddr;
                             "op" ::= $$true;
                             "byteEn" ::= #byteEn;
                             "data" ::= d2eVal1 _ d2e });
        Write "stall" <- $$true;
        Write "stalled" <- #d2e;
        Retv
                                
      with Rule "repLd" :=
        Read stall <- "stall";
        Assert #stall;
        Call val <- memRep();
        Call rf <- getRf2();
        Read stalled : d2eElt <- "stalled";
        Assert d2eOpType _ stalled == $$opLd;
        LET dst <- d2eDst _ stalled;
        Assert (#dst != $0);

        LET rawInst <- d2eRawInst _ stalled;
        LET laddr <- d2eAddr _ stalled;
        LET ldValWord <- #val!RsToProc@."data";
        LET ldType <- getLdType _ rawInst;
        LET ldVal <- calcLdVal _ laddr ldValWord ldType;
        Call setRf (#rf@[#dst <- #ldVal]);
        
        Call sbRemove(#dst);
        Write "stall" <- $$false;
        LET ppc <- d2eCurPc _ stalled;
        LET npcp <- d2eNextPc _ stalled;
        LET rawInst <- d2eRawInst _ stalled;
        commitPc ppc npcp rf rawInst

      with Rule "repLdZ" :=
        Read stall <- "stall";
        Assert #stall;
        Call val <- memRep();
        Call rf <- getRf2();
        Read stalled : d2eElt <- "stalled";
        Assert d2eOpType _ stalled == $$opLd;
        LET dst <- d2eDst _ stalled;
        Assert (#dst == $0);
        Call sbRemove(#dst);
        Write "stall" <- $$false;
        LET ppc <- d2eCurPc _ stalled;
        LET npcp <- d2eNextPc _ stalled;
        LET rawInst <- d2eRawInst _ stalled;
        commitPc ppc npcp rf rawInst

      with Rule "repSt" :=
        Read stall <- "stall";
        Assert #stall;
        Call val <- memRep();
        Call rf <- getRf2();
        Read stalled : d2eElt <- "stalled";
        Assert d2eOpType _ stalled == $$opSt;
        Write "stall" <- $$false;
        LET ppc <- d2eCurPc _ stalled;
        LET npcp <- d2eNextPc _ stalled;
        LET rawInst <- d2eRawInst _ stalled;
        commitPc ppc npcp rf rawInst
                                
      with Rule "wbNm" :=
        Read stall <- "stall";
        Assert !#stall;
        Call rf <- getRf2();
        Call e2w <- e2wDeq();
        LET d2e <- e2wDecInst _ e2w;

        LET fEpoch <- d2eEpoch _ d2e;
        Call eEpoch <- getEpoch();
        Assert (#fEpoch == #eEpoch);

        Assert d2eOpType _ d2e == $$opNm;
        LET dst <- d2eDst _ d2e;
        Assert (#dst != $0);
        LET val <- e2wVal _ e2w;
        Call setRf(#rf@[#dst <- #val]);
        Call sbRemove(#dst);
        LET ppc <- d2eCurPc _ d2e;
        LET npcp <- d2eNextPc _ d2e;
        LET rawInst <- d2eRawInst _ d2e;
        commitPc ppc npcp rf rawInst

      with Rule "wbNmZ" :=
        Read stall <- "stall";
        Assert !#stall;
        Call rf <- getRf2();
        Call e2w <- e2wDeq();
        LET d2e <- e2wDecInst _ e2w;

        LET fEpoch <- d2eEpoch _ d2e;
        Call eEpoch <- getEpoch();
        Assert (#fEpoch == #eEpoch);

        Assert d2eOpType _ d2e == $$opNm;
        LET dst <- d2eDst _ d2e;
        Assert (#dst == $0);
        Call sbRemove(#dst);
        LET ppc <- d2eCurPc _ d2e;
        LET npcp <- d2eNextPc _ d2e;
        LET rawInst <- d2eRawInst _ d2e;
        commitPc ppc npcp rf rawInst
    }.
    
  End WriteBack.

  Definition procThreeStage (init: ProcInit addrSize dataBytes rfIdx) :=
    ((fetchDecode (pcInit init))
       ++ regFile (rfInit init)
       ++ scoreBoard
       ++ PrimFifo.fifo PrimFifo.primPipelineFifoName d2eFifoName d2eElt
       ++ PrimFifo.fifoF PrimFifo.primBypassFifoName w2dFifoName w2dElt
       ++ executer
       ++ epoch
       ++ PrimFifo.fifo PrimFifo.primPipelineFifoName e2wFifoName e2wElt
       ++ wb)%kami.

End ProcThreeStage.

#[global] Hint Unfold regFile scoreBoard fetchDecode executer epoch wb procThreeStage : ModuleDefs.
#[global] Hint Unfold RqFromProc RsToProc memReq memRep
     d2eFifoName d2eEnq d2eDeq
     W2DStr w2dElt w2dFifoName w2dEnq w2dDeq w2dFull
     getRf1 getRf2 setRf getEpoch toggleEpoch
     e2wFifoName e2wEnq e2wDeq
     sbSearch1_Ld sbSearch2_Ld sbSearch1_St sbSearch2_St
     sbSearch1_Nm sbSearch2_Nm sbSearch3_Nm
     sbInsert sbRemove
     commitPc : MethDefs.

Section ProcThreeStageM.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Array Bool dataBytes)) -> (* byteEn *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eByteEn: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Array Bool dataBytes)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data dataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Pc addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Pc addrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  Variable (e2wElt: Kind).
  Variable (e2wPack:
              forall ty,
                Expr ty (SyntaxKind d2eElt) -> (* decInst *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* execVal *)
                Expr ty (SyntaxKind e2wElt)).
  Variables
    (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                            Expr ty (SyntaxKind d2eElt))
    (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Data dataBytes))).

  Definition p3st init :=
    procThreeStage fetch dec exec
                   d2ePack d2eOpType d2eDst d2eAddr d2eByteEn d2eVal1 d2eVal2
                   d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                   e2wPack e2wDecInst e2wVal
                   init.

End ProcThreeStageM.

#[global] Hint Unfold p3st : ModuleDefs.

Section Facts.
  Variable inName outName: string.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Array Bool dataBytes)) -> (* byteEn *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eByteEn: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Array Bool dataBytes)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data dataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Pc addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Pc addrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  Variable (e2wElt: Kind).
  Variable (e2wPack:
              forall ty,
                Expr ty (SyntaxKind d2eElt) -> (* decInst *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* execVal *)
                Expr ty (SyntaxKind e2wElt)).
  Variables
    (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                            Expr ty (SyntaxKind d2eElt))
    (e2wDst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Data dataBytes))).

  Lemma regFile_ModEquiv:
    forall init, ModPhoasWf (@regFile dataBytes rfIdx init).
  Proof. kequiv. Qed.
  #[local] Hint Resolve regFile_ModEquiv.

  Lemma scoreBoard_ModEquiv:
    ModPhoasWf (scoreBoard rfIdx).
  Proof. kequiv. Qed.
  #[local] Hint Resolve scoreBoard_ModEquiv.

  Lemma fetchDecode_ModEquiv:
    forall pcInit,
      ModPhoasWf (fetchDecode fetch dec d2ePack pcInit).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve fetchDecode_ModEquiv.

  Lemma executer_ModEquiv:
    ModPhoasWf (executer exec d2eOpType d2eVal1 d2eVal2 d2eRawInst d2eCurPc e2wPack).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve executer_ModEquiv.

  Lemma epoch_ModEquiv:
    ModPhoasWf epoch.
  Proof. kequiv. Qed.
  #[local] Hint Resolve epoch_ModEquiv.
  
  Lemma wb_ModEquiv:
    ModPhoasWf (wb dec exec
                   d2eOpType d2eDst d2eAddr d2eByteEn d2eVal1
                   d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                   e2wDecInst e2wVal).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve wb_ModEquiv.
  
  Lemma procThreeStage_ModEquiv:
    forall init,
      ModPhoasWf (p3st fetch dec exec
                       d2ePack d2eOpType d2eDst d2eAddr d2eByteEn d2eVal1 d2eVal2
                       d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                       e2wPack e2wDecInst e2wVal init).
  Proof.
    kequiv.
  Qed.

End Facts.

#[global] Hint Resolve regFile_ModEquiv
     scoreBoard_ModEquiv
     fetchDecode_ModEquiv
     executer_ModEquiv
     epoch_ModEquiv
     wb_ModEquiv
     procThreeStage_ModEquiv.

