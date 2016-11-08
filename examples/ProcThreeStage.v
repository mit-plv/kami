Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A fifo containing only one element.
 * Implementation is much simpler than the general fifo, implemented in Fifo.v
 *)
Section OneEltFifo.
  Variable fifoName: string.
  Variable dType: Kind.

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition enq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (Read isFull <- ^"full";
     Assert !#isFull;
     Write ^"elt" <- #d;
     Write ^"full" <- $$true;
     Retv)%kami_action.

  Definition deq {ty} : ActionT ty dType :=
    (Read isFull <- ^"full";
     Assert #isFull;
     Read elt <- ^"elt";
     Write ^"full" <- $$false;
     Ret #elt)%kami_action.

  Definition firstElt {ty} : ActionT ty dType :=
    (Read isFull <- ^"full";
     Assert #isFull;
     Read elt <- ^"elt";
     Ret #elt)%kami_action.

  Definition isFull {ty} : ActionT ty Bool :=
    (Read isFull <- ^"full";
     Ret #isFull)%kami_action.

  Definition flush {ty} : ActionT ty Void :=
    (Write ^"full" <- $$false;
     Retv)%kami_action.
  
  Definition oneEltFifo := MODULE {
    Register ^"elt" : dType <- Default
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
  }.

  Definition oneEltFifoEx1 := MODULE {
    Register ^"elt" : dType <- Default
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
    with Method ^"isFull"() : Bool := isFull
  }.

  Definition oneEltFifoEx2 := MODULE {
    Register ^"elt" : dType <- Default
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
    with Method ^"flush"() : Void := flush
  }.

End OneEltFifo.

Hint Unfold oneEltFifo oneEltFifoEx1 oneEltFifoEx2 : ModuleDefs.
Hint Unfold enq deq firstElt isFull flush : MethDefs.

Section D2eInst.
  Variables addrSize iaddrSize dataBytes rfIdx: nat.

  Definition d2eEltI :=
    STRUCT { "opType" :: Bit 2;
             "dst" :: Bit rfIdx;
             "addr" :: Bit addrSize;
             "val1" :: Data dataBytes;
             "val2" :: Data dataBytes;
             "rawInst" :: Data dataBytes;
             "curPc" :: Bit addrSize;
             "nextPc" :: Bit addrSize;
             "epoch" :: Bool }.

  Definition d2ePackI ty 
             (opTy: Expr ty (SyntaxKind (Bit 2)))
             (dst: Expr ty (SyntaxKind (Bit rfIdx)))
             (addr: Expr ty (SyntaxKind (Bit addrSize)))
             (val1 val2: Expr ty (SyntaxKind (Data dataBytes)))
             (rawInst: Expr ty (SyntaxKind (Data dataBytes)))
             (curPc: Expr ty (SyntaxKind (Bit addrSize)))
             (nextPc: Expr ty (SyntaxKind (Bit addrSize)))
             (epoch: Expr ty (SyntaxKind Bool)): Expr ty (SyntaxKind (Struct d2eEltI)) :=
    STRUCT { "opType" ::= opTy;
             "dst" ::= dst;
             "addr" ::= addr;
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
  Definition d2eVal1I ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Data dataBytes)) := (#d2e!d2eEltI@."val1")%kami_expr.
  Definition d2eVal2I ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Data dataBytes)) := (#d2e!d2eEltI@."val2")%kami_expr.
  Definition d2eRawInstI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Data dataBytes)) := (#d2e!d2eEltI@."rawInst")%kami_expr.
  Definition d2eCurPcI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#d2e!d2eEltI@."curPc")%kami_expr.
  Definition d2eNextPcI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#d2e!d2eEltI@."nextPc")%kami_expr.
  Definition d2eEpochI ty (d2e: fullType ty (SyntaxKind (Struct d2eEltI)))
    : Expr ty (SyntaxKind Bool) := (#d2e!d2eEltI@."epoch")%kami_expr.

End D2eInst.

Section E2wInst.
  Variables addrSize iaddrSize dataBytes rfIdx: nat.

  Definition e2wEltI :=
    STRUCT { "decInst" :: Struct (d2eEltI addrSize dataBytes rfIdx);
             "val" :: Data dataBytes }.

  Definition e2wPackI ty
             (decInst: Expr ty (SyntaxKind (Struct (d2eEltI addrSize dataBytes rfIdx))))
             (val: Expr ty (SyntaxKind (Data dataBytes))) : Expr ty (SyntaxKind (Struct e2wEltI))
    := STRUCT { "decInst" ::= decInst;
                "val" ::= val }%kami_expr.

  Definition e2wDecInstI ty (e2w: fullType ty (SyntaxKind (Struct e2wEltI)))
    : Expr ty (SyntaxKind (Struct (d2eEltI addrSize dataBytes rfIdx))) := (#e2w!e2wEltI@."decInst")%kami_expr.
  Definition e2wValI ty (e2w: fullType ty (SyntaxKind (Struct e2wEltI)))
    : Expr ty (SyntaxKind (Data dataBytes)) := (#e2w!e2wEltI@."val")%kami_expr.

End E2wInst.
  
(* A three-staged processor, where three sets -- {fetch, decode}, {execute}, and 
 * {mem, write-back} -- are modularly separated to form each stage. "epoch" registers are
 * used to handle incorrect branch prediction. Like a decoupled processor, memory operations are
 * stalled until getting the response.
 *)
Section ProcThreeStage.
  Variable inName outName: string.
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
            (alignAddr: AlignAddrT addrSize).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Definition memReq := MethodSig (inName -- "enq")(Struct RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : Struct RsToProc.

  (* Abstract d2eElt *)
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
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data dataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data dataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
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

  (* For correct pc redirection *)
  Definition w2dElt := Bit addrSize. 
  Definition w2dFifoName := "w2d"%string.
  Definition w2dEnq := MethodSig (w2dFifoName -- "enq")(w2dElt) : Void.
  Definition w2dDeq := MethodSig (w2dFifoName -- "deq")() : w2dElt.
  Definition w2dFull := MethodSig (w2dFifoName -- "isFull")() : Bool.

  Definition e2wFifoName := "e2w"%string.
  Definition e2wEnq := MethodSig (e2wFifoName -- "enq")(e2wElt) : Void.
  Definition e2wDeq := MethodSig (e2wFifoName -- "deq")() : e2wElt.
  
  Section RegFile.

    Definition regFile := MODULE {
      Register "rf" : Vector (Data dataBytes) rfIdx <- Default

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
                                 
      with Method "sbSearch1" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch2" (sidx: Bit rfIdx) : Bool :=
        Read flags <- "sbFlags";
        Ret #flags@[#sidx]

      with Method "sbSearch3" (sidx: Bit rfIdx) : Bool :=
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

    Definition sbSearch1 := MethodSig "sbSearch1"(Bit rfIdx) : Bool.
    Definition sbSearch2 := MethodSig "sbSearch2"(Bit rfIdx) : Bool.
    Definition sbSearch3 := MethodSig "sbSearch3"(Bit rfIdx) : Bool.
    Definition sbInsert := MethodSig "sbInsert"(Bit rfIdx) : Void.
    Definition sbRemove := MethodSig "sbRemove"(Bit rfIdx) : Void.
    
  End ScoreBoard.

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Bit addrSize)).

  Section FetchDecode.
    
    Definition fetchDecode := MODULE {
      Register "pc" : Bit addrSize <- Default
      with Register "pgm" : Vector (Data dataBytes) iaddrSize <- Default
      with Register "fEpoch" : Bool <- false
                                    
      with Rule "modifyPc" :=
        Call correctPc <- w2dDeq();
        Write "pc" <- #correctPc;
        Read pEpoch <- "fEpoch";
        Write "fEpoch" <- !#pEpoch;
        Retv
          
      with Rule "instFetchLd" :=
        Call w2dFull <- w2dFull();
        Assert !#w2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[alignPc _ ppc];
        Call rf <- getRf1();

        LET npc <- predictNextPc _ ppc;
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

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
        Call d2eEnq(d2ePack #opType #dst #laddr $$Default $$Default
                            #rawInst #ppc #npc #epoch);
        Call sbInsert(#dst);
        Retv

      with Rule "instFetchSt" :=
        Call w2dFull <- w2dFull();
        Assert !#w2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[alignPc _ ppc];
        Call rf <- getRf1();

        LET npc <- predictNextPc _ ppc;
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

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
        Call d2eEnq(d2ePack #opType $$Default #saddr #stVal $$Default
                            #rawInst #ppc #npc #epoch);
        Retv

      with Rule "instFetchTh" :=
        Call w2dFull <- w2dFull();
        Assert !#w2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[alignPc _ ppc];
        Call rf <- getRf1();

        LET npc <- predictNextPc _ ppc;
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

        LET opType <- getOptype _ rawInst;
        Assert (#opType == $$opTh);

        LET srcIdx <- getSrc1 _ rawInst;
        Call stall1 <- sbSearch1(#srcIdx);
        Assert !#stall1;

        LET srcVal <- #rf@[#srcIdx];
        Call d2eEnq(d2ePack #opType $$Default $$Default #srcVal $$Default
                            #rawInst #ppc #npc #epoch);
        Retv

      with Rule "instFetchNm" :=
        Call w2dFull <- w2dFull();
        Assert !#w2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[alignPc _ ppc];
        Call rf <- getRf1();

        LET npc <- predictNextPc _ ppc;
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

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
        
        Call d2eEnq(d2ePack #opType #dst $$Default #val1 #val2
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
        LET execVal <- exec _ val1 val2 ppc rawInst;
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
    Definition toHost := MethodSig "toHost"(Data dataBytes) : Void.
    
    Definition checkNextPc {ty} ppc npcp st rawInst :=
      (LET npc <- getNextPc ty st ppc rawInst;
       If (#npc != #npcp)
       then
         Call toggleEpoch();
         Call w2dEnq(#npc);
         Retv
       else
         Retv
        as _;
         Retv)%kami_action.

    Definition wb := MODULE {
      Register "stall" : Bool <- false
      with Register "stalled" : d2eElt <- Default

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
        LET dst <- d2eDst _ d2e;
        Assert #dst != $0;
        LET laddr <- d2eAddr _ d2e;
        Call memReq(STRUCT { "addr" ::= alignAddr _ laddr;
                             "op" ::= $$false;
                             "data" ::= $$Default });
        Write "stall" <- $$true;
        Write "stalled" <- #d2e;
        Retv
          
      with Rule "reqLdZ" :=
        Read stall <- "stall";
        Assert !#stall;
        Call rf <- getRf2();
        Call e2w <- e2wDeq();
        LET d2e <- e2wDecInst _ e2w;

        LET fEpoch <- d2eEpoch _ d2e;
        Call eEpoch <- getEpoch();
        Assert (#fEpoch == #eEpoch);

        Assert d2eOpType _ d2e == $$opLd;
        Assert d2eDst _ d2e == $0;
        LET ppc <- d2eCurPc _ d2e;
        LET npcp <- d2eNextPc _ d2e;
        LET rawInst <- d2eRawInst _ d2e;
        checkNextPc ppc npcp rf rawInst
                        
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
        Call memReq(STRUCT { "addr" ::= alignAddr _ saddr;
                             "op" ::= $$true;
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
        Call setRf (#rf@[#dst <- #val!RsToProc@."data"]);
        Call sbRemove(#dst);
        Write "stall" <- $$false;
        LET ppc <- d2eCurPc _ stalled;
        LET npcp <- d2eNextPc _ stalled;
        LET rawInst <- d2eRawInst _ stalled;
        checkNextPc ppc npcp rf rawInst

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
        checkNextPc ppc npcp rf rawInst
                                
      with Rule "execToHost" :=
        Read stall <- "stall";
        Assert !#stall;
        Call rf <- getRf2();
        Call e2w <- e2wDeq();
        LET d2e <- e2wDecInst _ e2w;

        LET fEpoch <- d2eEpoch _ d2e;
        Call eEpoch <- getEpoch();
        Assert (#fEpoch == #eEpoch);

        Assert d2eOpType _ d2e == $$opTh;
        Call toHost(d2eVal1 _ d2e);
        LET ppc <- d2eCurPc _ d2e;
        LET npcp <- d2eNextPc _ d2e;
        LET rawInst <- d2eRawInst _ d2e;
        checkNextPc ppc npcp rf rawInst

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
        checkNextPc ppc npcp rf rawInst

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
        checkNextPc ppc npcp rf rawInst
    }.
    
  End WriteBack.

  Definition procThreeStage := (fetchDecode
                                  ++ regFile
                                  ++ scoreBoard
                                  ++ oneEltFifo d2eFifoName d2eElt
                                  ++ oneEltFifoEx1 w2dFifoName (Bit addrSize)
                                  ++ executer
                                  ++ epoch
                                  ++ oneEltFifo e2wFifoName e2wElt
                                  ++ wb)%kami.

End ProcThreeStage.

Hint Unfold regFile scoreBoard fetchDecode executer epoch wb procThreeStage : ModuleDefs.
Hint Unfold RqFromProc RsToProc memReq memRep
     d2eFifoName d2eEnq d2eDeq
     w2dElt w2dFifoName w2dEnq w2dDeq w2dFull
     getRf1 getRf2 setRf getEpoch toggleEpoch
     e2wFifoName e2wEnq e2wDeq
     sbSearch1 sbSearch2 sbSearch3 sbInsert sbRemove
     toHost checkNextPc : MethDefs.

Section ProcThreeStageM.
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
            (alignAddr: AlignAddrT addrSize)
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
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data dataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data dataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
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

  Definition p3st := procThreeStage "rqFromProc"%string "rsToProc"%string
                                    getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                    getStAddr getStSrc calcStAddr getStVSrc
                                    getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr
                                    d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                                    d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                                    e2wPack e2wDecInst e2wVal
                                    predictNextPc.

End ProcThreeStageM.

Hint Unfold p3st : ModuleDefs.

Section Facts.
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
            (alignAddr: AlignAddrT addrSize)
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
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data dataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data dataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
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
    ModPhoasWf (regFile dataBytes rfIdx).
  Proof. kequiv. Qed.
  Hint Resolve regFile_ModEquiv.

  Lemma scoreBoard_ModEquiv:
    ModPhoasWf (scoreBoard rfIdx).
  Proof. kequiv. Qed.
  Hint Resolve scoreBoard_ModEquiv.

  Lemma oneEltFifo_ModEquiv:
    forall fifoName dType, ModPhoasWf (oneEltFifo fifoName dType).
  Proof. kequiv. Qed.
  Hint Resolve oneEltFifo_ModEquiv.
  
  Lemma oneEltFifoEx1_ModEquiv:
    forall fifoName dType, ModPhoasWf (oneEltFifoEx1 fifoName dType).
  Proof. kequiv. Qed.
  Hint Resolve oneEltFifoEx1_ModEquiv.

  Lemma oneEltFifoEx2_ModEquiv:
    forall fifoName dType, ModPhoasWf (oneEltFifoEx1 fifoName dType).
  Proof. kequiv. Qed.
  Hint Resolve oneEltFifoEx2_ModEquiv.

  Lemma decoder_ModEquiv:
    ModPhoasWf (fetchDecode getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                            getStAddr getStSrc calcStAddr getStVSrc getSrc1 getSrc2 getDst
                            alignPc d2ePack predictNextPc).
  Proof.
    kequiv.
  Qed.
  Hint Resolve decoder_ModEquiv.

  Lemma executer_ModEquiv:
    ModPhoasWf (executer rfIdx exec d2eOpType d2eVal1 d2eVal2
                         d2eRawInst d2eCurPc e2wPack).
  Proof.
    kequiv.
  Qed.
  Hint Resolve executer_ModEquiv.

  Lemma epoch_ModEquiv:
    ModPhoasWf epoch.
  Proof. kequiv. Qed.
  Hint Resolve epoch_ModEquiv.
  
  Lemma wb_ModEquiv:
    forall inName outName,
      ModPhoasWf (wb inName outName getNextPc alignAddr
                     d2eOpType d2eDst d2eAddr d2eVal1
                     d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                     e2wDecInst e2wVal).
  Proof.
    kequiv.
  Qed.
  Hint Resolve wb_ModEquiv.
  
  Lemma procThreeStage_ModEquiv:
    ModPhoasWf (p3st getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                     getStAddr getStSrc calcStAddr getStVSrc
                     getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr predictNextPc
                     d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                     d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                     e2wPack e2wDecInst e2wVal).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve regFile_ModEquiv
     scoreBoard_ModEquiv
     oneEltFifo_ModEquiv
     oneEltFifoEx1_ModEquiv
     oneEltFifoEx2_ModEquiv
     decoder_ModEquiv
     executer_ModEquiv
     epoch_ModEquiv
     wb_ModEquiv
     procThreeStage_ModEquiv.

