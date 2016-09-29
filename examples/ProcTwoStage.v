Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
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
Hint Unfold enq deq firstElt isFull : MethDefs.

Section D2eInst.
  Variables addrSize lgDataBytes rfIdx: nat.

  Definition d2eEltI :=
    STRUCT { "opType" :: Bit 2;
             "dst" :: Bit rfIdx;
             "addr" :: Bit addrSize;
             "val" :: Data lgDataBytes;
             "rawInst" :: Data lgDataBytes;
             "curPc" :: Bit addrSize;
             "nextPc" :: Bit addrSize;
             "epoch" :: Bool }.

  Definition d2ePackI ty 
             (opTy: Expr ty (SyntaxKind (Bit 2)))
             (dst: Expr ty (SyntaxKind (Bit rfIdx)))
             (addr: Expr ty (SyntaxKind (Bit addrSize)))
             (val: Expr ty (SyntaxKind (Data lgDataBytes)))
             (rawInst: Expr ty (SyntaxKind (Data lgDataBytes)))
             (curPc: Expr ty (SyntaxKind (Bit addrSize)))
             (nextPc: Expr ty (SyntaxKind (Bit addrSize)))
             (epoch: Expr ty (SyntaxKind Bool)): Expr ty (SyntaxKind d2eEltI) :=
    STRUCT { "opType" ::= opTy;
             "dst" ::= dst;
             "addr" ::= addr;
             "val" ::= val;
             "rawInst" ::= rawInst;
             "curPc" ::= curPc;
             "nextPc" ::= nextPc;
             "epoch" ::= epoch }%kami_expr.

  Definition d2eOpTypeI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind (Bit 2)) := (#d2e@."opType")%kami_expr.
  Definition d2eDstI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind (Bit rfIdx)) := (#d2e@."dst")%kami_expr.
  Definition d2eAddrI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#d2e@."addr")%kami_expr.
  Definition d2eValI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind (Data lgDataBytes)) := (#d2e@."val")%kami_expr.
  Definition d2eRawInstI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind (Data lgDataBytes)) := (#d2e@."rawInst")%kami_expr.
  Definition d2eCurPcI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#d2e@."curPc")%kami_expr.
  Definition d2eNextPcI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind (Bit addrSize)) := (#d2e@."nextPc")%kami_expr.
  Definition d2eEpochI ty (d2e: fullType ty (SyntaxKind d2eEltI))
    : Expr ty (SyntaxKind Bool) := (#d2e@."epoch")%kami_expr.

  Lemma d2eElt_opType:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eOpTypeI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr opType.
  Proof. reflexivity. Qed.

  Lemma d2eElt_dst:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eDstI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr dst.
  Proof. reflexivity. Qed.

  Lemma d2eElt_addr:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eAddrI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr addr.
  Proof. reflexivity. Qed.

  Lemma d2eElt_val:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eValI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr val.
  Proof. reflexivity. Qed.

  Lemma d2eElt_rawInst:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eRawInstI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr rawInst.
  Proof. reflexivity. Qed.

  Lemma d2eElt_curPc:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eCurPcI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr curPc.
  Proof. reflexivity. Qed.

  Lemma d2eElt_nextPc:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eNextPcI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr nextPc.
  Proof. reflexivity. Qed.

  Lemma d2eElt_epoch:
    forall opType dst addr val rawInst curPc nextPc epoch,
      evalExpr (d2eEpochI _ (evalExpr (d2ePackI opType dst addr val rawInst curPc nextPc epoch)))
      = evalExpr epoch.
  Proof. reflexivity. Qed.

End D2eInst.
  
(* A two-staged processor, where two sets, {fetch, decode} and {execute, commit, write-back},
 * are modularly separated to form each stage. "epoch" registers are used to handle incorrect
 * branch prediction. Like a decoupled processor, memory operations are stalled until getting 
 * the response.
 *)
Section ProcTwoStage.
  Variable inName outName: string.
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
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition memReq := MethodSig (inName -- "enq")(RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : RsToProc.

  (* Abstract d2eElt *)
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

  Definition d2eFifoName := "d2e"%string.
  Definition d2eEnq := MethodSig (d2eFifoName -- "enq")(d2eElt) : Void.
  Definition d2eDeq := MethodSig (d2eFifoName -- "deq")() : d2eElt.

  (* For correct pc redirection *)
  Definition e2dElt := Bit addrSize. 
  Definition e2dFifoName := "e2d"%string.
  Definition e2dEnq := MethodSig (e2dFifoName -- "enq")(e2dElt) : Void.
  Definition e2dDeq := MethodSig (e2dFifoName -- "deq")() : e2dElt.
  Definition e2dFull := MethodSig (e2dFifoName -- "isFull")() : Bool.

  Section RegFile.

    Definition regFile := MODULE {
      Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default

      with Method "getRf" () : Vector (Data lgDataBytes) rfIdx :=
        Read rf <- "rf";
        Ret #rf

      with Method "setRf" (rf: Vector (Data lgDataBytes) rfIdx) : Void :=
        Write "rf" <- #rf;
        Retv
    }.
      
    Definition getRf := MethodSig "getRf"() : Vector (Data lgDataBytes) rfIdx.
    Definition setRf := MethodSig "setRf"(Vector (Data lgDataBytes) rfIdx) : Void.

  End RegFile.

  Section ScoreBoard.

    Definition scoreBoard := MODULE {
      Register "idx" : Bit rfIdx <- Default
      with Register "valid" : Bool <- false
                                   
      with Method "search1" (idx1: Bit rfIdx) : Bool :=
        Read idx <- "idx";
        Read valid <- "valid";
        Ret (#valid && #idx == #idx1)

      with Method "search2" (idx2: Bit rfIdx) : Bool :=
        Read idx <- "idx";
        Read valid <- "valid";
        Ret (#valid && #idx == #idx2)

      with Method "insert" (nidx: Bit rfIdx) : Void :=
        Write "idx" <- #nidx;
        Write "valid" <- $$true;
        Retv
        
      with Method "remove" () : Void :=
        Write "valid" <- $$false;
        Retv
    }.

    Definition sbSearch1 := MethodSig "search1"(Bit rfIdx) : Bool.
    Definition sbSearch2 := MethodSig "search2"(Bit rfIdx) : Bool.
    Definition sbInsert := MethodSig "insert"(Bit rfIdx) : Void.
    Definition sbRemove := MethodSig "remove"() : Void.
    
  End ScoreBoard.

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Bit addrSize)).

  Section Decode.
    
    Definition decoder := MODULE {
      Register "pc" : Bit addrSize <- Default
      with Register "pgm" : Vector (Data lgDataBytes) addrSize <- Default
      with Register "fEpoch" : Bool <- false
                                    
      with Rule "modifyPc" :=
        Call correctPc <- e2dDeq();
        Write "pc" <- #correctPc;
        Read pEpoch <- "fEpoch";
        Write "fEpoch" <- !#pEpoch;
        Retv
          
      with Rule "instFetchLd" :=
        Call e2dFull <- e2dFull();
        Assert !#e2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[#ppc];
        Call rf <- getRf();

        LET npc <- predictNextPc _ ppc;
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

        LET opType <- getOptype _ rawInst;
        Assert (#opType == $$opLd);

        LET srcIdx <- getLdSrc _ rawInst;
        Call stall1 <- sbSearch1(#srcIdx);
        Assert !#stall1;
        LET addr <- getLdAddr _ rawInst;
        LET srcVal <- #rf@[#srcIdx];
        LET laddr <- calcLdAddr _ addr srcVal;
        Call d2eEnq(d2ePack #opType (getLdDst _ rawInst) #laddr $$Default
                            #rawInst #ppc #npc #epoch);
        Retv

      with Rule "instFetchSt" :=
        Call e2dFull <- e2dFull();
        Assert !#e2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[#ppc];
        Call rf <- getRf();

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
        Call d2eEnq(d2ePack #opType $$Default #saddr #stVal
                            #rawInst #ppc #npc #epoch);
        Retv

      with Rule "instFetchTh" :=
        Call e2dFull <- e2dFull();
        Assert !#e2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[#ppc];
        Call rf <- getRf();

        LET npc <- predictNextPc _ ppc;
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

        LET opType <- getOptype _ rawInst;
        Assert (#opType == $$opTh);

        LET srcIdx <- getSrc1 _ rawInst;
        Call stall1 <- sbSearch1(#srcIdx);
        Assert !#stall1;

        LET srcVal <- #rf@[#srcIdx];
        Call d2eEnq(d2ePack #opType $$Default $$Default #srcVal
                            #rawInst #ppc #npc #epoch);
        Retv

      with Rule "instFetchNm" :=
        Call e2dFull <- e2dFull();
        Assert !#e2dFull;
        Read ppc : Bit addrSize <- "pc";
        Read pgm <- "pgm";
        LET rawInst <- #pgm@[#ppc];
        Call rf <- getRf();

        LET npc <- predictNextPc _ ppc;
        Read epoch <- "fEpoch";
        Write "pc" <- #npc;

        LET opType <- getOptype _ rawInst;
        Assert (#opType == $$opNm);
        Call d2eEnq(d2ePack #opType $$Default $$Default $$Default
                            #rawInst #ppc #npc #epoch);
        Retv
    }.

  End Decode.

  Section Execute.
    Definition toHost := MethodSig "toHost"(Data lgDataBytes) : Void.

    Definition checkNextPc {ty} ppc npcp st rawInst :=
      (LET npc <- getNextPc ty st ppc rawInst;
       If (#npc != #npcp)
       then
         Read pEpoch <- "eEpoch";
         Write "eEpoch" <- !#pEpoch;
         Call e2dEnq(#npc);
         Retv
       else
         Retv
       as _;
       Retv)%kami_action.
    
    Definition executer := MODULE {
      Register "stall" : Bool <- false
      with Register "eEpoch" : Bool <- false
      with Register "stalled" : d2eElt <- Default

      with Rule "wrongEpoch" :=
        Read stall <- "stall";
        Assert !#stall;
        Call d2e <- d2eDeq();
        LET fEpoch <- d2eEpoch _ d2e;
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch != #eEpoch);
        Retv

      with Rule "reqLd" :=
        Read stall <- "stall";
        Assert !#stall;
        Call d2e <- d2eDeq();
        LET fEpoch <- d2eEpoch _ d2e;
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        Assert d2eOpType _ d2e == $$opLd;
        LET dst <- d2eDst _ d2e;
        Assert #dst != $0;
        Call memReq(STRUCT { "addr" ::= d2eAddr _ d2e;
                             "op" ::= $$false;
                             "data" ::= $$Default });
        Call sbInsert(#dst);
        Write "stall" <- $$true;
        Write "stalled" <- #d2e;
        Retv
          
      with Rule "reqLdZ" :=
        Read stall <- "stall";
        Assert !#stall;
        Call rf <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- d2eEpoch _ d2e;
        Read eEpoch <- "eEpoch";
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
        Call d2e <- d2eDeq();
        LET fEpoch <- d2eEpoch _ d2e;
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        Assert d2eOpType _ d2e == $$opSt;
        Call memReq(STRUCT { "addr" ::= d2eAddr _ d2e;
                             "op" ::= $$true;
                             "data" ::= d2eVal _ d2e });
        Write "stall" <- $$true;
        Write "stalled" <- #d2e;
        Retv
                                
      with Rule "repLd" :=
        Read stall <- "stall";
        Assert #stall;
        Call val <- memRep();
        Call rf <- getRf();
        Read stalled : d2eElt <- "stalled";
        Assert d2eOpType _ stalled == $$opLd;
        Call setRf (#rf@[d2eDst _ stalled <- #val@."data"]);
        Call sbRemove ();
        Write "stall" <- $$false;
        LET ppc <- d2eCurPc _ stalled;
        LET npcp <- d2eNextPc _ stalled;
        LET rawInst <- d2eRawInst _ stalled;
        checkNextPc ppc npcp rf rawInst

      with Rule "repSt" :=
        Read stall <- "stall";
        Assert #stall;
        Call val <- memRep();
        Call rf <- getRf();
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
        Call rf <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- d2eEpoch _ d2e;
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        Assert d2eOpType _ d2e == $$opTh;
        Call toHost(d2eVal _ d2e);
        LET ppc <- d2eCurPc _ d2e;
        LET npcp <- d2eNextPc _ d2e;
        LET rawInst <- d2eRawInst _ d2e;
        checkNextPc ppc npcp rf rawInst

      with Rule "execNm" :=
        Read stall <- "stall";
        Assert !#stall;
        Call rf <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- d2eEpoch _ d2e;
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        LET ppc <- d2eCurPc _ d2e;
        Assert d2eOpType _ d2e == $$opNm;
        LET rawInst <- d2eRawInst _ d2e;
        LET src1 <- getSrc1 _ rawInst;
        LET val1 <- #rf@[#src1];
        LET src2 <- getSrc2 _ rawInst;
        LET val2 <- #rf@[#src2];
        LET dst <- getDst _ rawInst;
        LET execVal <- exec _ val1 val2 ppc rawInst;
        Call setRf (#rf@[#dst <- #execVal]);
        LET ppc <- d2eCurPc _ d2e;
        LET npcp <- d2eNextPc _ d2e;
        checkNextPc ppc npcp rf rawInst
    }.
    
  End Execute.

  Definition procTwoStage := (decoder
                                ++ regFile
                                ++ scoreBoard
                                ++ oneEltFifo d2eFifoName d2eElt
                                ++ oneEltFifoEx1 e2dFifoName (Bit addrSize)
                                ++ executer)%kami.

End ProcTwoStage.

Hint Unfold regFile scoreBoard decoder executer procTwoStage : ModuleDefs.
Hint Unfold RqFromProc RsToProc memReq memRep
     (* d2eElt *) d2eFifoName d2eEnq d2eDeq
     e2dElt e2dFifoName e2dEnq e2dDeq e2dFull
     getRf setRf
     sbSearch1 sbSearch2 sbInsert sbRemove
     toHost checkNextPc : MethDefs.

Section ProcTwoStageM.
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

  Definition p2st := procTwoStage "rqFromProc"%string "rsToProc"%string
                                  getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                  getStAddr getStSrc calcStAddr getStVSrc
                                  getSrc1 getSrc2 getDst exec getNextPc
                                  d2ePack d2eOpType d2eDst d2eAddr d2eVal
                                  d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                                  predictNextPc.

End ProcTwoStageM.

Hint Unfold p2st : ModuleDefs.

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

  Lemma regFile_ModEquiv:
    ModPhoasWf (regFile lgDataBytes rfIdx).
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
    ModPhoasWf (decoder getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                        getStAddr getStSrc calcStAddr getStVSrc getSrc1
                        d2ePack predictNextPc).
  Proof. (* SKIP_PROOF_ON
    kequiv.
    END_SKIP_PROOF_ON *) admit.
  Qed.
  Hint Resolve decoder_ModEquiv.

  Lemma executer_ModEquiv:
    forall inName outName,
      ModPhoasWf (executer inName outName getSrc1 getSrc2 getDst exec getNextPc
                           d2eOpType d2eDst d2eAddr d2eVal
                           d2eRawInst d2eCurPc d2eNextPc d2eEpoch).
  Proof. (* SKIP_PROOF_ON
    kequiv.
    END_SKIP_PROOF_ON *) admit.
  Qed.
  Hint Resolve executer_ModEquiv.
  
  Lemma procTwoStage_ModEquiv:
    ModPhoasWf (p2st getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                     getStAddr getStSrc calcStAddr getStVSrc
                     getSrc1 getSrc2 getDst exec getNextPc predictNextPc
                     d2ePack d2eOpType d2eDst d2eAddr d2eVal
                     d2eRawInst d2eCurPc d2eNextPc d2eEpoch).
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
     procTwoStage_ModEquiv.

