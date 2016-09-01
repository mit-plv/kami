Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A two-staged processor, where two sets, {fetch, decode} and {execute, commit, write-back},
 * are modularly separated to form each stage. "epoch" registers are used to handle incorrect
 * branch prediction. Like a decoupled processor, memory operations are stalled until getting 
 * the response.
 *)
Section ProcTwoStage.
  Variables opIdx addrSize lgDataBytes rfIdx: nat.
  Variable inName outName: string.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition memReq := MethodSig (inName -- "enq")(RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : RsToProc.

  Definition d2eElt :=
    STRUCT { "instDec" :: DecInstK opIdx addrSize lgDataBytes rfIdx;
             "curPc" :: Bit addrSize;
             "nextPc" :: Bit addrSize;
             "epoch" :: Bool }.

  Definition d2eFifoName := "d2e"%string.
  Definition d2eEnq := MethodSig (d2eFifoName -- "enq")(d2eElt) : Void.
  Definition d2eDeq := MethodSig (d2eFifoName -- "deq")() : d2eElt.

  (* For correct pc redirection *)
  Definition e2dElt := Bit addrSize. 
  Definition e2dFifoName := "e2d"%string.
  Definition e2dEnq := MethodSig (e2dFifoName -- "enq")(e2dElt) : Void.
  Definition e2dDeq := MethodSig (e2dFifoName -- "deq")() : e2dElt.

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

  Section BranchPredictor.

    Definition branchPredictor := MODULE {
      Method "predictNextPc" (ppc: Bit addrSize) : Bit addrSize :=
        Ret (#ppc + $1)
    }.

  End BranchPredictor.
    
  Section Decode.
    Definition predictNextPc := MethodSig "predictNextPc"(Bit addrSize) : Bit addrSize.

    Definition decoder := MODULE {
      Register "pc" : Bit addrSize <- Default
      with Register "fetchStall" : Bool <- false
      with Register "fEpoch" : Bool <- false

      with Rule "modifyPc" :=
        Call correctPc <- e2dDeq();
        Write "pc" <- #correctPc;
        Read pEpoch <- "fEpoch";
        Write "fEpoch" <- !#pEpoch;
        Retv
        
      with Rule "reqInstFetch" :=
        Read fetchStall <- "fetchStall";
        Assert !#fetchStall;
        Read ppc <- "pc";
        Call memReq(STRUCT { "addr" ::= #ppc;
                             "op" ::= $$false;
                             "data" ::= $$Default });
        Write "fetchStall" <- $$true;
        Retv

      with Rule "repInstFetch" :=
        Call val <- memRep();
        LET rawInst <- #val@."data";
        Call st <- getRf();
        LET inst <- dec _ st rawInst;
        Read ppc <- "pc";
        Call npc <- predictNextPc(#ppc);
        Read epoch <- "fEpoch";
        Write "fetchStall" <- $$false;
        Write "pc" <- #npc;
        Call d2eEnq(STRUCT { "instDec" ::= #inst;
                             "curPc" ::= #ppc;
                             "nextPc" ::= #npc;
                             "epoch" ::= #epoch });
        Retv
    }.

  End Decode.

  Section Execute.
    Definition toHost := MethodSig "toHost"(Data lgDataBytes) : Void.

    Definition checkNextPc {ty} ppc npcp st inst :=
      (LET npc <- execNextPc ty st ppc inst;
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
      with Register "curInfo" : d2eElt <- Default

      with Rule "wrongEpoch" :=
        Read stall <- "stall";
        Assert !#stall;
        Call d2e <- d2eDeq();
        LET fEpoch <- #d2e@."epoch";
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch != #eEpoch);
        Retv
                              
      with Rule "reqLd" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- #d2e@."epoch";
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opLd;
        Assert #inst@."reg" != $0;
        Call memReq(STRUCT { "addr" ::= #inst@."addr";
                             "op" ::= $$false;
                             "data" ::= $$Default });
        Write "curInfo" <- #d2e;
        Write "stall" <- $$true;
        Retv 

      with Rule "reqLdZ" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- #d2e@."epoch";
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opLd;
        Assert #inst@."reg" == $0;
        LET ppc <- #d2e@."curPc";
        LET npcp <- #d2e@."nextPc";
        checkNextPc ppc npcp st inst
                        
      with Rule "reqSt" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- #d2e@."epoch";
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opSt;
        Call memReq(STRUCT { "addr" ::= #inst@."addr";
                             "op" ::= $$true;
                             "data" ::= #inst@."value" });
        Write "curInfo" <- #d2e;
        Write "stall" <- $$true;
        Retv
                                
      with Rule "repLd" :=
        Call val <- memRep();
        Call st <- getRf();
        Read curInfo : d2eElt <- "curInfo";
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #curInfo@."instDec";
        Assert #inst@."opcode" == $$opLd;
        Call setRf (#st@[#inst@."reg" <- #val@."data"]);
        Write "stall" <- $$false;
        LET ppc <- #curInfo@."curPc";
        LET npcp <- #curInfo@."nextPc";
        checkNextPc ppc npcp st inst

      with Rule "repSt" :=
        Call val <- memRep();
        Call st <- getRf();
        Read curInfo : d2eElt <- "curInfo";
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #curInfo@."instDec";
        Assert #inst@."opcode" == $$opSt;
        Write "stall" <- $$false;
        LET ppc <- #curInfo@."curPc";
        LET npcp <- #curInfo@."nextPc";
        checkNextPc ppc npcp st inst
                                
      with Rule "execToHost" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- #d2e@."epoch";
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opTh;
        Call toHost(#inst@."value");
        LET ppc <- #d2e@."curPc";
        LET npcp <- #d2e@."nextPc";
        checkNextPc ppc npcp st inst

      with Rule "execNm" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET fEpoch <- #d2e@."epoch";
        Read eEpoch <- "eEpoch";
        Assert (#fEpoch == #eEpoch);
        LET ppc <- #d2e@."curPc";
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert !(#inst@."opcode" == $$opLd
                  || #inst@."opcode" == $$opSt
                  || #inst@."opcode" == $$opTh);
        Call setRf (execState _ st ppc inst);
        LET ppc <- #d2e@."curPc";
        LET npcp <- #d2e@."nextPc";
        checkNextPc ppc npcp st inst
    }.
    
  End Execute.

  Definition procTwoStage := (decoder
                                ++ regFile
                                ++ branchPredictor
                                ++ fifo d2eFifoName 1 d2eElt
                                ++ fifo e2dFifoName 1 (Bit addrSize)
                                ++ executer)%kami.

End ProcTwoStage.

Hint Unfold regFile branchPredictor decoder executer procTwoStage : ModuleDefs.
Hint Unfold RqFromProc RsToProc memReq memRep
     d2eElt d2eFifoName d2eEnq d2eDeq
     e2dElt e2dFifoName e2dEnq e2dDeq
     getRf setRf predictNextPc toHost checkNextPc : MethDefs.

Section ProcTwoStageM.
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Definition p2st := procTwoStage "rqFromProc"%string "rsToProc"%string
                                  dec execState execNextPc opLd opSt opTh.

End ProcTwoStageM.

Section Facts.
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Lemma procTwoStage_ModEquiv:
    ModPhoasWf (p2st dec execState execNextPc opLd opSt opTh).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve procTwoStage_ModEquiv.

