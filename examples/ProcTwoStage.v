Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A two-staged processor, where two sets, {fetch, decode} and {execute, commit, write-back},
 * are modularly separated to form each stage. An "epoch" register is used to handle incorrect
 * branch prediction. Like a decoupled processor, memory operations are stalled until getting 
 * the response.
 *)
Section ProcTwoStage.
  Variables opIdx addrSize lgDataBytes rfIdx: nat.
  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variable inName outName: string.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  (* Called method signatures *)
  Definition memReq := MethodSig (inName -- "enq")(RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : RsToProc.

  Definition d2eElt := STRUCT { "instDec" :: DecInstK opIdx addrSize lgDataBytes rfIdx }.
  Definition d2eFifoName := "d2e"%string.
  Definition d2eEnq := MethodSig (d2eFifoName -- "enq")(d2eElt) : Void.
  Definition d2eDeq := MethodSig (d2eFifoName -- "deq")() : d2eElt.

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
        Call d2eEnq(STRUCT { "instDec" ::= #inst });
        Write "fetchStall" <- $$false;
        Read ppc <- "pc";
        Call npc <- predictNextPc(#ppc);
        Write "pc" <- #npc;
        Retv
    }.

  End Decode.

  Section Execute.
    Definition toHost := MethodSig "toHost"(Data lgDataBytes) : Void.

    Definition executer := MODULE {
      Register "stall" : Bool <- false
                                                 
      with Rule "reqLd" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opLd;
        Assert #inst@."reg" != $0;
        Call memReq(STRUCT { "addr" ::= #inst@."addr";
                             "op" ::= $$false;
                             "data" ::= $$Default });
        Write "stall" <- $$true;
        Retv

      with Rule "reqLdZ" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opLd;
        Assert #inst@."reg" == $0;
        Retv
                        
      with Rule "reqSt" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opSt;
        Call memReq(STRUCT { "addr" ::= #inst@."addr";
                             "op" ::= $$true;
                             "data" ::= #inst@."value" });
        Write "stall" <- $$true;
        Retv
                                
      with Rule "repLd" :=
        Call val <- memRep();
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opLd;
        Write "rf" <- #st@[#inst@."reg" <- #val@."data"];
        Write "stall" <- $$false;
        Retv

      with Rule "repSt" :=
        Call val <- memRep();
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opSt;
        Write "stall" <- $$false;
        Retv
                                
      with Rule "execToHost" :=
        Read stall <- "stall";
        Assert !#stall;
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert #inst@."opcode" == $$opTh;
        Call toHost(#inst@."value");
        Retv

      with Rule "execNm" :=
        Read stall <- "stall";
        Assert !#stall;
        Read ppc <- "pc";
        Call st <- getRf();
        Call d2e <- d2eDeq();
        LET inst : DecInstK opIdx addrSize lgDataBytes rfIdx <- #d2e@."instDec";
        Assert !(#inst@."opcode" == $$opLd
                  || #inst@."opcode" == $$opSt
                  || #inst@."opcode" == $$opTh);
        Write "rf" <- execState _ st ppc inst;
        Retv
    }.
    
  End Execute.

  Definition procTwoStage := (decoder
                                ++ branchPredictor
                                ++ fifo d2eFifoName 1 d2eElt
                                ++ executer)%kami.

End ProcTwoStage.

