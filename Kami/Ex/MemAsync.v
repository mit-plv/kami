Require Import Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.Reflection Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate Kami.RefinementFacts.
Require Import Kami.SemFacts Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo.

Set Implicit Arguments.

Section Middleman.
  Variable inName outName: string.
  Variable addrSize dataBytes: nat.

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Definition getReq := MethodSig (inName -- "deq")() : Struct RqFromProc.
  Definition setRep := MethodSig (outName -- "enq")(Struct RsToProc) : Void.
  Definition memOp := MethodSig "memOp"(Struct RqFromProc) : Struct RsToProc.

  Definition mid :=
    MODULE {
      Register "memRq" : Struct RqFromProc <- Default
      with Register "memRqFull" : Bool <- Default
                                
      with Rule "pullMemRq" :=
        Read memRqFull <- "memRqFull";
        Assert !#memRqFull;
        Call req <- getReq();
        Write "memRq" <- #req;
        Write "memRqFull" <- $$true;
        Retv
        
      with Rule "processMemRq" :=
        Read memRqFull <- "memRqFull";
        Read memRq <- "memRq";
        Assert #memRqFull;
        Call rep <- memOp(#memRq);
        Call setRep(#rep);
        Retv
    }.

End Middleman.

Hint Unfold mid : ModuleDefs.
Hint Unfold RqFromProc RsToProc getReq setRep memOp : MethDefs.

Section MemAsync.
  Variables (addrSize fifoSize dataBytes: nat).

  Definition minst := memInst addrSize dataBytes.

  Definition inQ := @simpleFifo "rqFromProc" fifoSize (Struct (RqFromProc addrSize dataBytes)).
  Definition outQ := @simpleFifo "rsToProc" fifoSize (Struct (RsToProc dataBytes)).
  Definition ioQ := ConcatMod inQ outQ.
  Definition midQ := mid "rqFromProc" "rsToProc" addrSize dataBytes.
  
  Definition iom := ConcatMod ioQ midQ.

  Definition memAsyncWoQ := ConcatMod midQ minst.
  Definition memAsync := ConcatMod iom minst.

End MemAsync.

Hint Unfold minst inQ outQ ioQ midQ iom
     memAsyncWoQ memAsync : ModuleDefs.

Section Facts.
  Variables (addrSize fifoSize dataBytes: nat).

  Lemma midQ_ModEquiv:
    ModPhoasWf (midQ addrSize dataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve midQ_ModEquiv.

  Lemma iom_ModEquiv:
    ModPhoasWf (iom addrSize fifoSize dataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve iom_ModEquiv.

  Lemma memAsyncWoQ_ModEquiv:
    ModPhoasWf (memAsyncWoQ addrSize dataBytes).
  Proof.
    kequiv.
  Qed.

  Lemma memAsync_ModEquiv:
    ModPhoasWf (memAsync addrSize fifoSize dataBytes).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate midQ_ModEquiv iom_ModEquiv
     memAsyncWoQ_ModEquiv memAsync_ModEquiv.

