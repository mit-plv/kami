Require Import Bool String List.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.Reflection Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate Kami.RefinementFacts.
Require Import Kami.SemFacts Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.NativeFifo.

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
      Rule "processLd" :=
        Call req <- getReq();
        Assert !#req!RqFromProc@."op";
        Call rep <- memOp(#req);
        Call setRep(#rep);
        Retv

      with Rule "processSt" :=
        Call req <- getReq();
        Assert #req!RqFromProc@."op";
        Call rep <- memOp(#req);
        Call setRep(#rep);
        Retv
    }.

End Middleman.

Hint Unfold mid : ModuleDefs.
Hint Unfold RqFromProc RsToProc getReq setRep memOp : MethDefs.

Section MemAsync.
  Variables (addrSize fifoSize dataBytes: nat).
  Variables (memInit: MemInit addrSize dataBytes)
            (ammio: AbsMMIO addrSize).

  Definition mm := mm memInit ammio.

  Definition inQ :=
    @nativeSimpleFifo "rqFromProc" (Struct (RqFromProc addrSize dataBytes)) Default.
  
  Definition outQ :=
    @nativeSimpleFifo "rsToProc" (Struct (RsToProc dataBytes)) Default.
  
  Definition ioQ := ConcatMod inQ outQ.
  Definition midQ := mid "rqFromProc" "rsToProc" addrSize dataBytes.
  
  Definition iom := ConcatMod ioQ midQ.

  Definition memAsyncWoQ := ConcatMod midQ mm.
  Definition memAsync := ConcatMod iom mm.

End MemAsync.

Hint Unfold mm inQ outQ ioQ midQ iom memAsyncWoQ memAsync : ModuleDefs.

Section Facts.
  Variables (addrSize dataBytes: nat).
  Variables (memInit: MemInit addrSize dataBytes)
            (ammio: AbsMMIO addrSize).

  Lemma midQ_ModEquiv:
    ModPhoasWf (midQ addrSize dataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve midQ_ModEquiv.

  Lemma iom_ModEquiv:
    ModPhoasWf (iom addrSize dataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve iom_ModEquiv.

  Lemma memAsyncWoQ_ModEquiv:
    ModPhoasWf (memAsyncWoQ memInit ammio).
  Proof.
    kequiv.
  Qed.

  Lemma memAsync_ModEquiv:
    ModPhoasWf (memAsync memInit ammio).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate midQ_ModEquiv iom_ModEquiv
     memAsyncWoQ_ModEquiv memAsync_ModEquiv.

