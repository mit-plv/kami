Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A decoupled processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * This processor does NOT use a ROB, which implies that it just stalls
 * until getting a memory operation response.
 *)
Section ProcDec.
  Variable inName outName: string.
  Variables opIdx addrSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  (* Called method signatures *)
  Definition memReq := MethodSig (inName -- "enq")(RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : RsToProc.
  Definition toHost := MethodSig "toHost"(Data lgDataBytes) : Void.

  Definition nextPc {ty} ppc st inst :=
    (Write "pc" <- execNextPc ty st ppc inst;
     Write "fetch" <- $$true;
     Retv)%kami_action.

  Definition procDec := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default
    with Register "fetch" : Bool <- true
    with Register "fetched" : Data lgDataBytes <- Default                                   
    with Register "fetchStall" : Bool <- false
    with Register "stall" : Bool <- false
                                 
    with Rule "reqInstFetch" :=
      Read fetch <- "fetch";
      Assert #fetch;
      Read fetchStall <- "fetchStall";
      Assert !#fetchStall;
      Read ppc <- "pc";
      Call memReq(STRUCT { "addr" ::= #ppc;
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Write "fetchStall" <- $$true;
      Retv

    with Rule "repInstFetch" :=
      Read fetch <- "fetch";
      Assert #fetch;
      Call val <- memRep();
      LET rawInst <- #val@."data";
      Write "fetched" <- #rawInst;
      Write "fetch" <- $$false;
      Write "fetchStall" <- $$false;
      Retv
      
    with Rule "reqLd" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read stall <- "stall";
      Assert !#stall;
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert #inst@."opcode" == $$opLd;
      Call memReq(STRUCT { "addr" ::= #inst@."addr";
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Write "stall" <- $$true;
      Retv
        
    with Rule "reqSt" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read stall <- "stall";
      Assert !#stall;
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert #inst@."opcode" == $$opSt;
      Call memReq(STRUCT {  "addr" ::= #inst@."addr";
                            "op" ::= $$true;
                            "data" ::= #inst@."value" });
      Write "stall" <- $$true;
      Retv
                      
    with Rule "repLd" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Call val <- memRep();
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert #inst@."opcode" == $$opLd;
      Write "rf" <- #st@[#inst@."reg" <- #val@."data"];
      Write "stall" <- $$false;
      nextPc ppc st inst
                      
    with Rule "repSt" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Call val <- memRep();
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert #inst@."opcode" == $$opSt;
      Write "stall" <- $$false;
      nextPc ppc st inst
                      
    with Rule "execToHost" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read stall <- "stall";
      Assert !#stall;
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert #inst@."opcode" == $$opTh;
      Call toHost(#inst@."value");
      nextPc ppc st inst

    with Rule "execNm" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read stall <- "stall";
      Assert !#stall;
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert !(#inst@."opcode" == $$opLd
            || #inst@."opcode" == $$opSt
            || #inst@."opcode" == $$opTh);
      Write "rf" <- execState _ st ppc inst;
      nextPc ppc st inst                          
  }.

End ProcDec.

Hint Unfold procDec : ModuleDefs.
Hint Unfold RqFromProc RsToProc memReq memRep toHost nextPc : MethDefs.

Section ProcDecM.
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Definition pdec := procDec "rqFromProc"%string "rsToProc"%string dec execState execNextPc
                             opLd opSt opTh.
  Definition pdecs (i: nat) := duplicate pdec i.

  Definition pdecf := ConcatMod pdec (iom addrSize fifoSize lgDataBytes).
  Definition pdecfs (i: nat) := duplicate pdecf i.
  Definition procDecM (n: nat) := ConcatMod (pdecfs n) (minst addrSize lgDataBytes n).

End ProcDecM.

Hint Unfold pdec pdecf pdecfs procDecM : ModuleDefs.

Section Facts.
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Lemma pdec_ModEquiv:
    ModPhoasWf (pdec dec execState execNextPc opLd opSt opTh).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdec_ModEquiv.

  Lemma pdecf_ModEquiv:
    ModPhoasWf (pdecf fifoSize dec execState execNextPc opLd opSt opTh).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecf_ModEquiv.

  Variable n: nat.

  Lemma pdecfs_ModEquiv:
    ModPhoasWf (pdecfs fifoSize dec execState execNextPc opLd opSt opTh n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecfs_ModEquiv.

  Lemma procDecM_ModEquiv:
    ModPhoasWf (procDecM fifoSize dec execState execNextPc opLd opSt opTh n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pdec_ModEquiv pdecf_ModEquiv pdecfs_ModEquiv procDecM_ModEquiv.

