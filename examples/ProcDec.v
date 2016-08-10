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
  Variables opIdx addrSize iaddrSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize iaddrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  (* Called method signatures *)
  Definition memReq := MethodSig (inName -- "enq")(RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : RsToProc.
  Definition toHost := MethodSig "toHost"(Data lgDataBytes) : Void.

  Definition nextPc {ty} ppc st inst :=
    (Write "pc" <- execNextPc ty st ppc inst;
     Retv)%kami_action.

  Definition reqLd {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opLd;
     Call memReq(STRUCT { "addr" ::= #inst@."addr";
                          "op" ::= $$false;
                          "data" ::= $$Default });
     Write "stall" <- $$true;
     Retv)%kami_action.

  Definition reqSt {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opSt;
     Call memReq(STRUCT {  "addr" ::= #inst@."addr";
                           "op" ::= $$true;
                           "data" ::= #inst@."value" });
     Write "stall" <- $$true;
     Retv)%kami_action.

  Definition repLd {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opLd;
     Write "rf" <- #st@[#inst@."reg" <- #val@."data"];
     Write "stall" <- $$false;
     nextPc ppc st inst)%kami_action.

  Definition repSt {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opSt;
     Write "stall" <- $$false;
     nextPc ppc st inst)%kami_action.

  Definition execToHost {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opTh;
     Call toHost(#inst@."value");
     Retv)%kami_action.

  Definition execNm {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert !(#inst@."opcode" == $$opLd
           || #inst@."opcode" == $$opSt
           || #inst@."opcode" == $$opTh);
     Write "rf" <- execState _ st ppc inst;
     nextPc ppc st inst)%kami_action.

  Definition procDec := MODULE {
    Register "pc" : Bit iaddrSize <- Default
    with Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default
    with Register "stall" : Bool <- false

    with Rule "reqLd" := reqLd
    with Rule "reqSt" := reqSt
    with Rule "repLd" := repLd
    with Rule "repSt" := repSt
    with Rule "execToHost" := execToHost
    with Rule "execNm" := execNm
  }.

End ProcDec.

Hint Unfold procDec : ModuleDefs.
Hint Unfold RqFromProc RsToProc memReq memRep toHost nextPc
     reqLd reqSt repLd repSt execToHost execNm : MethDefs.

Section ProcDecM.
  Variables opIdx addrSize iaddrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize iaddrSize lgDataBytes rfIdx.

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
  Variables opIdx addrSize iaddrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize iaddrSize lgDataBytes rfIdx.

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

