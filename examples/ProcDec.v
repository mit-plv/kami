Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Notations Lts.Semantics Lts.Specialize Lts.Duplicate Lts.Equiv Lts.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A decoupled processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * This processor does NOT use a ROB, which implies that it just stalls
 * until getting a memory operation response.
 *)
Section ProcDec.
  Variable inName outName: string.
  Variables addrSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Definition opLd : ConstT (Bit 2) := WO~0~0.
  Definition opSt : ConstT (Bit 2) := WO~0~1.
  Definition opHt : ConstT (Bit 2) := WO~1~0.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  (* Called method signatures *)
  Definition memReq := MethodSig (inName .. "enq")(RqFromProc) : Void.
  Definition memRep := MethodSig (outName .. "deq")() : RsToProc.
  Definition halt := MethodSig "HALT"() : Void.

  Definition nextPc {ty} ppc st inst :=
    (Write "pc" <- execNextPc ty st ppc inst;
     Retv)%kami.

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
     Retv)%kami.

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
     Retv)%kami.

  Definition repLd {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opLd;
     Write "rf" <- #st@[#inst@."reg" <- #val@."data"];
     Write "stall" <- $$false;
     nextPc ppc st inst)%kami.

  Definition repSt {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opSt;
     Write "stall" <- $$false;
     nextPc ppc st inst)%kami.

  Definition execHt {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert #inst@."opcode" == $$opHt;
     Call halt();
     Retv)%kami.

  Definition execNm {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     LET inst <- dec _ st ppc;
     Assert !(#inst@."opcode" == $$opLd
           || #inst@."opcode" == $$opSt
           || #inst@."opcode" == $$opHt);
     Write "rf" <- execState _ st ppc inst;
     nextPc ppc st inst)%kami.

  Definition procDec := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default
    with Register "stall" : Bool <- false

    with Rule "reqLd" := reqLd
    with Rule "reqSt" := reqSt
    with Rule "repLd" := repLd
    with Rule "repSt" := repSt
    with Rule "execHt" := execHt
    with Rule "execNm" := execNm
  }.

End ProcDec.

Hint Unfold procDec : ModuleDefs.
Hint Unfold RqFromProc RsToProc opLd opSt opHt
     memReq memRep halt nextPc
     reqLd reqSt repLd repSt execHt execNm : MethDefs.

Section ProcDecM.
  Variables addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Definition pdec := procDec "Ins"%string "Outs"%string dec execState execNextPc.
  Definition pdecs (i: nat) := duplicate pdec i.

  Definition pdecf := ConcatMod pdec (iom addrSize fifoSize lgDataBytes).
  Definition pdecfs (i: nat) := duplicate pdecf i.
  Definition procDecM (n: nat) := ConcatMod (pdecfs n) (minst addrSize lgDataBytes n).

End ProcDecM.

Hint Unfold pdec pdecf pdecfs procDecM : ModuleDefs.

Section Facts.
  Variables addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Lemma pdec_ModEquiv:
    forall m,
      m = pdec dec execState execNextPc ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdec_ModEquiv.

  Lemma pdecf_ModEquiv:
    forall fsz m,
      m = pdecf fsz dec execState execNextPc ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecf_ModEquiv.

  Lemma pdecfs_ModEquiv:
    forall fsz n m,
      m = pdecfs fsz dec execState execNextPc n ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecfs_ModEquiv.

  Lemma procDecM_ModEquiv:
    forall fsz n m,
      m = procDecM fsz dec execState execNextPc n ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pdec_ModEquiv pdecf_ModEquiv pdecfs_ModEquiv procDecM_ModEquiv.

