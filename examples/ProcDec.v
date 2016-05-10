Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Specialize Lts.Equiv Lts.Tactics.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A decoupled processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * This processor does NOT use a ROB, which implies that it just stalls
 * until getting a memory operation response.
 *)
Section ProcDec.
  Variable inName outName: string.
  Variables addrSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition getNextPc ty ppc st inst := fst (exec ty st ppc inst).
  Definition getNextState ty ppc st := snd (exec ty st ppc (dec ty st ppc)).

  Definition opLd : ConstT (Bit 2) := WO~0~0.
  Definition opSt : ConstT (Bit 2) := WO~0~1.
  Definition opHt : ConstT (Bit 2) := WO~1~0.

  (* Called method signatures *)
  Definition memReq := MethodSig (inName .. "enq")(memAtomK addrSize valSize) : Void.
  Definition memRep := MethodSig (outName .. "deq")() : memAtomK addrSize valSize.
  Definition halt := MethodSig "HALT"() : Void.

  Definition nextPc {ty} ppc st : ActionT ty Void := (
    Write "pc" <- #(getNextPc _ ppc st (dec _ st ppc));
    Retv
  )%kami.

  Definition reqLd {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     Assert #(dec _ st ppc)@."opcode" == $$opLd;
     Call memReq(STRUCT {  "type" ::= $$memLd;
                           "addr" ::= #(dec _ st ppc)@."addr";
                           "value" ::= $$Default });
     Write "stall" <- $$true;
     Retv)%kami.

  Definition reqSt {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     Assert #(dec _ st ppc)@."opcode" == $$opSt;
     Call memReq(STRUCT {  "type" ::= $$opSt;
                           "addr" ::= #(dec _ st ppc)@."addr";
                           "value" ::= #(dec _ st ppc)@."value" });
     Write "stall" <- $$true;
     Retv)%kami.

  Definition repLd {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- "pc";
     Read st <- "rf";
     (* Assert #val@."type" == $$opLd; *)
     Assert #(dec _ st ppc)@."opcode" == $$opLd;
     Write "rf" <- #st@[#(dec _ st ppc)@."reg" <- #val@."value"];
     Write "stall" <- $$false;
     nextPc ppc st)%kami.

  Definition repSt {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- "pc";
     Read st <- "rf";
     (* Assert #val@."type" == $$opSt; *)
     Assert #(dec _ st ppc)@."opcode" == $$opSt;
     Write "stall" <- $$false;
     nextPc ppc st)%kami.

  Definition execHt {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     Assert #(dec _ st ppc)@."opcode" == $$opHt;
     Call halt();
     Retv)%kami.

  Definition execNm {ty} : ActionT ty Void :=
    (Read stall <- "stall";
     Assert !#stall;
     Read ppc <- "pc";
     Read st <- "rf";
     Assert !(#(dec _ st ppc)@."opcode" == $$opLd
           || #(dec _ st ppc)@."opcode" == $$opSt
           || #(dec _ st ppc)@."opcode" == $$opHt);
     Write "rf" <- #(getNextState _ ppc st);
     nextPc ppc st)%kami.

  Definition procDec := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Bit valSize) rfIdx <- Default
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
Hint Unfold getNextPc getNextState opLd opSt opHt
     memReq memRep halt nextPc
     reqLd reqSt repLd repSt execHt execNm : MethDefs.

Section ProcDecM.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition pdec := procDec "Ins"%string "Outs"%string dec exec.

  Definition pdecf := ConcatMod pdec (iom addrSize fifoSize (Bit valSize)).
  Definition pdecfs (i: nat) := duplicate pdecf i.
  Definition procDecM (n: nat) := ConcatMod (pdecfs n) (minst addrSize (Bit valSize) n).

End ProcDecM.

Hint Unfold pdec pdecf pdecfs procDecM : ModuleDefs.

Section Facts.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.
  Hypotheses (HdecEquiv: DecEquiv dec)
             (HexecEquiv_1: ExecEquiv_1 dec exec)
             (HexecEquiv_2: ExecEquiv_2 dec exec).

  Lemma pdecf_ModEquiv:
    forall fsz m,
      m = pdecf fsz dec exec ->
      ModEquiv type typeUT m.
  Proof.
    (* kequiv_with ltac:(idtac; dec_exec_equiv dec exec HdecEquiv HexecEquiv_1 HexecEquiv_2). *)
    admit.
  Qed.
  Hint Resolve pdecf_ModEquiv.

  Lemma pdecfs_ModEquiv:
    forall fsz n m,
      m = pdecfs fsz dec exec n ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecfs_ModEquiv.

  Lemma procDecM_ModEquiv:
    forall fsz n m,
      m = procDecM fsz dec exec n ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pdecf_ModEquiv pdecfs_ModEquiv procDecM_ModEquiv.

