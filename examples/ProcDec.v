Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A decoupled processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * This processor does NOT use a ROB, which implies that it just stalls
 * until getting a memory operation response.
 *)
Section ProcDec.
  Variable i: nat.
  Variable inName outName: string.
  Variables addrSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition getNextPc ppc st inst := fst (exec st ppc inst).
  Definition getNextState ppc st := snd (exec st ppc (dec st ppc)).

  Definition opLd : ConstT (Bit 2) := WO~0~0.
  Definition opSt : ConstT (Bit 2) := WO~0~1.
  Definition opHt : ConstT (Bit 2) := WO~1~0.

  Notation "^ s" := (s __ i) (at level 0).

  (* Called method signatures *)
  Definition memReq := MethodSig (inName -n- "enq")(memAtomK addrSize valSize) : Void.
  Definition memRep := MethodSig (outName -n- "deq")() : memAtomK addrSize valSize.
  Definition halt := MethodSig ^"HALT"() : Void.

  Definition nextPc ppc st := ACTION {
    Write ^"pc" <- #(getNextPc ppc st (dec st ppc));
    Retv
  }.

  Definition reqLd :=
    (Read stall <- ^"stall";
     Assert !#stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert #(dec st ppc)@."opcode" == $$opLd;
     Call memReq(STRUCT {  "type" ::= $$memLd;
                           "addr" ::= #(dec st ppc)@."addr";
                           "value" ::= $$Default });
     Write ^"stall" <- $$true;
     Retv)%kami.

  Definition reqSt :=
    (Read stall <- ^"stall";
     Assert !#stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert #(dec st ppc)@."opcode" == $$opSt;
     Call memReq(STRUCT {  "type" ::= $$opSt;
                           "addr" ::= #(dec st ppc)@."addr";
                           "value" ::= #(dec st ppc)@."value" });
     Write ^"stall" <- $$true;
     Retv)%kami.

  Definition repLd :=
    (Call val <- memRep();
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert #val@."type" == $$opLd;
     Write ^"rf" <- #st@[#(dec st ppc)@."reg" <- #val@."value"];
     Write ^"stall" <- $$false;
     nextPc ppc st)%kami.

  Definition repSt :=
    (Call val <- memRep();
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert #val@."type" == $$opSt;
     Write ^"stall" <- $$false;
     nextPc ppc st)%kami.

  Definition execHt :=
    (Read stall <- ^"stall";
     Assert !#stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert #(dec st ppc)@."opcode" == $$opHt;
     Call halt();
     Retv)%kami.

  Definition execNm :=
    (Read stall <- ^"stall";
     Assert #stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert !(#(dec st ppc)@."opcode" == $$opLd
           || #(dec st ppc)@."opcode" == $$opSt
           || #(dec st ppc)@."opcode" == $$opHt);
     Write ^"rf" <- #(getNextState ppc st);
     nextPc ppc st)%kami.

  Definition procDec := MODULE {
    Register ^"pc" : Bit addrSize <- Default
    with Register ^"rf" : Vector (Bit valSize) rfIdx <- Default
    with Register ^"stall" : Bool <- false

    with Rule ^"reqLd" := reqLd
    with Rule ^"reqSt" := reqSt
    with Rule ^"repLd" := repLd
    with Rule ^"repSt" := repSt
    with Rule ^"execHt" := execHt
    with Rule ^"execNm" := execNm
  }.
End ProcDec.

Hint Unfold getNextPc nextPc memReq memRep halt.
Hint Unfold procDec : ModuleDefs.

Section ProcDecM.
  Variables addrSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition pdeci (i: nat) := procDec i ("Ins"__ i) ("Outs"__ i) dec exec.

  Definition pdecfi (i: nat) := ConcatMod (pdeci i) (iomi addrSize (Bit valSize) i).

  Fixpoint pdecfs (i: nat) :=
    match i with
      | O => pdecfi O
      | S i' => ConcatMod (pdecfi i) (pdecfs i')
    end.

  Definition procDecM (n: nat) := ConcatMod (pdecfs n) (minst addrSize (Bit valSize) n).

  Section Facts.

    Lemma regsInDomain_pdeci i: RegsInDomain (pdeci i).
    Proof.
      regsInDomain_tac.
    Qed.

    Lemma regsInDomain_pdecfi i: RegsInDomain (pdecfi i).
    Proof.
      apply concatMod_RegsInDomain;
      [apply regsInDomain_pdeci|apply regsInDomain_iomi].
    Qed.

  End Facts.

End ProcDecM.

Hint Unfold pdeci pdecfi pdecfs procDecM : ModuleDefs.
