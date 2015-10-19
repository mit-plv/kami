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
  Variables opIdx addrSize valSize rfIdx: nat.

  Notation "^ s" := (s __ i) (at level 0).

  Definition execK := ExecK opIdx addrSize valSize rfIdx.
  Definition  decK := DecK opIdx addrSize valSize rfIdx.
  Definition stateAddrK := stateAndAddrK addrSize valSize rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Notation "^ s" := (s __ i) (at level 0).

  (* Called method signatures *)
  Definition memReq := MethodSig (inName -n- "enq")(memAtomK addrSize valSize) : Void.
  Definition memRep := MethodSig (outName -n- "deq")() : memAtomK addrSize valSize.
  Definition halt := MethodSig ^"HALT"() : Void.

  Definition reqLd {ty} : ActionT ty Void :=
    (Read stall <- ^"stall";
     Assert !#stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
     Call decoded <- decK( #stppc );
     Assert (#decoded)@."opcode" == $$opLd;
     Call memReq(STRUCT {  "type" ::= $$memLd;
                           "addr" ::= #(decoded)@."addr";
                           "value" ::= $$Default });
     Write ^"stall" <- $$true;
     Retv)%kami.

  Definition reqSt {ty} : ActionT ty Void :=
    (Read stall <- ^"stall";
     Assert !#stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
     Call decoded <- decK( #stppc );
     Assert (#decoded)@."opcode" == $$opSt;
     Call memReq(STRUCT {  "type" ::= $$memSt;
                           "addr" ::= #(decoded)@."addr";
                           "value" ::= #(decoded)@."value" });
     Write ^"stall" <- $$true;
     Retv)%kami.

  Definition repLd {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert #val@."type" == $$memLd;
     Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
     Call decoded <- decK(#stppc);
     Write ^"rf" <- #st@[#(decoded)@."reg" <- #val@."value"];
     Write ^"stall" <- $$false;
     Call executed <- execK( STRUCT { "fst" ::= #stppc; "snd" ::= #decoded });
     Write ^"pc" <- (#executed)@."fst";
       Retv)%kami.

  Definition repSt {ty} : ActionT ty Void :=
    (Call val <- memRep();
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Assert #val@."type" == $$memSt;
     Write ^"stall" <- $$false;
     Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
     Call decoded <- decK(#stppc);
     Call executed <- execK( STRUCT { "fst" ::= #stppc; "snd" ::= #decoded });
     Write ^"pc" <- (#executed)@."fst";
     Retv)%kami.

  Definition execHt {ty} : ActionT ty Void :=
    (Read stall <- ^"stall";
     Assert !#stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
     Call decoded <- decK( #stppc );
     Assert #(decoded)@."opcode" == $$opHt;
     Call halt();
     Retv)%kami.

  Definition execNm {ty} : ActionT ty Void :=
    (Read stall <- ^"stall";
     Assert !#stall;
     Read ppc <- ^"pc";
     Read st <- ^"rf";
     Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
     Call decoded <- decK( #stppc );
     Assert !(#(decoded)@."opcode" == $$opLd
           || #(decoded)@."opcode" == $$opSt
           || #(decoded)@."opcode" == $$opHt);
     Call executed <- execK( STRUCT { "fst" ::= #stppc; "snd" ::= #decoded });
     Write ^"pc" <- (#executed)@."fst";
     Write ^"rf" <- (#executed)@."snd";
     Retv)%kami.

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

Hint Unfold memReq memRep halt.
Hint Unfold procDec : ModuleDefs.

Section ProcDecM.
  Variables opIdx addrSize valSize rfIdx: nat.

  Variables opLd opSt opHt: ConstT (Bit opIdx).
  Definition pdeci (i: nat) := procDec i ("Ins"__ i) ("Outs"__ i) addrSize valSize rfIdx opLd opSt opHt.

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
