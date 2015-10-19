Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement.

(* The SC module is defined as follows: SC = n * Pinst + Minst,
 * where Pinst denotes an instantaneous processor core
 * and Minst denotes an instantaneous memory.
 *)

(* Abstract ISA *)
Section DecExec.
  Variables opIdx addrSize valSize rfIdx: nat.

  Definition StateK := Vector (Bit valSize) rfIdx.

  Definition DecInstK := STRUCT {
    "opcode" :: Bit opIdx;
    "reg" :: Bit rfIdx;
    "addr" :: Bit addrSize;
    "value" :: Bit valSize
  }.

  Definition Pair (A B : Kind) := STRUCT {
    "fst" :: A;
    "snd" :: B
  }.

  Definition stateAndAddrK := Pair StateK (Bit addrSize).

  Definition DecK := MethodSig "absDec"( stateAndAddrK ) : DecInstK. 
  Definition ExecK := MethodSig "absExec"( Pair stateAndAddrK DecInstK ) : stateAndAddrK.
  (* ExecK returns the next state and the next program counter address *)

End DecExec.

(* The module definition for Minst with n ports *)
Section MemInst.
  Variable n : nat.
  Variable addrSize : nat.
  Variable dType : Kind.

  Definition atomK := STRUCT {
    "type" :: Bit 2;
    "addr" :: Bit addrSize;
    "value" :: dType
  }.

  Definition memLd : ConstT (Bit 2) := WO~0~0.
  Definition memSt : ConstT (Bit 2) := WO~0~1.

  Definition memInst := MODULE {
    Register "mem" : Vector dType addrSize <- Default

    with Repeat n as i {
      Method ("exec"__ i)(a : atomK) : atomK :=
        If (#a@."type" == $$memLd) then
          Read memv <- "mem";
          Let ldval <- #memv@[#a@."addr"];
          Ret (STRUCT { "type" ::= #a@."type"; "addr" ::= #a@."addr"; "value" ::= #ldval }
               :: atomK)
        else
          Read memv <- "mem";
          Write "mem" <- #memv@[ #a@."addr" <- #a@."value" ];
          Ret #a
        as na;
        Ret #na
    }
  }.
End MemInst.

Hint Unfold memInst: ModuleDefs.

(* The module definition for Pinst *)
Section ProcInst.
  Variable i : nat.
  Variables opIdx addrSize valSize rfIdx : nat.

  (* External abstract ISA: dec and exec *)
  Definition execK := ExecK opIdx addrSize valSize rfIdx.
  Definition  decK := DecK opIdx addrSize valSize rfIdx.
  Definition stateAddrK := stateAndAddrK addrSize valSize rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Notation "^ s" := (s __ i) (at level 0).

  Definition memAtomK := atomK addrSize (Bit valSize).

  Definition execCm := MethodSig ^"exec"(memAtomK) : memAtomK.
  Definition haltCm := MethodSig ^"HALT"(Bit 0) : Bit 0.

  Definition nextPc {ty} (stppc decoded : Expr ty _) : ActionT ty Void := 
    (Call executed <- execK( STRUCT { "fst" ::= stppc; "snd" ::= decoded });
     Write ^"pc" <- (#executed)@."fst";
     Retv)%kami.


  Definition procInst := MODULE {
    Register ^"pc" : Bit addrSize <- Default
    with Register ^"rf" : Vector (Bit valSize) rfIdx <- Default

    with Rule ^"execLd" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
      Call decoded <- decK( #stppc );
      Assert (#decoded)@."opcode" == $$opLd;
      Call ldRep <- execCm(STRUCT {  "type" ::= $$memLd;
                                     "addr" ::= (#decoded)@."addr";
                                    "value" ::= $$Default });
      Write ^"rf" <- #st@[ (#decoded)@."reg" <- #ldRep@."value"];
      (nextPc #stppc #decoded)

    with Rule ^"execSt" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
      Call decoded <- decK( #stppc );
      Assert #(decoded)@."opcode" == $$opSt;
      Call execCm(STRUCT {  "type" ::= $$memSt;
                            "addr" ::= #(decoded)@."addr";
                           "value" ::= #(decoded)@."value" });
      (nextPc #stppc #decoded)

    with Rule ^"execHt" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
      Call decoded <- decK( #stppc );
      Assert #(decoded)@."opcode" == $$opHt;
      Call haltCm();
      Retv

    with Rule ^"execNm" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Let stppc <- STRUCT { "fst" ::= #st; "snd" ::= #ppc };
      Call decoded <- decK( #stppc );
      Assert !(#(decoded)@."opcode" == $$opLd
             || #(decoded)@."opcode" == $$opSt
             || #(decoded)@."opcode" == $$opHt);
      Call executed <- execK( STRUCT { "fst" ::= #stppc; "snd" ::= #decoded });
      Write ^"rf" <- #(executed)@."snd";
      Write ^"pc" <- #(executed)@."fst";
      Retv

    with Rule ^"voidRule" :=
      Retv
  }.
End ProcInst.

Hint Unfold execCm haltCm nextPc.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables opIdx addrSize valSize rfIdx : nat.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Variable n: nat.

  Definition pinsti (i: nat) :=
    procInst i opIdx addrSize valSize rfIdx opLd opSt opHt.

  Fixpoint pinsts (i: nat): Modules :=
    match i with
      | O => pinsti O
      | S i' => ConcatMod (pinsti i) (pinsts i')
    end.
  
  Definition minst := memInst n addrSize (Bit valSize).

  Definition sc := ConcatMod (pinsts n) minst.

End SC.

Hint Unfold pinsti pinsts minst sc : ModuleDefs.

Section Facts.
  Variables opIdx addrSize valSize rfIdx : nat.
  Variables opLd opSt opHt: ConstT (Bit opIdx).
  Variable i: nat.

  Lemma regsInDomain_pinsti:
    RegsInDomain (pinsti opIdx addrSize valSize rfIdx opLd opSt opHt i).
  Proof.
    regsInDomain_tac.
  Qed.

End Facts.
