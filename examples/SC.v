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

  Definition StateK := SyntaxKind (Vector (Bit valSize) rfIdx).
  Definition StateT := fullType type StateK.

  Definition DecInstK := SyntaxKind (STRUCT {
    "opcode" :: Bit opIdx;
    "reg" :: Bit rfIdx;
    "addr" :: Bit addrSize;
    "value" :: Bit valSize
  }).
  Definition DecInstT := fullType type DecInstK.

  Definition DecT := StateT -> fullType type (SyntaxKind (Bit addrSize)) -> DecInstT.
  Definition ExecT := StateT -> fullType type (SyntaxKind (Bit addrSize)) -> DecInstT ->
                      fullType type (SyntaxKind (Bit addrSize)) * StateT.
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
  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Definition getNextPc ppc st := fst (exec st ppc (dec st ppc)).
  Definition getNextState ppc st := snd (exec st ppc (dec st ppc)).

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Notation "^ s" := (s __ i) (at level 0).

  Definition memAtomK := atomK addrSize (Bit valSize).

  Definition execCm := MethodSig ^"exec"(memAtomK) : memAtomK.
  Definition haltCm := MethodSig ^"HALT"(Bit 0) : Bit 0.

  Definition nextPc ppc st := ACTION {
    Write ^"pc" <- $$(getNextPc ppc st);
    Retv
  }.

  Definition procInst := MODULE {
    Register ^"pc" : Bit addrSize <- Default
    with Register ^"rf" : Vector (Bit valSize) rfIdx <- Default

    with Rule ^"execLd" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Assert #(dec st ppc)@."opcode" == $$opLd;
      Call ldRep <- execCm(STRUCT {  "type" ::= $$memLd;
                                     "addr" ::= #(dec st ppc)@."addr";
                                    "value" ::= $$Default });
      Write ^"rf" <- #st@[#(dec st ppc)@."reg" <- #ldRep@."value"];
      nextPc ppc st

    with Rule ^"execSt" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Assert #(dec st ppc)@."opcode" == $$opSt;
      Call execCm(STRUCT {  "type" ::= $$memSt;
                            "addr" ::= #(dec st ppc)@."addr";
                           "value" ::= #(dec st ppc)@."value" });
      nextPc ppc st

    with Rule ^"execHt" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Assert #(dec st ppc)@."opcode" == $$opHt;
      Call haltCm();
      Retv

    with Rule ^"execNm" :=
      Read ppc <- ^"pc";
      Read st <- ^"rf";
      Assert !(#(dec st ppc)@."opcode" == $$opLd
             || #(dec st ppc)@."opcode" == $$opSt
             || #(dec st ppc)@."opcode" == $$opHt);
      Write ^"rf" <- #(getNextState ppc st);
      nextPc ppc st

    with Rule ^"voidRule" :=
      Retv
  }.
End ProcInst.

Hint Unfold execCm haltCm getNextPc getNextState nextPc.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables opIdx addrSize valSize rfIdx : nat.

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Variable n: nat.

  Definition pinsti (i: nat) :=
    procInst i opIdx addrSize valSize rfIdx dec exec opLd opSt opHt.

  Fixpoint pinsts (i: nat): Modules type :=
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

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Lemma regsInDomain_pinsti:
    RegsInDomain (pinsti opIdx _ _ _ dec exec opLd opSt opHt i).
  Proof.
    regsInDomain_tac.
  Qed.

End Facts.
