Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Kami.Syntax Kami.Notations.
Require Import Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Kami.ParametricSyntax.

Set Implicit Arguments.

(* The SC module is defined as follows: SC = n * Pinst + Minst,
 * where Pinst denotes an instantaneous processor core
 * and Minst denotes an instantaneous memory.
 *)

(* Abstract ISA *)
Section DecExec.
  Variables opIdx addrSize lgDataBytes rfIdx: nat.

  Definition StateK := SyntaxKind (Vector (Data lgDataBytes) rfIdx).
  Definition StateT (ty : Kind -> Type) := fullType ty StateK.
  Definition StateE (ty : Kind -> Type) := Expr ty StateK.

  Definition DecInstK :=
    STRUCT {
        "opcode" :: Bit opIdx;
        "reg" :: Bit rfIdx;
        "addr" :: Bit addrSize;
        "value" :: Data lgDataBytes;
        "inst" :: Data lgDataBytes
      }.
  Definition DecInstT (ty : Kind -> Type) := fullType ty (SyntaxKind DecInstK).
  Definition DecInstE (ty : Kind -> Type) := Expr ty (SyntaxKind DecInstK).

  Definition DecT := forall ty, StateT ty -> (* rf *)
                                fullType ty (SyntaxKind (Data lgDataBytes)) -> (* raw inst *)
                                DecInstE ty.
  Definition ExecStateT := forall ty, StateT ty -> (* rf *)
                                      fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                      DecInstT ty -> (* decoded inst *)
                                      StateE ty. (* next state *)
  Definition ExecNextPcT := forall ty, StateT ty -> (* rf *)
                                       fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       DecInstT ty -> (* decoded inst *)
                                       Expr ty (SyntaxKind (Bit addrSize)). (* next pc *)

End DecExec.

Hint Unfold StateK StateT StateE DecInstK DecInstT DecInstE : MethDefs.

(* The module definition for Minst with n ports *)
Section MemInst.
  Variable n : nat.
  Variable addrSize : nat.
  Variable lgDataBytes : nat.

  Definition RqFromProc := RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := RsToProc lgDataBytes.

  Definition memInstM := META {
    Register "mem" : Vector (Data lgDataBytes) addrSize <- Default

    with Repeat Method till n by "exec" (a : RqFromProc) : RsToProc :=
      If !#a@."op" then (* load *)
        Read memv <- "mem";
        LET ldval <- #memv@[#a@."addr"];
        Ret (STRUCT { "data" ::= #ldval } :: RsToProc)
      else (* store *)
        Read memv <- "mem";
        Write "mem" <- #memv@[ #a@."addr" <- #a@."data" ];
        Ret (STRUCT { "data" ::= $$Default } :: RsToProc)
      as na;
      Ret #na
  }.
    
  Definition memInst := modFromMeta memInstM.
  
End MemInst.

Hint Unfold RqFromProc RsToProc : MethDefs.
Hint Unfold memInstM memInst : ModuleDefs.

(* The module definition for Pinst *)
Section ProcInst.
  Variables opIdx addrSize lgDataBytes rfIdx : nat.

  (* External abstract ISA: dec and exec *)
  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Definition execCm := MethodSig "exec"(RqFromProc addrSize lgDataBytes) : RsToProc lgDataBytes.
  Definition toHostCm := MethodSig "toHost"(Data lgDataBytes) : Bit 0.

  Definition nextPc {ty} ppc st inst :=
    (Write "pc" <- execNextPc ty st ppc inst;
     Write "fetch" <- $$true;
     Retv)%kami_action.

  Definition procInst := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default
    with Register "fetch" : Bool <- true
    with Register "fetched" : Data lgDataBytes <- Default
                                 
    with Rule "instFetch" :=
      Read fetch <- "fetch";
      Assert #fetch;
      Read ppc <- "pc";
      Call rawInst <- execCm(STRUCT { "addr" ::= #ppc;
                                      "op" ::= $$false;
                                      "data" ::= $$Default });
      Write "fetched" <- #rawInst@."data";
      Write "fetch" <- $$false;
      Retv

    with Rule "execLd" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      LET regIdx <- #inst@."reg";
      Assert (#regIdx != $0);
      Assert #inst@."opcode" == $$opLd;
      Call ldRep <- execCm(STRUCT { "addr" ::= #inst@."addr";
                                    "op" ::= $$false;
                                    "data" ::= $$Default });
      Write "rf" <- #st@[#regIdx <- #ldRep@."data"];
      nextPc ppc st inst

    with Rule "execLdZ" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      LET regIdx <- #inst@."reg";
      Assert (#regIdx == $0);
      nextPc ppc st inst

    with Rule "execSt" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert #inst@."opcode" == $$opSt;
      Call execCm(STRUCT { "addr" ::= #inst@."addr";
                           "op" ::= $$true;
                           "data" ::= #inst@."value" });
      nextPc ppc st inst

    with Rule "execToHost" :=
      Read fetch <- "fetch";
      Assert !#fetch;
      Read ppc <- "pc";
      Read st <- "rf";
      Read rawInst <- "fetched";
      LET inst <- dec _ st rawInst;
      Assert #inst@."opcode" == $$opTh;
      Call toHostCm(#inst@."value");
      nextPc ppc st inst

    with Rule "execNm" :=
      Read fetch <- "fetch";
      Assert !#fetch;
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

End ProcInst.

Hint Unfold execCm toHostCm nextPc : MethDefs.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables opIdx addrSize lgDataBytes rfIdx : nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Variable n: nat.

  Definition pinst := procInst dec execState execNextPc opLd opSt opTh.
  Definition pinsts (i: nat): Modules := duplicate pinst i.
  Definition minst := memInst n addrSize lgDataBytes.

  Definition sc := ConcatMod (pinsts n) minst.

End SC.

Hint Unfold pinst pinsts minst sc : ModuleDefs.

Section Facts.
  Variables opIdx addrSize lgDataBytes rfIdx : nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.
  
  Variables opLd opSt opTh: ConstT (Bit opIdx).

  Lemma pinst_ModEquiv:
    ModPhoasWf (pinst dec execState execNextPc opLd opSt opTh).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pinst_ModEquiv.

  Variable n: nat.
  
  Lemma pinsts_ModEquiv:
    ModPhoasWf (pinsts dec execState execNextPc opLd opSt opTh n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pinsts_ModEquiv.

  Lemma memInstM_ModEquiv:
    MetaModPhoasWf (memInstM n addrSize lgDataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve memInstM_ModEquiv.

  Lemma sc_ModEquiv:
    ModPhoasWf (sc dec execState execNextPc opLd opSt opTh n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pinst_ModEquiv pinsts_ModEquiv memInstM_ModEquiv sc_ModEquiv.

