Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.MetaSyntax Lts.Notations.
Require Import Lts.Semantics Lts.Specialize Lts.Duplicate Lts.Equiv Lts.Tactics.
Require Import Ex.MemTypes.

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
        "value" :: Data lgDataBytes
      }.
  Definition DecInstT (ty : Kind -> Type) := fullType ty (SyntaxKind DecInstK).
  Definition DecInstE (ty : Kind -> Type) := Expr ty (SyntaxKind DecInstK).

  Definition DecT := forall ty, StateT ty -> fullType ty (SyntaxKind (Bit addrSize)) ->
                                DecInstE ty.
  Definition ExecStateT := forall ty, StateT ty -> fullType ty (SyntaxKind (Bit addrSize)) ->
                                      DecInstT ty ->
                                      StateE ty.
  Definition ExecNextPcT := forall ty, StateT ty -> fullType ty (SyntaxKind (Bit addrSize)) ->
                                       DecInstT ty ->
                                       Expr ty (SyntaxKind (Bit addrSize)).

End DecExec.

Hint Unfold StateK StateT StateE DecInstK DecInstT DecInstE : MethDefs.

(* The module definition for Minst with n ports *)
Section MemInst.
  Variable n : nat.
  Variable addrSize : nat.
  Variable lgDataBytes : nat.

  Definition RqFromProc := RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := RsToProc lgDataBytes.

  Definition memInst := MODULE {
    Register "mem" : Vector (Data lgDataBytes) addrSize <- Default

    with Repeat Method as i till n by "exec" (a : RqFromProc) : RsToProc :=
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
  
End MemInst.

Hint Unfold RqFromProc RsToProc : MethDefs.
Hint Unfold memInst : ModuleDefs.

(* The module definition for Pinst *)
Section ProcInst.
  Variables opIdx addrSize lgDataBytes rfIdx : nat.

  (* External abstract ISA: dec and exec *)
  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Definition execCm := MethodSig "exec"(RqFromProc addrSize lgDataBytes) : RsToProc lgDataBytes.
  Definition haltCm := MethodSig "HALT"(Bit 0) : Bit 0.

  Definition nextPc {ty} ppc st inst :=
    (Write "pc" <- execNextPc ty st ppc inst;
     Retv)%kami.

  Definition procInst := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default

    with Rule "execLd" :=
      Read ppc <- "pc";
      Read st <- "rf";
      LET inst <- dec _ st ppc;
      Assert #inst@."opcode" == $$opLd;
      Call ldRep <- execCm(STRUCT { "addr" ::= #inst@."addr";
                                    "op" ::= $$false;
                                    "data" ::= $$Default });
      Write "rf" <- #st@[#inst@."reg" <- #ldRep@."data"];
      nextPc ppc st inst

    with Rule "execSt" :=
      Read ppc <- "pc";
      Read st <- "rf";
      LET inst <- dec _ st ppc;
      Assert #inst@."opcode" == $$opSt;
      Call execCm(STRUCT { "addr" ::= #inst@."addr";
                           "op" ::= $$true;
                           "data" ::= #inst@."value" });
      nextPc ppc st inst

    with Rule "execHt" :=
      Read ppc <- "pc";
      Read st <- "rf";
      LET inst <- dec _ st ppc;
      Assert #inst@."opcode" == $$opHt;
      Call haltCm();
      Retv

    with Rule "execNm" :=
      Read ppc <- "pc";
      Read st <- "rf";
      LET inst <- dec _ st ppc;
      Assert !(#inst@."opcode" == $$opLd
             || #inst@."opcode" == $$opSt
             || #inst@."opcode" == $$opHt);
      Write "rf" <- execState _ st ppc inst;
      nextPc ppc st inst
  }.

End ProcInst.

Hint Unfold execCm haltCm nextPc : MethDefs.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables opIdx addrSize lgDataBytes rfIdx : nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Variable n: nat.

  Definition pinst := procInst dec execState execNextPc opLd opSt opHt.
  Definition pinsts (i: nat): Modules := duplicate pinst i.
  Definition minst := memInst n addrSize lgDataBytes.

  Definition sc := ConcatMod (pinsts n) minst.

End SC.

Hint Unfold pinst pinsts minst sc : ModuleDefs.

Require Import MetaSyntax.

Section Facts.
  Variables opIdx addrSize lgDataBytes rfIdx : nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.
  
  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Lemma pinst_ModEquiv:
    forall m,
      m = pinst dec execState execNextPc opLd opSt opHt ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.
  Hint Resolve pinst_ModEquiv.
  
  Lemma pinsts_ModEquiv:
    forall n m,
      m = pinsts dec execState execNextPc opLd opSt opHt n ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.
  Hint Resolve pinsts_ModEquiv.

  Lemma memInst_ModEquiv:
    forall n a d m,
      m = memInst n a d ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
    unfold memInst; simpl.
    apply MethsEquiv_app; [|constructor].

    induction n; intros.
    - kequiv.
    - constructor; [|auto].
      kequiv.
  Qed.
  Hint Resolve memInst_ModEquiv.

  Lemma sc_ModEquiv:
    forall n m,
      m = sc dec execState execNextPc opLd opSt opHt n ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pinst_ModEquiv pinsts_ModEquiv memInst_ModEquiv sc_ModEquiv.

