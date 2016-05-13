Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.MetaSyntax Lts.Notations.
Require Import Lts.Semantics Lts.Specialize Lts.Equiv Lts.Tactics.

Set Implicit Arguments.

(* The SC module is defined as follows: SC = n * Pinst + Minst,
 * where Pinst denotes an instantaneous processor core
 * and Minst denotes an instantaneous memory.
 *)

(* Abstract ISA *)
Section DecExec.
  Variables opIdx addrSize valSize rfIdx: nat.

  Definition StateK := SyntaxKind (Vector (Bit valSize) rfIdx).
  Definition StateT (ty : Kind -> Type) := fullType ty StateK.
  Definition StateE (ty : Kind -> Type) := Expr ty StateK.

  Definition DecInstK :=
    STRUCT {
        "opcode" :: Bit opIdx;
        "reg" :: Bit rfIdx;
        "addr" :: Bit addrSize;
        "value" :: Bit valSize
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

  (* Definition DecEquiv (dec: DecT) := *)
  (*   forall (v1: fullType type StateK) *)
  (*          (v1': fullType typeUT StateK) *)
  (*          (v2: fullType type (SyntaxKind (Bit addrSize))) *)
  (*          (v2': fullType typeUT (SyntaxKind (Bit addrSize))) G, *)
  (*     In ((vars v1 v1')) G -> In ((vars v2 v2')) G -> *)
  (*     ExprEquiv G *)
  (*               (#(dec (fullType type) v1 v2))%kami *)
  (*               (#(dec (fullType typeUT) v1' v2'))%kami. *)

  (* Definition ExecEquiv_1 (dec: DecT) (exec: ExecT) := *)
  (*   forall (v1: fullType type StateK) *)
  (*          (v1': fullType typeUT StateK) *)
  (*          (v2: fullType type (SyntaxKind (Bit addrSize))) *)
  (*          (v2': fullType typeUT (SyntaxKind (Bit addrSize))) G, *)
  (*     In ((vars v1 v1')) G -> In ((vars v2 v2')) G -> *)
  (*     ExprEquiv G *)
  (*               #(fst (exec (fullType type) v1 v2 (dec (fullType type) v1 v2)))%kami *)
  (*               #(fst (exec (fullType typeUT) v1' v2' (dec (fullType typeUT) v1' v2')))%kami. *)

  (* Definition ExecEquiv_2 (dec: DecT) (exec: ExecT) := *)
  (*   forall (v1: fullType type StateK) *)
  (*          (v1': fullType typeUT StateK) *)
  (*          (v2: fullType type (SyntaxKind (Bit addrSize))) *)
  (*          (v2': fullType typeUT (SyntaxKind (Bit addrSize))) G, *)
  (*     In ((vars v1 v1')) G -> In ((vars v2 v2')) G -> *)
  (*     ExprEquiv G *)
  (*               #(snd (exec (fullType type) v1 v2 (dec (fullType type) v1 v2)))%kami *)
  (*               #(snd (exec (fullType typeUT) v1' v2' (dec (fullType typeUT) v1' v2')))%kami. *)

End DecExec.

Hint Unfold StateK StateT StateE DecInstK DecInstT DecInstE : MethDefs.

(* Ltac dec_exec_equiv dec exec HdecEquiv HexecEquiv_1 HexecEquiv_2 := *)
(*   match goal with *)
(*   | [ |- ExprEquiv _ (#(dec _ _ _))%kami (#(dec _ _ _))%kami ] => *)
(*     apply HdecEquiv *)
(*   | [ |- ExprEquiv _ (#(fst (exec _ _ _ (dec _ _ _))))%kami *)
(*                    (#(fst (exec _ _ _ (dec _ _ _))))%kami ] => *)
(*     apply HexecEquiv_1 *)
(*   | [ |- ExprEquiv _ (#(snd (exec _ _ _ (dec _ _ _))))%kami *)
(*                    (#(snd (exec _ _ _ (dec _ _ _))))%kami ] => *)
(*     apply HexecEquiv_2 *)
(*   end. *)

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

    with Repeat Method as i till n by "exec" (a : atomK) : atomK :=
      If (#a@."type" == $$memLd) then
        Read memv <- "mem";
        LET ldval <- #memv@[#a@."addr"];
        Ret (STRUCT { "type" ::= #a@."type"; "addr" ::= #a@."addr"; "value" ::= #ldval }
                    :: atomK)
      else
        Read memv <- "mem";
        Write "mem" <- #memv@[ #a@."addr" <- #a@."value" ];
        Ret #a
      as na;
      Ret #na
  }.
  
End MemInst.

Hint Unfold atomK memLd memSt : MethDefs.
Hint Unfold memInst : ModuleDefs.

(* The module definition for Pinst *)
Section ProcInst.
  Variables opIdx addrSize valSize rfIdx : nat.

  (* External abstract ISA: dec and exec *)
  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable execState: ExecStateT opIdx addrSize valSize rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize valSize rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Definition memAtomK := atomK addrSize (Bit valSize).

  Definition execCm := MethodSig "exec"(memAtomK) : memAtomK.
  Definition haltCm := MethodSig "HALT"(Bit 0) : Bit 0.

  Definition nextPc {ty} ppc st inst :=
    (Write "pc" <- execNextPc ty st ppc inst;
     Retv)%kami.

  Definition procInst := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Bit valSize) rfIdx <- Default

    with Rule "execLd" :=
      Read ppc <- "pc";
      Read st <- "rf";
      LET inst <- dec _ st ppc;
      Assert #inst@."opcode" == $$opLd;
      Call ldRep <- execCm(STRUCT {  "type" ::= $$memLd;
                                     "addr" ::= #inst@."addr";
                                    "value" ::= $$Default });
      Write "rf" <- #st@[#inst@."reg" <- #ldRep@."value"];
      nextPc ppc st inst

    with Rule "execSt" :=
      Read ppc <- "pc";
      Read st <- "rf";
      LET inst <- dec _ st ppc;
      Assert #inst@."opcode" == $$opSt;
      Call execCm(STRUCT {  "type" ::= $$memSt;
                            "addr" ::= #inst@."addr";
                           "value" ::= #inst@."value" });
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

Hint Unfold memAtomK execCm haltCm nextPc : MethDefs.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables opIdx addrSize valSize rfIdx : nat.

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable execState: ExecStateT opIdx addrSize valSize rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize valSize rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Variable n: nat.

  Definition pinst := procInst dec execState execNextPc opLd opSt opHt.
  Definition pinsts (i: nat): Modules := duplicate pinst i.
  Definition minst := memInst n addrSize (Bit valSize).

  Definition sc := ConcatMod (pinsts n) minst.

End SC.

Hint Unfold pinst pinsts minst sc : ModuleDefs.

Require Import MetaSyntax.

Section Facts.
  Variables opIdx addrSize valSize rfIdx : nat.

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable execState: ExecStateT opIdx addrSize valSize rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize valSize rfIdx.
  (* Hypotheses (HdecEquiv: DecEquiv dec) *)
  (*            (HexecEquiv_1: ExecEquiv_1 dec exec) *)
  (*            (HexecEquiv_2: ExecEquiv_2 dec exec). *)
  
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

