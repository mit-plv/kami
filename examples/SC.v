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
  Definition StateT (ty : FullKind -> Type) := ty StateK.

  Definition DecInstK := SyntaxKind (STRUCT {
    "opcode" :: Bit opIdx;
    "reg" :: Bit rfIdx;
    "addr" :: Bit addrSize;
    "value" :: Bit valSize
  }).
  Definition DecInstT (ty : FullKind -> Type) := ty DecInstK.

  Definition DecT := forall ty, StateT ty -> ty (SyntaxKind (Bit addrSize)) -> DecInstT ty.
  Definition ExecT := forall ty, StateT ty -> ty (SyntaxKind (Bit addrSize)) -> DecInstT ty ->
                                 ty (SyntaxKind (Bit addrSize)) * StateT ty.

  Definition DecEquiv (dec: DecT) :=
    forall (v1: fullType type StateK)
           (v1': fullType typeUT StateK)
           (v2: fullType type (SyntaxKind (Bit addrSize)))
           (v2': fullType typeUT (SyntaxKind (Bit addrSize))) G,
      In ((vars v1 v1')) G -> In ((vars v2 v2')) G ->
      ExprEquiv G
                (#(dec (fullType type) v1 v2))%kami
                (#(dec (fullType typeUT) v1' v2'))%kami.

  Definition ExecEquiv_1 (dec: DecT) (exec: ExecT) :=
    forall (v1: fullType type StateK)
           (v1': fullType typeUT StateK)
           (v2: fullType type (SyntaxKind (Bit addrSize)))
           (v2': fullType typeUT (SyntaxKind (Bit addrSize))) G,
      In ((vars v1 v1')) G -> In ((vars v2 v2')) G ->
      ExprEquiv G
                #(fst (exec (fullType type) v1 v2 (dec (fullType type) v1 v2)))%kami
                #(fst (exec (fullType typeUT) v1' v2' (dec (fullType typeUT) v1' v2')))%kami.

  Definition ExecEquiv_2 (dec: DecT) (exec: ExecT) :=
    forall (v1: fullType type StateK)
           (v1': fullType typeUT StateK)
           (v2: fullType type (SyntaxKind (Bit addrSize)))
           (v2': fullType typeUT (SyntaxKind (Bit addrSize))) G,
      In ((vars v1 v1')) G -> In ((vars v2 v2')) G ->
      ExprEquiv G
                #(snd (exec (fullType type) v1 v2 (dec (fullType type) v1 v2)))%kami
                #(snd (exec (fullType typeUT) v1' v2' (dec (fullType typeUT) v1' v2')))%kami.

End DecExec.

Hint Unfold StateK StateT DecInstK DecInstT : MethDefs.

Ltac dec_exec_equiv dec exec HdecEquiv HexecEquiv_1 HexecEquiv_2 :=
  match goal with
  | [ |- ExprEquiv _ (#(dec _ _ _))%kami (#(dec _ _ _))%kami ] =>
    apply HdecEquiv
  | [ |- ExprEquiv _ (#(fst (exec _ _ _ (dec _ _ _))))%kami
                   (#(fst (exec _ _ _ (dec _ _ _))))%kami ] =>
    apply HexecEquiv_1
  | [ |- ExprEquiv _ (#(snd (exec _ _ _ (dec _ _ _))))%kami
                   (#(snd (exec _ _ _ (dec _ _ _))))%kami ] =>
    apply HexecEquiv_2
  end.

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
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Definition getNextPc ty ppc st := fst (exec (fullType ty) st ppc (dec (fullType ty) st ppc)).
  Definition getNextState ty ppc st := snd (exec (fullType ty) st ppc (dec (fullType ty) st ppc)).

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Definition memAtomK := atomK addrSize (Bit valSize).

  Definition execCm := MethodSig "exec"(memAtomK) : memAtomK.
  Definition haltCm := MethodSig "HALT"(Bit 0) : Bit 0.

  Definition nextPc {ty} ppc st :=
    (Write "pc" <- #(getNextPc ty ppc st);
     Retv)%kami.

  Definition procInst := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Bit valSize) rfIdx <- Default

    with Rule "execLd" :=
      Read ppc <- "pc";
      Read st <- "rf";
      Assert #(dec _ st ppc)@."opcode" == $$opLd;
      Call ldRep <- execCm(STRUCT {  "type" ::= $$memLd;
                                     "addr" ::= #(dec _ st ppc)@."addr";
                                    "value" ::= $$Default });
      Write "rf" <- #st@[#(dec _ st ppc)@."reg" <- #ldRep@."value"];
      (nextPc ppc st)

    with Rule "execSt" :=
      Read ppc <- "pc";
      Read st <- "rf";
      Assert #(dec _ st ppc)@."opcode" == $$opSt;
      Call execCm(STRUCT {  "type" ::= $$memSt;
                            "addr" ::= #(dec _ st ppc)@."addr";
                           "value" ::= #(dec _ st ppc)@."value" });
      nextPc ppc st

    with Rule "execHt" :=
      Read ppc <- "pc";
      Read st <- "rf";
      Assert #(dec _ st ppc)@."opcode" == $$opHt;
      Call haltCm();
      Retv

    with Rule "execNm" :=
      Read ppc <- "pc";
      Read st <- "rf";
      Assert !(#(dec _ st ppc)@."opcode" == $$opLd
             || #(dec _ st ppc)@."opcode" == $$opSt
             || #(dec _ st ppc)@."opcode" == $$opHt);
      Write "rf" <- #(getNextState _ ppc st);
      nextPc ppc st
  }.

End ProcInst.

Hint Unfold getNextPc getNextState memAtomK execCm haltCm nextPc : MethDefs.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables opIdx addrSize valSize rfIdx : nat.

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Variable n: nat.

  Definition pinst := procInst dec exec opLd opSt opHt.
  Definition pinsts (i: nat): Modules := duplicate pinst i.
  Definition minst := memInst n addrSize (Bit valSize).

  Definition sc := ConcatMod (pinsts n) minst.

End SC.

Hint Unfold pinst pinsts minst sc : ModuleDefs.

Require Import MetaSyntax.

Section Facts.
  Variables opIdx addrSize valSize rfIdx : nat.

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.
  Hypotheses (HdecEquiv: DecEquiv dec)
             (HexecEquiv_1: ExecEquiv_1 dec exec)
             (HexecEquiv_2: ExecEquiv_2 dec exec).
  
  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Lemma pinst_ModEquiv:
    forall m,
      m = pinst dec exec opLd opSt opHt ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.
  Hint Resolve pinst_ModEquiv.
  
  Lemma pinsts_ModEquiv:
    forall n m,
      m = pinsts dec exec opLd opSt opHt n ->
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
    - constructor.
    - constructor; [|assumption].
      kequiv.
  Qed.
  Hint Resolve memInst_ModEquiv.

  Lemma sc_ModEquiv:
    forall n m,
      m = sc dec exec opLd opSt opHt n ->
      ModEquiv type typeUT m.
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pinst_ModEquiv pinsts_ModEquiv memInst_ModEquiv sc_ModEquiv.

