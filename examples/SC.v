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

  (* opcode-related *)
  Definition OpcodeK := SyntaxKind (Bit opIdx).
  Definition OpcodeE (ty: Kind -> Type) := Expr ty OpcodeK.
  Definition OpcodeT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> OpcodeE ty.

  Definition opLd := WO~0~0.
  Definition opSt := WO~0~1.
  Definition opTh := WO~1~0.
  Definition opNm := WO~1~1.
  
  Definition OptypeK := SyntaxKind (Bit 2).
  Definition OptypeE (ty: Kind -> Type) := Expr ty OptypeK.
  Definition OptypeT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> OptypeE ty.
  
  (* load-related *)
  Definition LdDstK := SyntaxKind (Bit rfIdx).
  Definition LdDstE (ty: Kind -> Type) := Expr ty LdDstK.
  Definition LdDstT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> LdDstE ty.

  Definition LdAddrK := SyntaxKind (Bit addrSize).
  Definition LdAddrE (ty: Kind -> Type) := Expr ty LdAddrK.
  Definition LdAddrT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> LdAddrE ty.

  Definition LdSrcK := SyntaxKind (Bit rfIdx).
  Definition LdSrcE (ty: Kind -> Type) := Expr ty LdSrcK.
  Definition LdSrcT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> LdSrcE ty.

  Definition LdAddrCalcT :=
    forall ty,
      fullType ty (SyntaxKind (Bit addrSize)) -> (* base address *)
      fullType ty (SyntaxKind (Data lgDataBytes)) -> (* dst value *)
      Expr ty (SyntaxKind (Bit addrSize)).
  
  (* store-related *)
  Definition StAddrK := SyntaxKind (Bit addrSize).
  Definition StAddrE (ty: Kind -> Type) := Expr ty StAddrK.
  Definition StAddrT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> StAddrE ty.
  
  Definition StSrcK := SyntaxKind (Bit rfIdx).
  Definition StSrcE (ty: Kind -> Type) := Expr ty StSrcK.
  Definition StSrcT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> StSrcE ty.

  Definition StAddrCalcT :=
    forall ty,
      fullType ty (SyntaxKind (Bit addrSize)) -> (* base address *)
      fullType ty (SyntaxKind (Data lgDataBytes)) -> (* dst value *)
      Expr ty (SyntaxKind (Bit addrSize)).

  Definition StVSrcK := SyntaxKind (Bit rfIdx).
  Definition StVSrcE (ty: Kind -> Type) := Expr ty StVSrcK.
  Definition StVSrcT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> StVSrcE ty.

  (* general sources *)
  Definition Src1K := SyntaxKind (Bit rfIdx).
  Definition Src1E (ty: Kind -> Type) := Expr ty Src1K.
  Definition Src1T := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> Src1E ty.

  Definition Src2K := SyntaxKind (Bit rfIdx).
  Definition Src2E (ty: Kind -> Type) := Expr ty Src2K.
  Definition Src2T := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> Src2E ty.

  (* general destination *)
  Definition DstK := SyntaxKind (Bit rfIdx).
  Definition DstE (ty: Kind -> Type) := Expr ty DstK.
  Definition DstT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> DstE ty.
  
  (* execution *)
  Definition StateK := SyntaxKind (Vector (Data lgDataBytes) rfIdx).
  Definition StateT (ty : Kind -> Type) := fullType ty StateK.
  Definition StateE (ty : Kind -> Type) := Expr ty StateK.

  Definition ExecT := forall ty, fullType ty (SyntaxKind (Data lgDataBytes)) -> (* val1 *)
                                 fullType ty (SyntaxKind (Data lgDataBytes)) -> (* val2 *)
                                 fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                 fullType ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                                 Expr ty (SyntaxKind (Data lgDataBytes)). (* executed value *)
  Definition NextPcT := forall ty, StateT ty -> (* rf *)
                                   fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                   fullType ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                                   Expr ty (SyntaxKind (Bit addrSize)). (* next pc *)
  
End DecExec.

Hint Unfold OpcodeK OpcodeE OpcodeT OptypeK OptypeE OptypeT opLd opSt opTh opNm
     LdDstK LdDstE LdDstT LdAddrK LdAddrE LdAddrT LdSrcK LdSrcE LdSrcT
     StAddrK StAddrE StAddrT StSrcK StSrcE StSrcT StVSrcK StVSrcE StVSrcT
     Src1K Src1E Src1T Src2K Src2E Src2T
     StateK StateE StateT ExecT NextPcT : MethDefs.

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
  Variables addrSize lgDataBytes rfIdx : nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT lgDataBytes)
            (getLdDst: LdDstT lgDataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize lgDataBytes)
            (getLdSrc: LdSrcT lgDataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize lgDataBytes)
            (getStAddr: StAddrT addrSize lgDataBytes)
            (getStSrc: StSrcT lgDataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize lgDataBytes)
            (getStVSrc: StVSrcT lgDataBytes rfIdx)
            (getSrc1: Src1T lgDataBytes rfIdx)
            (getSrc2: Src2T lgDataBytes rfIdx)
            (getDst: DstT lgDataBytes rfIdx)
            (exec: ExecT addrSize lgDataBytes)
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx).

  Definition execCm := MethodSig "exec"(RqFromProc addrSize lgDataBytes) : RsToProc lgDataBytes.
  Definition toHostCm := MethodSig "toHost"(Data lgDataBytes) : Bit 0.

  Definition nextPc {ty} ppc st rawInst :=
    (Write "pc" <- getNextPc ty st ppc rawInst;
     Retv)%kami_action.

  Definition procInst := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default
    with Register "pgm" : Vector (Data lgDataBytes) addrSize <- Default
                                 
    with Rule "execLd" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
      LET rawInst <- #pgm@[#ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET dstIdx <- getLdDst _ rawInst;
      Assert (#dstIdx != $0);
      LET addr <- getLdAddr _ rawInst;
      LET srcIdx <- getLdSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      Call ldRep <- execCm(STRUCT { "addr" ::= #laddr;
                                    "op" ::= $$false;
                                    "data" ::= $$Default });
      Write "rf" <- #rf@[#dstIdx <- #ldRep@."data"];
      nextPc ppc rf rawInst
             
    with Rule "execLdZ" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
      LET rawInst <- #pgm@[#ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET regIdx <- getLdDst _ rawInst;
      Assert (#regIdx == $0);
      nextPc ppc rf rawInst

    with Rule "execSt" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
      LET rawInst <- #pgm@[#ppc];
      Assert (getOptype _ rawInst == $$opSt);
      LET addr <- getStAddr _ rawInst;
      LET srcIdx <- getStSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET vsrcIdx <- getStVSrc _ rawInst;
      LET stVal <- #rf@[#vsrcIdx];
      LET saddr <- calcStAddr _ addr srcVal;
      Call execCm(STRUCT { "addr" ::= #saddr;
                           "op" ::= $$true;
                           "data" ::= #stVal });
      nextPc ppc rf rawInst

    with Rule "execToHost" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
      LET rawInst <- #pgm@[#ppc];
      Assert (getOptype _ rawInst == $$opTh);
      LET valIdx <- getSrc1 _ rawInst;
      LET val <- #rf@[#valIdx];
      Call toHostCm(#val);
      nextPc ppc rf rawInst

    with Rule "execNm" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
      LET rawInst <- #pgm@[#ppc];
      Assert (getOptype _ rawInst == $$opNm);
      LET src1 <- getSrc1 _ rawInst;
      LET val1 <- #rf@[#src1];
      LET src2 <- getSrc2 _ rawInst;
      LET val2 <- #rf@[#src2];
      LET dst <- getDst _ rawInst;
      LET execVal <- exec _ val1 val2 ppc rawInst;
      Write "rf" <- #rf@[#dst <- #execVal];
      nextPc ppc rf rawInst
  }.

End ProcInst.

Hint Unfold execCm toHostCm nextPc : MethDefs.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables addrSize lgDataBytes rfIdx : nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT lgDataBytes)
            (getLdDst: LdDstT lgDataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize lgDataBytes)
            (getLdSrc: LdSrcT lgDataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize lgDataBytes)
            (getStAddr: StAddrT addrSize lgDataBytes)
            (getStSrc: StSrcT lgDataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize lgDataBytes)
            (getStVSrc: StVSrcT lgDataBytes rfIdx)
            (getSrc1: Src1T lgDataBytes rfIdx)
            (getSrc2: Src2T lgDataBytes rfIdx)
            (getDst: DstT lgDataBytes rfIdx)
            (exec: ExecT addrSize lgDataBytes)
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx).

  Variable n: nat.

  Definition pinst := procInst getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                               getStAddr getStSrc calcStAddr getStVSrc
                               getSrc1 getSrc2 getDst exec getNextPc.
  Definition pinsts (i: nat): Modules := duplicate pinst i.
  Definition minst := memInst n addrSize lgDataBytes.

  Definition sc := ConcatMod (pinsts n) minst.

End SC.

Hint Unfold pinst pinsts minst sc : ModuleDefs.

Section Facts.
  Variables addrSize lgDataBytes rfIdx : nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT lgDataBytes)
            (getLdDst: LdDstT lgDataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize lgDataBytes)
            (getLdSrc: LdSrcT lgDataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize lgDataBytes)
            (getStAddr: StAddrT addrSize lgDataBytes)
            (getStSrc: StSrcT lgDataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize lgDataBytes)
            (getStVSrc: StVSrcT lgDataBytes rfIdx)
            (getSrc1: Src1T lgDataBytes rfIdx)
            (getSrc2: Src2T lgDataBytes rfIdx)
            (getDst: DstT lgDataBytes rfIdx)
            (exec: ExecT addrSize lgDataBytes)
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx).

  Lemma pinst_ModEquiv:
    ModPhoasWf (pinst getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                      getStAddr getStSrc calcStAddr getStVSrc
                      getSrc1 getSrc2 getDst exec getNextPc).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pinst_ModEquiv.

  Variable n: nat.
  
  Lemma pinsts_ModEquiv:
    ModPhoasWf (pinsts getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc n).
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
    ModPhoasWf (sc getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                   getStAddr getStSrc calcStAddr getStVSrc
                   getSrc1 getSrc2 getDst exec getNextPc n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pinst_ModEquiv pinsts_ModEquiv memInstM_ModEquiv sc_ModEquiv.

