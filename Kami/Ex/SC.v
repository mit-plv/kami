Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct.
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
  Variables opIdx addrSize iaddrSize dataBytes rfIdx: nat.

  (* opcode-related *)
  Definition OpcodeK := SyntaxKind (Bit opIdx).
  Definition OpcodeE (ty: Kind -> Type) := Expr ty OpcodeK.
  Definition OpcodeT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> OpcodeE ty.

  Definition opLd := WO~0~0.
  Definition opSt := WO~0~1.
  Definition opNm := WO~1~1.
  
  Definition OptypeK := SyntaxKind (Bit 2).
  Definition OptypeE (ty: Kind -> Type) := Expr ty OptypeK.
  Definition OptypeT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> OptypeE ty.
  
  (* load-related *)
  Definition LdDstK := SyntaxKind (Bit rfIdx).
  Definition LdDstE (ty: Kind -> Type) := Expr ty LdDstK.
  Definition LdDstT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> LdDstE ty.

  Definition LdAddrK := SyntaxKind (Bit addrSize).
  Definition LdAddrE (ty: Kind -> Type) := Expr ty LdAddrK.
  Definition LdAddrT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> LdAddrE ty.

  Definition LdSrcK := SyntaxKind (Bit rfIdx).
  Definition LdSrcE (ty: Kind -> Type) := Expr ty LdSrcK.
  Definition LdSrcT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> LdSrcE ty.

  Definition LdAddrCalcT :=
    forall ty,
      fullType ty (SyntaxKind (Bit addrSize)) -> (* base address *)
      fullType ty (SyntaxKind (Data dataBytes)) -> (* dst value *)
      Expr ty (SyntaxKind (Bit addrSize)).
  
  (* store-related *)
  Definition StAddrK := SyntaxKind (Bit addrSize).
  Definition StAddrE (ty: Kind -> Type) := Expr ty StAddrK.
  Definition StAddrT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> StAddrE ty.
  
  Definition StSrcK := SyntaxKind (Bit rfIdx).
  Definition StSrcE (ty: Kind -> Type) := Expr ty StSrcK.
  Definition StSrcT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> StSrcE ty.

  Definition StAddrCalcT :=
    forall ty,
      fullType ty (SyntaxKind (Bit addrSize)) -> (* base address *)
      fullType ty (SyntaxKind (Data dataBytes)) -> (* dst value *)
      Expr ty (SyntaxKind (Bit addrSize)).

  Definition StVSrcK := SyntaxKind (Bit rfIdx).
  Definition StVSrcE (ty: Kind -> Type) := Expr ty StVSrcK.
  Definition StVSrcT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> StVSrcE ty.

  (* general sources *)
  Definition Src1K := SyntaxKind (Bit rfIdx).
  Definition Src1E (ty: Kind -> Type) := Expr ty Src1K.
  Definition Src1T := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> Src1E ty.

  Definition Src2K := SyntaxKind (Bit rfIdx).
  Definition Src2E (ty: Kind -> Type) := Expr ty Src2K.
  Definition Src2T := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> Src2E ty.

  (* general destination *)
  Definition DstK := SyntaxKind (Bit rfIdx).
  Definition DstE (ty: Kind -> Type) := Expr ty DstK.
  Definition DstT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> DstE ty.
  
  (* execution *)
  Definition StateK := SyntaxKind (Vector (Data dataBytes) rfIdx).
  Definition StateT (ty : Kind -> Type) := fullType ty StateK.
  Definition StateE (ty : Kind -> Type) := Expr ty StateK.

  Definition ExecT := forall ty, fullType ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                                 fullType ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                                 fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                 fullType ty (SyntaxKind (Data dataBytes)) -> (* rawInst *)
                                 Expr ty (SyntaxKind (Data dataBytes)). (* executed value *)
  Definition NextPcT := forall ty, StateT ty -> (* rf *)
                                   fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                   fullType ty (SyntaxKind (Data dataBytes)) -> (* rawInst *)
                                   Expr ty (SyntaxKind (Bit addrSize)). (* next pc *)
  Definition AlignPcT := forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                    Expr ty (SyntaxKind (Bit iaddrSize)). (* aligned pc *)
  Definition AlignAddrT := forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                                      Expr ty (SyntaxKind (Bit addrSize)). (* aligned addr *)
  
End DecExec.

Hint Unfold OpcodeK OpcodeE OpcodeT OptypeK OptypeE OptypeT opLd opSt opNm
     LdDstK LdDstE LdDstT LdAddrK LdAddrE LdAddrT LdSrcK LdSrcE LdSrcT
     StAddrK StAddrE StAddrT StSrcK StSrcE StSrcT StVSrcK StVSrcE StVSrcT
     Src1K Src1E Src1T Src2K Src2E Src2T
     StateK StateE StateT ExecT NextPcT AlignPcT AlignAddrT : MethDefs.

(* The module definition for Minst with n ports *)
Section MemInst.
  Variable n : nat.
  Variable addrSize : nat.
  Variable dataBytes : nat.

  Definition RqFromProc := RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := RsToProc dataBytes.

  Definition memInstExec {ty} : ty (Struct RqFromProc) -> GenActionT Void ty (Struct RsToProc) :=
    fun (a: ty (Struct RqFromProc)) =>
      (If !#a!RqFromProc@."op" then (* load *)
         Read memv <- "mem";
         LET ldval <- #memv@[#a!RqFromProc@."addr"];
         Ret (STRUCT { "data" ::= #ldval } :: Struct RsToProc)
       else (* store *)
         Read memv <- "mem";
         Write "mem" <- #memv@[ #a!RqFromProc@."addr" <- #a!RqFromProc@."data" ];
         Ret (STRUCT { "data" ::= $$Default } :: Struct RsToProc)
       as na;
       Ret #na)%kami_gen.

  Definition memInstM := META {
    Register "mem" : Vector (Data dataBytes) addrSize <- Default

    with Repeat Method till n by "memOp" (a : Struct RqFromProc) : Struct RsToProc :=
      (memInstExec a)
  }.
    
  Definition memInst := modFromMeta memInstM.

  Definition memOp := MethodSig "memOp"(Struct RqFromProc) : Struct RsToProc.
  
End MemInst.

Section MMIO.
  Variable addrSize: nat.
  Variable dataBytes: nat.

  Definition IsMMIOE (ty: Kind -> Type) := Expr ty (SyntaxKind Bool).
  Definition IsMMIOT :=
    forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> IsMMIOE ty.

  Variable (isMMIO: IsMMIOT).

  Local Notation RqFromProc := (RqFromProc addrSize dataBytes).
  Local Notation RsToProc := (RsToProc dataBytes).

  Definition mmioExec :=
    MethodSig "mmioExec"(Struct RqFromProc): Struct RsToProc.

  Definition mm := MODULE {
    Register "mem" : Vector (Data dataBytes) addrSize <- Default

    with Method "mmOp" (a : Struct RqFromProc): Struct RsToProc :=
      LET addr <- #a!RqFromProc@."addr";

      If (isMMIO _ addr) then (** mmio *)
        Call rs <- mmioExec(#a);
        Ret #rs
      else
        If !#a!RqFromProc@."op" then (** load *)
          Read memv <- "mem";
          LET ldval <- #memv@[#a!RqFromProc@."addr"];
          Ret (STRUCT { "data" ::= #ldval } :: Struct RsToProc)
        else (** store *)
          Read memv <- "mem";
          Write "mem" <- #memv@[ #a!RqFromProc@."addr" <- #a!RqFromProc@."data" ];
          Ret (STRUCT { "data" ::= $$Default } :: Struct RsToProc)
        as na;
        Ret #na
      as na;
      Ret #na
  }.
    
  Definition mmOp := MethodSig "mmOp"(Struct RqFromProc) : Struct RsToProc.

End MMIO.

Hint Unfold RqFromProc RsToProc memInstExec mmioExec : MethDefs.
Hint Unfold memInstM memInst mm : ModuleDefs.

(* The module definition for Pinst *)
Section ProcInst.
  Variables addrSize iaddrSize dataBytes rfIdx : nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT dataBytes)
            (getLdDst: LdDstT dataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize dataBytes)
            (getLdSrc: LdSrcT dataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize dataBytes)
            (getStSrc: StSrcT dataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT dataBytes rfIdx)
            (getSrc1: Src1T dataBytes rfIdx)
            (getSrc2: Src2T dataBytes rfIdx)
            (getDst: DstT dataBytes rfIdx)
            (exec: ExecT addrSize dataBytes)
            (getNextPc: NextPcT addrSize dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize).

  Definition nextPc {ty} ppc st rawInst :=
    (Write "pc" <- getNextPc ty st ppc rawInst;
     Retv)%kami_action.

  Record ProcInit := { pcInit : ConstT (Bit addrSize);
                       rfInit : ConstT (Vector (Data dataBytes) rfIdx)
                     }.
  Definition procInitDefault :=
    {| pcInit := Default; rfInit := Default |}.

  Local Notation memOp := (memOp addrSize dataBytes).

  Definition pgmLdRq :=
    MethodSig "pgmLdRq"(Void) : Void.

  Definition PgmLdRs :=
    STRUCT { "data" :: Data dataBytes;
             "isEnd" :: Bool
           }.
  Definition pgmLdRs :=
    MethodSig "pgmLdRs"(): Struct PgmLdRs.
  
  Variables (procInit: ProcInit).

  Definition procInst := MODULE {
    Register "pc" : Bit addrSize <- (pcInit procInit)
    with Register "rf" : Vector (Data dataBytes) rfIdx <- (rfInit procInit)

    with Register "pinit" : Bool <- Default
    with Register "pinitOfs" : Bit iaddrSize <- Default
    with Register "pgm" : Vector (Data dataBytes) iaddrSize <- Default

    (** Phase 1: initialize the program [pinit == false] *)

    with Rule "rqInit" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Call pgmLdRq ();
      Retv

    with Rule "rsInitCont" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Call irs <- pgmLdRs ();
      Read pinitOfs : Bit iaddrSize <- "pinitOfs";
      Read pgm <- "pgm";
      Assert !#irs!PgmLdRs@."isEnd";
      Write "pgm" <- #pgm@[#pinitOfs <- #irs!PgmLdRs@."data"];
      Write "pinitOfs" <- #pinitOfs + $1;
      Retv

    with Rule "rsInitEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Call irs <- pgmLdRs ();
      Read pinitOfs : Bit iaddrSize <- "pinitOfs";
      Read pgm <- "pgm";
      Assert #irs!PgmLdRs@."isEnd";
      Write "pgm" <- #pgm@[#pinitOfs <- #irs!PgmLdRs@."data"];
      Write "pinit" <- !#pinit;
      Retv

    (** Phase 2: execute the program [pinit == true] *)
        
    with Rule "execLd" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm@[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET dstIdx <- getLdDst _ rawInst;
      Assert (#dstIdx != $0);
      LET addr <- getLdAddr _ rawInst;
      LET srcIdx <- getLdSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      Call ldRep <- memOp(STRUCT { "addr" ::= alignAddr _ laddr;
                                   "op" ::= $$false;
                                   "data" ::= $$Default });
      Write "rf" <- #rf@[#dstIdx <- #ldRep!(RsToProc dataBytes)@."data"];
      nextPc ppc rf rawInst
             
    with Rule "execLdZ" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm@[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET regIdx <- getLdDst _ rawInst;
      Assert (#regIdx == $0);
      nextPc ppc rf rawInst

    with Rule "execSt" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm@[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opSt);
      LET addr <- getStAddr _ rawInst;
      LET srcIdx <- getStSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET vsrcIdx <- getStVSrc _ rawInst;
      LET stVal <- #rf@[#vsrcIdx];
      LET saddr <- calcStAddr _ addr srcVal;
      Call memOp(STRUCT { "addr" ::= alignAddr _ saddr;
                          "op" ::= $$true;
                          "data" ::= #stVal });
      nextPc ppc rf rawInst

    with Rule "execNm" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm@[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opNm);
      LET src1 <- getSrc1 _ rawInst;
      LET val1 <- #rf@[#src1];
      LET src2 <- getSrc2 _ rawInst;
      LET val2 <- #rf@[#src2];
      LET dst <- getDst _ rawInst;
      Assert (#dst != $0);
      LET execVal <- exec _ val1 val2 ppc rawInst;
      Write "rf" <- #rf@[#dst <- #execVal];
      nextPc ppc rf rawInst

    with Rule "execNmZ" :=
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm@[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opNm);
      LET dst <- getDst _ rawInst;
      Assert (#dst == $0);
      nextPc ppc rf rawInst
  }.

End ProcInst.

Hint Unfold memOp nextPc procInitDefault pgmLdRq pgmLdRs PgmLdRs : MethDefs.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables addrSize iaddrSize dataBytes rfIdx : nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT dataBytes)
            (getLdDst: LdDstT dataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize dataBytes)
            (getLdSrc: LdSrcT dataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize dataBytes)
            (getStSrc: StSrcT dataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT dataBytes rfIdx)
            (getSrc1: Src1T dataBytes rfIdx)
            (getSrc2: Src2T dataBytes rfIdx)
            (getDst: DstT dataBytes rfIdx)
            (exec: ExecT addrSize dataBytes)
            (getNextPc: NextPcT addrSize dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize)
            (isMMIO: IsMMIOT addrSize).

  Variable n: nat.

  Definition pinst := procInst getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                               getStAddr getStSrc calcStAddr getStVSrc
                               getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr.

  Variables (procInit: ProcInit addrSize dataBytes rfIdx).

  (** Just for singlecore (for now) *)
  Definition scmm := ConcatMod (pinst procInit) (mm addrSize isMMIO).

End SC.

Hint Unfold pinst scmm : ModuleDefs.

Section Facts.
  Variables addrSize iaddrSize dataBytes rfIdx : nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT dataBytes)
            (getLdDst: LdDstT dataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize dataBytes)
            (getLdSrc: LdSrcT dataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize dataBytes)
            (getStSrc: StSrcT dataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT dataBytes rfIdx)
            (getSrc1: Src1T dataBytes rfIdx)
            (getSrc2: Src2T dataBytes rfIdx)
            (getDst: DstT dataBytes rfIdx)
            (exec: ExecT addrSize dataBytes)
            (getNextPc: NextPcT addrSize dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize).

  Lemma pinst_ModEquiv:
    forall init,
      ModPhoasWf (pinst getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                        getStAddr getStSrc calcStAddr getStVSrc
                        getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr init).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pinst_ModEquiv.

  Variable n: nat.
  
  Lemma memInstM_ModEquiv:
    MetaModPhoasWf (memInstM n addrSize dataBytes).
  Proof.
    kequiv.
  Qed.
  Hint Resolve memInstM_ModEquiv.

  Variable (isMMIO: IsMMIOT addrSize).

  Lemma mm_ModEquiv: ModPhoasWf (mm addrSize isMMIO).
  Proof.
    kequiv.
  Qed.
  
  Lemma scmm_ModEquiv:
    forall inits,
      ModPhoasWf (scmm getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr
                       isMMIO inits).
  Proof.
    kequiv.
  Qed.
  
End Facts.

Hint Resolve pinst_ModEquiv memInstM_ModEquiv mm_ModEquiv scmm_ModEquiv.

