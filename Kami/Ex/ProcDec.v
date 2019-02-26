Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A memory-decoupled, in-order processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * It just stalls until it gets a memory operation response.
 *)
Section ProcDec.
  Variable inName outName: string.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT instBytes)
            (getLdDst: LdDstT instBytes rfIdx)
            (getLdAddr: LdAddrT addrSize instBytes)
            (getLdSrc: LdSrcT instBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize instBytes)
            (getStSrc: StSrcT instBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT instBytes rfIdx)
            (getSrc1: Src1T instBytes rfIdx)
            (getSrc2: Src2T instBytes rfIdx)
            (getDst: DstT instBytes rfIdx)
            (exec: ExecT addrSize instBytes dataBytes)
            (getNextPc: NextPcT addrSize instBytes dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  (* Called method signatures *)
  Definition memReq := MethodSig (inName -- "enq")(Struct RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : Struct RsToProc.
  Definition pgmInit := pgmInit iaddrSize instBytes.

  Definition nextPc {ty} ppc st rawInst :=
    (Write "pc" <- getNextPc ty st ppc rawInst;
     Retv)%kami_action.

  Variable (procInit: ProcInit addrSize dataBytes rfIdx).

  Definition procDec := MODULE {
    Register "pc" : Bit addrSize <- (pcInit procInit)
    with Register "rf" : Vector (Data dataBytes) rfIdx <- (rfInit procInit)
    with Register "pinit" : Bool <- Default
    with Register "pinitOfs" : Bit iaddrSize <- Default
    with Register "pgm" : Vector (Data instBytes) iaddrSize <- Default
    with Register "stall" : Bool <- false

    (** Phase 1: initialize the program [pinit == false] *)

    with Rule "pgmInit" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitOfs : Bit iaddrSize <- "pinitOfs";
      Assert ((UniBit (Inv _) #pinitOfs) != $0);
      Call irs <- pgmInit (#pinitOfs);
      Read pgm <- "pgm";
      Write "pgm" <- #pgm@[#pinitOfs <- #irs];
      Write "pinitOfs" <- #pinitOfs + $1;
      Retv

    with Rule "pgmInitEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitOfs : Bit iaddrSize <- "pinitOfs";
      Assert ((UniBit (Inv _) #pinitOfs) == $0);
      Call irs <- pgmInit (#pinitOfs);
      Read pgm <- "pgm";
      Write "pgm" <- #pgm@[#pinitOfs <- #irs];
      Write "pinit" <- !#pinit;
      Retv

    (** Phase 2: execute the program [pinit == true] *)

    with Rule "reqLd" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc : Bit addrSize <- "pc";
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
      Call memReq(STRUCT { "addr" ::= alignAddr _ laddr;
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Write "stall" <- $$true;
      Retv

    with Rule "reqLdZ" :=
      Read stall <- "stall";
      Assert !#stall;
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

    with Rule "reqSt" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc : Bit addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opSt);
      LET addr <- getStAddr _ rawInst;
      LET srcIdx <- getStSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET vsrcIdx <- getStVSrc _ rawInst;
      LET stVal <- #rf@[#vsrcIdx];
      LET saddr <- calcStAddr _ addr srcVal;
      Call memReq(STRUCT { "addr" ::= alignAddr _ saddr;
                           "op" ::= $$true;
                           "data" ::= #stVal });
      Write "stall" <- $$true;
      Retv
                      
    with Rule "repLd" :=
      Call val <- memRep();
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET dstIdx <- getLdDst _ rawInst;
      Write "rf" <- #rf@[#dstIdx <- #val!RsToProc@."data"];
      Write "stall" <- $$false;
      nextPc ppc rf rawInst
                      
    with Rule "repSt" :=
      Call val <- memRep();
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opSt);
      Write "stall" <- $$false;
      nextPc ppc rf rawInst
                      
    with Rule "execNm" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[alignPc _ ppc];
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
      Read stall <- "stall";
      Assert !#stall;
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opNm);
      LET dst <- getDst _ rawInst;
      Assert (#dst == $0);
      nextPc ppc rf rawInst
  }.

End ProcDec.

Hint Unfold procDec : ModuleDefs.
Hint Unfold RqFromProc RsToProc memReq memRep pgmInit nextPc : MethDefs.

Section ProcDecM.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT instBytes)
            (getLdDst: LdDstT instBytes rfIdx)
            (getLdAddr: LdAddrT addrSize instBytes)
            (getLdSrc: LdSrcT instBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize instBytes)
            (getStSrc: StSrcT instBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT instBytes rfIdx)
            (getSrc1: Src1T instBytes rfIdx)
            (getSrc2: Src2T instBytes rfIdx)
            (getDst: DstT instBytes rfIdx)
            (exec: ExecT addrSize instBytes dataBytes)
            (getNextPc: NextPcT addrSize instBytes dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize).

  Definition pdec init :=
    procDec "rqFromProc"%string "rsToProc"%string
            getOptype getLdDst getLdAddr getLdSrc calcLdAddr
            getStAddr getStSrc calcStAddr getStVSrc
            getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr init.

  Variables (procInits: list (ProcInit addrSize dataBytes rfIdx)).

  Definition pdecs (i: nat) :=
    duplicate (fun iv => pdec (nth_default (procInitDefault addrSize dataBytes rfIdx)
                                           procInits iv)) i.

  Definition pdecf init := (pdec init ++ iom addrSize fifoSize dataBytes)%kami.
  Definition pdecfs (i: nat) :=
    duplicate (fun iv => pdecf (nth_default (procInitDefault addrSize dataBytes rfIdx)
                                            procInits iv)) i.
  Definition procDecM (n: nat) := (pdecfs n ++ minst addrSize dataBytes n)%kami.

End ProcDecM.

Hint Unfold pdec pdecf pdecfs procDecM : ModuleDefs.

Section Facts.
  Variables opIdx addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT instBytes)
            (getLdDst: LdDstT instBytes rfIdx)
            (getLdAddr: LdAddrT addrSize instBytes)
            (getLdSrc: LdSrcT instBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize instBytes)
            (getStSrc: StSrcT instBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT instBytes rfIdx)
            (getSrc1: Src1T instBytes rfIdx)
            (getSrc2: Src2T instBytes rfIdx)
            (getDst: DstT instBytes rfIdx)
            (exec: ExecT addrSize instBytes dataBytes)
            (getNextPc: NextPcT addrSize instBytes dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize).

  Lemma pdec_ModEquiv:
    forall init,
      ModPhoasWf (pdec getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr init).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdec_ModEquiv.

  Lemma pdecf_ModEquiv:
    forall init,
      ModPhoasWf (pdecf fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                        getStAddr getStSrc calcStAddr getStVSrc
                        getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr init).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecf_ModEquiv.

  Variable n: nat.

  Lemma pdecfs_ModEquiv:
    forall inits,
      ModPhoasWf (pdecfs fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                         getStAddr getStSrc calcStAddr getStVSrc
                         getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr inits n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecfs_ModEquiv.

  Lemma procDecM_ModEquiv:
    forall inits,
      ModPhoasWf (procDecM fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                           getStAddr getStSrc calcStAddr getStVSrc
                           getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr inits n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pdec_ModEquiv pdecf_ModEquiv pdecfs_ModEquiv procDecM_ModEquiv.

