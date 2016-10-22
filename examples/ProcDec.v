Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A decoupled processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * This processor does NOT use a ROB, which implies that it just stalls
 * until getting a memory operation response.
 *)
Section ProcDec.
  Variable inName outName: string.
  Variables addrSize iaddrSize lgDataBytes rfIdx: nat.

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
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  (* Called method signatures *)
  Definition memReq := MethodSig (inName -- "enq")(Struct RqFromProc) : Void.
  Definition memRep := MethodSig (outName -- "deq")() : Struct RsToProc.
  Definition toHost := MethodSig "toHost"(Data lgDataBytes) : Void.

  Definition nextPc {ty} ppc st rawInst :=
    (Write "pc" <- getNextPc ty st ppc rawInst;
     Retv)%kami_action.

  Definition procDec := MODULE {
    Register "pc" : Bit addrSize <- Default
    with Register "rf" : Vector (Data lgDataBytes) rfIdx <- Default
    with Register "pgm" : Vector (Data lgDataBytes) iaddrSize <- Default
    with Register "stall" : Bool <- false
                                 
    with Rule "reqLd" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc : Bit addrSize <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
      LET rawInst <- #pgm@[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET dstIdx <- getLdDst _ rawInst;
      Assert (#dstIdx != $0);
      LET addr <- getLdAddr _ rawInst;
      LET srcIdx <- getLdSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      Call memReq(STRUCT { "addr" ::= #laddr;
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Write "stall" <- $$true;
      Retv

    with Rule "reqLdZ" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
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
      Read pgm <- "pgm";
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opSt);
      LET addr <- getStAddr _ rawInst;
      LET srcIdx <- getStSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET vsrcIdx <- getStVSrc _ rawInst;
      LET stVal <- #rf@[#vsrcIdx];
      LET saddr <- calcStAddr _ addr srcVal;
      Call memReq(STRUCT { "addr" ::= #saddr;
                           "op" ::= $$true;
                           "data" ::= #stVal });
      Write "stall" <- $$true;
      Retv
                      
    with Rule "repLd" :=
      Call val <- memRep();
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
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
      Read pgm <- "pgm";
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opSt);
      Write "stall" <- $$false;
      nextPc ppc rf rawInst
                      
    with Rule "execToHost" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opTh);
      LET valIdx <- getSrc1 _ rawInst;
      LET val <- #rf@[#valIdx];
      Call toHost(#val);
      nextPc ppc rf rawInst

    with Rule "execNm" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc <- "pc";
      Read rf <- "rf";
      Read pgm <- "pgm";
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
      Read pgm <- "pgm";
      LET rawInst <- #pgm @[alignPc _ ppc];
      Assert (getOptype _ rawInst == $$opNm);
      LET dst <- getDst _ rawInst;
      Assert (#dst == $0);
      nextPc ppc rf rawInst
  }.

End ProcDec.

Hint Unfold procDec : ModuleDefs.
Hint Unfold RqFromProc RsToProc memReq memRep toHost nextPc : MethDefs.

Section ProcDecM.
  Variables addrSize iaddrSize fifoSize lgDataBytes rfIdx: nat.

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
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize).

  Definition pdec := procDec "rqFromProc"%string "rsToProc"%string
                             getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                             getStAddr getStSrc calcStAddr getStVSrc
                             getSrc1 getSrc2 getDst exec getNextPc alignPc.
  Definition pdecs (i: nat) := duplicate pdec i.

  Definition pdecf := ConcatMod pdec (iom addrSize fifoSize lgDataBytes).
  Definition pdecfs (i: nat) := duplicate pdecf i.
  Definition procDecM (n: nat) := ConcatMod (pdecfs n) (minst addrSize lgDataBytes n).

End ProcDecM.

Hint Unfold pdec pdecf pdecfs procDecM : ModuleDefs.

Section Facts.
  Variables opIdx addrSize iaddrSize fifoSize lgDataBytes rfIdx: nat.

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
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize).

  Lemma pdec_ModEquiv:
    ModPhoasWf (pdec getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                     getStAddr getStSrc calcStAddr getStVSrc
                     getSrc1 getSrc2 getDst exec getNextPc alignPc).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdec_ModEquiv.

  Lemma pdecf_ModEquiv:
    ModPhoasWf (pdecf fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                      getStAddr getStSrc calcStAddr getStVSrc
                      getSrc1 getSrc2 getDst exec getNextPc alignPc).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecf_ModEquiv.

  Variable n: nat.

  Lemma pdecfs_ModEquiv:
    ModPhoasWf (pdecfs fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc alignPc n).
  Proof.
    kequiv.
  Qed.
  Hint Resolve pdecfs_ModEquiv.

  Lemma procDecM_ModEquiv:
    ModPhoasWf (procDecM fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                         getStAddr getStSrc calcStAddr getStVSrc
                         getSrc1 getSrc2 getDst exec getNextPc alignPc n).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve pdec_ModEquiv pdecf_ModEquiv pdecfs_ModEquiv procDecM_ModEquiv.

