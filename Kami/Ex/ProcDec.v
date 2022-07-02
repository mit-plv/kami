Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAsync.

Set Implicit Arguments.

(* A memory-decoupled, in-order processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * It just stalls until it gets a memory operation response.
 *)
Section ProcDec.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  (* Called method signatures *)
  Definition memReq := MethodSig ("rqFromProc" -- "enq")(Struct RqFromProc) : Void.
  Definition memRep := MethodSig ("rsToProc" -- "deq")() : Struct RsToProc.

  Definition nextPc {ty} ppc st rawInst :=
    (Write "pc" <- getNextPc ty st ppc rawInst;
     Retv)%kami_action.

  Variable (procInit: ProcInit addrSize dataBytes rfIdx).

  Definition procDec := MODULE {
    Register "pc" : Pc addrSize <- (pcInit procInit)
    with Register "rf" : Vector (Data dataBytes) rfIdx <- (rfInit procInit)
    with Register "pinit" : Bool <- Default
    with Register "pinitRq" : Bool <- Default
    with Register "pinitRqOfs" : Bit iaddrSize <- Default
    with Register "pinitRsOfs" : Bit iaddrSize <- Default
    with Register "pgm" : Vector (Data instBytes) iaddrSize <- Default
    with Register "stall" : Bool <- false

    (** Phase 1: initialize the program [pinit == false] *)

    with Rule "pgmInitRq" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRq <- "pinitRq";
      Assert !#pinitRq;
      Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
      Assert ((UniBit (Inv _) #pinitRqOfs) != $0);

      Call memReq(STRUCT { "addr" ::= toAddr _ pinitRqOfs;
                           "op" ::= $$false;
                           "byteEn" ::= $$Default;
                           "data" ::= $$Default });
      Write "pinitRqOfs" <- #pinitRqOfs + $1;
      Retv

    with Rule "pgmInitRqEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRq <- "pinitRq";
      Assert !#pinitRq;
      Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
      Assert ((UniBit (Inv _) #pinitRqOfs) == $0);
      Call memReq(STRUCT { "addr" ::= toAddr _ pinitRqOfs;
                           "op" ::= $$false;
                           "byteEn" ::= $$Default;
                           "data" ::= $$Default });
      Write "pinitRq" <- $$true;
      Write "pinitRqOfs" : Bit iaddrSize <- $0;
      Retv
        
    with Rule "pgmInitRs" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRsOfs : Bit iaddrSize <- "pinitRsOfs";
      Assert ((UniBit (Inv _) #pinitRsOfs) != $0);

      Call ldData <- memRep();
      LET ldVal <- #ldData!RsToProc@."data";
      LET inst <- alignInst _ ldVal;
      Read pgm <- "pgm";
      Write "pgm" <- #pgm@[#pinitRsOfs <- #inst];
      Write "pinitRsOfs" <- #pinitRsOfs + $1;
      Retv

    with Rule "pgmInitRsEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRsOfs : Bit iaddrSize <- "pinitRsOfs";
      Assert ((UniBit (Inv _) #pinitRsOfs) == $0);

      Call ldData <- memRep();
      LET ldVal <- #ldData!RsToProc@."data";
      LET inst <- alignInst _ ldVal;
      Read pgm <- "pgm";
      Write "pgm" <- #pgm@[#pinitRsOfs <- #inst];
      Write "pinit" <- !#pinit;
      Write "pinitRsOfs" : Bit iaddrSize <- $0;
      Retv

    (** Phase 2: execute the program [pinit == true] *)

    with Rule "reqLd" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc : Pc addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm@[toIAddr _ ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET addr <- getLdAddr _ rawInst;
      LET srcIdx <- getLdSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      Call memReq(STRUCT { "addr" ::= #laddr;
                           "op" ::= $$false;
                           "byteEn" ::= $$Default;
                           "data" ::= $$Default });
      Write "stall" <- $$true;
      Retv

    with Rule "reqSt" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc : Pc addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[toIAddr _ ppc];
      Assert (getOptype _ rawInst == $$opSt);
      LET addr <- getStAddr _ rawInst;
      LET srcIdx <- getStSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET vsrcIdx <- getStVSrc _ rawInst;
      LET stVal <- #rf@[#vsrcIdx];
      LET saddr <- calcStAddr _ addr srcVal;
      LET byteEn <- calcStByteEn _ rawInst;
      Call memReq(STRUCT { "addr" ::= #saddr;
                           "op" ::= $$true;
                           "byteEn" ::= #byteEn;
                           "data" ::= #stVal });
      Write "stall" <- $$true;
      Retv
                      
    with Rule "repLd" :=
      Call val <- memRep();
      Read ppc : Pc addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[toIAddr _ ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET dstIdx <- getLdDst _ rawInst;
      Assert (#dstIdx != $0);
      LET addr <- getLdAddr _ rawInst;
      LET srcIdx <- getLdSrc _ rawInst;
      LET srcVal <- #rf@[#srcIdx];
      LET laddr <- calcLdAddr _ addr srcVal;
      LET ldValWord <- #val!RsToProc@."data";
      LET ldType <- getLdType _ rawInst;
      LET ldVal <- calcLdVal _ laddr ldValWord ldType;
      Write "rf" <- #rf@[#dstIdx <- #ldVal];
      Write "stall" <- $$false;
      nextPc ppc rf rawInst

    with Rule "repLdZ" :=
      Call val <- memRep();
      Read ppc : Pc addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[toIAddr _ ppc];
      Assert (getOptype _ rawInst == $$opLd);
      LET dstIdx <- getLdDst _ rawInst;
      Assert (#dstIdx == $0);
      Write "stall" <- $$false;
      nextPc ppc rf rawInst

    with Rule "repSt" :=
      Call val <- memRep();
      Read ppc : Pc addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[toIAddr _ ppc];
      Assert (getOptype _ rawInst == $$opSt);
      Write "stall" <- $$false;
      nextPc ppc rf rawInst
                      
    with Rule "execNm" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc : Pc addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[toIAddr _ ppc];
      Assert (getOptype _ rawInst == $$opNm);
      LET src1 <- getSrc1 _ rawInst;
      LET val1 <- #rf@[#src1];
      LET src2 <- getSrc2 _ rawInst;
      LET val2 <- #rf@[#src2];
      LET dst <- getDst _ rawInst;
      Assert (#dst != $0);
      LET execVal <- doExec _ val1 val2 ppc rawInst;
      Write "rf" <- #rf@[#dst <- #execVal];
      nextPc ppc rf rawInst

    with Rule "execNmZ" :=
      Read stall <- "stall";
      Assert !#stall;
      Read ppc : Pc addrSize <- "pc";
      Read rf <- "rf";
      Read pinit <- "pinit";
      Read pgm : Vector (Data instBytes) iaddrSize <- "pgm";
      Assert #pinit;
      LET rawInst <- #pgm @[toIAddr _ ppc];
      Assert (getOptype _ rawInst == $$opNm);
      LET dst <- getDst _ rawInst;
      Assert (#dst == $0);
      nextPc ppc rf rawInst
  }.

End ProcDec.

#[global] Hint Unfold procDec : ModuleDefs.
#[global] Hint Unfold RqFromProc RsToProc memReq memRep nextPc : MethDefs.

Section ProcDecM.
  Variables (addrSize maddrSize iaddrSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Definition pdec init :=
    procDec fetch dec exec init.

  Variables (procInit: ProcInit addrSize dataBytes rfIdx)
            (memInit: MemInit maddrSize).

  Definition pdecf := (pdec procInit ++ iom addrSize dataBytes)%kami.
  Definition procDecM := (pdecf ++ mm Hdb memInit ammio)%kami.

End ProcDecM.

#[global] Hint Unfold pdec pdecf procDecM : ModuleDefs.

Section Facts.
  Variables (addrSize maddrSize iaddrSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Lemma pdec_ModEquiv:
    forall init, ModPhoasWf (pdec fetch dec exec init).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve pdec_ModEquiv.

  Lemma pdecf_ModEquiv:
    forall init, ModPhoasWf (pdecf fetch dec exec init).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve pdecf_ModEquiv.

  Lemma procDecM_ModEquiv:
    forall procInit (memInit: MemInit maddrSize),
      ModPhoasWf (procDecM Hdb fetch dec exec ammio procInit memInit).
  Proof.
    kequiv.
  Qed.

End Facts.

#[global] Hint Resolve pdec_ModEquiv pdecf_ModEquiv procDecM_ModEquiv.

