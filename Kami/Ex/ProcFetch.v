Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.OneEltFifo Ex.Fifo Ex.MemAsync Ex.ProcFetchDecode.
Require Import Kami.PrimBram.

Set Implicit Arguments.

Section FetchICache.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (predictNextPc:
               forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                          Expr ty (SyntaxKind (Pc iaddrSize))).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Definition icache: Modules :=
    bram1 "pgm" 1 iaddrSize (Data instBytes).

  Definition instRq :=
    MethodSig ("pgm" -- "putRq")
              (Struct (BramRq iaddrSize (Data instBytes))): Void.
  Definition instRs :=
    MethodSig ("pgm" -- "getRs")(): Data instBytes.

  Definition f2dEnq := f2dEnq f2dElt.
  Definition f2dDeq := f2dDeq f2dElt.

  Definition w2dDeq := w2dDeq iaddrSize.

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Definition memReq := memReq addrSize dataBytes.
  Definition memRep := memRep dataBytes.

  Variables (pcInit : ConstT (Pc iaddrSize)).

  Definition fetcher := MODULE {
    Register "pc" : Pc iaddrSize <- pcInit
    with Register "pinit" : Bool <- Default
    with Register "pinitRqOfs" : Bit iaddrSize <- Default
    with Register "pinitRsOfs" : Bit iaddrSize <- Default
    with Register "pinstRsOfs" : Bit iaddrSize <- Default
    with Register "fEpoch" : Bool <- false
    with Register "fStall" : Bool <- false

    (** Phase 1: initialize the program [pinit == false] *)

    with Rule "pgmInitRq" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
      Assert ((UniBit (Inv _) #pinitRqOfs) != $0);

      Call memReq(STRUCT { "addr" ::= (_zeroExtend_ #pinitRqOfs) << $$(natToWord 2 2);
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Write "pinitRqOfs" <- #pinitRqOfs + $1;
      Retv

    with Rule "pgmInitRqEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRqOfs : Bit iaddrSize <- "pinitRqOfs";
      Assert ((UniBit (Inv _) #pinitRqOfs) == $0);
      Call memReq(STRUCT { "addr" ::= (_zeroExtend_ #pinitRqOfs) << $$(natToWord 2 2);
                           "op" ::= $$false;
                           "data" ::= $$Default });
      Retv
        
    with Rule "pgmInitRs" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinitRsOfs : Bit iaddrSize <- "pinitRsOfs";

      Call ldData <- memRep();
      LET ldVal <- #ldData!RsToProc@."data";
      LET inst <- alignInst _ ldVal;
      Call instRq(STRUCT { "write" ::= $$true;
                           "addr" ::= #pinitRsOfs;
                           "datain" ::= #inst });
      Write "pinitRsOfs" <- #pinitRsOfs + $1;
      Retv

    with Rule "pgmInitAck" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinstRsOfs : Bit iaddrSize <- "pinstRsOfs";
      Assert ((UniBit (Inv _) #pinstRsOfs) != $0);

      Call instRs();
      Write "pinstRsOfs" <- #pinstRsOfs + $1;
      Retv
        
    with Rule "pgmInitAckEnd" :=
      Read pinit <- "pinit";
      Assert !#pinit;
      Read pinstRsOfs : Bit iaddrSize <- "pinstRsOfs";
      Assert ((UniBit (Inv _) #pinstRsOfs) == $0);

      Call instRs();
      Write "pinit" <- !#pinit;
      Retv

    (** Phase 2: execute the program [pinit == true] *)
                                  
    with Rule "modifyPc" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Read stall <- "fStall";
      Assert !#stall;
      Call correctPc <- w2dDeq();
      Write "pc" <- #correctPc;
      Read pEpoch <- "fEpoch";
      Write "fEpoch" <- !#pEpoch;
      Call f2dFlush();
      Retv

    with Rule "instFetchRq" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Read stall <- "fStall";
      Assert !#stall;
      Read pc : Pc iaddrSize <- "pc";
      Call instRq(STRUCT { "write" ::= $$false;
                           "addr" ::= _truncLsb_ #pc;
                           "datain" ::= $$Default });
      Write "fStall" <- $$true;
      Retv

    with Rule "instFetchRs" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Read stall <- "fStall";
      Assert #stall;
      Call inst <- instRs();
      Read pc : Pc iaddrSize <- "pc";
      Read epoch <- "fEpoch";
      LET npc <- predictNextPc _ pc;
      Call f2dEnq(f2dPack #inst #pc #npc #epoch);
      Write "pc" <- #npc;
      Write "fStall" <- $$false;
      Retv
  }.

  Definition fetchICache := (fetcher ++ icache)%kami.

End FetchICache.

Hint Unfold fetcher icache fetchICache : ModuleDefs.
Hint Unfold instRq instRs
     f2dEnq f2dDeq w2dDeq RqFromProc RsToProc
     memReq memRep: MethDefs.

Section Facts.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch instBytes dataBytes)
            (predictNextPc:
               forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                          Expr ty (SyntaxKind (Pc iaddrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc iaddrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Lemma fetcher_ModEquiv:
    forall pcInit, ModPhoasWf (fetcher addrSize fetch predictNextPc f2dPack pcInit).
  Proof. kequiv. Qed.
  Hint Resolve fetcher_ModEquiv.

  Lemma fetchICache_ModEquiv:
    forall pcInit,
      ModPhoasWf (fetchICache addrSize fetch predictNextPc f2dPack pcInit).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve fetcher_ModEquiv fetchICache_ModEquiv.

