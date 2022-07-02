Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.Tactics.
Require Import Kami.PrimBram Kami.PrimFifo.

Require Import Ex.Btb Ex.MemTypes Ex.SC Ex.MemAsync Ex.ProcFetchDecode.

Set Implicit Arguments.

Section FetchICache.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.
  Variable (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Definition icache: Modules :=
    bram1 "pgm" iaddrSize (Data instBytes).

  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).
  Definition btb: Modules := btb getIndex getTag.

  Definition instRq :=
    MethodSig ("pgm" -- "putRq")
              (Struct (BramRq iaddrSize (Data instBytes))): Void.
  Definition instRs :=
    MethodSig ("pgm" -- "getRs")(): Data instBytes.

  Definition predictPc := MethodSig "btbPredPc"(Bit addrSize): Bit addrSize.
  Definition trainPc := MethodSig "btbUpdate"(Struct (BtbUpdateStr addrSize)): Void.

  Definition f2dEnq := f2dEnq f2dElt.
  Definition f2dDeq := f2dDeq f2dElt.

  Definition W2DStr := ProcThreeStage.W2DStr addrSize.
  Definition w2dDeq := w2dDeq addrSize.

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Definition memReq := memReq addrSize dataBytes.
  Definition memRep := memRep dataBytes.

  Variables (pcInit : ConstT (Pc addrSize)).

  Definition fetcher := MODULE {
    Register "pc" : Pc addrSize <- pcInit
    with Register "pinit" : Bool <- Default
    with Register "pinitRq" : Bool <- Default
    with Register "pinitRqOfs" : Bit iaddrSize <- Default
    with Register "pinitRsOfs" : Bit iaddrSize <- Default
    with Register "fEpoch" : Bool <- false
    with Register "pcUpdated" : Bool <- false
                             
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
      Call instRq(STRUCT { "write" ::= $$true;
                           "addr" ::= #pinitRsOfs;
                           "datain" ::= #inst });
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
      Call instRq(STRUCT { "write" ::= $$true;
                           "addr" ::= #pinitRsOfs;
                           "datain" ::= #inst });
      Write "pinit" <- $$true;
      Write "pinitRsOfs" : Bit iaddrSize <- $0;
      Retv

    (** Phase 2: execute the program [pinit == true] *)
                                  
    with Rule "modifyPc" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Call correctPc <- w2dDeq();
      LET prevPc <- #correctPc!W2DStr@."prevPc";
      LET nextPc <- #correctPc!W2DStr@."nextPc";
      Write "pc" <- #nextPc;
      Read pEpoch <- "fEpoch";
      Write "fEpoch" <- !#pEpoch;
      Call f2dClear();
      Write "pcUpdated" <- $$true;
      Call trainPc (STRUCT {"curPc" ::= #prevPc;
                            "nextPc" ::= #nextPc });
      Retv

    with Rule "instFetchRq" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Read pc : Pc addrSize <- "pc";
      Read epoch : Bool <- "fEpoch";
      Call instRq(STRUCT { "write" ::= $$false;
                           "addr" ::= toIAddr _ pc;
                           "datain" ::= $$Default });
      Write "pcUpdated" <- $$false;
      Retv

    with Rule "instFetchRs" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Read pcUpdated <- "pcUpdated";
      Assert !#pcUpdated;
      Call inst <- instRs();
      Read pc : Pc addrSize <- "pc";
      (* Predict a next pc using BTB *)
      Call predPc <- predictPc(#pc);
      Read epoch <- "fEpoch";
      Call f2dEnq(f2dPack #inst #pc #predPc #epoch);
      Write "pc" <- #predPc;
      Retv

    with Rule "instFetchRsIgnore" :=
      Read pinit <- "pinit";
      Assert #pinit;
      Read pcUpdated <- "pcUpdated";
      Assert #pcUpdated;
      Call instRs();
      Write "pcUpdated" <- $$false;
      Retv
  }.

  Definition fetchICache := (fetcher ++ icache ++ btb)%kami.

End FetchICache.

#[global] Hint Unfold fetcher icache btb fetchICache : ModuleDefs.
#[global] Hint Unfold instRq instRs predictPc trainPc
     f2dEnq f2dDeq W2DStr w2dDeq RqFromProc RsToProc
     memReq memRep: MethDefs.

Section Facts.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variable (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Array Bool dataBytes)) -> (* byteEn *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Lemma fetcher_ModEquiv:
    forall pcInit, ModPhoasWf (fetcher fetch f2dPack pcInit).
  Proof. kequiv. Qed.
  #[local] Hint Resolve fetcher_ModEquiv.

  Lemma fetchICache_ModEquiv:
    forall pcInit,
      ModPhoasWf (fetchICache fetch f2dPack getIndex getTag pcInit).
  Proof.
    kequiv.
  Qed.

End Facts.

#[global] Hint Resolve fetcher_ModEquiv fetchICache_ModEquiv.

