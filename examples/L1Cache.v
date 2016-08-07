Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Notations Lts.Semantics.
Require Import Lts.ParametricEquiv Lts.Wf Lts.ParametricWf Lts.Tactics.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Lts.ParametricSyntax.

Set Implicit Arguments.

Section L1Cache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Definition AddrBits := TagBits + IdxBits + LgNumDatas.
  Definition Addr := Bit AddrBits.
  Definition Tag := Bit TagBits.
  Definition Idx := Bit IdxBits.
  Definition TagIdx := Bit (TagBits + IdxBits).
  Definition Data := Bit (LgDataBytes * 8).
  Definition Offset := Bit LgNumDatas.
  Definition Line := Vector Data LgNumDatas.
 
  Definition RqFromProc := Ex.MemTypes.RqFromProc LgDataBytes Addr.
  Definition RsToProc := Ex.MemTypes.RsToProc LgDataBytes.
  Definition FromP := Ex.MemTypes.FromP LgDataBytes LgNumDatas TagIdx Id.
  Definition RqFromP := Ex.MemTypes.RqFromP TagIdx.
  Definition RsFromP := Ex.MemTypes.RsFromP LgDataBytes LgNumDatas TagIdx Id.
  Definition RqToP := Ex.MemTypes.RqToP TagIdx Id.
  Definition RsToP := Ex.MemTypes.RsToP LgDataBytes LgNumDatas TagIdx.

  Definition rqFromProcPop := MethodSig "rqFromProc"--"deq" (Void): RqFromProc.
  Definition rqFromProcFirst := MethodSig "rqFromProc"--"firstElt" (Void): RqFromProc.
  Definition fromPPop := MethodSig "fromParent"--"deq" (Void): FromP.

  Definition rsToProcEnq := MethodSig "rsToProc"--"enq" (RsToProc): Void.
  Definition rqToPEnq := MethodSig "rqToParent"--"enq" (RqToP): Void.
  Definition rsToPEnq := MethodSig "rsToParent"--"enq" (RsToP): Void.

  Definition readLine := MethodSig "line"--"read" (Idx): Line.
  Definition writeLine := MethodSig "line"--"write" (WritePort IdxBits Line): Void.
  Definition readTag := MethodSig "tag"--"read" (Idx): Tag.
  Definition writeTag := MethodSig "tag"--"write" (WritePort IdxBits Tag): Void.
  Definition readCs := MethodSig "cs"--"read" (Idx): Msi.
  Definition writeCs := MethodSig "cs"--"write" (WritePort IdxBits Msi): Void.

  Section UtilFunctions.
    Variable var: Kind -> Type.
    Definition getTagIdx (x: (Addr @ var)%kami): (TagIdx @ var)%kami :=
      UniBit (TruncLsb (TagBits + IdxBits) LgNumDatas) x.
    
    Definition getTag (x: (Addr @ var)%kami): (Tag @ var)%kami :=
      UniBit (TruncLsb TagBits IdxBits) (getTagIdx x).

    Definition getIdx (x: (Addr @ var)%kami): (Idx @ var)%kami :=
      UniBit (Trunc TagBits IdxBits) (getTagIdx x).

    Definition getOffset (x: (Addr @ var)%kami): (Offset @ var)%kami :=
      UniBit (Trunc (TagBits + IdxBits) LgNumDatas) x.
    
    Definition makeTagIdx (tag: (Tag@var)%kami) (idx: (Idx@var)%kami) :=
      BinBit (Concat TagBits IdxBits) tag idx.

    Definition getIdxFromTagIdx (x: (TagIdx @var)%kami): (Idx @ var)%kami :=
      UniBit (Trunc TagBits IdxBits) x.
      
    Definition getTagFromTagIdx (x: (TagIdx @var)%kami): (Tag @ var)%kami :=
      UniBit (TruncLsb TagBits IdxBits) x.
      

  End UtilFunctions.

  Definition l1Cache :=
    SIN {
        Register "procRqValid": Bool <- @ConstBool false
        with Register "procRqReplace": Bool <- @ConstBool false
        with Register "procRqWait": Bool <- @ConstBool false
        with Register "procRq": RqFromProc <- Default

        (*                                 
        with Rule "ldHit" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcPop();
          Assert !#rq@."op";
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);
          Assert ((#cs >= $ Sh) && #tag == getTag #rq@."addr");
          Call line <- readLine(#idx);
          Call rsToProcEnq(STRUCT {
                               "data" ::= #line@[getOffset #rq@."addr"]
                               (* "id" ::= #rq@."id" *)
                          });
          Retv

        with Rule "stHit" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcPop();
          Assert #rq@."op";
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);
          Assert (#cs == $ Mod && #tag == getTag #rq@."addr");
          Call line <- readLine(#idx);
          LET offset <- getOffset #rq@."addr";
          Call rsToProcEnq(STRUCT {
                               "data" ::= $$Default
                               (* "id" ::= #rq@."id" *)
                          });
          LET updLine <- #line@[#offset <- #rq@."data"];
          Call writeLine(STRUCT{"addr" ::= #idx; "data" ::= #updLine});
          Retv
        *)

        with Rule "l1MissByState" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);
          Assert (#tag == getTag #rq@."addr" && #cs == $ Sh && #rq@."op");
          Write "procRqValid" <- $$ true;
          Write "procRqReplace" <- $$ false;
          Write "procRqWait" <- $$ false;
          Write "procRq" <- #rq;
          Retv

        with Rule "l1MissByLine" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);
          Assert (!(#tag == getTag #rq@."addr") || #cs == $ Inv);
          Write "procRqValid" <- $$ true;
          Write "procRqReplace" <- $$ true;
          Write "procRqWait" <- $$ false;
          Write "procRq" <- #rq;
          Retv

        with Rule "l1Hit" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);
          Assert ((#tag == getTag #rq@."addr") &&
                  (#cs == $ Sh && !#rq@."op" || #cs == $ Mod && #rq@."op"));
          Write "procRqValid" <- $$ true;
          Write "procRqReplace" <- $$ false;
          Write "procRqWait" <- $$ false;
          Write "procRq" <- #rq;
          Retv


        with Rule "writeback" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert #replace;
          Read rq: RqFromProc <- "procRq";
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);
          Call line <- readLine(#idx);
          If !(#cs == $ Inv)
          then (Call rsToPEnq(STRUCT{"addr" ::= makeTagIdx #tag #idx; "to" ::= $ Inv; "line" ::= #line; "isVol" ::= $$ true}); Retv)
          else Retv as _;
          Call writeCs(STRUCT{ "addr" ::= #idx; "data" ::= $ Inv});
          Write "procRqReplace" <- $$ false;
          Retv

        with Rule "upgRq" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert !#replace;
          Read rq: RqFromProc <- "procRq";
          LET idx <- getIdx #rq@."addr";
          Call cs <- readCs(#idx);
          LET toS: Msi <- IF #rq@."op" then $ Mod else $ Sh;
          Read wait <- "procRqWait";
          Call tag <- readTag(#idx);
          Assert (!#wait && (#cs == $ Msi.Inv ||
                                      ((#tag == getTag #rq@."addr") && (#cs < #toS))));
          Call rqToPEnq(STRUCT{"addr" ::= getTagIdx #rq@."addr"; "from" ::= #cs; "to" ::= #toS; "id" ::= $$ Default});
          Write "procRqWait" <- $$ true;
          Retv

        with Rule "upgRs" :=
          Call fromP <- fromPPop();
          Assert !#fromP@."isRq";
          LET idx <- getIdxFromTagIdx #fromP@."addr";
          Call cs <- readCs(#idx);
          Call writeCs(STRUCT{"addr" ::= #idx; "data" ::= #fromP@."to"});
          Call writeTag(STRUCT{"addr" ::= #idx; "data" ::= getTagFromTagIdx #fromP@."addr"});
          Write "procRqWait" <- $$ false;
          If #cs == $ Inv then Call writeLine(STRUCT{"addr" ::= #idx; "data" ::= #fromP@."line"}); Retv
                          else Retv as _;
          Retv

        with Rule "ld" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert !#replace;
          Read rq: RqFromProc <- "procRq";
          Assert !#rq@."op";
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Assert #tag == getTag (#rq@."addr");
          Call cs <- readCs(#idx);
          Assert #cs >= $ Sh;
          Call line <- readLine(#idx);
          Write "procRqValid" <- $$ false;
          Call rsToProcEnq(STRUCT {
                               "data" ::= #line@[getOffset #rq@."addr"]
                               (* "id" ::= #rq@."id" *)
                          });
          Call rq' <- rqFromProcPop();
          Assert #rq == #rq';
          Retv

        with Rule "st" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert !#replace;
          Read rq: RqFromProc <- "procRq";
          Assert #rq@."op";
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Assert #tag == getTag (#rq@."addr");
          Call cs <- readCs(#idx);
          Assert #cs == $ Mod;
          Call line <- readLine(#idx);
          Write "procRqValid" <- $$ false;
          LET offset <- getOffset #rq@."addr";
          Call rsToProcEnq(STRUCT {
                               "data" ::= $$Default
                               (* "id" ::= #rq@."id" *)
                          });
          Call writeLine(STRUCT{"addr" ::= #idx; "data" ::= #line@[#offset <- #rq@."data"]});
          Call rq' <- rqFromProcPop();
          Assert #rq == #rq';
          Retv

        with Rule "drop" :=
          Call fromP <- fromPPop();
          Assert #fromP@."isRq";
          LET idx <- getIdxFromTagIdx #fromP@."addr";
          Call cs <- readCs(#idx);
          Call tag <- readTag(#idx);
          Assert (#cs <= #fromP@."to") || !(#tag == getTagFromTagIdx #fromP@."addr");
          Retv

        with Rule "pProcess" :=
          Call fromP <- fromPPop();
          Assert #fromP@."isRq";
          LET idx <- getIdxFromTagIdx #fromP@."addr";
          Call cs <- readCs(#idx);
          Call tag <- readTag(#idx);
          Call line <- readLine(#idx);
          Assert (#cs > #fromP@."to") && (#tag == getTagFromTagIdx #fromP@."addr");
          Read valid <- "procRqValid";
          Read wait <- "procRqWait";
          Read procRq: RqFromProc <- "procRq";
          Assert !(#valid && !#wait && getTagIdx #procRq@."addr" == #fromP@."addr" &&
                  (#procRq@."op" && #cs == $ Mod || (!#procRq@."op" && #cs == $ Sh)));
          Call rsToPEnq(STRUCT{"addr" ::= #fromP@."addr"; "to" ::= #fromP@."to"; "line" ::= #line; "isVol" ::= $$ false});
          Call writeCs(STRUCT{"addr" ::= #idx; "data" ::= #fromP@."to"});
          Retv
      }.
End L1Cache.

Hint Unfold AddrBits Addr Tag Idx TagIdx Data Offset Line : MethDefs.
Hint Unfold RqFromProc RsToProc FromP RqFromP RsFromP RqToP RsToP : MethDefs.
Hint Unfold rqFromProcPop fromPPop rsToProcEnq rqToPEnq rsToPEnq : MethDefs.
Hint Unfold readLine writeLine readTag writeTag readCs writeCs : MethDefs.
Hint Unfold getTagIdx getTag getIdx getOffset makeTagIdx : MethDefs.

Hint Unfold l1Cache : ModuleDefs.

Section Facts.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable n: nat.

  Lemma l1Cache_ModEquiv:
    forall ty1 ty2,
      MetaModEquiv ty1 ty2 (getMetaFromSinNat n (l1Cache IdxBits TagBits
                                                         LgNumDatas LgDataBytes Id)).
  Proof. (* SKIP_PROOF_ON
    kequiv.
    END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma l1Cache_ValidRegs:
    forall ty,
      ValidRegsMetaModule ty (getMetaFromSinNat n (l1Cache IdxBits TagBits
                                                           LgNumDatas LgDataBytes Id)).
  Proof. (* SKIP_PROOF_ON
    kvr.
    END_SKIP_PROOF_ON *) admit.
  Qed.

End Facts.

Hint Resolve l1Cache_ModEquiv l1Cache_ValidRegs.

