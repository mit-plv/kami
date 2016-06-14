Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Notations Lts.Semantics.
Require Import Lts.Equiv Lts.ParametricEquiv Lts.Tactics.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Lts.ParametricSyntax.

Set Implicit Arguments.

Section L1Cache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Definition AddrBits := TagBits + IdxBits + (LgNumDatas + LgDataBytes).
  Definition Addr := Bit AddrBits.
  Definition Tag := Bit TagBits.
  Definition Idx := Bit IdxBits.
  Definition TagIdx := Bit (TagBits + IdxBits).
  Definition Data := Bit (LgDataBytes * 8).
  Definition Offset := Bit LgNumDatas.
  Definition Line := Vector Data LgNumDatas.
 
  Definition RqFromProc := Ex.MemTypes.RqFromProc LgDataBytes Addr.
  Definition RsToProc := Ex.MemTypes.RsToProc LgDataBytes.
  Definition FromP := Ex.MemTypes.FromP LgDataBytes LgNumDatas Addr Id.
  Definition RqFromP := Ex.MemTypes.RqFromP Addr.
  Definition RsFromP := Ex.MemTypes.RsFromP LgDataBytes LgNumDatas Addr Id.
  Definition RqToP := Ex.MemTypes.RqToP Addr Id.
  Definition RsToP := Ex.MemTypes.RsToP LgDataBytes LgNumDatas Addr.

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
      UniBit (TruncLsb (TagBits + IdxBits) (LgNumDatas + LgDataBytes)) x.
    
    Definition getTag (x: (Addr @ var)%kami): (Tag @ var)%kami :=
      UniBit (TruncLsb TagBits IdxBits) (getTagIdx x).

    Definition getIdx (x: (Addr @ var)%kami): (Idx @ var)%kami :=
      UniBit (ZeroExtendTrunc (TagBits + IdxBits) IdxBits) (getTagIdx x).

    Definition getOffset (x: (Addr @ var)%kami): (Offset @ var)%kami :=
      UniBit (TruncLsb LgNumDatas LgDataBytes) (UniBit (ZeroExtendTrunc AddrBits (LgNumDatas + LgDataBytes)) x).
    
    Definition getAddr (tag: (Tag@var)%kami) (idx: (Idx@var)%kami) :=
      BinBit (Concat (TagBits + IdxBits) (LgNumDatas + LgDataBytes))
             (BinBit (Concat TagBits IdxBits) tag idx)
             ($ 0)%kami_expr.
    
  End UtilFunctions.

  Definition l1Cache :=
    SIN {
        Register "procRqValid": Bool <- @ConstBool false
        with Register "procRqReplace": Bool <- @ConstBool false
        with Register "procRqWait": Bool <- @ConstBool false

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
          Retv

        with Rule "writeback" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert #replace;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);
          Call line <- readLine(#idx);
          If !(#cs == $ Inv)
          then (Call rsToPEnq(STRUCT{"addr" ::= getAddr #tag #idx; "to" ::= $ Inv; "line" ::= #line}); Retv)
          else Retv as _;
          Call writeCs(STRUCT{ "addr" ::= #idx; "data" ::= $ Inv});
          Write "procRqReplace" <- $$ false;
          Retv

        with Rule "upgRq" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert !#replace;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq@."addr";
          Call cs <- readCs(#idx);
          LET toS: Msi <- IF #rq@."op" then $ Mod else $ Sh;
          Read wait <- "procRqWait";
          Assert (!#wait && (#cs < #toS));
          Call rqToPEnq(STRUCT{"addr" ::= #rq@."addr"; "from" ::= #cs; "to" ::= #toS; "id" ::= $$ Default});
          Write "procRqWait" <- $$ true;
          Retv

        with Rule "upgRs" :=
          Call fromP <- fromPPop();
          Assert !#fromP@."isRq";
          LET idx <- getIdx #fromP@."addr";
          Call cs <- readCs(#idx);
          Call writeCs(STRUCT{"addr" ::= #idx; "data" ::= #fromP@."to"});
          Write "procRqWait" <- $$ false;
          If #cs == $ Inv then Call writeLine(STRUCT{"addr" ::= #idx; "data" ::= #fromP@."line"}); Retv
                          else Retv as _;
          Retv

        with Rule "ldDeferred" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert !#replace;
          Call rq <- rqFromProcPop();
          Assert !#rq@."op";
          LET idx <- getIdx #rq@."addr";
          Call cs <- readCs(#idx);
          Assert #cs >= $ Sh;
          Call line <- readLine(#idx);
          Write "procRqValid" <- $$ false;
          Call rsToProcEnq(STRUCT {
                               "data" ::= #line@[getOffset #rq@."addr"]
                               (* "id" ::= #rq@."id" *)
                          });
          Retv

        with Rule "stDeferred" :=
          Read valid <- "procRqValid";
          Assert #valid;
          Read replace <- "procRqReplace";
          Assert !#replace;
          Call rq <- rqFromProcPop();
          Assert #rq@."op";
          LET idx <- getIdx #rq@."addr";
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
          Retv

        with Rule "drop" :=
          Call fromP <- fromPPop();
          Assert #fromP@."isRq";
          LET idx <- getIdx #fromP@."addr";
          Call cs <- readCs(#idx);
          Call tag <- readTag(#idx);
          Assert (#cs <= #fromP@."to") || !(#tag == getTag #fromP@."addr");
          Retv

        with Rule "pProcess" :=
          Call fromP <- fromPPop();
          Assert #fromP@."isRq";
          LET idx <- getIdx #fromP@."addr";
          Call cs <- readCs(#idx);
          Call tag <- readTag(#idx);
          Call line <- readLine(#idx);
          Assert (#cs > #fromP@."to") && (#tag == getTag #fromP@."addr");
          Read valid <- "procRqValid";
          Read wait <- "procRqWait";
          Read procRq: RqFromProc <- "procRq";
          Assert !(#valid && !#wait && getTagIdx #procRq@."addr" == getTagIdx #fromP@."addr" &&
                  (#procRq@."op" && #cs == $ Mod || (!#procRq@."op" && #cs == $ Sh)));
          Call rsToPEnq(STRUCT{"addr" ::= #fromP@."addr"; "to" ::= #fromP@."to"; "line" ::= #line});
          Call writeCs(STRUCT{"addr" ::= #idx; "data" ::= #fromP@."to"});
          Retv
      }.
End L1Cache.

Hint Unfold AddrBits Addr Tag Idx TagIdx Data Offset Line : MethDefs.
Hint Unfold RqFromProc RsToProc FromP RqFromP RsFromP RqToP RsToP : MethDefs.
Hint Unfold rqFromProcPop fromPPop rsToProcEnq rqToPEnq rsToPEnq : MethDefs.
Hint Unfold readLine writeLine readTag writeTag readCs writeCs : MethDefs.
Hint Unfold getTagIdx getTag getIdx getOffset getAddr : MethDefs.

Hint Unfold l1Cache : ModuleDefs.

Section Facts.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Lemma l1Cache_ModEquiv n:
    forall ty1 ty2,
      MetaModEquiv ty1 ty2 (getMetaFromSinNat n (l1Cache IdxBits TagBits
                                                         LgNumDatas LgDataBytes Id)).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve l1Cache_ModEquiv.

