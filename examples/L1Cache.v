Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile.

Set Implicit Arguments.

Section L1Cache.
  Variables IdxBits TagBits LgDataBytes LgNumDatas: nat.
  Variable Id: Kind.
  Definition AddrBits := TagBits + (IdxBits + (LgNumDatas + LgDataBytes)).
  Definition Addr := Bit AddrBits.
  Definition Tag := Bit TagBits.
  Definition Idx := Bit IdxBits.
  Definition Data := Bit (LgDataBytes * 8).
  Definition Offset := Bit LgNumDatas.
  Definition Line := Vector Data LgNumDatas.
 
  Definition RqFromProc := Ex.MemTypes.RqFromProc LgDataBytes Addr Id.
  Definition RsToProc := Ex.MemTypes.RsToProc LgDataBytes Id.
  Definition FromP := Ex.MemTypes.FromP LgDataBytes LgNumDatas Addr Id.
  Definition RqFromP := Ex.MemTypes.RqFromP Addr.
  Definition RsFromP := Ex.MemTypes.RsFromP LgDataBytes LgNumDatas Addr Id.
  Definition RqToP := Ex.MemTypes.RqToP  Addr Id.
  Definition RsToP := Ex.MemTypes.RsToP LgDataBytes LgNumDatas Addr.

  Definition rqFromProcPop := MethodSig "rqFromProc.pop" (Void): RqFromProc.
  Definition fromPPop := MethodSig "fromP.pop" (Void): FromP.

  Definition rsToProcEnq := MethodSig "rsToProc.enq" (RsToProc): Void.
  Definition rqToPEnq := MethodSig "rqToP.enq" (RqToP): Void.
  Definition rsToPEnq := MethodSig "rsToP.enq" (RsToP): Void.

  Definition readLine := MethodSig "line.read" (Idx): Line.
  Definition writeLine := MethodSig "line.write" (WritePort IdxBits Line): Void.
  Definition readTag := MethodSig "tag.read" (Idx): Tag.
  Definition writeTag := MethodSig "tag.write" (WritePort IdxBits Tag): Void.
  Definition readCs := MethodSig "cs.read" (Idx): Msi.
  Definition writeCs := MethodSig "cs.write" (WritePort IdxBits Tag): Void.

  Section UtilFunctions.
    Variable var: Kind -> Type.
    Definition getTag (x: (Addr @ var)%kami): (Tag @ var)%kami :=
      UniBit (TruncLsb TagBits (IdxBits + (LgNumDatas + LgDataBytes))) x.
    Definition getIdx (x: (Addr @ var)%kami): (Idx @ var)%kami :=
      UniBit (TruncLsb IdxBits (LgNumDatas + LgDataBytes)) (UniBit (ZeroExtendTrunc AddrBits (IdxBits + (LgNumDatas + LgDataBytes))) x).
    Definition getOffset (x: (Addr @ var)%kami): (Offset @ var)%kami :=
      UniBit (TruncLsb LgNumDatas LgDataBytes) (UniBit (ZeroExtendTrunc AddrBits (LgNumDatas + LgDataBytes)) x).
  End UtilFunctions.
    
  Definition L1Cache :=
    MODULE {
        Register "procRqValid": Bool <- @ConstBool false
        with Register "procRq": RqFromProc <- Default
        with Register "procRqReplace": Bool <- @ConstBool false
        with Register "procRqWait": Bool <- @ConstBool false

        with Rule "ldHit" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcPop();
          Assert !#rq@."op";
          Call tag <- readTag(getIdx #rq@."addr");
          Call cs <- readCs(getIdx #rq@."addr");  
          Assert ((#cs >= $ Sh) && #tag == getTag #rq@."addr");
          Call line <- readLine(getIdx #rq@."addr");  
          Call rsToProcEnq(STRUCT{"data" ::= #line@[getOffset #rq@."addr"]; "id" ::= #rq@."id"});
          Retv

        with Rule "stHit" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcPop();
          Assert #rq@."op";
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);  
          Assert ((#cs == $ Mod) && #tag == getTag #rq@."addr");
          Call line <- readLine(#idx);
          LET offset <- getOffset #rq@."addr";
          Call rsToProcEnq(STRUCT{"data" ::= #line@[#offset]; "id" ::= #rq@."id"});
          LET updLine <- #line@[#offset <- #rq@."data"];
          Call writeLine(STRUCT{"addr" ::= #idx; "data" ::= #updLine});
          Retv

        with Rule "replacement" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcPop();
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Assert (!(#tag == getTag #rq@."addr"));
          Write "procRqValid" <- $$ true;
          Write "procRqReplace" <- $$ true;
          Write "procRqWait" <- $$ false;
          Retv

        with Rule "haveLine" :=
          Read valid <- "procRqValid";
          Assert !#valid;
          Call rq <- rqFromProcPop();
          LET idx <- getIdx #rq@."addr";
          Call tag <- readTag(#idx);
          Call cs <- readCs(#idx);  
          Assert ((#tag == getTag #rq@."addr") &&
                  ((!#rq@."op" && (#cs < $ Sh)) || (#rq@."op" && (#cs < $ Mod))));
          Write "procRqValid" <- $$ true;
          Write "procRqReplace" <- $$ false;
          Write "procRqWait" <- $$ false;
          Write "procRq" <- rq;
          Retv
      }.
End L1Cache.
