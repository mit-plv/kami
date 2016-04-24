Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Tactics.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile.

Set Implicit Arguments.

Section Fold.
  Variable var: Kind -> Type.
  Variable A: Kind.
  Variable lgIdx: nat.
  Variable f: (((Bit lgIdx)@var)%kami -> (A@var)%kami -> (A@var)%kami).
  Variable init: (A@var)%kami.

  Fixpoint foldInc' n: (A@var)%kami :=
      match n with
        | O => init
        | S m => f ($ m)%kami (foldInc' m)
      end.

  Definition foldInc := foldInc' (wordToNat (wones lgIdx)).
End Fold.

Section Mem.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Definition AddrBits := IdxBits + (LgNumDatas + LgDataBytes).
  Definition Addr := Bit AddrBits.
  Definition Idx := Bit IdxBits.
  Definition Data := Bit (LgDataBytes * 8).
  Definition Offset := Bit LgNumDatas.
  Definition Line := Vector Data LgNumDatas.
 
  Definition RqToP := Ex.MemTypes.RqToP Addr Id.
  Definition RqFromC := Ex.MemTypes.RqFromC LgNumChildren Addr Id.
  Definition RsToP := Ex.MemTypes.RsToP LgDataBytes LgNumDatas Addr.
  Definition RsFromC := Ex.MemTypes.RsFromC LgDataBytes LgNumDatas LgNumChildren Addr.
  Definition FromP := Ex.MemTypes.FromP LgDataBytes LgNumDatas Addr Id.
  Definition ToC := Ex.MemTypes.ToC LgDataBytes LgNumDatas LgNumChildren Addr Id.

  Definition rqFromCPop := MethodSig "rqFromC".."pop" (Void): RqFromC.
  Definition rsFromCPop := MethodSig "rsFromC".."pop" (Void): RsFromC.

  Definition toCEnq := MethodSig "toC".."enq" (ToC): Void.

  Definition Dir := Vector Msi LgNumChildren.
  
  Definition Dirw := Vector Bool LgNumChildren.
  
  Definition readLine := MethodSig "mline".."read" (Idx): Line.
  Definition writeLine := MethodSig "mline".."write" (WritePort IdxBits Line): Void.
  Definition readDir := MethodSig "mcs".."read" (Idx): Dir.
  Definition writeDir := MethodSig "mcs".."write" (WritePort IdxBits Dir): Void.

  Definition Child := MemTypes.Child LgNumChildren.
  
  Section UtilFunctions.
    Variable var: Kind -> Type.
    Definition getIdx (x: (Addr @ var)%kami): (Idx @ var)%kami :=
      UniBit (TruncLsb IdxBits (LgNumDatas + LgDataBytes)) x.
    
    Definition getOffset (x: (Addr @ var)%kami): (Offset @ var)%kami :=
      UniBit (TruncLsb LgNumDatas LgDataBytes) (UniBit (ZeroExtendTrunc AddrBits (LgNumDatas + LgDataBytes)) x).
    
    Definition getAddr (idx: (Idx@var)%kami) :=
      BinBit (Concat IdxBits (LgNumDatas + LgDataBytes)) idx ($ 0)%kami.

    Definition othersCompat (c: (Child@var)%kami) (x: (Msi@var)%kami) (dir: (Dir@var)%kami) :=
      foldInc (fun idx old =>
                 IF !(c == idx)
                 then isCompat x (dir@[idx])%kami && old
                 else old)%kami ($$ true)%kami.

    Definition findIncompat (c: (Child@var)%kami) (x: (Msi@var)%kami)
               (dir: (Dir@var)%kami) (dirw: (Dirw@var)%kami): ((Maybe Child)@var)%kami :=
      foldInc (fun idx (old: ((Maybe Child) @ var)%kami) =>
                 IF !old@."valid" && !(c == idx) && !(isCompat x (dir@[idx])%kami) && !(dirw@[idx])%kami
                 then STRUCT{"valid" ::= $$ true ; "value" ::= idx}
               else old)%kami (STRUCT{"valid" ::= $$ false; "value" ::= $$ Default})%kami.
  End UtilFunctions.

  Definition dirwInit: ConstT Dirw := ConstVector (replicate (@ConstBool false) _).

  Definition memDir :=
    MODULE {
        Register "cRqValid": Bool <- @ConstBool false
        with Register "cRq": RqFromC <- Default
        with Register "cRqDirw": Dirw <- dirwInit

        with Rule "hit" :=
          Read valid <- "cRqValid";
          Assert !#valid;
          Call rqChild <- rqFromCPop();
          LET c <- #rqChild@."child";
          LET rq: SyntaxKind RqToP <- #rqChild@."rq";
          LET idx <- getIdx (#rq@."addr");
          Call dir <- readDir(#idx);
          Assert #dir@[#c] <= #rq@."from";
          Assert (othersCompat #c #rq@."to" #dir);
          Call line <- readLine(#idx);
          LET rs: SyntaxKind FromP <- STRUCT{"isRq" ::= $$ false; "addr" ::= #rq@."addr"; "to" ::= #rq@."to"; "line" ::= #line; "id" ::= #rq@."id"};
          Call toCEnq(STRUCT{"child" ::= #c; "msg" ::= #rs});
          LET dir' <- #dir@[#c <- #rq@."to"];
          Call writeDir(STRUCT{"addr" ::= #idx; "data" ::= #dir'});
          Retv

        with Rule "missByState" :=                
          Read valid <- "cRqValid";
          Assert !#valid;
          Call rqChild <- rqFromCPop();
          LET c <- #rqChild@."child";
          LET rq: SyntaxKind RqToP <- #rqChild@."rq";
          LET idx <- getIdx (#rq@."addr");
          Call dir <- readDir(#idx);
          Assert !((#dir@[#c] <= #rq@."from") && (othersCompat #c #rq@."to" #dir));
          Write "cRqValid" <- $$ true;
          Write "cRq" <- #rqChild;
          LET dirw: SyntaxKind Dirw <- VEC (replicate ($$ false) _);
          Write "cRqDirw" <- #dirw;
          Retv

        with Rule "dwnRq" :=
          Read valid <- "cRqValid";
          Assert #valid;
          Read rqChild: RqFromC <- "cRq";
          LET c <- #rqChild@."child";
          LET rq: SyntaxKind RqToP <- #rqChild@."rq";
          Call dir <- readDir(getIdx #rq@."addr");
          Read dirw <- "cRqDirw";  
          LET i <- findIncompat #c #rq@."to" #dir #dirw;
          Assert #i@."valid";
          LET rq': SyntaxKind FromP <- STRUCT{"isRq" ::= $$ true; "addr" ::= #rq@."addr"; "to" ::= toCompat #rq@."to"; "line" ::= $$ Default; "id" ::= $$ Default};
          Call toCEnq(STRUCT{"child" ::= #c; "msg" ::= #rq'});
          LET dirw' <- #dirw@[#c <- $$ true];
          Write "cRqDirw" <- #dirw';
          Retv

        with Rule "dwnRs" :=
          Call rsChild <- rsFromCPop();
          LET c <- #rsChild@."child";
          LET rs: SyntaxKind RsToP <- #rsChild@."rs";
          LET idx <- getIdx #rs@."addr";
          Call dir <- readDir(#idx);
          LET dir' <- #dir@[#c <- #rs@."to"];
          Call writeDir(STRUCT{"addr" ::= #idx; "data" ::= #dir'});
          Read dirw <- "cRqDirw";
          LET dirw' <- #dirw@[#c <- $$ false];
          Write "cRqDirw" <- #dirw';
          If #dir@[#c] == $ Mod
          then Call writeLine(STRUCT{"addr" ::= #idx; "data" ::= #rs@."line"}); Retv
          else Retv as _;
          Retv

        with Rule "deferred" :=
          Read valid <- "cRqValid";
          Assert #valid;
          Call rqChild <- rqFromCPop();
          LET c <- #rqChild@."child";
          LET rq: SyntaxKind RqToP <- #rqChild@."rq";
          LET idx <- getIdx (#rq@."addr");
          Call dir <- readDir(#idx);
          Assert #dir@[#c] <= #rq@."from";
          Assert (othersCompat #c #rq@."to" #dir);
          Call line <- readLine(#idx);
          LET rs: SyntaxKind FromP <- STRUCT{"isRq" ::= $$ false; "addr" ::= #rq@."addr"; "to" ::= #rq@."to"; "line" ::= #line; "id" ::= #rq@."id"};
          Call toCEnq(STRUCT{"child" ::= #c; "msg" ::= #rs});
          LET dir' <- #dir@[#c <- #rq@."to"];
          Call writeDir(STRUCT{"addr" ::= #idx; "data" ::= #dir'});
          Write "cRqValid" <- $$ false;
          Retv
      }.
End Mem.

Hint Unfold AddrBits Addr Idx Data Offset Line : MethDefs.
Hint Unfold RqToP RqFromC RsToP RsFromC FromP ToC : MethDefs.
Hint Unfold rqFromCPop rsFromCPop toCEnq Dir Dirw : MethDefs.
Hint Unfold readLine writeLine readDir writeDir Child : MethDefs.
Hint Unfold getIdx getOffset getAddr othersCompat findIncompat dirwInit : MethDefs.

Hint Unfold memDir : ModuleDefs.

Section Facts.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Lemma memDir_ModEquiv:
    ModEquiv type typeUT (memDir IdxBits LgNumDatas LgDataBytes LgNumChildren Id).
  Proof.
    admit.
  Qed.

End Facts.

Hint Immediate memDir_ModEquiv.

