Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.ParametricEquiv.
Require Import Kami.Wf Kami.ParametricWf Kami.Tactics.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.Names.

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
        | S m => f ($ m)%kami_expr (foldInc' m)
      end.

  Definition foldInc := foldInc' (wordToNat (wones lgIdx)).
End Fold.

Section Mem.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Definition AddrBits := IdxBits.
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
  
  Definition rqFromCPop := MethodSig (rqFromChild -- deqName) (Void): Struct RqFromC.
  Definition rqFromCFirst := MethodSig (rqFromChild -- firstEltName) (Void): Struct RqFromC.
  Definition rsFromCPop := MethodSig (rsFromChild -- deqName) (Void): Struct RsFromC.

  Definition toCEnq := MethodSig (toChild -- enqName) (Struct ToC): Void.

  Definition Dir := Vector Msi LgNumChildren.
  
  Definition Dirw := Vector Bool LgNumChildren.
  
  Definition lineRead := MethodSig (mline -- read) (Idx): Line.
  Definition lineWrite := MethodSig (mline -- write) (Struct (WritePort IdxBits Line))
                          : Void.
  Definition dirRead := MethodSig (mcs -- read) (Idx): Dir.
  Definition dirWrite := MethodSig (mcs -- write) (Struct (WritePort IdxBits Dir)): Void.

  Definition Child := MemTypes.Child LgNumChildren.
  
  Section UtilFunctions.
    Variable var: Kind -> Type.
    Definition getIdx (x: (Addr @ var)%kami): (Idx @ var)%kami :=
      x.
    
    Definition getOffset (x: (Addr @ var)%kami): (Offset @ var)%kami :=
      UniBit (ZeroExtendTrunc AddrBits LgNumDatas) x.
    
    Definition getAddr (idx: (Idx@var)%kami) :=
      BinBit (Concat IdxBits LgNumDatas) idx ($ 0)%kami_expr.

    Definition othersCompat (c: (Child@var)%kami) (x: (Msi@var)%kami) (dir: (Dir@var)%kami) :=
      foldInc (fun idx old =>
                 IF !(c == idx)
                 then isCompat x (dir@[idx])%kami && old
                 else old)%kami_expr ($$ true)%kami_expr.

    Definition findIncompat (c: (Child@var)%kami) (x: (Msi@var)%kami)
               (dir: (Dir@var)%kami) (dirw: (Dirw@var)%kami):
      ((Struct (Maybe Child))@var)%kami :=
      foldInc (fun idx (old: ((Struct (Maybe Child)) @ var)%kami) =>
                 IF !old!(Maybe Child)@.isValid && !(c == idx) && !(isCompat x (dir@[idx])%kami) && !(dirw@[idx])%kami
                 then STRUCT{isValid ::= $$ true ; value ::= idx}
               else old)%kami_expr
              (STRUCT{isValid ::= $$ false; value ::= $$ Default})%kami_expr.
    
  End UtilFunctions.

  Definition dirwInit: ConstT Dirw := ConstVector (replicate (@ConstBool false) _).

  Definition memDir :=
    META {
        Register cRqValidReg: Bool <- false
        with Register cRqDirwReg: Dirw <- dirwInit
        with Register cRqReg: Struct RqFromC <- Default

        with Rule missByState :=
          Read valid <- cRqValidReg;
          Assert !#valid;
          Call rqChild <- rqFromCFirst();
          LET c <- #rqChild!RqFromC@.child;
          LET rqT: Struct RqToP <- #rqChild!RqFromC@.rq;
          LET idx <- getIdx (#rqT!RqToP@.addr);
          Call dir <- dirRead(#idx);
          Assert (#dir@[#c] <= #rqT!RqToP@.from);
          Write cRqValidReg <- $$ true;
          LET dirw: Dirw <- VEC (replicate ($$ false) _);
          Write cRqDirwReg <- #dirw;
          Write cRqReg <- #rqChild;
          Retv

        with Rule dwnRq :=
          Read valid <- cRqValidReg;
          Assert #valid;
          Call rqChild <- rqFromCFirst();
          LET c <- #rqChild!RqFromC@.child;
          LET rqT: Struct RqToP <- #rqChild!RqFromC@.rq;
          Call dir <- dirRead(getIdx #rqT!RqToP@.addr);
          Read dirw <- cRqDirwReg;
          LET i <- findIncompat #c #rqT!RqToP@.to #dir #dirw;
          Assert #i!(Maybe Child)@.isValid;
          LET rq': Struct FromP <- STRUCT{isRq ::= $$ true; addr ::= #rqT!RqToP@.addr; to ::= toCompat #rqT!RqToP@.to; line ::= $$ Default; id ::= $$ Default};
          Call toCEnq(STRUCT{child ::= #c; msg ::= #rq'});
          LET dirw' <- #dirw@[#c <- $$ true];
          Write cRqDirwReg <- #dirw';
          Retv

        with Rule dwnRs_wait :=
          Call rsChild <- rsFromCPop();
          LET c <- #rsChild!RsFromC@.child;
          LET rs: Struct RsToP <- #rsChild!RsFromC@.rs;
          LET idx <- getIdx #rs!RsToP@.addr;
          Call dir <- dirRead(#idx);
          LET dir' <- #dir@[#c <- #rs!RsToP@.to];
          Call dirWrite(STRUCT{addr ::= #idx; data ::= #dir'});
          If #dir@[#c] == $ Mod
          then Call lineWrite(STRUCT{addr ::= #idx; data ::= #rs!RsToP@.line}); Retv
          else Retv as _;
          Read rqChild: Struct RqFromC <- cRqReg;
          LET rq: Struct RqToP <- #rqChild!RqFromC@.rq;
          Read valid <- cRqValidReg;
          Assert #valid && #rq!RqToP@.addr == #rs!RsToP@.addr;
          Read dirw <- cRqDirwReg;
          LET dirw' <- #dirw@[#c <- $$ false];
          Write cRqDirwReg <- #dirw';
          Retv

        with Rule dwnRs_noWait :=
          Call rsChild <- rsFromCPop();
          LET c <- #rsChild!RsFromC@.child;
          LET rs: Struct RsToP <- #rsChild!RsFromC@.rs;
          LET idx <- getIdx #rs!RsToP@.addr;
          Call dir <- dirRead(#idx);
          LET dir' <- #dir@[#c <- #rs!RsToP@.to];
          Call dirWrite(STRUCT{addr ::= #idx; data ::= #dir'});
          If #dir@[#c] == $ Mod
          then Call lineWrite(STRUCT{addr ::= #idx; data ::= #rs!RsToP@.line}); Retv
          else Retv as _;
          Read rqChild: Struct RqFromC <- cRqReg;
          LET rq: Struct RqToP <- #rqChild!RqFromC@.rq;
          Read valid <- cRqValidReg;
          Assert !(#valid && #rq!RqToP@.addr == #rs!RsToP@.addr);
          Retv
            
        with Rule deferred :=
          Read valid <- cRqValidReg;
          Assert #valid;
          Call rqChild <- rqFromCPop();
          LET c <- #rqChild!RqFromC@.child;
          LET rq: Struct RqToP <- #rqChild!RqFromC@.rq;
          LET idx <- getIdx (#rq!RqToP@.addr);
          Call dir <- dirRead(#idx);
          Assert #dir@[#c] <= #rq!RqToP@.from;
          Assert (othersCompat #c #rq!RqToP@.to #dir);
          Call lineT <- lineRead(#idx);
          LET rs: Struct FromP <-
                        STRUCT{isRq ::= $$ false; addr ::= #rq!RqToP@.addr; to ::= #rq!RqToP@.to; line ::= #lineT; id ::= #rq!RqToP@.id};
          Call toCEnq(STRUCT{child ::= #c; msg ::= #rs});
          LET dir' <- #dir@[#c <- #rq!RqToP@.to];
          Call dirWrite(STRUCT{addr ::= #idx; data ::= #dir'});
          Write cRqValidReg <- $$ false;
          Retv
      }.
End Mem.

Hint Unfold AddrBits Addr Idx Data Offset Line : MethDefs.
Hint Unfold RqToP RqFromC RsToP RsFromC FromP ToC : MethDefs.
Hint Unfold rqFromCPop rsFromCPop toCEnq Dir Dirw : MethDefs.
Hint Unfold lineRead lineWrite dirRead dirWrite Child : MethDefs.
Hint Unfold getIdx getOffset getAddr othersCompat findIncompat dirwInit : MethDefs.

Hint Unfold memDir : ModuleDefs.

Section Facts.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Lemma memDir_ModEquiv:
    MetaModPhoasWf (memDir IdxBits LgNumDatas LgDataBytes LgNumChildren Id).
  Proof. (* SKIP_PROOF_ON
    kequiv.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma memDir_ValidRegs:
    MetaModRegsWf (memDir IdxBits LgNumDatas LgDataBytes LgNumChildren Id).
  Proof. (* SKIP_PROOF_ON
    kvr.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End Facts.

Hint Resolve memDir_ModEquiv memDir_ValidRegs.

