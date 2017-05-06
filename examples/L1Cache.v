Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.ParametricEquiv Kami.Wf Kami.ParametricWf Kami.Tactics.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Kami.ParametricSyntax Ex.Names.

Set Implicit Arguments.

Section L1Cache.
  Variables IdxBits TagBits LgNumDatas DataBytes: nat.
  Variable Id: Kind.

  Definition AddrBits := LgNumDatas + (IdxBits + TagBits).
  Definition Addr := Bit AddrBits.
  Definition Tag := Bit TagBits.
  Definition Idx := Bit IdxBits.
  Definition TagIdx := Bit (IdxBits + TagBits).
  Definition Data := Bit (DataBytes * 8).
  Definition Offset := Bit LgNumDatas.
  Definition Line := Vector Data LgNumDatas.
 
  Definition RqFromProc := Ex.MemTypes.RqFromProc DataBytes Addr.
  Definition RsToProc := Ex.MemTypes.RsToProc DataBytes.
  Definition FromP := Ex.MemTypes.FromP DataBytes LgNumDatas TagIdx Id.
  Definition RqFromP := Ex.MemTypes.RqFromP TagIdx.
  Definition RsFromP := Ex.MemTypes.RsFromP DataBytes LgNumDatas TagIdx Id.
  Definition RqToP := Ex.MemTypes.RqToP TagIdx Id.
  Definition RsToP := Ex.MemTypes.RsToP DataBytes LgNumDatas TagIdx.

  Definition rqFromProcPop := MethodSig (rqFromProc -- deqName) (Void): Struct RqFromProc.
  Definition rqFromProcFirst := MethodSig (rqFromProc -- firstEltName) (Void):
                                  Struct RqFromProc.
  Definition fromPPop := MethodSig (fromParent -- deqName) (Void): Struct FromP.

  Definition rsToProcEnq := MethodSig (rsToProc -- enqName) (Struct RsToProc): Void.
  Definition rqToPEnq := MethodSig (rqToParent -- enqName) (Struct RqToP): Void.
  Definition rsToPEnq := MethodSig (rsToParent -- enqName) (Struct RsToP): Void.

  Definition lineRead := MethodSig (line -- read) (Idx): Line.
  Definition lineWrite := MethodSig (line -- write) (Struct (WritePort IdxBits Line)): Void.
  Definition tagRead0 := MethodSig (tag -- read0) (Idx): Tag.
  Definition tagRead1 := MethodSig (tag -- read1) (Idx): Tag.
  Definition tagRead2 := MethodSig (tag -- read2) (Idx): Tag.
  Definition tagRead3 := MethodSig (tag -- read3) (Idx): Tag.
  Definition tagRead4 := MethodSig (tag -- read4) (Idx): Tag.
  Definition tagRead5 := MethodSig (tag -- read5) (Idx): Tag.
  Definition tagRead6 := MethodSig (tag -- read6) (Idx): Tag.
  Definition tagRead7 := MethodSig (tag -- read7) (Idx): Tag.
  Definition tagRead8 := MethodSig (tag -- read8) (Idx): Tag.
  Definition tagWrite := MethodSig (tag -- write) (Struct (WritePort IdxBits Tag)): Void.
  Definition csRead0 := MethodSig (cs -- read0) (Idx): Msi.
  Definition csRead1 := MethodSig (cs -- read1) (Idx): Msi.
  Definition csRead2 := MethodSig (cs -- read2) (Idx): Msi.
  Definition csRead3 := MethodSig (cs -- read3) (Idx): Msi.
  Definition csRead4 := MethodSig (cs -- read4) (Idx): Msi.
  Definition csRead5 := MethodSig (cs -- read5) (Idx): Msi.
  Definition csRead6 := MethodSig (cs -- read6) (Idx): Msi.
  Definition csRead7 := MethodSig (cs -- read7) (Idx): Msi.
  Definition csRead8 := MethodSig (cs -- read8) (Idx): Msi.
  Definition csWrite := MethodSig (cs --write) (Struct (WritePort IdxBits Msi)): Void.


  
  Section UtilFunctions.
    Variable var: Kind -> Type.
    Definition getTagIdx (x: (Addr @ var)%kami): (TagIdx @ var)%kami :=
      UniBit (TruncLsb LgNumDatas (IdxBits + TagBits)) x.
    
    Definition getTag (x: (Addr @ var)%kami): (Tag @ var)%kami :=
      UniBit (TruncLsb IdxBits TagBits) (getTagIdx x).

    Definition getIdx (x: (Addr @ var)%kami): (Idx @ var)%kami :=
      UniBit (Trunc IdxBits TagBits) (getTagIdx x).

    Definition getOffset (x: (Addr @ var)%kami): (Offset @ var)%kami :=
      UniBit (Trunc LgNumDatas (IdxBits + TagBits)) x.
    
    Definition makeTagIdx (tag: (Tag@var)%kami) (idx: (Idx@var)%kami) : (TagIdx @ var)%kami :=
      BinBit (Concat TagBits IdxBits) tag idx.

    Definition getIdxFromTagIdx (x: (TagIdx @var)%kami): (Idx @ var)%kami :=
      UniBit (Trunc IdxBits TagBits) x.
      
    Definition getTagFromTagIdx (x: (TagIdx @var)%kami): (Tag @ var)%kami :=
      UniBit (TruncLsb IdxBits TagBits) x.

  End UtilFunctions.

  Definition l1Cache :=
    SIN {
        Register procRqValidReg: Bool <- false
        with Register procRqReplaceReg: Bool <- false
        with Register procRqWaitReg: Bool <- false
        with Register procRqReg: Struct RqFromProc <- Default

        with Rule l1MissByState :=
          Read valid <- procRqValidReg;
          Assert !#valid;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq!RqFromProc@.addr;
          Call tag <- tagRead1(#idx);
          Call cs <- csRead1(#idx);
          Assert (#tag == getTag #rq!RqFromProc@.addr && #cs == $ Sh && #rq!RqFromProc@.op);
          Write procRqValidReg <- $$ true;
          Write procRqReplaceReg <- $$ false;
          Write procRqWaitReg <- $$ false;
          Write procRqReg <- #rq;
          Retv

        with Rule l1MissByLine :=
          Read valid <- procRqValidReg;
          Assert !#valid;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq!RqFromProc@.addr;
          Call tag <- tagRead2(#idx);
          Call cs <- csRead2(#idx);
          Assert (!(#tag == getTag #rq!RqFromProc@.addr) || #cs == $ Inv);
          Write procRqValidReg <- $$ true;
          Write procRqReplaceReg <- $$ true;
          Write procRqWaitReg <- $$ false;
          Write procRqReg <- #rq;
          Retv
 
                                            
        with Rule l1Hit :=
          Read valid <- procRqValidReg;
          Assert !#valid;
          Call rq <- rqFromProcFirst();
          LET idx <- getIdx #rq!RqFromProc@.addr;
          Call tag <- tagRead3(#idx);
          Call cs <- csRead3(#idx);
          Assert ((#tag == getTag #rq!RqFromProc@.addr) &&
                  ((#cs >= $ Sh) && !#rq!RqFromProc@.op || #cs == $ Mod && #rq!RqFromProc@.op));
          Write procRqValidReg <- $$ true;
          Write procRqReplaceReg <- $$ false;
          Write procRqWaitReg <- $$ false;
          Write procRqReg <- #rq;
          Retv

        with Rule writeback :=
          Read valid <- procRqValidReg;
          Assert #valid;
          Read replace <- procRqReplaceReg;
          Assert #replace;
          Read rq: Struct RqFromProc <- procRqReg;
          LET idx <- getIdx #rq!RqFromProc@.addr;
          Call tag <- tagRead0(#idx);
          Call cs <- csRead0(#idx);
          Call lineT <- lineRead(#idx);
          If !(#cs == $ Inv)
          then (Call rsToPEnq(STRUCT{addr ::= makeTagIdx #tag #idx; to ::= $ Inv; line ::= #lineT; isVol ::= $$ true}); Retv)
          else Retv as _;
          Call csWrite(STRUCT{ addr ::= #idx; data ::= $ Inv});
          Write procRqReplaceReg <- $$ false;
          Retv
                                            
        with Rule upgRq :=
          Read valid <- procRqValidReg;
          Assert #valid;
          Read replace <- procRqReplaceReg;
          Assert !#replace;
          Read rq: Struct RqFromProc <- procRqReg;
          LET idx <- getIdx #rq!RqFromProc@.addr;
          Call cs <- csRead4(#idx);
          LET toS: Msi <- IF #rq!RqFromProc@.op then $ Mod else $ Sh;
          Read wait <- procRqWaitReg;
          Call tag <- tagRead4(#idx);
          Assert (!#wait && (#cs == $ Msi.Inv ||
                                      ((#tag == getTag #rq!RqFromProc@.addr) && (#cs < #toS))));
          Call rqToPEnq(STRUCT{addr ::= getTagIdx #rq!RqFromProc@.addr; from ::= #cs; to ::= #toS; id ::= $$ Default});
          Write procRqWaitReg <- $$ true;
          Retv

        with Rule upgRs :=
          Call fromP <- fromPPop();
          Assert !#fromP!FromP@.isRq;
          LET idx <- getIdxFromTagIdx #fromP!FromP@.addr;
          Call cs <- csRead0(#idx);
          Call csWrite(STRUCT{addr ::= #idx; data ::= #fromP!FromP@.to});
          Call tagWrite(STRUCT{addr ::= #idx; data ::= getTagFromTagIdx #fromP!FromP@.addr});
          Write procRqWaitReg <- $$ false;
          If #cs == $ Inv then Call lineWrite(STRUCT{addr ::= #idx; data ::= #fromP!FromP@.line}); Retv
                          else Retv as _;
          Read valid <- procRqValidReg;
          Assert #valid;                  
          Read wait <- procRqWaitReg;
          Assert #wait;
          Read rq: Struct RqFromProc <- procRqReg;
          Assert #fromP!FromP@.addr == getTagIdx #rq!RqFromProc@.addr;
          Read replace <- procRqReplaceReg;
          Assert !#replace;
          Retv

        with Rule ld :=
          Read valid <- procRqValidReg;
          Assert #valid;
          Read replace <- procRqReplaceReg;
          Assert !#replace;
          Read rq: Struct RqFromProc <- procRqReg;
          Assert !#rq!RqFromProc@.op;
          LET idx <- getIdx #rq!RqFromProc@.addr;
          Call tag <- tagRead5(#idx);
          Assert #tag == getTag (#rq!RqFromProc@.addr);
          Call cs <- csRead5(#idx);
          Assert #cs >= $ Sh;
          Call line <- lineRead(#idx);
          Write procRqValidReg <- $$ false;
          Call rq' <- rqFromProcPop();
          Call rsToProcEnq(STRUCT {
                               data ::= #line@[getOffset #rq!RqFromProc@.addr]
                               (* id ::= #rq@.id *)
                          });
          Assert #rq == #rq';
          Retv

        with Rule st :=
          Read valid <- procRqValidReg;
          Assert #valid;
          Read replace <- procRqReplaceReg;
          Assert !#replace;
          Read rq: Struct RqFromProc <- procRqReg;
          Assert #rq!RqFromProc@.op;
          LET idx <- getIdx #rq!RqFromProc@.addr;
          Call tag <- tagRead6(#idx);
          Assert #tag == getTag (#rq!RqFromProc@.addr);
          Call cs <- csRead6(#idx);
          Assert #cs == $ Mod;
          Call line <- lineRead(#idx);
          Write procRqValidReg <- $$ false;
          LET offset <- getOffset #rq!RqFromProc@.addr;
          Call rq' <- rqFromProcPop();
          Call rsToProcEnq(STRUCT {
                               data ::= $$Default
                               (* id ::= #rq@.id *)
                          });
          Call lineWrite(STRUCT{addr ::= #idx; data ::= #line@[#offset <- #rq!RqFromProc@.data]});
          Assert #rq == #rq';
          Retv

        with Rule drop :=
          Call fromP <- fromPPop();
          Assert #fromP!FromP@.isRq;
          LET idx <- getIdxFromTagIdx #fromP!FromP@.addr;
          Call cs <- csRead7(#idx);
          Call tag <- tagRead7(#idx);
          Assert (#cs <= #fromP!FromP@.to) || !(#tag == getTagFromTagIdx #fromP!FromP@.addr);
          Retv

        with Rule pProcess :=
          Call fromP <- fromPPop();
          Assert #fromP!FromP@.isRq;
          LET idx <- getIdxFromTagIdx #fromP!FromP@.addr;
          Call cs <- csRead8(#idx);
          Call tag <- tagRead8(#idx);
          Call lineT <- lineRead(#idx);
          Assert (#cs > #fromP!FromP@.to) && (#tag == getTagFromTagIdx #fromP!FromP@.addr);
          Read valid <- procRqValidReg;
          Read wait <- procRqWaitReg;
          Read procRq: Struct RqFromProc <- procRqReg;
          Assert !(#valid && !#wait && getTagIdx #procRq!RqFromProc@.addr == #fromP!FromP@.addr &&
                  (#procRq!RqFromProc@.op && #cs == $ Mod || (!#procRq!RqFromProc@.op && #cs == $ Sh)));
          Call rsToPEnq(STRUCT{addr ::= #fromP!FromP@.addr; to ::= #fromP!FromP@.to; line ::= #lineT; isVol ::= $$ false});
          Call csWrite(STRUCT{addr ::= #idx; data ::= #fromP!FromP@.to});
          Retv
      }.
End L1Cache.

Hint Unfold AddrBits Addr Tag Idx TagIdx Data Offset Line : MethDefs.
Hint Unfold RqFromProc RsToProc FromP RqFromP RsFromP RqToP RsToP : MethDefs.
Hint Unfold rqFromProcPop fromPPop rsToProcEnq rqToPEnq rsToPEnq : MethDefs.
Hint Unfold lineRead lineWrite tagRead0 tagRead1 tagRead2 tagRead3 tagRead4
     tagRead5 tagRead6 tagRead7 tagRead8 tagWrite
     csRead0 csRead1 csRead2 csRead3 csRead4 csRead5 csRead6 csRead7 csRead8
     csWrite : MethDefs.
Hint Unfold getTagIdx getTag getIdx getOffset makeTagIdx : MethDefs.

Hint Unfold l1Cache : ModuleDefs.

Section Facts.
  Variables IdxBits TagBits LgNumDatas DataBytes: nat.
  Variable Id: Kind.

  Variable n: nat.

  Lemma l1Cache_ModEquiv:
    MetaModPhoasWf (getMetaFromSinNat n (l1Cache IdxBits TagBits LgNumDatas DataBytes Id)).
  Proof. (* SKIP_PROOF_OFF *)
    kequiv.
    (* END_SKIP_PROOF_OFF *)
  Qed.

  Lemma l1Cache_ValidRegs:
    MetaModRegsWf (getMetaFromSinNat n (l1Cache IdxBits TagBits LgNumDatas DataBytes Id)).
  Proof. (* SKIP_PROOF_OFF *)
    kvr.
    (* END_SKIP_PROOF_OFF *)
  Qed.

End Facts.

Hint Resolve l1Cache_ModEquiv l1Cache_ValidRegs.

