Require Import Ex.MemCache Kami.Notations Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts.
Require Import Kami.ParametricEquiv Kami.ParametricInline String Kami.ParametricInlineLtac.
Require Import Kami.ParametricSyntax Lib.CommonTactics Lib.Reflection Kami.Tactics List Ex.Names Lib.Indexer Ex.RegFile.
Require Import Ex.L1Cache Ex.MemDir Ex.ChildParent.

Set Implicit Arguments.
Set Asymmetric Patterns.

Ltac cacheCbv H :=
  cbv
    [ ChildParent.AddrBits ChildParent.Addr ChildParent.Idx ChildParent.Data
      ChildParent.Offset ChildParent.Line
      ChildParent.RqToP ChildParent.RqFromC ChildParent.RsToP ChildParent.RsFromC
      ChildParent.FromP ChildParent.ToC
      ChildParent.rqToPPop ChildParent.rqFromCEnq ChildParent.rsToPPop
      ChildParent.rsFromCEnq ChildParent.toCPop ChildParent.fromPEnq
      
      L1Cache.AddrBits L1Cache.Addr L1Cache.Tag L1Cache.Idx L1Cache.TagIdx
      L1Cache.Data L1Cache.Offset L1Cache.Line L1Cache.RqFromProc
      L1Cache.RsToProc L1Cache.FromP L1Cache.RqFromP L1Cache.RsFromP
      L1Cache.RqToP L1Cache.RsToP L1Cache.rqFromProcPop L1Cache.fromPPop
      L1Cache.rsToProcEnq L1Cache.rqToPEnq L1Cache.rsToPEnq L1Cache.lineRead
      L1Cache.lineWrite L1Cache.tagWrite
      L1Cache.csRead0 L1Cache.csRead1 L1Cache.csRead2
      L1Cache.csRead3 L1Cache.csRead4 L1Cache.csRead5
      L1Cache.csRead6 L1Cache.csRead7 L1Cache.csRead8
      L1Cache.tagRead0 L1Cache.tagRead1 L1Cache.tagRead2
      L1Cache.tagRead3 L1Cache.tagRead4 L1Cache.tagRead5
      L1Cache.tagRead6 L1Cache.tagRead7 L1Cache.tagRead8

      L1Cache.csWrite L1Cache.rqFromProcFirst

      MemCache.MIdxBits

      MemDir.AddrBits MemDir.Addr MemDir.Idx MemDir.Data MemDir.Offset
      MemDir.Line
      MemDir.RqToP MemDir.RqFromC MemDir.RsToP
      MemDir.RsFromC MemDir.FromP MemDir.ToC
      MemDir.rqFromCPop MemDir.rsFromCPop MemDir.toCEnq MemDir.Dir MemDir.Dirw
      MemDir.lineRead MemDir.lineWrite

      MemDir.dirRead0 MemDir.dirRead1 MemDir.dirRead2 MemDir.dirRead3

      MemDir.dirWrite MemDir.Child

      MemTypes.MemOp MemTypes.Child MemTypes.Data MemTypes.Line MemTypes.RqToP
      MemTypes.RsToP MemTypes.RqFromC MemTypes.RsFromC MemTypes.ToC MemTypes.FromP

      Msi.Msi
      RegFile.Addr RegFile.regFileM RegFile.regFileS RegFile.regFile

      ChildParent.childParent

      Fifo.fifo Fifo.simpleFifo
      Fifo.fifoS Fifo.simpleFifoS

      FifoCorrect.fifo FifoCorrect.nfifo

      L1Cache.l1Cache l1 l1cs l1tag l1line l1Cache childParent

      MemCache.memDir MemCache.mline MemCache.mdir MemCache.memDirC MemCache.memCache
      MemCache.nl1C MemCache.nfifoRqFromC MemCache.nfifoRsFromC MemCache.nfifoToC
      MemCache.nchildParentC MemCache.nmemCache

      MemDir.memDir

      NativeFifo.nativeFifo NativeFifo.nativeSimpleFifo NativeFifo.nativeFifoS
      NativeFifo.nativeSimpleFifoS NativeFifo.nativeFifoM
      NativeFifo.nativeSimpleFifoM
      
      nfifoRqToP nfifoRsToP nfifoFromP

      NativeFifo.listEltK NativeFifo.listEnq NativeFifo.listEltT
    ] in H.

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas DataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition nmemCacheInl_flat: MetaModule.
  Proof.
    pose (nmemCache IdxBits TagBits LgNumDatas DataBytes Id LgNumChildren) as m;
      cacheCbv m; commonCbv m.
    simpl in m;
    unfold Lib.VectorFacts.Vector_find in m;
    simpl in m.

    finish_def.
  Defined.

  Theorem nmemCacheInl_flat_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            DataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_flat) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_flat.
  Proof.
    assert (mRef: modFromMeta
                    (nmemCache IdxBits TagBits LgNumDatas DataBytes Id LgNumChildren)
                    <<== modFromMeta nmemCacheInl_flat) by
        (abstract (cbv [nmemCacheInl_flat]; unfold MethsT;
                   rewrite @idElementwiseId; apply traceRefines_refl)).
    assert (mEquiv: forall ty, MetaModEquiv ty typeUT nmemCacheInl_flat)
      by (abstract (cbv [nmemCacheInl_flat];
                    kequiv)).

    finish_ref.
  Qed.

  Local Definition nmemCacheInl': MetaModule.
  Proof.
    start_def nmemCacheInl_flat.

    ssF cacheCbv (mline -- read) deferred.
  
    ssF cacheCbv (mcs -- read1) missByState.
    ssF cacheCbv (mcs -- read2) dwnRq.
    ssNoF cacheCbv (mcs -- read0) dwnRs_wait.
    ssF cacheCbv (mcs -- read0) dwnRs_noWait.
    ssF cacheCbv (mcs -- read3) deferred.

    ssNoF cacheCbv (mline -- write) dwnRs_wait.
    ssF cacheCbv (mline -- write) dwnRs_noWait.

    ssNoF cacheCbv (mcs -- write) dwnRs_wait.
    ssNoF cacheCbv (mcs -- write) dwnRs_noWait.
    ssF cacheCbv (mcs -- write) deferred.

    ssNoF cacheCbv (toChild -- enqName) dwnRq.
    ssF cacheCbv (toChild -- enqName) deferred.

    ssNoF cacheCbv (rqFromChild -- firstEltName) missByState.
    ssF cacheCbv (rqFromChild -- firstEltName) dwnRq.
    
    ssF cacheCbv (rqFromChild -- deqName) deferred.

    ssNoF cacheCbv (rsFromChild -- deqName) dwnRs_wait.
    ssF cacheCbv (rsFromChild -- deqName) dwnRs_noWait.

    gsF cacheCbv (rsFromChild -- enqName) rsFromCToPRule.

    gsF cacheCbv (rqFromChild -- enqName) rqFromCToPRule.
    
    gsF cacheCbv (toChild -- deqName) fromPToCRule.

    ggF cacheCbv (cs -- read1) l1MissByState.
    ggF cacheCbv (cs -- read2) l1MissByLine.
    ggF cacheCbv (cs -- read3) l1Hit.
    ggNoF cacheCbv (cs -- read0) writeback.
    ggF cacheCbv (cs -- read4) upgRq.
    ggF cacheCbv (cs -- read0) upgRs.

    ggF cacheCbv (cs -- read5) ld.
    ggF cacheCbv (cs -- read6) st.
    ggF cacheCbv (cs -- read7) drop.
    ggF cacheCbv (cs -- read8) pProcess.

    ggF cacheCbv (tag -- read1) l1MissByState.
    ggF cacheCbv (tag -- read2) l1MissByLine.
    ggF cacheCbv (tag -- read3) l1Hit.
    ggF cacheCbv (tag -- read0) writeback.
    ggF cacheCbv (tag -- read4) upgRq.
    ggF cacheCbv (tag -- read5) ld.
    ggF cacheCbv (tag -- read6) st.
    ggF cacheCbv (tag -- read7) drop.
    ggF cacheCbv (tag -- read8) pProcess.

    ggNoF cacheCbv (line -- read) writeback.
    ggNoF cacheCbv (line -- read) ld.
    ggNoF cacheCbv (line -- read) st.
    ggF cacheCbv (line -- read) pProcess.
    ggNoF cacheCbv (cs -- write) writeback.
    ggNoF cacheCbv (cs -- write) upgRs.
    ggF cacheCbv (cs -- write) pProcess.

    ggF cacheCbv (tag -- write) upgRs.
    ggNoF cacheCbv (line -- write) upgRs.
    ggF cacheCbv (line -- write) st.
    ggNoF cacheCbv (fromParent -- deqName) upgRs.
    ggNoF cacheCbv (fromParent -- deqName) drop.
    ggF cacheCbv (fromParent -- deqName) pProcess.
    ggF cacheCbv (rqToParent -- enqName) upgRq.
    ggNoF cacheCbv (rsToParent -- enqName) writeback.
    ggF cacheCbv (rsToParent -- enqName) pProcess.
    ggF cacheCbv (rqToParent -- deqName) rqFromCToPRule.
    ggF cacheCbv (rsToParent -- deqName) rsFromCToPRule.
    ggF cacheCbv (fromParent -- enqName) fromPToCRule.

    
    finish_def.
  Defined.

  Definition nmemCacheInl := ltac:(let y := eval cbv [nmemCacheInl'] in
                                   nmemCacheInl' in exact y).


  Theorem nmemCacheInl_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            DataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl.
  Proof.
    (* SKIP_PROOF_ON
    start_ref nmemCacheInl_flat nmemCacheInl_flat_pf.
  
    ssFilt cacheCbv (mline -- read) deferred.
  
    ssFilt cacheCbv (mcs -- read1) missByState.
    ssFilt cacheCbv (mcs -- read2) dwnRq.
    ssNoFilt cacheCbv (mcs -- read0) dwnRs_wait.
    ssFilt cacheCbv (mcs -- read0) dwnRs_noWait.
    ssFilt cacheCbv (mcs -- read3) deferred.

    ssNoFilt cacheCbv (mline -- write) dwnRs_wait.
    ssFilt cacheCbv (mline -- write) dwnRs_noWait.

    ssNoFilt cacheCbv (mcs -- write) dwnRs_wait.
    ssNoFilt cacheCbv (mcs -- write) dwnRs_noWait.
    ssFilt cacheCbv (mcs -- write) deferred.

    ssNoFilt cacheCbv (toChild -- enqName) dwnRq.
    ssFilt cacheCbv (toChild -- enqName) deferred.

    ssNoFilt cacheCbv (rqFromChild -- firstEltName) missByState.
    ssFilt cacheCbv (rqFromChild -- firstEltName) dwnRq.
    
    ssFilt cacheCbv (rqFromChild -- deqName) deferred.

    ssNoFilt cacheCbv (rsFromChild -- deqName) dwnRs_wait.
    ssFilt cacheCbv (rsFromChild -- deqName) dwnRs_noWait.

    gsFilt cacheCbv (rsFromChild -- enqName) rsFromCToPRule.

    gsFilt cacheCbv (rqFromChild -- enqName) rqFromCToPRule.
    
    gsFilt cacheCbv (toChild -- deqName) fromPToCRule.

    ggFilt cacheCbv (cs -- read1) l1MissByState.
    ggFilt cacheCbv (cs -- read2) l1MissByLine.
    ggFilt cacheCbv (cs -- read3) l1Hit.
    ggNoFilt cacheCbv (cs -- read0) writeback.
    ggFilt cacheCbv (cs -- read4) upgRq.
    ggFilt cacheCbv (cs -- read0) upgRs.

    ggFilt cacheCbv (cs -- read5) ld.
    ggFilt cacheCbv (cs -- read6) st.
    ggFilt cacheCbv (cs -- read7) drop.
    ggFilt cacheCbv (cs -- read8) pProcess.

    ggFilt cacheCbv (tag -- read1) l1MissByState.
    ggFilt cacheCbv (tag -- read2) l1MissByLine.
    ggFilt cacheCbv (tag -- read3) l1Hit.
    ggFilt cacheCbv (tag -- read0) writeback.
    ggFilt cacheCbv (tag -- read4) upgRq.
    ggFilt cacheCbv (tag -- read5) ld.
    ggFilt cacheCbv (tag -- read6) st.
    ggFilt cacheCbv (tag -- read7) drop.
    ggFilt cacheCbv (tag -- read8) pProcess.

    ggNoFilt cacheCbv (line -- read) writeback.
    ggNoFilt cacheCbv (line -- read) ld.
    ggNoFilt cacheCbv (line -- read) st.
    ggFilt cacheCbv (line -- read) pProcess.


    ggNoFilt cacheCbv (cs -- write) writeback.
    ggNoFilt cacheCbv (cs -- write) upgRs.

    ggFilt cacheCbv (cs -- write) pProcess.
    ggFilt cacheCbv (tag -- write) upgRs.
    ggNoFilt cacheCbv (line -- write) upgRs.
    ggFilt cacheCbv (line -- write) st.
    ggNoFilt cacheCbv (fromParent -- deqName) upgRs.
    ggNoFilt cacheCbv (fromParent -- deqName) drop.
    ggFilt cacheCbv (fromParent -- deqName) pProcess.
    ggFilt cacheCbv (rqToParent -- enqName) upgRq.
    ggNoFilt cacheCbv (rsToParent -- enqName) writeback.
    ggFilt cacheCbv (rsToParent -- enqName) pProcess.
    ggFilt cacheCbv (rqToParent -- deqName) rqFromCToPRule.
    ggFilt cacheCbv (rsToParent -- deqName) rsFromCToPRule.
    ggFilt cacheCbv (fromParent -- enqName) fromPToCRule.

    END_SKIP_PROOF_ON *) apply cheat.
  Qed.
End MemCacheInl.
