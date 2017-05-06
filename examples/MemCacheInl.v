Require Import Ex.MemCache Kami.Notations Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts.
Require Import Kami.ParametricEquiv Kami.ParametricInline String Kami.ParametricInlineLtac.
Require Import Kami.ParametricSyntax Lib.CommonTactics Lib.Reflection Kami.Tactics List Ex.Names Lib.Indexer Ex.RegFile.
Require Import Ex.L1Cache Ex.MemDir Ex.ChildParent.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.

Ltac simplMod :=
  match goal with
    | m :=
  ?modM: MetaModule |- _ =>
  let mEq := fresh "mEq" in
  let HeqmEq := fresh "HeqmEq" in
  remember m as mEq;
    unfold m in HeqmEq;
    clear m;
    cbv [inlineGenGenDm
           inlineGenSinDm inlineSinSinDm
           getGenGenBody
           getGenSinBody getSinSinBody
           appendGenGenAction appendSinSinAction appendSinGenAction
           convNameRec nameVal nameRec isRep projT1
           
           ChildParent.AddrBits ChildParent.Addr ChildParent.Idx ChildParent.Data
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

           L1Cache.csWrite

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

           Msi.Msi RegFile.Addr StringEq.string_eq StringEq.ascii_eq Bool.eqb andb

           eq_rect ret arg

        ] in HeqmEq;
    rewrite signature_eq in HeqmEq; unfold eq_rect in HeqmEq;
    simpl in HeqmEq;
    match type of HeqmEq with
      | ?sth = ?m => pose m; clear sth HeqmEq
    end
  end.

Ltac ggNoF dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                 ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenGenDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := mts |}; clear m
               end
           end
  end; simplMod.

Ltac ggF dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                 ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenGenDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := preDm ++ sufDm |}; clear m
               end
           end
  end; simplMod.

Ltac gsNoF dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := mts |}; clear m
               end
           end
  end.

Ltac gsF dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                    ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          RepRule strA goodFn getConstK goodFn2
                                          (fun ty =>
                                             inlineGenSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn noDup :: sufR;
                        metaMeths := preDm ++ sufDm |}; clear m
               end
           end
  end; simplMod.

Ltac ssNoF dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          OneRule
                                          (fun ty =>
                                             inlineSinSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn :: sufR;
                        metaMeths := mts |}; clear m
               end
           end
  end; simplMod.

Ltac ssF dm r :=
  match goal with
    | m := {| metaRegs :=?rgs; metaRules := ?rls; metaMeths := ?mts |} |- _ =>
           let dmTriple := find dm (@nil MetaMeth) mts in
           let rTriple := find r (@nil MetaRule) rls in
           match dmTriple with
             | (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
               match rTriple with
                 | (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                   pose
                     {| metaRegs := rgs;
                        metaRules := preR ++
                                          OneRule
                                          (fun ty =>
                                             inlineSinSinDm
                                               (bdr ty)
                                               (nameVal dmn) bdm) rn :: sufR;
                        metaMeths := preDm ++ sufDm |}; clear m
               end
           end
  end; simplMod.

Ltac start_def m := let mod := fresh in pose m as mod; cbv [m] in mod.

Ltac finish_def :=
  match goal with
    | m := ?mod: MetaModule |- _ =>
           cbv [NativeFifo.listEltK NativeFifo.listEnq NativeFifo.listEltT] in m;
             simpl in m; clear -m;
             exact mod
  end.


Ltac start_pf2 m mpf :=
  let mod := fresh in
  let pf1 := fresh in
  let pf2 := fresh in
  pose m as mod;
    pose proof mpf as [pf1 pf2];
    fold mod in pf1, pf2;
    cbv [m] in mod.

Ltac finish_pf :=
  match goal with
    | mRef:
        modFromMeta _
                    <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      (abstract exact (conj mRef mEquiv))
  end.




Ltac simplifyMod :=
  match goal with
    | mRef:
        modFromMeta _
                    <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      unfold m in mRef, mEquiv;
  clear m;
  cbv [inlineGenGenDm
         inlineGenSinDm inlineSinSinDm
         getGenGenBody
         getGenSinBody getSinSinBody
         appendGenGenAction appendSinSinAction appendSinGenAction
         convNameRec nameVal nameRec isRep projT1
         
         ChildParent.AddrBits ChildParent.Addr ChildParent.Idx ChildParent.Data
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

         L1Cache.csWrite

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

         Msi.Msi RegFile.Addr StringEq.string_eq StringEq.ascii_eq Bool.eqb andb

         eq_rect ret arg

      ] in mRef, mEquiv;
  rewrite signature_eq in mRef, mEquiv; unfold eq_rect in mRef, mEquiv;
  simpl in mRef, mEquiv
end;
  match goal with
    | mRef:
        modFromMeta _
                    <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      let newm := fresh in
      pose m as newm;
        fold newm in mRef;
        fold newm in mEquiv
  end.


Ltac noFilt ltac dm r :=
  match goal with
    | mRef:
        modFromMeta _
                    <<== modFromMeta ?m,
        mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
      ltac dm r;
        match goal with
          | m'Ref:
              modFromMeta ?m <<== modFromMeta ?m',
              m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
            apply (traceRefines_trans_elem mRef) in m'Ref; clear mRef;
            let newm := fresh in
            pose m' as newm;
              fold newm in m'Ref;
              fold newm in m'Equiv;
              simpl in newm; clear m mEquiv
        end
  end; simplifyMod.

Ltac ggNoFilt dm r := noFilt inlineGenDmGenRule_NoFilt dm r.
Ltac gsNoFilt dm r := noFilt inlineSinDmGenRule_NoFilt dm r.
Ltac ssNoFilt dm r := noFilt inlineSinDmSinRule_NoFilt dm r.

Ltac ggFilt dm r := noFilt inlineGenDmGenRule_Filt dm r.
Ltac gsFilt dm r := noFilt inlineSinDmGenRule_Filt dm r.
Ltac ssFilt dm r := noFilt inlineSinDmSinRule_Filt dm r.


  





Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas DataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition nmemCacheInl_flat: MetaModule.
  Proof.
    pose (nmemCache IdxBits TagBits LgNumDatas DataBytes Id LgNumChildren) as m;

    cbv [
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
        
          makeMetaModule
          getMetaFromSinNat makeSinModule getMetaFromSin
          sinRegs sinRules sinMeths rulesToRep regsToRep methsToRep
          convSinToGen concatMetaMod app metaRegs
          metaRules metaMeths

          ChildParent.AddrBits ChildParent.Addr ChildParent.Idx ChildParent.Data
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
          L1Cache.lineWrite L1Cache.tagWrite L1Cache.csWrite

          L1Cache.csRead0 L1Cache.csRead1 L1Cache.csRead2
          L1Cache.csRead3 L1Cache.csRead4 L1Cache.csRead5
          L1Cache.csRead6 L1Cache.csRead7 L1Cache.csRead8
          L1Cache.tagRead0 L1Cache.tagRead1 L1Cache.tagRead2
          L1Cache.tagRead3 L1Cache.tagRead4 L1Cache.tagRead5
          L1Cache.tagRead6 L1Cache.tagRead7 L1Cache.tagRead8

          L1Cache.RqFromProc L1Cache.rqFromProcFirst

          MemCache.MIdxBits

          MemDir.AddrBits MemDir.Addr MemDir.Idx MemDir.Data MemDir.Offset MemDir.Line
          MemDir.RqToP MemDir.RqFromC MemDir.RsToP MemDir.RsFromC MemDir.FromP MemDir.ToC
          MemDir.rqFromCPop MemDir.rsFromCPop MemDir.toCEnq MemDir.Dir MemDir.Dirw
          MemDir.lineRead MemDir.lineWrite MemDir.dirWrite MemDir.Child

          MemDir.dirRead0 MemDir.dirRead1 MemDir.dirRead2 MemDir.dirRead3

          MemTypes.MemOp MemTypes.Child MemTypes.Data MemTypes.Line
          MemTypes.RsToP MemTypes.RqFromC MemTypes.RsFromC MemTypes.ToC

          RegFile.regFileM RegFile.regFileS RegFile.regFile

          nfifoRqToP nfifoRsToP nfifoFromP

          String.append

          fullType

          ret arg

          projT1 projT2

          Lib.VectorFacts.Vector_find
      ] in m.
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

    finish_pf.
  Qed.

  Definition nmemCacheInl: MetaModule.
  Proof.
    start_def nmemCacheInl_flat.

    ssF (mline -- read) deferred.
  
    ssF (mcs -- read1) missByState.
    ssF (mcs -- read2) dwnRq.
    ssNoF (mcs -- read0) dwnRs_wait.
    ssF (mcs -- read0) dwnRs_noWait.
    ssF (mcs -- read3) deferred.

    ssNoF (mline -- write) dwnRs_wait.
    ssF (mline -- write) dwnRs_noWait.

    ssNoF (mcs -- write) dwnRs_wait.
    ssNoF (mcs -- write) dwnRs_noWait.
    ssF (mcs -- write) deferred.

    ssNoF (toChild -- enqName) dwnRq.
    ssF (toChild -- enqName) deferred.

    ssNoF (rqFromChild -- firstEltName) missByState.
    ssF (rqFromChild -- firstEltName) dwnRq.
    
    ssF (rqFromChild -- deqName) deferred.

    ssNoF (rsFromChild -- deqName) dwnRs_wait.
    ssF (rsFromChild -- deqName) dwnRs_noWait.

    gsF (rsFromChild -- enqName) rsFromCToPRule.

    gsF (rqFromChild -- enqName) rqFromCToPRule.
    
    gsF (toChild -- deqName) fromPToCRule.

    ggF (cs -- read1) l1MissByState.
    ggF (cs -- read2) l1MissByLine.
    ggF (cs -- read3) l1Hit.
    ggNoF (cs -- read0) writeback.
    ggF (cs -- read4) upgRq.
    ggF (cs -- read0) upgRs.

    ggF (cs -- read5) ld.
    ggF (cs -- read6) st.
    ggF (cs -- read7) drop.
    ggF (cs -- read8) pProcess.

    ggF (tag -- read1) l1MissByState.
    ggF (tag -- read2) l1MissByLine.
    ggF (tag -- read3) l1Hit.
    ggF (tag -- read0) writeback.
    ggF (tag -- read4) upgRq.
    ggF (tag -- read5) ld.
    ggF (tag -- read6) st.
    ggF (tag -- read7) drop.
    ggF (tag -- read8) pProcess.

    ggNoF (line -- read) writeback.
    ggNoF (line -- read) ld.
    ggNoF (line -- read) st.
    ggF (line -- read) pProcess.
    ggNoF (cs -- write) writeback.
    ggNoF (cs -- write) upgRs.
    ggF (cs -- write) pProcess.

    ggF (tag -- write) upgRs.
    ggNoF (line -- write) upgRs.
    ggF (line -- write) st.
    ggNoF (fromParent -- deqName) upgRs.
    ggNoF (fromParent -- deqName) drop.
    ggF (fromParent -- deqName) pProcess.
    ggF (rqToParent -- enqName) upgRq.
    ggNoF (rsToParent -- enqName) writeback.
    ggF (rsToParent -- enqName) pProcess.
    ggF (rqToParent -- deqName) rqFromCToPRule.
    ggF (rsToParent -- deqName) rsFromCToPRule.
    ggF (fromParent -- enqName) fromPToCRule.

    
    finish_def.
  Defined.



  Theorem nmemCacheInl_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            DataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl.
  Proof.
    (* SKIP_PROOF_OFF *)
    start_pf2 nmemCacheInl_flat nmemCacheInl_flat_pf.
  
    ssFilt (mline -- read) deferred.
  
    ssFilt (mcs -- read1) missByState.
    ssFilt (mcs -- read2) dwnRq.
    ssNoFilt (mcs -- read0) dwnRs_wait.
    ssFilt (mcs -- read0) dwnRs_noWait.
    ssFilt (mcs -- read3) deferred.

    ssNoFilt (mline -- write) dwnRs_wait.
    ssFilt (mline -- write) dwnRs_noWait.

    ssNoFilt (mcs -- write) dwnRs_wait.
    ssNoFilt (mcs -- write) dwnRs_noWait.
    ssFilt (mcs -- write) deferred.

    ssNoFilt (toChild -- enqName) dwnRq.
    ssFilt (toChild -- enqName) deferred.

    ssNoFilt (rqFromChild -- firstEltName) missByState.
    ssFilt (rqFromChild -- firstEltName) dwnRq.
    
    ssFilt (rqFromChild -- deqName) deferred.

    ssNoFilt (rsFromChild -- deqName) dwnRs_wait.
    ssFilt (rsFromChild -- deqName) dwnRs_noWait.

    gsFilt (rsFromChild -- enqName) rsFromCToPRule.

    gsFilt (rqFromChild -- enqName) rqFromCToPRule.
    
    gsFilt (toChild -- deqName) fromPToCRule.

    ggFilt (cs -- read1) l1MissByState.
    ggFilt (cs -- read2) l1MissByLine.
    ggFilt (cs -- read3) l1Hit.
    ggNoFilt (cs -- read0) writeback.
    ggFilt (cs -- read4) upgRq.
    ggFilt (cs -- read0) upgRs.

    ggFilt (cs -- read5) ld.
    ggFilt (cs -- read6) st.
    ggFilt (cs -- read7) drop.
    ggFilt (cs -- read8) pProcess.

    ggFilt (tag -- read1) l1MissByState.
    ggFilt (tag -- read2) l1MissByLine.
    ggFilt (tag -- read3) l1Hit.
    ggFilt (tag -- read0) writeback.
    ggFilt (tag -- read4) upgRq.
    ggFilt (tag -- read5) ld.
    ggFilt (tag -- read6) st.
    ggFilt (tag -- read7) drop.
    ggFilt (tag -- read8) pProcess.

    ggNoFilt (line -- read) writeback.
    ggNoFilt (line -- read) ld.
    ggNoFilt (line -- read) st.
    ggFilt (line -- read) pProcess.


    ggNoFilt (cs -- write) writeback.
    ggNoFilt (cs -- write) upgRs.

    ggFilt (cs -- write) pProcess.
    ggFilt (tag -- write) upgRs.
    ggNoFilt (line -- write) upgRs.
    ggFilt (line -- write) st.
    ggNoFilt (fromParent -- deqName) upgRs.
    ggNoFilt (fromParent -- deqName) drop.
    ggFilt (fromParent -- deqName) pProcess.
    ggFilt (rqToParent -- enqName) upgRq.
    ggNoFilt (rsToParent -- enqName) writeback.
    ggFilt (rsToParent -- enqName) pProcess.
    ggFilt (rqToParent -- deqName) rqFromCToPRule.
    ggFilt (rsToParent -- deqName) rsFromCToPRule.
    ggFilt (fromParent -- enqName) fromPToCRule.

    finish_pf.
    (* END_SKIP_PROOF_OFF *)
  Qed.
End MemCacheInl.

Close Scope string.
