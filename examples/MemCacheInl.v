Require Import Ex.MemCache Kami.Notations Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts.
Require Import Kami.ParametricEquiv Kami.ParametricInline String Kami.ParametricInlineLtac.
Require Import Kami.ParametricSyntax Lib.CommonTactics Lib.Reflection Kami.Tactics List.

Set Implicit Arguments.

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
           L1Cache.rsToProcEnq L1Cache.rqToPEnq L1Cache.rsToPEnq L1Cache.readLine
           L1Cache.writeLine L1Cache.readTag L1Cache.writeTag
           L1Cache.readCs L1Cache.writeCs

           MemCache.MIdxBits

           MemDir.AddrBits MemDir.Addr MemDir.Idx MemDir.Data MemDir.Offset
           MemDir.Line
           MemDir.RqToP MemDir.RqFromC MemDir.RsToP
           MemDir.RsFromC MemDir.FromP MemDir.ToC
           MemDir.rqFromCPop MemDir.rsFromCPop MemDir.toCEnq MemDir.Dir MemDir.Dirw
           MemDir.readLine MemDir.writeLine MemDir.readDir
           MemDir.writeDir MemDir.Child

           MemTypes.MemOp MemTypes.Child MemTypes.Data MemTypes.Line MemTypes.RqToP
           MemTypes.RsToP MemTypes.RqFromC MemTypes.RsFromC MemTypes.ToC MemTypes.FromP

           Msi.Msi RegFile.Addr StringEq.string_eq StringEq.ascii_eq Bool.eqb andb

           eq_rect ret arg Struct.GetAttrType

        ] in HeqmEq;
    rewrite signature_eq in HeqmEq; unfold eq_rect in HeqmEq; simpl in HeqmEq;
    match type of HeqmEq with
      | ?sth = ?m => pose m; clear sth HeqmEq
    end
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
         L1Cache.rsToProcEnq L1Cache.rqToPEnq L1Cache.rsToPEnq L1Cache.readLine
         L1Cache.writeLine L1Cache.readTag L1Cache.writeTag
         L1Cache.readCs L1Cache.writeCs

         MemCache.MIdxBits

         MemDir.AddrBits MemDir.Addr MemDir.Idx MemDir.Data MemDir.Offset
         MemDir.Line
         MemDir.RqToP MemDir.RqFromC MemDir.RsToP
         MemDir.RsFromC MemDir.FromP MemDir.ToC
         MemDir.rqFromCPop MemDir.rsFromCPop MemDir.toCEnq MemDir.Dir MemDir.Dirw
         MemDir.readLine MemDir.writeLine MemDir.readDir
         MemDir.writeDir MemDir.Child

         MemTypes.MemOp MemTypes.Child MemTypes.Data MemTypes.Line MemTypes.RqToP
         MemTypes.RsToP MemTypes.RqFromC MemTypes.RsFromC MemTypes.ToC MemTypes.FromP

         Msi.Msi RegFile.Addr StringEq.string_eq StringEq.ascii_eq Bool.eqb andb

         eq_rect ret arg Struct.GetAttrType

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
             cbv [Indexer.withPrefix Indexer.prefixSymbol] in m;
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





Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition nmemCacheInl_flat: MetaModule.
  Proof.
    pose (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren) as m;

    (*    repeat autounfold with ModuleDefs in m; *)
    
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

          Indexer.withPrefix Indexer.prefixSymbol

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
          L1Cache.rsToProcEnq L1Cache.rqToPEnq L1Cache.rsToPEnq L1Cache.readLine
          L1Cache.writeLine L1Cache.readTag L1Cache.writeTag L1Cache.readCs L1Cache.writeCs

          L1Cache.RqFromProc L1Cache.rqFromProcFirst

          MemCache.MIdxBits

          MemDir.AddrBits MemDir.Addr MemDir.Idx MemDir.Data MemDir.Offset MemDir.Line
          MemDir.RqToP MemDir.RqFromC MemDir.RsToP MemDir.RsFromC MemDir.FromP MemDir.ToC
          MemDir.rqFromCPop MemDir.rsFromCPop MemDir.toCEnq MemDir.Dir MemDir.Dirw
          MemDir.readLine MemDir.writeLine MemDir.readDir MemDir.writeDir MemDir.Child

          MemTypes.MemOp MemTypes.Child MemTypes.Data MemTypes.Line
          MemTypes.RsToP MemTypes.RqFromC MemTypes.RsFromC MemTypes.ToC

          RegFile.regFileM RegFile.regFileS RegFile.regFile

          nfifoRqToP nfifoRsToP nfifoFromP

          String.append

          fullType

          ret arg

          projT1 projT2

          (*
          Struct.attrName Struct.attrType

          
          getDefaultConst
          makeConst

          RegFile.DataArray Msi.Msi

          getDefaultConstBit

          MemTypes.RqToP MemTypes.RsToProc MemTypes.FromP
          Void

          NativeFifo.nativeEnqS
          MemTypes.RqFromProc

          NativeFifo.listEltK
          NativeFifo.nativeDeqS
          NativeFifo.nativeFirstEltS
           *)
      ] in m;
    simpl in m.

    finish_def.
  Defined.

  Theorem nmemCacheInl_flat_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_flat) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_flat.
  Proof.
    (* SKIP_PROOF_ON
    assert (mRef: modFromMeta
                    (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren)
                    <<== modFromMeta nmemCacheInl_flat) by
        (abstract (cbv [nmemCacheInl_flat]; unfold MethsT;
                   rewrite @idElementwiseId; apply traceRefines_refl)).
    assert (mEquiv: forall ty, MetaModEquiv ty typeUT nmemCacheInl_flat)
      by (abstract (cbv [nmemCacheInl_flat];
                    kequiv)).

    finish_pf.
        END_SKIP_PROOF_ON *) admit.

  Qed.

  Definition nmemCacheInl_1: MetaModule.
  Proof.
    start_def nmemCacheInl_flat.

    ssF "read.mline" "deferred".
  
    ssNoF "read.mcs" "missByState".
    ssNoF "read.mcs" "dwnRq".
    ssNoF "read.mcs" "dwnRs_wait".
    ssNoF "read.mcs" "dwnRs_noWait".
    ssF "read.mcs" "deferred".

    ssNoF "write.mline" "dwnRs_wait".
    ssF "write.mline" "dwnRs_noWait".

    ssNoF "write.mcs" "dwnRs_wait".
    ssNoF "write.mcs" "dwnRs_noWait".
    ssF "write.mcs" "deferred".

    finish_def.
  Defined.

  Theorem nmemCacheInl_1_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_1) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_1.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_flat nmemCacheInl_flat_pf.
    
    ssFilt "read.mline" "deferred".
  
    ssNoFilt "read.mcs" "missByState".
    ssNoFilt "read.mcs" "dwnRq".
    ssNoFilt "read.mcs" "dwnRs_wait".
    ssNoFilt "read.mcs" "dwnRs_noWait".
    ssFilt "read.mcs" "deferred".

    ssNoFilt "write.mline" "dwnRs_wait".
    ssFilt "write.mline" "dwnRs_noWait".

    ssNoFilt "write.mcs" "dwnRs_wait".
    ssNoFilt "write.mcs" "dwnRs_noWait".
    ssFilt "write.mcs" "deferred".

    finish_pf.
       END_SKIP_PROOF_ON *) admit.
  Qed.

  Definition nmemCacheInl_2: MetaModule.
  Proof.

    start_def nmemCacheInl_1.
    ssNoF "enq.toChild" "dwnRq".
    ssF "enq.toChild" "deferred".

    ssNoF "firstElt.rqFromChild" "missByState".
    ssF "firstElt.rqFromChild" "dwnRq".
    
    ssF "deq.rqFromChild" "deferred".

    ssNoF "deq.rsFromChild" "dwnRs_wait".
    ssF "deq.rsFromChild" "dwnRs_noWait".

    finish_def.
  Defined.

  Theorem nmemCacheInl_2_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_2) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_2.
  Proof.
    (* SKIP_PROOF_ON

    start_pf2 nmemCacheInl_1 nmemCacheInl_1_pf.
    
    ssNoFilt "enq.toChild" "dwnRq".
    ssFilt "enq.toChild" "deferred".

    ssNoFilt "firstElt.rqFromChild" "missByState".
    ssFilt "firstElt.rqFromChild" "dwnRq".
    
    ssFilt "deq.rqFromChild" "deferred".

    ssNoFilt "deq.rsFromChild" "dwnRs_wait".
    ssFilt "deq.rsFromChild" "dwnRs_noWait".

    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Definition nmemCacheInl_3: MetaModule.
  Proof.

    start_def nmemCacheInl_2.
    gsF "enq.rsFromChild" "rsFromCToP".

    gsF "enq.rqFromChild" "rqFromCToP".
    
    gsF "deq.toChild" "fromPToC".

    finish_def.
  Defined.

  Theorem nmemCacheInl_3_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_3) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_3.
  Proof.
    (* SKIP_PROOF_ON

    start_pf2 nmemCacheInl_2 nmemCacheInl_2_pf.
    gsFilt "enq.rsFromChild" "rsFromCToP".

    gsFilt "enq.rqFromChild" "rqFromCToP".
    
    gsFilt "deq.toChild" "fromPToC".

    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.
  

  
  Definition nmemCacheInl_4: MetaModule.
  Proof.
    start_def nmemCacheInl_3.

    ggNoF "read.cs" "l1MissByState".
    ggNoF "read.cs" "l1MissByLine".
    ggNoF "read.cs" "l1Hit".
    ggNoF "read.cs" "writeback".
    ggNoF "read.cs" "upgRq".
    ggNoF "read.cs" "upgRs".

    finish_def.
  Defined.

  Definition nmemCacheInl_4_5: MetaModule.
  Proof.
    start_def nmemCacheInl_4.
    
    ggNoF "read.cs" "ld".
    ggNoF "read.cs" "st".
    ggNoF "read.cs" "drop".
    ggF "read.cs" "pProcess".

    finish_def.
  Defined.

  Theorem nmemCacheInl_4_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_4) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_4.
  Proof.
    (* SKIP_PROOF_ON

    start_pf2 nmemCacheInl_3 nmemCacheInl_3_pf.

    ggNoFilt "read.cs" "l1MissByState".
    ggNoFilt "read.cs" "l1MissByLine".
    ggNoFilt "read.cs" "l1Hit".    
    ggNoFilt "read.cs" "writeback".
    ggNoFilt "read.cs" "upgRq".
    ggNoFilt "read.cs" "upgRs".

    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.
    
  Theorem nmemCacheInl_4_5_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_4_5) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_4_5.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_4 nmemCacheInl_4_pf.

    ggNoFilt "read.cs" "ld".
    ggNoFilt "read.cs" "st".
    ggNoFilt "read.cs" "drop".
    ggFilt "read.cs" "pProcess".

    finish_pf.
       END_SKIP_PROOF_ON *) admit.
  Qed.
End MemCacheInl.

Section MemCacheInl2.

  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition nmemCacheInl_4_5': MetaModule.
  Proof.
    pose (nmemCacheInl_4_5 IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren) as sth.
    unfold nmemCacheInl_4_5 in sth.
    match goal with
      | m := ?mod |- _ => exact mod
    end.
  Defined.

  Theorem nmemCacheInl_4_5'_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_4_5') /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_4_5'.
  Proof.
    (* SKIP_PROOF_ON
    eapply nmemCacheInl_4_5_pf; eauto.
        END_SKIP_PROOF_ON *) admit.
  Qed.
  

  
  Definition nmemCacheInl_5: MetaModule.
  Proof.
    start_def nmemCacheInl_4_5'.
    
    ggNoF "read.tag" "l1MissByState".
    ggNoF "read.tag" "l1MissByLine".
    ggNoF "read.tag" "l1Hit".    
    ggNoF "read.tag" "writeback".
    ggNoF "read.tag" "upgRq".
    ggNoF "read.tag" "ld".
    ggNoF "read.tag" "st".
    ggNoF "read.tag" "drop".
    ggF "read.tag" "pProcess".

    finish_def.
  Defined.

  Theorem nmemCacheInl_5_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_5) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_5.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_4_5' nmemCacheInl_4_5'_pf.
    
    ggNoFilt "read.tag" "l1MissByState".
    ggNoFilt "read.tag" "l1MissByLine".
    ggNoFilt "read.tag" "l1Hit".    
    ggNoFilt "read.tag" "writeback".
    ggNoFilt "read.tag" "upgRq".
    ggNoFilt "read.tag" "ld".
    ggNoFilt "read.tag" "st".
    ggNoFilt "read.tag" "drop".
    ggFilt "read.tag" "pProcess".

    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.
End MemCacheInl2.
  
Section MemCacheInl3.

  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition nmemCacheInl_5': MetaModule.
  Proof.
    pose (nmemCacheInl_5 IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren) as sth.
    unfold nmemCacheInl_5 in sth.
    match goal with
      | m := ?mod |- _ => exact mod
    end.
  Defined.

  Theorem nmemCacheInl_5'_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_5') /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_5'.
  Proof.
    (* SKIP_PROOF_ON
    eapply nmemCacheInl_5_pf; eauto.
        END_SKIP_PROOF_ON *) admit.
  Qed.
  

  Definition nmemCacheInl_6: MetaModule.
  Proof.
    start_def nmemCacheInl_5'.
    ggNoF "read.line" "writeback".
    ggNoF "read.line" "ld".
    ggNoF "read.line" "st".
    ggF "read.line" "pProcess".
    finish_def.
  Defined.

  Definition nmemCacheInl_6_3: MetaModule.
  Proof.
    start_def nmemCacheInl_6.
    ggNoF "write.cs" "writeback".
    ggNoF "write.cs" "upgRs".
    finish_def.
  Defined.

  Definition nmemCacheInl_6_6: MetaModule.
  Proof.
    start_def nmemCacheInl_6_3.
    ggF "write.cs" "pProcess".

    finish_def.
  Defined.

  Theorem nmemCacheInl_6_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_6) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_6.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_5' nmemCacheInl_5'_pf.
    
    ggNoFilt "read.line" "writeback".
    ggNoFilt "read.line" "ld".
    ggNoFilt "read.line" "st".
    ggFilt "read.line" "pProcess".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem nmemCacheInl_6_3_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_6_3) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_6_3.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_6 nmemCacheInl_6_pf.
    
    ggNoFilt "write.cs" "writeback".
    ggNoFilt "write.cs" "upgRs".

    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem nmemCacheInl_6_6_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_6_6) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_6_6.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_6_3 nmemCacheInl_6_3_pf.
    
    ggFilt "write.cs" "pProcess".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.
End MemCacheInl3.
  
Section MemCacheInl4.

  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition nmemCacheInl_6_6': MetaModule.
  Proof.
    pose (nmemCacheInl_6_6 IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren) as sth.
    unfold nmemCacheInl_6_6 in sth.
    match goal with
      | m := ?mod |- _ => exact mod
    end.
  Defined.

  Theorem nmemCacheInl_6_6'_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_6_6') /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_6_6'.
  Proof.
    (* SKIP_PROOF_ON
    eapply nmemCacheInl_6_6_pf; eauto.
        END_SKIP_PROOF_ON *) admit.
  Qed.
  

  Definition nmemCacheInl_7: MetaModule.
  Proof.
    start_def nmemCacheInl_6_6'.
    ggF "write.tag" "upgRs".
    finish_def.
  Defined.

  Definition nmemCacheInl_7_3: MetaModule.
  Proof.
    start_def nmemCacheInl_7.
    ggNoF "write.line" "upgRs".
    ggF "write.line" "st".
    finish_def.
  Defined.
  
  Definition nmemCacheInl_7_7: MetaModule.
  Proof.
    start_def nmemCacheInl_7_3.

    ggNoF "deq.fromParent" "upgRs".
    ggNoF "deq.fromParent" "drop".
    ggF "deq.fromParent" "pProcess".
    finish_def.
  Defined.

  Theorem nmemCacheInl_7_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_7) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_7.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_6_6' nmemCacheInl_6_6'_pf.
    ggFilt "write.tag" "upgRs".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem nmemCacheInl_7_3_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_7_3) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_7_3.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_7 nmemCacheInl_7_pf.
    ggNoFilt "write.line" "upgRs".
    ggFilt "write.line" "st".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem nmemCacheInl_7_7_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_7_7) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_7_7.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_7_3 nmemCacheInl_7_3_pf.
    ggNoFilt "deq.fromParent" "upgRs".
    ggNoFilt "deq.fromParent" "drop".
    ggFilt "deq.fromParent" "pProcess".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.
End MemCacheInl4.

Section MemCacheInl5.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition nmemCacheInl_7_7': MetaModule.
  Proof.
    pose (nmemCacheInl_7_7 IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren) as sth.
    unfold nmemCacheInl_7_7 in sth.
    match goal with
      | m := ?mod |- _ => exact mod
    end.
  Defined.

  Theorem nmemCacheInl_7_7'_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_7_7') /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_7_7'.
  Proof.
    (* SKIP_PROOF_ON
    eapply nmemCacheInl_7_7_pf; eauto.
        END_SKIP_PROOF_ON *) admit.
  Qed.
  

  Definition nmemCacheInl_8: MetaModule.
  Proof.
    start_def nmemCacheInl_7_7'.
    ggF "enq.rqToParent" "upgRq".
    finish_def.
  Defined.

  Definition nmemCacheInl_9: MetaModule.
  Proof.
    start_def nmemCacheInl_8.
    ggNoF "enq.rsToParent" "writeback".
    ggF "enq.rsToParent" "pProcess".
    finish_def.
  Defined.

  Definition nmemCacheInl_10: MetaModule.
  Proof.
    start_def nmemCacheInl_9.
    ggF "deq.rqToParent" "rqFromCToP".
    finish_def.
  Defined.
    
  Definition nmemCacheInl_11: MetaModule.
  Proof.
    start_def nmemCacheInl_10.
    ggF "deq.rsToParent" "rsFromCToP".
    finish_def.
  Defined.

  
  Definition nmemCacheInl: MetaModule.
  Proof.
    start_def nmemCacheInl_11.
    ggF "enq.fromParent" "fromPToC".
    finish_def.
  Defined.

  Theorem nmemCacheInl_8_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_8) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_8.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_7_7' nmemCacheInl_7_7'_pf.
    ggFilt "enq.rqToParent" "upgRq".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem nmemCacheInl_9_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_9) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_9.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_8 nmemCacheInl_8_pf.
    ggNoFilt "enq.rsToParent" "writeback".
    ggFilt "enq.rsToParent" "pProcess".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem nmemCacheInl_10_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_10) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_10.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_9 nmemCacheInl_9_pf.
    ggFilt "deq.rqToParent" "rqFromCToP".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.
  
  Theorem nmemCacheInl_11_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl_11) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl_11.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_10 nmemCacheInl_10_pf.
    ggFilt "deq.rsToParent" "rsFromCToP".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem nmemCacheInl_pf:
    (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                            LgDataBytes Id LgNumChildren) <<== modFromMeta nmemCacheInl) /\
    forall ty, MetaModEquiv ty typeUT nmemCacheInl.
  Proof.
    (* SKIP_PROOF_ON
    start_pf2 nmemCacheInl_11 nmemCacheInl_11_pf.
    ggFilt "enq.fromParent" "fromPToC".
    finish_pf.
        END_SKIP_PROOF_ON *) admit.
  Qed.
End MemCacheInl5.

Close Scope string.
