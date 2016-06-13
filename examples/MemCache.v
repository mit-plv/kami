Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Notations.
Require Import Lts.Equiv Lts.Tactics Lts.Specialize Lts.Duplicate.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Lts.ParametricEquiv Lts.ParametricInline.

Set Implicit Arguments.

Section MemCache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.
  Variable n: nat. (* number of l1 caches (cores) *)

  Definition l1Cache := getMetaFromSinNat n (l1Cache IdxBits TagBits LgNumDatas LgDataBytes Id).
  Definition l1cs := getMetaFromSinNat n (regFileS "cs"%string IdxBits Msi Default eq_refl).
  Definition l1tag :=
    getMetaFromSinNat n (regFileS "tag"%string IdxBits (L1Cache.Tag TagBits) Default eq_refl).
  Definition l1line :=
    getMetaFromSinNat n (regFileS "line"%string IdxBits
                                  (L1Cache.Line LgNumDatas LgDataBytes) Default eq_refl).

  Definition l1 := l1Cache +++ (l1cs +++ l1tag +++ l1line).

  Definition MIdxBits := TagBits + IdxBits.

  Definition fifoRqFromProc :=
    getMetaFromSinNat n
                      (fifoS "rqFromProc" (rsz FifoSize)
                             (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoRsToProc :=
    getMetaFromSinNat
      n (fifoS "rsToProc" (rsz FifoSize) (RsToProc LgDataBytes) eq_refl).
  Definition fifoRqToP :=
    getMetaFromSinNat
      n (fifoS "rqToParent" (rsz FifoSize) (RqToP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).
  Definition fifoRsToP :=
    getMetaFromSinNat
      n (fifoS "rsToParent" (rsz FifoSize) (RsToP MIdxBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoFromP :=
    getMetaFromSinNat
      n (fifoS "fromParent" (rsz FifoSize) (FromP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).

  Definition l1C :=
    l1 +++ (fifoRqFromProc +++ fifoRsToProc +++ fifoRqToP +++ fifoRsToP +++ fifoFromP).

  Definition childParent := childParent MIdxBits LgNumDatas LgDataBytes n Id.

  Definition fifoRqFromC :=
    fifoM "rqFromChild" (rsz FifoSize) (RqFromC MIdxBits LgNumDatas LgDataBytes n Id) eq_refl.
  Definition fifoRsFromC :=
    fifoM "rsFromChild" (rsz FifoSize) (RsFromC MIdxBits LgNumDatas LgDataBytes n) eq_refl.
  Definition fifoToC := fifoM "toChild" (rsz FifoSize) (ToC MIdxBits LgNumDatas LgDataBytes n Id)
                              eq_refl.

  Definition childParentC := (childParent +++ fifoRqFromC +++ fifoRsFromC +++ fifoToC)%kami.

  Definition memDir := memDir MIdxBits LgNumDatas LgDataBytes n Id.
  Definition mline := regFileM "mline"%string MIdxBits (MemDir.Line LgNumDatas LgDataBytes)
                               Default eq_refl.
  Definition mdir := regFileM "mcs"%string MIdxBits (MemDir.Dir n) Default eq_refl.

  Definition memDirC := (memDir +++ mline +++ mdir)%kami.

  Definition memCache := (l1C +++ childParentC +++ memDirC)%kami.

  (* For applying a substitution lemma *)
  Definition fifosInMemCache :=
    modFromMeta
      ((fifoRqFromProc +++ fifoRsToProc +++ fifoRqToP +++ fifoRsToP +++ fifoFromP)
         +++ (fifoRqFromC +++ fifoRsFromC +++ fifoToC)).

  Definition othersInMemCache :=
    modFromMeta (l1 +++ childParent +++ memDirC).

End MemCache.

Hint Unfold MIdxBits: MethDefs.
Hint Unfold l1Cache l1cs l1tag l1line l1
     fifoRqFromProc fifoRsToProc fifoRqToP fifoRsToP fifoFromP
     l1C
     childParent fifoRqFromC fifoRsFromC fifoToC childParentC
     memDir mline mdir memDirC memCache: ModuleDefs.

Section MemCacheNativeFifo.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable n: nat. (* number of l1 caches (cores) *)

  Definition nfifoRqFromProc :=
    getMetaFromSinNat n (@nativeFifoS "rqFromProc"
                                      (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes)
                                      Default eq_refl).
  Definition nfifoRsToProc :=
    getMetaFromSinNat n (@nativeFifoS "rsToProc" (RsToProc LgDataBytes) Default eq_refl).
  Definition nfifoRqToP :=
    getMetaFromSinNat n (@nativeFifoS "rqToParent"
                                      (RqToP (MIdxBits IdxBits TagBits)
                                             LgNumDatas LgDataBytes Id)
                                      Default eq_refl).
  Definition nfifoRsToP :=
    getMetaFromSinNat n (@nativeFifoS "rsToParent"
                                      (RsToP (MIdxBits IdxBits TagBits)
                                             LgNumDatas LgDataBytes)
                                      Default eq_refl).
  Definition nfifoFromP :=
    getMetaFromSinNat n (@nativeFifoS "fromParent"
                                      (FromP (MIdxBits IdxBits TagBits)
                                             LgNumDatas LgDataBytes Id)
                                      Default eq_refl).

  Definition nl1C :=
    (l1 IdxBits TagBits LgNumDatas LgDataBytes Id n)
      +++ (nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP).

  Definition nfifoRqFromC :=
    @nativeFifoM "rqFromChild" (RqFromC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n Id)
                 Default eq_refl.
  
  Definition nfifoRsFromC :=
    @nativeFifoM "rsFromChild" (RsFromC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n) Default
                 eq_refl.
  
  Definition nfifoToC :=
    @nativeFifoM "toChild" (ToC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n Id) Default
                 eq_refl.

  Definition nchildParentC :=
    ((childParent IdxBits TagBits LgNumDatas LgDataBytes Id n)
       +++ nfifoRqFromC +++ nfifoRsFromC +++ nfifoToC)%kami.

  Definition nmemCache :=
    (nl1C +++ nchildParentC +++ (memDirC IdxBits TagBits LgNumDatas LgDataBytes Id n))%kami.

  (* For applying a substitution lemma *)
  Definition nfifosInNMemCache :=
    modFromMeta
      ((nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP)
         +++ (nfifoRqFromC +++ nfifoRsFromC +++ nfifoToC)).
  
End MemCacheNativeFifo.

Hint Unfold nl1C nmemCache: ModuleDefs.

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Notation "'LargeMetaModule'" := {| metaRegs := _; metaRules := _; metaMeths := _ |}.
  
  Definition nmemCacheInl:
    {m: MetaModule &
       (modFromMeta m <<==
        modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                               LgDataBytes Id FifoSize)) /\
        forall ty, MetaModEquiv ty typeUT m}.
  Proof.
    pose (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize) as Heqm.
    repeat autounfold with ModuleDefs in Heqm;
    cbv [makeMetaModule getMetaFromSinNat makeSinModule getMetaFromSin
                        sinRegs sinRules sinMeths rulesToRep regsToRep methsToRep
                        convSinToGen] in Heqm;
    simpl in Heqm;
    unfold concatMetaMod in Heqm; simpl in Heqm;
    unfold Indexer.withPrefix in Heqm; simpl in Heqm.
    assert (mEquiv: forall ty, MetaModEquiv ty typeUT Heqm) by admit.
    
    assert (H1: NoDup (map getMetaMethName (metaMeths Heqm))) by
        (subst; simpl; clear; noDupLtac).
    assert (H2: NoDup (map getMetaRuleName (metaRules Heqm))) by
        (subst; simpl; clear; noDupLtac).
    pose "read.cs"%string as dm.
    pose "ldHit"%string as r.
    subst.
    let dmTriple := eval simpl in (findDm dm nil (metaMeths Heqm)) in
        let rTriple := eval simpl in (findR r nil (metaRules Heqm)) in
          match dmTriple with
            | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                     ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
              match rTriple with
                | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                        ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                  pose ({| metaRegs := metaRegs Heqm;
                           metaRules :=
                             preR ++ RepRule strA goodFn getConstK goodFn2
                                  (fun ty => inlineGenGenDm (bdr ty) dm bdm)
                                  rn noDup :: sufR;
                           metaMeths := metaMeths Heqm |}) as moduleItself;
                    pose proof (@inlineGenGenDmToRule_traceRefines_NoFilt
                                  Heqm A strA goodFn GenK getConstK goodFn2
                                  bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                  sufR eq_refl H1 H2) as inlinePf;
                    pose proof
                         (@inlineGenGenDmToRule_ModEquiv_NoFilt
                            Heqm mEquiv A strA goodFn GenK getConstK goodFn2
                            bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                            sufR eq_refl H1 H2
                         ) as equivPf
              end
          end.
    exact (existT (fun m =>
                     (modFromMeta m <<==
                                  modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                                                         LgDataBytes Id FifoSize)) /\
                     forall ty, MetaModEquiv ty typeUT m
                  ) moduleItself (cheat _)).
  Defined.
    {m: MetaModule &
       (modFromMeta m <<==
        modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                               LgDataBytes Id FifoSize)) /\
        forall ty, MetaModEquiv ty typeUT m}.
    
    Print Ltac ketrans.
    
    inlineGenDmGenRule_NoFilt m mEquiv "read.cs"%string "ldHit"%string.
<<<<<<< HEAD

Require Import Lib.FMap Lts.Refinement Lts.Substitute FifoCorrect.

Section Refinement.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)

  Lemma memCache_refines_nmemCache:
    (modFromMeta
       (memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n))
      <<== (modFromMeta
              (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id n)).
  Proof.
    unfold modFromMeta.

    evar (im1: Modules); ktrans im1; unfold im1; clear im1.

    - unfold MethsT; rewrite <-SemFacts.idElementwiseId.

      pose (fifosInMemCache IdxBits TagBits LgNumDatas LgDataBytes
                            Id (rsz FifoSize) n) as fifos.
      pose (nfifosInNMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n) as nfifos.
      pose (othersInMemCache IdxBits TagBits LgNumDatas LgDataBytes Id n) as others.

      apply substitute_flattened_refines_interacting
      with (regs := (getRegInits fifos))
             (rules := (getRules fifos))
             (dms := (getDefsBodies fifos))
             (sregs := (getRegInits nfifos))
             (srules := (getRules nfifos))
             (sdms := (getDefsBodies nfifos))
             (regs' := (getRegInits others))
             (rules' := (getRules others))
             (dms' := (getDefsBodies others)); admit. (* 23 subgoals haha *)

    - apply traceRefines_same_module_structure; admit. (* 5 subgoals *)

  Qed.

End Refinement.
=======
   *)

End MemCacheInl.
>>>>>>> 644f9491ca8c6bc24493222bacb062023536a846

