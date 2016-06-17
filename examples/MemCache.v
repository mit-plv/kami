Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Notations Lts.SemFacts.
Require Import Lts.Equiv Lts.Tactics Lts.Specialize Lts.Duplicate Lts.Refinement.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Lts.ParametricEquiv Lts.ParametricInline.

Set Implicit Arguments.

Section MemCache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.
  Variable LgNumChildren: nat.

  Definition l1Cache := getMetaFromSinNat LgNumChildren (l1Cache IdxBits TagBits LgNumDatas LgDataBytes Id).
  Definition l1cs := getMetaFromSinNat LgNumChildren (@regFileS "cs"%string IdxBits Msi Default eq_refl).
  Definition l1tag :=
    getMetaFromSinNat LgNumChildren (@regFileS "tag"%string IdxBits (L1Cache.Tag TagBits) Default eq_refl).
  Definition l1line :=
    getMetaFromSinNat LgNumChildren (@regFileS "line"%string IdxBits
                                  (L1Cache.Line LgNumDatas LgDataBytes) Default eq_refl).

  Definition l1 := l1Cache +++ (l1cs +++ l1tag +++ l1line).

  Definition MIdxBits := TagBits + IdxBits.

  Definition fifoRqFromProc :=
    getMetaFromSinNat LgNumChildren
                      (fifoS "rqFromProc" (rsz FifoSize)
                             (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoRsToProc :=
    getMetaFromSinNat
      LgNumChildren (simpleFifoS "rsToProc" (rsz FifoSize) (RsToProc LgDataBytes) eq_refl).
  Definition fifoRqToP :=
    getMetaFromSinNat
      LgNumChildren (simpleFifoS "rqToParent" (rsz FifoSize) (RqToP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).
  Definition fifoRsToP :=
    getMetaFromSinNat
      LgNumChildren (simpleFifoS "rsToParent" (rsz FifoSize) (RsToP MIdxBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoFromP :=
    getMetaFromSinNat
      LgNumChildren (simpleFifoS "fromParent" (rsz FifoSize) (FromP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).

  Definition l1C :=
    l1 +++ (fifoRqFromProc +++ fifoRsToProc +++ fifoRqToP +++ fifoRsToP +++ fifoFromP).

  Definition childParent := childParent MIdxBits LgNumDatas LgDataBytes LgNumChildren Id.

  Definition fifoRqFromC :=
    simpleFifoM "rqFromChild" (rsz FifoSize) (RqFromC MIdxBits LgNumDatas LgDataBytes LgNumChildren Id) eq_refl.
  Definition fifoRsFromC :=
    simpleFifoM "rsFromChild" (rsz FifoSize) (RsFromC MIdxBits LgNumDatas LgDataBytes LgNumChildren) eq_refl.
  Definition fifoToC := simpleFifoM "toChild" (rsz FifoSize) (ToC MIdxBits LgNumDatas LgDataBytes LgNumChildren Id) eq_refl.

  Definition childParentC := (childParent +++ fifoRqFromC +++ fifoRsFromC +++ fifoToC)%kami.

  Definition memDir := memDir MIdxBits LgNumDatas LgDataBytes LgNumChildren Id.
  Definition mline := @regFileM "mline"%string MIdxBits (MemDir.Line LgNumDatas LgDataBytes)
                                Default eq_refl.
  Definition mdir := @regFileM "mcs"%string MIdxBits (MemDir.Dir LgNumChildren) Default eq_refl.

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

  Variable LgNumChildren: nat.

  Definition nfifoRqFromProc :=
    getMetaFromSinNat LgNumChildren (@nativeFifoS "rqFromProc"
                                      (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes)
                                      Default eq_refl).
  Definition nfifoRsToProc :=
    getMetaFromSinNat LgNumChildren (@nativeSimpleFifoS "rsToProc" (RsToProc LgDataBytes) Default eq_refl).
  Definition nfifoRqToP :=
    getMetaFromSinNat LgNumChildren (@nativeSimpleFifoS "rqToParent"
                                            (RqToP (MIdxBits IdxBits TagBits)
                                                   LgNumDatas LgDataBytes Id)
                                            Default eq_refl).
  Definition nfifoRsToP :=
    getMetaFromSinNat LgNumChildren (@nativeSimpleFifoS "rsToParent"
                                            (RsToP (MIdxBits IdxBits TagBits)
                                                   LgNumDatas LgDataBytes)
                                            Default eq_refl).
  Definition nfifoFromP :=
    getMetaFromSinNat LgNumChildren (@nativeSimpleFifoS "fromParent"
                                            (FromP (MIdxBits IdxBits TagBits)
                                                   LgNumDatas LgDataBytes Id)
                                            Default eq_refl).

  Definition nl1C :=
    (l1 IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren)
      +++ (nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP).

  Definition nfifoRqFromC :=
    @nativeSimpleFifoM "rqFromChild" (RqFromC (MIdxBits IdxBits TagBits)
                                              LgNumDatas LgDataBytes LgNumChildren Id)
                       Default eq_refl.
  
  Definition nfifoRsFromC :=
    @nativeSimpleFifoM "rsFromChild" (RsFromC (MIdxBits IdxBits TagBits)
                                              LgNumDatas LgDataBytes LgNumChildren)
                       Default eq_refl.
  
  Definition nfifoToC :=
    @nativeSimpleFifoM "toChild" (ToC (MIdxBits IdxBits TagBits)
                                      LgNumDatas LgDataBytes LgNumChildren Id)
                       Default eq_refl.

  Definition nchildParentC :=
    ((childParent IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren)
       +++ nfifoRqFromC +++ nfifoRsFromC +++ nfifoToC)%kami.

  Definition nmemCache :=
    (nl1C +++ nchildParentC +++ (memDirC IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren))%kami.

  (* For applying a substitution lemma *)
  Definition nfifosInNMemCache :=
    modFromMeta
      ((nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP)
         +++ (nfifoRqFromC +++ nfifoRsFromC +++ nfifoToC)).
  
End MemCacheNativeFifo.

Hint Unfold nfifoRqFromProc nfifoRsToProc nfifoRqToP nfifoRsToP nfifoFromP
     nl1C nfifoRqFromC nfifoRsFromC nfifoToC nchildParentC nmemCache: ModuleDefs.


