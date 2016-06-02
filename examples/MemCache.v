Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Notations.
Require Import Lts.Equiv Lts.Tactics Lts.Specialize Lts.Duplicate.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect.

Set Implicit Arguments.

Section MemCache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.
  Variable n: nat. (* number of l1 caches (cores) *)

  Definition l1Cache := l1Cache IdxBits TagBits LgNumDatas LgDataBytes Id.
  Definition l1cs := regFileS "cs"%string IdxBits Msi Default eq_refl.
  Definition l1tag := regFileS "tag"%string IdxBits (L1Cache.Tag TagBits) Default eq_refl.
  Definition l1line := regFileS "line"%string IdxBits
                                (L1Cache.Line LgNumDatas LgDataBytes) Default eq_refl.

  Definition l1 := l1Cache +++ l1cs +++ l1tag +++ l1line.

  Definition MIdxBits := TagBits + IdxBits.

  Definition fifoRqFromProc :=
    fifoS "rqFromProc" (rsz FifoSize)
          (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes) eq_refl.
  Definition fifoRsToProc := fifoS "rsToProc" (rsz FifoSize) (RsToProc LgDataBytes) eq_refl.
  Definition fifoRqToP :=
    fifoS "rqToP" (rsz FifoSize) (RqToP MIdxBits LgNumDatas LgDataBytes Id) eq_refl.
  Definition fifoRsToP :=
    fifoS "rsToP" (rsz FifoSize) (RsToP MIdxBits LgNumDatas LgDataBytes) eq_refl.
  Definition fifoFromP :=
    fifoS "fromP" (rsz FifoSize) (FromP MIdxBits LgNumDatas LgDataBytes Id) eq_refl.

  Definition l1C :=
    l1 +++ fifoRqFromProc +++ fifoRsToProc +++ fifoRqToP +++ fifoRsToP +++ fifoFromP.

  (* TODO: l1C -> repeated l1C *)
  Definition l1s := ParametricSyntax.makeModule l1C.

  Definition childParent := childParent MIdxBits LgNumDatas LgDataBytes n Id.

  Definition fifoRqFromC :=
    fifo "rqFromC" (rsz FifoSize) (RqFromC MIdxBits LgNumDatas LgDataBytes n Id).
  Definition fifoRsFromC :=
    fifo "rsFromC" (rsz FifoSize) (RsFromC MIdxBits LgNumDatas LgDataBytes n).
  Definition fifoToC := fifo "toC" (rsz FifoSize) (ToC MIdxBits LgNumDatas LgDataBytes n Id).

  Definition childParentC := (childParent ++ fifoRqFromC ++ fifoRsFromC ++ fifoToC)%kami.

  Definition memDir := memDir MIdxBits LgNumDatas LgDataBytes n Id.
  Definition mline := regFile "mline"%string MIdxBits (MemDir.Line LgNumDatas LgDataBytes) Default.
  Definition mdir := regFile "mcs"%string MIdxBits (MemDir.Dir n) Default.

  Definition memDirC := (memDir ++ mline ++ mdir)%kami.

  Definition memCache := (l1s ++ childParentC ++ memDirC)%kami.
              
End MemCache.

Hint Unfold MIdxBits: MethDefs.
Hint Unfold l1Cache l1cs l1tag l1line l1
     fifoRqFromProc fifoRsToProc fifoRqToP fifoRsToP fifoFromP
     l1C l1s
     childParent fifoRqFromC fifoRsFromC fifoToC childParentC
     memDir mline mdir memDirC memCache: ModuleDefs.

Section MemCacheNativeFifo.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable n: nat. (* number of l1 caches (cores) *)

  Definition nfifoRqFromProc :=
    @nativeFifoS "rqFromProc" (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes) Default eq_refl.
  Definition nfifoRsToProc :=
    @nativeFifoS "rsToProc" (RsToProc LgDataBytes) Default eq_refl.
  Definition nfifoRqToP :=
    @nativeFifoS "rqToP" (RqToP (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes Id)
                 Default eq_refl.
  Definition nfifoRsToP :=
    @nativeFifoS "rsToP" (RsToP (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes)
                 Default eq_refl.
  Definition nfifoFromP :=
    @nativeFifoS "fromP" (FromP (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes Id)
                 Default eq_refl.

  Definition nl1C :=
    (l1 IdxBits TagBits LgNumDatas LgDataBytes Id)
      +++ nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP.

  (* TODO: nl1C -> repeated nl1C *)
  Definition nl1s := ParametricSyntax.makeModule nl1C.

  Definition nfifoRqFromC :=
    @nativeFifo "rqFromC" (RqFromC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n Id) Default.
  Definition nfifoRsFromC :=
    @nativeFifo "rsFromC" (RsFromC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n) Default.
  Definition nfifoToC :=
    @nativeFifo "toC" (ToC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n Id) Default.

  Definition nchildParentC :=
    ((childParent IdxBits TagBits LgNumDatas LgDataBytes Id n)
       ++ nfifoRqFromC ++ nfifoRsFromC ++ nfifoToC)%kami.

  Definition nmemCache :=
    (nl1s ++ nchildParentC ++ (memDirC IdxBits TagBits LgNumDatas LgDataBytes Id n))%kami.
              
End MemCacheNativeFifo.

Require Import Lib.FMap Lts.Refinement FifoCorrect.

Section Refinement.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)

  (* TODO: memCache <= nmemCache, from the fact: fifoS <= nativeFifoS *)

End Refinement.

