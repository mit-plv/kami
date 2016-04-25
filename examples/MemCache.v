Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Tactics Lts.Specialize.
Require Import Ex.Msi Ex.MemTypes Ex.Fifo Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.

Set Implicit Arguments.

Section MemCache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)

  Definition l1Cache := l1Cache IdxBits TagBits LgNumDatas LgDataBytes Id.
  (* TODO: fix default values *)
  Definition l1cs := regFile "cs"%string IdxBits Msi Default.
  Definition l1tag := regFile "tag"%string IdxBits (L1Cache.Tag TagBits) Default.
  Definition l1line := regFile "line"%string IdxBits (L1Cache.Line LgNumDatas LgDataBytes) Default.

  Definition l1 := (l1Cache ++ l1cs ++ l1tag ++ l1line)%kami.

  Definition MIdxBits := TagBits + IdxBits.

  Definition fifoRqFromProc := fifo "rqFromProc" FifoSize
                                    (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes Id).
  Definition fifoRsToProc := fifo "rsToProc" FifoSize (RsToProc LgDataBytes Id).
  Definition fifoRqToP := fifo "rqToP" FifoSize (RqToP MIdxBits LgNumDatas LgDataBytes Id).
  Definition fifoRsToP := fifo "rsToP" FifoSize (RsToP MIdxBits LgNumDatas LgDataBytes).
  Definition fifoFromP := fifo "fromP" FifoSize (FromP MIdxBits LgNumDatas LgDataBytes Id).

  Definition l1C :=
    (l1 ++ fifoRqFromProc ++ fifoRsToProc ++ fifoRqToP ++ fifoRsToP ++ fifoFromP)%kami.
  
  Definition l1s := duplicate l1C n.

  Definition childParent := childParent MIdxBits LgNumDatas LgDataBytes n Id.

  Definition fifoRqFromC := fifo "rqFromC" FifoSize (RqFromC MIdxBits LgNumDatas LgDataBytes n Id).
  Definition fifoRsFromC := fifo "rsFromC" FifoSize (RsFromC MIdxBits LgNumDatas LgDataBytes n).
  Definition fifoToC := fifo "toC" FifoSize (ToC MIdxBits LgNumDatas LgDataBytes n Id).

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

Section Facts.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.
  
  Variable FifoSize: nat.
  Variable n: nat.

  Lemma memCache_ModEquiv:
    ModEquiv type typeUT (memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n).
  Proof.
    admit.
  Qed.

End Facts.

Hint Immediate memCache_ModEquiv.

