Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Tactics Lts.Specialize.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect.

Set Implicit Arguments.

Section MemCache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.
  Variable n: nat. (* number of l1 caches (cores) *)

  Definition l1Cache := l1Cache IdxBits TagBits LgNumDatas LgDataBytes Id.
  Definition l1cs := regFile "cs"%string IdxBits Msi Default.
  Definition l1tag := regFile "tag"%string IdxBits (L1Cache.Tag TagBits) Default.
  Definition l1line := regFile "line"%string IdxBits (L1Cache.Line LgNumDatas LgDataBytes) Default.

  Definition l1 := (l1Cache ++ l1cs ++ l1tag ++ l1line)%kami.

  Definition MIdxBits := TagBits + IdxBits.

  Definition fifoRqFromProc := fifo "rqFromProc" (rsz FifoSize)
                                    (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes Id).
  Definition fifoRsToProc := fifo "rsToProc" (rsz FifoSize) (RsToProc LgDataBytes Id).
  Definition fifoRqToP := fifo "rqToP" (rsz FifoSize) (RqToP MIdxBits LgNumDatas LgDataBytes Id).
  Definition fifoRsToP := fifo "rsToP" (rsz FifoSize) (RsToP MIdxBits LgNumDatas LgDataBytes).
  Definition fifoFromP := fifo "fromP" (rsz FifoSize) (FromP MIdxBits LgNumDatas LgDataBytes Id).

  Definition l1C :=
    (l1 ++ fifoRqFromProc ++ fifoRsToProc ++ fifoRqToP ++ fifoRsToP ++ fifoFromP)%kami.
  
  Definition l1s := duplicate l1C n.

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

Section Facts.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.
  
  Variable FifoSize: nat.
  Variable n: nat.

  Lemma memCache_ModEquiv:
    ModEquiv type typeUT
             (memCache IdxBits TagBits LgNumDatas LgDataBytes Id (rsz FifoSize) n).
  Proof.
    admit.
  Qed.

End Facts.

Hint Immediate memCache_ModEquiv.

Section MemCacheNativeFifo.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable n: nat. (* number of l1 caches (cores) *)

  Definition nfifoRqFromProc :=
    @nativeFifo "rqFromProc" (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes Id) Default.
  Definition nfifoRsToProc := @nativeFifo "rsToProc" (RsToProc LgDataBytes Id) Default.
  Definition nfifoRqToP :=
    @nativeFifo "rqToP" (RqToP (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes Id) Default.
  Definition nfifoRsToP :=
    @nativeFifo "rsToP" (RsToP (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes) Default.
  Definition nfifoFromP :=
    @nativeFifo "fromP" (FromP (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes Id) Default.

  Definition nl1C :=
    ((l1 IdxBits TagBits LgNumDatas LgDataBytes Id)
       ++ nfifoRqFromProc ++ nfifoRsToProc ++ nfifoRqToP ++ nfifoRsToP ++ nfifoFromP)%kami.

  Definition nl1s := duplicate nl1C n.

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

(* Require Import Lib.FMap Lts.Refinement FifoCorrect. *)

(* Section Refinement. *)
(*   Variables IdxBits TagBits LgNumDatas LgDataBytes: nat. *)
(*   Variable Id: Kind. *)

(*   Variable FifoSize: nat. *)

(*   Variable n: nat. (* number of l1 caches (cores) *) *)

(*   Lemma l1C_refines_nl1C: *)
(*     (l1C IdxBits TagBits LgNumDatas LgDataBytes Id (rsz FifoSize)) *)
(*       <<== (nl1C IdxBits TagBits LgNumDatas LgDataBytes Id). *)
(*   Proof. *)
(*     kmodular. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - krefl. *)
(*     - kmodularn. *)
(*       + admit. *)
(*       + admit. *)
(*       + admit. *)
(*       + admit. *)
(*       + apply fifo_refines_nativefifo. *)
(*   Abort. *)

(* End Refinement. *)

