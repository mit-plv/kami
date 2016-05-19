Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Tactics Lts.Specialize.
Require Import Ex.Msi Ex.MemTypes Ex.Fifo Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.SC Ex.MemAtomic Ex.MemCache.

Set Implicit Arguments.

Section MemCorrect.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.
  Variable FifoSize: nat.

  Variable n: nat. (* number of caches (cores) *)

  Definition memCache := MemCache.memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n.
  Definition memAtomic := memAtomic (AddrBits IdxBits LgNumDatas LgDataBytes)
                                    FifoSize LgDataBytes n.

  Lemma memCache_refines_memAtomic: memCache <<== memAtomic.
  Proof.
    unfold memCache, MemCache.memCache.
    unfold memAtomic, MemAtomic.memAtomic.
    admit.
  Qed.

End MemCorrect.

