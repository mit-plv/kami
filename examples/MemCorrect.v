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

  Definition memCache := memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize.

  (* TODO: fix parameters *)
  Definition memAtomic := memAtomic (AddrBits IdxBits LgNumDatas LgDataBytes) FifoSize
                                    (memAtomK (AddrBits IdxBits LgNumDatas LgDataBytes)
                                              (LgDataBytes * 8))
                                    MemCache.n.

  Hint Unfold memCache: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT memCache) => unfold memCache. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT memAtomic) => unfold memAtomic. (* for kequiv *)

  (* TODO: need a mapping which drops cache-related communications *)
  Theorem memCache_refines_memAtomic: memCache <<== memAtomic.
  Proof.
    admit.
  Qed.

End MemCorrect.