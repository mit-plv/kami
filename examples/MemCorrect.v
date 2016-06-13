Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Tactics Lts.Specialize.
Require Import Ex.Msi Ex.MemTypes Ex.Fifo Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.SC Ex.MemAtomic Ex.MemCache ParametricSyntax Lib.Indexer.

Set Implicit Arguments.

Section MemCorrect.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.
  Variable FifoSize: nat.

  Variable n: nat. (* number of caches (cores) *)

  Definition memCache := MemCache.memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n.
  Definition nmemCache := MemCache.nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id n.
  Definition memAtomic := memAtomic (L1Cache.AddrBits IdxBits TagBits LgNumDatas LgDataBytes)
                                    LgDataBytes n.

  Lemma memCache_refines_memAtomic: makeModule memCache <<== memAtomic.
  Proof.
    ktrans (makeModule nmemCache);
      [unfold MethsT; rewrite <-SemFacts.idElementwiseId;
       apply memCache_refines_nmemCache|].
    
    admit. (* vmurali TODO *)
  Qed.

End MemCorrect.

