Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Equiv Lts.Tactics Lts.Specialize.
Require Import Ex.Msi Ex.MemTypes Ex.Fifo Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.SC Ex.MemAtomic Ex.MemCache Ex.MemCacheSubst Lib.Indexer.

Set Implicit Arguments.

Section MemCorrect.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.
  Variable FifoSize: nat.
  Variable LgNumChildren: nat.

  Definition memCache :=
    MemCache.memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize LgNumChildren.
  Definition nmemCache :=
    MemCache.nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id LgNumChildren.
  Definition memAtomicWoQ :=
    memAtomicWoQ (L1Cache.AddrBits IdxBits TagBits LgNumDatas LgDataBytes)
                 LgDataBytes (Word.wordToNat (Word.wones LgNumChildren)).

  (* TODO: give the right p *)
  Axiom dropP: string -> sigT SignT -> option (sigT SignT).

  Lemma memCache_refines_memAtomic: modFromMeta memCache <<=[dropP] memAtomicWoQ.
  Proof.
    apply Refinement.traceRefines_trans with (p:= id) (mb:= modFromMeta nmemCache);
      [unfold MethsT; rewrite <-SemFacts.idElementwiseId;
       apply memCache_refines_nmemCache|].
    
    admit. (* vmurali TODO *)
  Qed.

End MemCorrect.

