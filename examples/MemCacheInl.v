Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Inline Lts.InlineFacts_2 Lts.Tactics.
Require Import Ex.SC Ex.MemCache.

Require Import Bool List Lib.Struct Lib.Indexer String Lib.StringEq.

Set Implicit Arguments.

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.
  Variable FifoSize: nat.
  
  Definition n := 1. (* number of caches (cores) *)
  Hint Unfold n: ModulesDefs.

  (* Definition memCache := memCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize n. *)
  (* Hint Unfold memCache: ModuleDefs. (* for kinline_compute *) *)
  
  (* Definition memCacheInl: Modules * bool. *)
  (* Proof. *)
  (*   remember (inlineF memCache) as inlined. *)
  (*   kinline_compute_in Heqinlined. *)
  (*   match goal with *)
  (*   | [H: inlined = ?m |- _] => *)
  (*     exact m *)
  (*   end. *)
  (* Defined. *)

End MemCacheInl.

