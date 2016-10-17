Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.FMap.
Require Import Kami.Syntax Kami.ParametricSyntax Kami.Semantics Kami.RefinementFacts.
Require Import Kami.Wf Kami.Tactics Kami.Specialize.
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
    memAtomicWoQ (L1Cache.AddrBits IdxBits TagBits LgNumDatas)
                 LgDataBytes (wordToNat (Word.wones LgNumChildren)).

  Definition dropFirstElts :=
    dropN ("rqFromProc" -- "firstElt") (wordToNat (wones LgNumChildren)).

  (* "dropFirstElts" properties *)
  Section DropFirstElts.
    Lemma firstElts_SubList:
      forall n,
        SubList
          (duplicateElt (Indexer.withPrefix "rqFromProc" "firstElt") (wordToNat (wones n)))
          (getDefs (modFromMeta (fifoRqFromProc IdxBits TagBits LgNumDatas LgDataBytes FifoSize n))).
    Proof.
      unfold modFromMeta, getDefs; simpl; intros.
      repeat rewrite namesOf_app.
      do 2 apply SubList_app_2; apply SubList_app_1.
      apply SubList_refl'.
      clear; induction (wordToNat (wones n)); [reflexivity|].
      simpl; f_equal; auto.
    Qed.

    Lemma dropFirstElts_Some:
      forall k v,
        ~ In k (duplicateElt (Indexer.withPrefix "rqFromProc" "firstElt")
                             (wordToNat (wones LgNumChildren))) ->
        dropFirstElts k v = Some v.
    Proof.
      unfold dropFirstElts; intros.
      rewrite dropN_dropPs.
      remember (dropPs _ _ _) as kv; destruct kv.
      - apply eq_sym, dropPs_Some in Heqkv; dest; subst; auto.
      - apply eq_sym, dropPs_None in Heqkv; elim H; auto.
    Qed.

  End DropFirstElts.

  Lemma memCache_refines_memAtomic: modFromMeta memCache <<=[dropFirstElts] memAtomicWoQ.
  Proof.
    ketrans_r; [apply memCache_refines_nmemCache|].
    ketrans_l; [|apply memAtomicWoQInl_refines_memAtomicWoQ].

    apply cheat. (* vmurali TODO *)
  Qed.

  (** Converting memCache to ConcatMod *)

  Require Import Kami.ModuleBoundEx.
  
  Ltac toModules m :=
    match m with
    | (?m1 +++ ?m2) =>
      let nm1 := toModules m1 in
      let nm2 := toModules m2 in
      constr:(ConcatMod nm1 nm2)
    | _ => let um := eval red in m in
               let nm := toModules um in constr:nm
    | _ => constr:(modFromMeta m)
    end.

  Definition memCacheMod: Modules.
    let nm := toModules memCache in (exact nm).
  Defined.

  Lemma memCacheMod_refines_memCache: memCacheMod <<== modFromMeta memCache.
  Proof. (* SKIP_PROOF_ON
    ketrans; [|apply modFromMeta_comm_2].
    kmodular;
      [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
      |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
      | |].
    - ketrans; [|apply modFromMeta_comm_2].
      kmodular;
        [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
        |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
        | |].
      + ketrans; [|apply modFromMeta_comm_2].
        kmodular;
          [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
          |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
          | |].
        * ketrans; [|apply modFromMeta_comm_2].
          kmodular;
            [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
            |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
            | |].
          { krefl. }
          { ketrans; [|apply modFromMeta_comm_2].
            kmodular;
              [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
              |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
              | |].
            { ketrans; [|apply modFromMeta_comm_2].
              kmodular;
                [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
                |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
                | |].
              { krefl. }
              { krefl. }
            }
            { krefl. }
          }
        * ketrans; [|apply modFromMeta_comm_2].
          kmodular;
            [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
            |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
            | |].
          { ketrans; [|apply modFromMeta_comm_2].
            kmodular;
              [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
              |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
              | |].
            { krefl. }
            { krefl. }
          }
          { krefl. }
      + ketrans; [|apply modFromMeta_comm_2].
        kmodular;
          [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
          |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
          | |].
        * krefl.
        * ketrans; [|apply modFromMeta_comm_2].
          kmodular;
            [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
            |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
          | |].
          { ketrans; [|apply modFromMeta_comm_2].
            kmodular;
              [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
              |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
              | |].
            { krefl. }
            { krefl. }
          }
          { krefl. }
    - ketrans; [|apply modFromMeta_comm_2].
      kmodular;
        [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
        |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
        | |].
      + ketrans; [|apply modFromMeta_comm_2].
        kmodular;
          [kdisj_edms_cms_ex (wordToNat (wones LgNumChildren))
          |kdisj_ecms_dms_ex (wordToNat (wones LgNumChildren))
          | |].
        * krefl.
        * krefl.
      + krefl.
        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End MemCorrect.

