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

  Definition l1Cache := getMetaFromSinNat n (l1Cache IdxBits TagBits LgNumDatas LgDataBytes Id).
  Definition l1cs := getMetaFromSinNat n (regFileS "cs"%string IdxBits Msi Default eq_refl).
  Definition l1tag :=
    getMetaFromSinNat n (regFileS "tag"%string IdxBits (L1Cache.Tag TagBits) Default eq_refl).
  Definition l1line :=
    getMetaFromSinNat n (regFileS "line"%string IdxBits
                                  (L1Cache.Line LgNumDatas LgDataBytes) Default eq_refl).

  Definition l1 := l1Cache +++ (l1cs +++ l1tag +++ l1line).

  Definition MIdxBits := TagBits + IdxBits.

  Definition fifoRqFromProc :=
    getMetaFromSinNat n
                      (fifoS "rqFromProc" (rsz FifoSize)
                             (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoRsToProc :=
    getMetaFromSinNat
      n (fifoS "rsToProc" (rsz FifoSize) (RsToProc LgDataBytes) eq_refl).
  Definition fifoRqToP :=
    getMetaFromSinNat
      n (fifoS "rqToP" (rsz FifoSize) (RqToP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).
  Definition fifoRsToP :=
    getMetaFromSinNat
      n (fifoS "rsToP" (rsz FifoSize) (RsToP MIdxBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoFromP :=
    getMetaFromSinNat
      n (fifoS "fromP" (rsz FifoSize) (FromP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).

  Definition l1C :=
    l1 +++ (fifoRqFromProc +++ fifoRsToProc +++ fifoRqToP +++ fifoRsToP +++ fifoFromP).

  Definition childParent := childParent MIdxBits LgNumDatas LgDataBytes n Id.

  Definition fifoRqFromC :=
    fifoM "rqFromC" (rsz FifoSize) (RqFromC MIdxBits LgNumDatas LgDataBytes n Id) eq_refl.
  Definition fifoRsFromC :=
    fifoM "rsFromC" (rsz FifoSize) (RsFromC MIdxBits LgNumDatas LgDataBytes n) eq_refl.
  Definition fifoToC := fifoM "toC" (rsz FifoSize) (ToC MIdxBits LgNumDatas LgDataBytes n Id)
                              eq_refl.

  Definition childParentC := (childParent +++ fifoRqFromC +++ fifoRsFromC +++ fifoToC)%kami.

  Definition memDir := memDir MIdxBits LgNumDatas LgDataBytes n Id.
  Definition mline := regFileM "mline"%string MIdxBits (MemDir.Line LgNumDatas LgDataBytes)
                               Default eq_refl.
  Definition mdir := regFileM "mcs"%string MIdxBits (MemDir.Dir n) Default eq_refl.

  Definition memDirC := (memDir +++ mline +++ mdir)%kami.

  Definition memCache := (l1C +++ childParentC +++ memDirC)%kami.
              
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

  Variable n: nat. (* number of l1 caches (cores) *)

  Definition nfifoRqFromProc :=
    getMetaFromSinNat n (@nativeFifoS "rqFromProc"
                                      (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes)
                                      Default eq_refl).
  Definition nfifoRsToProc :=
    getMetaFromSinNat n (@nativeFifoS "rsToProc" (RsToProc LgDataBytes) Default eq_refl).
  Definition nfifoRqToP :=
    getMetaFromSinNat n (@nativeFifoS "rqToP"
                                      (RqToP (MIdxBits IdxBits TagBits)
                                             LgNumDatas LgDataBytes Id)
                                      Default eq_refl).
  Definition nfifoRsToP :=
    getMetaFromSinNat n (@nativeFifoS "rsToP"
                                      (RsToP (MIdxBits IdxBits TagBits)
                                             LgNumDatas LgDataBytes)
                                      Default eq_refl).
  Definition nfifoFromP :=
    getMetaFromSinNat n (@nativeFifoS "fromP"
                                      (FromP (MIdxBits IdxBits TagBits)
                                             LgNumDatas LgDataBytes Id)
                                      Default eq_refl).

  Definition nl1C :=
    (l1 IdxBits TagBits LgNumDatas LgDataBytes Id n)
      +++ (nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP).

  Definition nfifoRqFromC :=
    @nativeFifoM "rqFromC" (RqFromC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n Id)
                 Default eq_refl.
  
  Definition nfifoRsFromC :=
    @nativeFifoM "rsFromC" (RsFromC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n) Default
                 eq_refl.
  
  Definition nfifoToC :=
    @nativeFifoM "toC" (ToC (MIdxBits IdxBits TagBits) LgNumDatas LgDataBytes n Id) Default
                 eq_refl.

  Definition nchildParentC :=
    ((childParent IdxBits TagBits LgNumDatas LgDataBytes Id n)
       +++ nfifoRqFromC +++ nfifoRsFromC +++ nfifoToC)%kami.

  Definition nmemCache :=
    (nl1C +++ nchildParentC +++ (memDirC IdxBits TagBits LgNumDatas LgDataBytes Id n))%kami.
              
End MemCacheNativeFifo.

Require Import Lib.FMap Lts.Refinement FifoCorrect.

Section Refinement.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Variable n: nat. (* number of l1 caches (cores) *)

  (*
  Lemma l1s_refines_nl1s:
    (l1s IdxBits TagBits LgNumDatas LgDataBytes Id (rsz FifoSize) n)
      <<== (nl1s IdxBits TagBits LgNumDatas LgDataBytes Id n).
  Proof.
    evar (im1: Modules); ktrans im1; unfold im1;
      [unfold MethsT; rewrite <-SemFacts.idElementwiseId; apply makeModule_comm_1|].
    evar (im2: Modules); ktrans im2; unfold im2;
      [|unfold MethsT; rewrite <-SemFacts.idElementwiseId; apply makeModule_comm_2].
    clear im1 im2.

    admit.
    (* simple kmodular. *)
    (* - admit. (* kequiv for metamodule / automation *) *)
    (* - admit. (* ditto *) *)
    (* - admit. (* ditto *) *)
    (* - admit. (* ditto *) *)
    (* - kdisj_regs. *)
    (* - kdisj_regs. *)
    (* - admit. (* need to extend kvalid_regs *) *)
    (* - admit. (* ditto *) *)
    (* - kdisj_dms. *)
    (* - kdisj_cms. *)
    (* - kdisj_dms. *)
    (* - kdisj_cms. *)
    (* - admit. (* need to extend kdef_call_sub *) *)
    (* - admit. (* ditto *) *)
    (* - auto. *)
    (* - krefl. *)
    (* - admit. *)
  Qed.
  

  Lemma childParentC_refines_nchildParentC:
    (childParentC IdxBits TagBits LgNumDatas LgDataBytes Id (rsz FifoSize) n)
      <<== (nchildParentC IdxBits TagBits LgNumDatas LgDataBytes Id n).
  Proof. (* SKIP_PROOF_ON
    simple kmodular;
      [kequiv|kequiv|kequiv|kequiv
       |kdisj_regs|kdisj_regs|kvalid_regs|kvalid_regs
       |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
       |kdef_call_sub|kdef_call_sub
       |kinteracting| |].
    - krefl.
    - simple kmodularn;
        [kequiv|kequiv|kequiv|kequiv
         |kdisj_regs|kdisj_regs|kvalid_regs|kvalid_regs
         |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
         |knoninteracting|knoninteracting
         | |].
      + apply fifo_refines_nativefifo.
      + simple kmodularn;
          [kequiv|kequiv|kequiv|kequiv
           |kdisj_regs|kdisj_regs|kvalid_regs|kvalid_regs
           |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
           |knoninteracting|knoninteracting
           | |].
        * apply fifo_refines_nativefifo.
        * apply fifo_refines_nativefifo.
          END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma memCache_refines_nmemCache:
    (memCache IdxBits TagBits LgNumDatas LgDataBytes Id (rsz FifoSize) n)
      <<== (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id n).
  Proof.
    admit.
    
    (* simple kmodular. *)
    (* - admit. (* need kequiv for metamodule / automation *) *)
    (* - admit. (* ditto *) *)
    (* - admit. (* ditto *) *)
    (* - admit. (* ditto *) *)
    (* - kdisj_regs *)
    (* - kdisj_regs *)
    (* - admit. (* need to extend kvalid_regs *) *)
    (* - admit. (* need to extend kvalid_regs *) *)
    (* - kdisj_dms *)
    (* - kdisj_cms *)
    (* - kdisj_dms *)
    (* - kdisj_cms *)
    (* - admit. (* need to extend kdef_call_sub *) *)
    (* - admit. (* need to extend kdef_call_sub *) *)
    (* - kinteracting. *)
    (* - apply l1s_refines_nl1s. *)
    (* - simple kmodular. *)
    (*   + admit. (* need kequiv for metamodule / automation *) *)
    (*   + admit. (* ditto *) *)
    (*   + admit. (* ditto *) *)
    (*   + admit. (* ditto *) *)
    (*   + kdisj_regs *)
    (*   + kdisj_regs *)
    (*   + admit. (* extend kvalid_regs *) *)
    (*   + admit. (* extend kvalid_regs *) *)
    (*   + kdisj_dms *)
    (*   + kdisj_cms *)
    (*   + kdisj_dms *)
    (*   + kdisj_cms *)
    (*   + admit. (* need to extend kdef_call_sub *) *)
    (*   + admit. (* need to extend kdef_call_sub *) *)
    (*   + kinteracting. *)
    (*   + apply childParencC_refines_nchildParentC. *)
    (*   + krefl. *)
  Qed.
   *)

End Refinement.

