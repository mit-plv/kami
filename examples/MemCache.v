Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Notations Lts.SemFacts.
Require Import Lts.Equiv Lts.Tactics Lts.Specialize Lts.Duplicate Lts.Refinement.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Lts.ParametricEquiv Lts.ParametricInline.
Require Import Lts.ParametricInlineLtac.

Set Implicit Arguments.

Section MemCache.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.
  Variable n: nat. (* number of l1 caches (cores) *)

  Definition l1Cache := getMetaFromSinNat n (l1Cache IdxBits TagBits LgNumDatas LgDataBytes Id).
  Definition l1cs := getMetaFromSinNat n (@regFileS "cs"%string IdxBits Msi Default eq_refl).
  Definition l1tag :=
    getMetaFromSinNat n (@regFileS "tag"%string IdxBits (L1Cache.Tag TagBits) Default eq_refl).
  Definition l1line :=
    getMetaFromSinNat n (@regFileS "line"%string IdxBits
                                  (L1Cache.Line LgNumDatas LgDataBytes) Default eq_refl).

  Definition l1 := l1Cache +++ (l1cs +++ l1tag +++ l1line).

  Definition MIdxBits := TagBits + IdxBits.

  Definition fifoRqFromProc :=
    getMetaFromSinNat n
                      (fifoS "rqFromProc" (rsz FifoSize)
                             (RqFromProc IdxBits TagBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoRsToProc :=
    getMetaFromSinNat
      n (simpleFifoS "rsToProc" (rsz FifoSize) (RsToProc LgDataBytes) eq_refl).
  Definition fifoRqToP :=
    getMetaFromSinNat
      n (simpleFifoS "rqToParent" (rsz FifoSize) (RqToP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).
  Definition fifoRsToP :=
    getMetaFromSinNat
      n (simpleFifoS "rsToParent" (rsz FifoSize) (RsToP MIdxBits LgNumDatas LgDataBytes) eq_refl).
  Definition fifoFromP :=
    getMetaFromSinNat
      n (simpleFifoS "fromParent" (rsz FifoSize) (FromP MIdxBits LgNumDatas LgDataBytes Id) eq_refl).

  Definition l1C :=
    l1 +++ (fifoRqFromProc +++ fifoRsToProc +++ fifoRqToP +++ fifoRsToP +++ fifoFromP).

  Definition childParent := childParent MIdxBits LgNumDatas LgDataBytes n Id.

  Definition fifoRqFromC :=
    simpleFifoM "rqFromChild" (rsz FifoSize) (RqFromC MIdxBits LgNumDatas LgDataBytes n Id) eq_refl.
  Definition fifoRsFromC :=
    simpleFifoM "rsFromChild" (rsz FifoSize) (RsFromC MIdxBits LgNumDatas LgDataBytes n) eq_refl.
  Definition fifoToC := simpleFifoM "toChild" (rsz FifoSize) (ToC MIdxBits LgNumDatas LgDataBytes n Id)
                                    eq_refl.

  Definition childParentC := (childParent +++ fifoRqFromC +++ fifoRsFromC +++ fifoToC)%kami.

  Definition memDir := memDir MIdxBits LgNumDatas LgDataBytes n Id.
  Definition mline := @regFileM "mline"%string MIdxBits (MemDir.Line LgNumDatas LgDataBytes)
                                Default eq_refl.
  Definition mdir := @regFileM "mcs"%string MIdxBits (MemDir.Dir n) Default eq_refl.

  Definition memDirC := (memDir +++ mline +++ mdir)%kami.

  Definition memCache := (l1C +++ childParentC +++ memDirC)%kami.

  (* For applying a substitution lemma *)
  Definition fifosInMemCache :=
    modFromMeta
      ((fifoRqFromProc +++ fifoRsToProc +++ fifoRqToP +++ fifoRsToP +++ fifoFromP)
         +++ (fifoRqFromC +++ fifoRsFromC +++ fifoToC)).

  Definition othersInMemCache :=
    modFromMeta (l1 +++ childParent +++ memDirC).

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
    getMetaFromSinNat n (@nativeSimpleFifoS "rsToProc" (RsToProc LgDataBytes) Default eq_refl).
  Definition nfifoRqToP :=
    getMetaFromSinNat n (@nativeSimpleFifoS "rqToParent"
                                            (RqToP (MIdxBits IdxBits TagBits)
                                                   LgNumDatas LgDataBytes Id)
                                            Default eq_refl).
  Definition nfifoRsToP :=
    getMetaFromSinNat n (@nativeSimpleFifoS "rsToParent"
                                            (RsToP (MIdxBits IdxBits TagBits)
                                                   LgNumDatas LgDataBytes)
                                            Default eq_refl).
  Definition nfifoFromP :=
    getMetaFromSinNat n (@nativeSimpleFifoS "fromParent"
                                            (FromP (MIdxBits IdxBits TagBits)
                                                   LgNumDatas LgDataBytes Id)
                                            Default eq_refl).

  Definition nl1C :=
    (l1 IdxBits TagBits LgNumDatas LgDataBytes Id n)
      +++ (nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP).

  Definition nfifoRqFromC :=
    @nativeSimpleFifoM "rqFromChild" (RqFromC (MIdxBits IdxBits TagBits)
                                              LgNumDatas LgDataBytes n Id)
                       Default eq_refl.
  
  Definition nfifoRsFromC :=
    @nativeSimpleFifoM "rsFromChild" (RsFromC (MIdxBits IdxBits TagBits)
                                              LgNumDatas LgDataBytes n)
                       Default eq_refl.
  
  Definition nfifoToC :=
    @nativeSimpleFifoM "toChild" (ToC (MIdxBits IdxBits TagBits)
                                      LgNumDatas LgDataBytes n Id)
                       Default eq_refl.

  Definition nchildParentC :=
    ((childParent IdxBits TagBits LgNumDatas LgDataBytes Id n)
       +++ nfifoRqFromC +++ nfifoRsFromC +++ nfifoToC)%kami.

  Definition nmemCache :=
    (nl1C +++ nchildParentC +++ (memDirC IdxBits TagBits LgNumDatas LgDataBytes Id n))%kami.

  (* For applying a substitution lemma *)
  Definition nfifosInNMemCache :=
    modFromMeta
      ((nfifoRqFromProc +++ nfifoRsToProc +++ nfifoRqToP +++ nfifoRsToP +++ nfifoFromP)
         +++ (nfifoRqFromC +++ nfifoRsFromC +++ nfifoToC)).
  
End MemCacheNativeFifo.

Hint Unfold nl1C nmemCache: ModuleDefs.

Theorem traceRefines_trans_elem: forall m1 m2 m3: Modules,
                                   (m1 <<== m2) -> (m2 <<== m3) -> (m1 <<== m3).
Proof.
  intros.
  unfold MethsT in *; rewrite idElementwiseId in *.
  eapply traceRefines_trans; eauto.
Qed.

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable FifoSize: nat.

  Open Scope string.

  Ltac changeNames mod modRef modEquiv dmod dmodRef dmodEquiv :=
    let ddmodRef := fresh in
    pose proof (traceRefines_trans_elem modRef dmodRef) as ddmodRef;
    unfold mod in dmod;
    clear dmodRef mod modRef modEquiv;
    pose dmod as mod; unfold dmod in mod;
    pose proof dmodEquiv as modEquiv; clear dmodEquiv;
    replace dmod with mod in modEquiv by reflexivity;
    pose proof ddmodRef as modRef; clear ddmodRef;
    replace dmod with mod in modRef by reflexivity; clear dmod.

  Ltac ggNoFilt mod modRef modEquiv dm r :=
    let dmod := fresh in
    let dmodRef := fresh in
    let dmodEquiv := fresh in
    inlineGenDmGenRule_NoFilt mod modEquiv dm r dmod dmodRef dmodEquiv;
    changeNames mod modRef modEquiv dmod dmodRef dmodEquiv.

  Local Notation "'LargeMetaModule'" := {| metaRegs := _;
                                           metaRules := _;
                                           metaMeths := _ |}.
  
  Definition nmemCacheInl:
    {m: MetaModule &
       (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                               LgDataBytes Id FifoSize) <<== modFromMeta m) /\
        forall ty, MetaModEquiv ty typeUT m}.
  Proof.
    (* assert (startEquiv: forall ty, MetaModEquiv ty typeUT *)
    (*                                             (nmemCache IdxBits TagBits LgNumDatas *)
    (*                                             LgDataBytes Id FifoSize)) by admit. *)
    (* pose (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize) as mod. *)
    (* assert (modRef: modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize) *)
    (*                             <<== modFromMeta mod) by *)
    (*     (unfold MethsT; rewrite @idElementwiseId; apply traceRefines_refl). *)

    (* repeat autounfold with ModuleDefs in mod; *)
    (* cbv [makeMetaModule getMetaFromSinNat makeSinModule getMetaFromSin *)
    (*                     sinRegs sinRules sinMeths rulesToRep regsToRep methsToRep *)
    (*                     convSinToGen] in mod; *)
    (* simpl in mod; *)
    (* unfold concatMetaMod in mod; simpl in mod; *)
    (* unfold Indexer.withPrefix in mod; simpl in mod. *)
    (* assert (modEquiv: forall ty, MetaModEquiv ty typeUT mod) by (unfold mod; apply startEquiv). *)

    (* ggNoFilt mod modRef modEquiv "read.cs" "ldHit". *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "stHit". *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "upgRq". *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "upgRs". *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "l1MissByState". *)
    
    (* ggNoFilt mod modRef modEquiv "read.cs" "l1MissByLine". *)
    (* idtac. *)
    (* simpl. *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "ldDeferred". *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "stDeferred". *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "drop". *)
    (* ggNoFilt mod modRef modEquiv "read.cs" "writeback". *)
    (* ggFilt mod modRef modEquiv "read.cs" "pProcess". *)
    
    (* exact (existT _ mod (conj modRef modEquiv)). *)
    admit.
  Defined.

  Close Scope string.
  
End MemCacheInl.

