Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Semantics Lts.Notations Lts.SemFacts.
Require Import Lts.Equiv Lts.Tactics Lts.Specialize Lts.Duplicate Lts.Refinement.
Require Import Ex.Msi Ex.MemTypes Ex.RegFile Ex.L1Cache Ex.ChildParent Ex.MemDir.
Require Import Ex.Fifo Ex.NativeFifo Ex.FifoCorrect Lts.ParametricEquiv Lts.ParametricInline.

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

  (*
  Ltac changeNames mod modRef modEquiv dmod dmodRef dmodEquiv :=
    let ddmodRef := fresh in
    pose proof (traceRefines_trans_elem modRef dmodRef) as ddmodRef;
    unfold mod in dmod;
    clear dmodRef mod modRef modEquiv;
    pose dmod as mod; unfold dmod in mod;
    pose proof dmodEquiv as modEquiv; clear dmodEquiv;
    replace dmod with mod in modEquiv by (apply eq_refl);
    pose proof ddmodRef as modRef; clear ddmodRef;
    replace dmod with mod in modRef by (apply eq_refl); clear dmod.
   *)

  Require Import Lts.ParametricInlineLtac.
  Ltac ggNoFilt dm r :=
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        inlineGenDmGenRule_NoFilt m mEquiv dm r;
          match goal with
            | m'Ref:
                modFromMeta ?m <<== modFromMeta ?m',
                m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
              apply (traceRefines_trans_elem mRef) in m'Ref; clear mRef;
              let newm := fresh in
              pose m' as newm;
                fold newm in m'Ref;
                fold newm in m'Equiv;
                simpl in newm;
                clear mEquiv m
          end
    end.
    (*
    let dmod := fresh in
    let dmodRef := fresh in
    let dmodEquiv := fresh in
    inlineGenDmGenRule_NoFilt mod modEquiv dm r dmod dmodRef dmodEquiv;
    changeNames mod modRef modEquiv dmod dmodRef dmodEquiv *)

  Local Notation "'LargeMetaModule'" := {| metaRegs := _;
                                           metaRules := _;
                                           metaMeths := _ |}.


  
  Definition nmemCacheInl:
    {m: MetaModule &
       (modFromMeta (nmemCache IdxBits TagBits LgNumDatas
                               LgDataBytes Id FifoSize) <<== modFromMeta m) /\
        forall ty, MetaModEquiv ty typeUT m}.
  Proof.
    pose (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize) as m.
    assert (mRef: modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                                <<== modFromMeta m) by
        (unfold MethsT; rewrite @idElementwiseId; apply traceRefines_refl).

    repeat autounfold with ModuleDefs in m;
    cbv [makeMetaModule getMetaFromSinNat makeSinModule getMetaFromSin
                        sinRegs sinRules sinMeths rulesToRep regsToRep methsToRep
                        convSinToGen] in m;
    simpl in m;
    unfold concatMetaMod in m; simpl in m;
    unfold Indexer.withPrefix in m; simpl in m.
    assert (mEquiv: forall ty, MetaModEquiv ty typeUT m) by kequiv.

    
    Reset Profile.
    Start Profiling.
    ggNoFilt "read.cs" "ldHit".
    ggNoFilt "read.cs" "stHit".
    ggNoFilt "read.cs" "upgRq".
    ggNoFilt "read.cs" "upgRs".
    ggNoFilt "read.cs" "l1MissByState".
    ggNoFilt "read.cs" "l1MissByLine".
    ggNoFilt "read.cs" "ldDeferred".
    ggNoFilt "read.cs" "stDeferred".
    ggNoFilt "read.cs" "drop".
    ggNoFilt "read.cs" "writeback".
    Stop Profiling.
    Show Profile.

Ltac inlineGenDmGenRule_Filt m mEquiv dm r :=
  let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
      (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
        let rTriple := eval simpl in (findR r nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let H3 := fresh in
                    let H4 := fresh in
                    let H5 := fresh in
                    assert
                      (H3:
                         forall r',
                           In r' (preR ++ sufR) ->
                           match r' with
                             | OneRule _ _ => True
                             | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                               noCallDmSigGenA (bgenB typeUT)
                                               {| isRep := true; nameRec := dmn |}
                                               (projT1 bdm) = true
                           end) (* by
                        (let isIn := fresh in
                         intros ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn) *);
                      assert
                        (H4:
                           forall dm',
                             In dm' (metaMeths m) ->
                             match dm' with
                               | OneMeth _ _ => True
                               | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                 noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                 {| isRep := true; nameRec := dmn |}
                                                 (projT1 bdm) = true
                             end) (* by
                        (let isIn := fresh in
                         intros ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn) *);
                      assert
                        (H5: exists call : NameRecIdx,
                               In call (getCallsGenA (bdr typeUT)) /\
                               nameVal (nameRec call) = nameVal dmn /\ isRep call = true) by
                          (eexists {| isRep := true;
                                      nameRec := {| nameVal := nameVal dmn;
                                                    goodName := _ |} |};
                           split; [simpl; tauto | split; reflexivity]); (*
                      let m'Ref := fresh in
                      let m'Equiv := fresh in
                      pose proof (@inlineGenGenDmToRule_traceRefines_Filt
                                    m A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule H3 H4 H5) as m'Ref;
                        pose proof (@inlineGenGenDmToRule_ModEquiv_NoFilt
                                      m mEquiv A strA goodFn GenK getConstK goodFn2
                                      bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                      sufR eq_refl noDupMeth noDupRule H4) as m'Equiv;
                        clear noDupMeth noDupRule H3 H4 H5 *) idtac
                end
            end.
    inlineGenDmGenRule_Filt H0 H5 "read.cs" "pProcess".
    progress let isIn := fresh in
             intros ? isIn;
               repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
               destruct isIn.
    
                        (*(let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn); *)

    
    intros ? ? ? ? ? ? ? ? ? ? isIn; simpl in isIn.
    destruct isIn as [murali | isIn].
    
    inversion murali.
    injection murali as [_ _ _ _ bgen _ _].
    inversion murali; subst; clear murali.
    simpl.
    inv murali.
    [subst; reflexivity | ].
    repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]).
    repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]).
    destruct isIn.
                    asser
    clear m.
    match goal with
      | m'Ref:
          modFromMeta _ <<== modFromMeta ?m',
          m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
        let newm := fresh in
        pose m' as newm;
          fold newm in m'Ref;
          fold newm in m'Equiv;
          simpl in newm;
          clear m
    end.
    clear m.
    inlineGenDmGenRule_NoFilt m mEquiv "read.cs" "ldHit".
    Reset Profile.
    Start Profiling.

    let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
    (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm "read.cs" nil (metaMeths m)) in
        let rTriple := eval simpl in (findR "ldHit" nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let m'Ref := fresh in
                    let m'Equiv := fresh in
                    pose proof (@inlineGenGenDmToRule_traceRefines_NoFilt
                                  m A strA goodFn GenK getConstK goodFn2
                                  bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                  sufR eq_refl noDupMeth noDupRule) as m'Ref;
                      pose proof (@inlineGenGenDmToRule_ModEquiv_NoFilt
                                    m mEquiv A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule) as m'Equiv;
                      clear noDupMeth noDupRule
                end
            end.

    
    inlineGenDmGenRule_NoFilt m mEquiv "read.cs" "ldHit".
    match goal with
      | mRef:
          modFromMeta (nmemCache IdxBits TagBits LgNumDatas LgDataBytes Id FifoSize)
                      <<== modFromMeta ?m,
          mEquiv: forall ty, MetaModEquiv ty typeUT ?m |- _ =>
        inlineGenDmGenRule_NoFilt m mEquiv dm r;
          match goal with
            | m'Ref:
                modFromMeta ?m <<== modFromMeta ?m',
              m'Equiv: forall ty, MetaModEquiv ty typeUT ?m' |- _ =>
              pose proof (traceRefines_trans_elem mRef m'Ref); clear mRef m'Ref;
              pose m' as newm;
              fold newm in m'Ref;
              fold newm in m'Equiv;
              clear m
          end;
          clear mEquiv
    end.
    
    ggNoFilt "read.cs" "ldHit".

    ggNoFilt "read.cs" "stHit".


    ggNoFilt "read.cs" "upgRq".

    Stop Profiling.
    Show Profile.

    Reset Profile.
    Start Profiling.
    ggNoFilt "read.cs" "upgRs".
    Stop Profiling.
    Show Profile.


    ggNoFilt "read.cs" "l1MissByState".

    Stop Profiling.
    Show Profile.

    Reset Profile.
    Start Profiling.
    
    ggNoFilt mod modRef modEquiv "read.cs" "l1MissByLine".
    Stop Profiling.
    Show Profile.
    
    ggNoFilt mod modRef modEquiv "read.cs" "ldDeferred".
    ggNoFilt mod modRef modEquiv "read.cs" "stDeferred".
    ggNoFilt mod modRef modEquiv "read.cs" "drop".
    ggNoFilt mod modRef modEquiv "read.cs" "writeback".
    ggFilt mod modRef modEquiv "read.cs" "pProcess".
    
    exact (existT _ mod (conj modRef modEquiv)). *)
    admit.
  Defined.

  Close Scope string.
  
End MemCacheInl.

