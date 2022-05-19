Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Kami.PrimFifo.
Require Import Ex.MemTypes Ex.MemAsync.
Require Import Ex.SC Ex.ProcDec Ex.ProcThreeStage Ex.ProcFetch
        Ex.ProcFetchDecode Ex.ProcFDInl Ex.ProcFDInv Ex.ProcFCorrect.
Require Import Eqdep.

Set Implicit Arguments.

Section FetchDecode.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Array Bool dataBytes)) -> (* byteEn *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).

  Variable (f2dElt: Kind).
  Variable (f2dPack:
              forall ty,
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind f2dElt)).
  Variables
    (f2dRawInst: forall ty, fullType ty (SyntaxKind f2dElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (f2dCurPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind (Pc addrSize)))
    (f2dNextPc: forall ty, fullType ty (SyntaxKind f2dElt) ->
                           Expr ty (SyntaxKind (Pc addrSize)))
    (f2dEpoch: forall ty, fullType ty (SyntaxKind f2dElt) ->
                          Expr ty (SyntaxKind Bool)).

  Hypotheses (Hf2dRawInst: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dRawInst _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr rawInst)
             (Hf2dCurPc: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dCurPc _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr curPc)
             (Hf2dNextPc: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dNextPc _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr nextPc)
             (Hf2dEpoch: forall rawInst curPc nextPc epoch,
                 evalExpr (f2dEpoch _ (evalExpr (f2dPack rawInst curPc nextPc epoch))) =
                 evalExpr epoch)
             (Hf2dpackExt:
                forall rawInst1 curPc1 nextPc1 epoch1 rawInst2 curPc2 nextPc2 epoch2,
                  evalExpr rawInst1 = evalExpr rawInst2 ->
                  evalExpr curPc1 = evalExpr curPc2 ->
                  evalExpr nextPc1 = evalExpr nextPc2 ->
                  evalExpr epoch1 = evalExpr epoch2 ->
                  evalExpr (f2dPack rawInst1 curPc1 nextPc1 epoch1) =
                  evalExpr (f2dPack rawInst2 curPc2 nextPc2 epoch2)).

  Context {indexSize tagSize: nat}.
  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSize)) ->
                                Expr ty (SyntaxKind (Bit tagSize))).

  Variables (pcInit : ConstT (Pc addrSize)).

  Definition fetchICacheDecode :=
    ((fetchICache fetch f2dPack getIndex getTag pcInit)
       ++ (PrimFifo.fifoC PrimFifo.primPipelineFifoName f2dFifoName f2dElt)
       ++ (decoder dec d2ePack f2dRawInst f2dCurPc f2dNextPc f2dEpoch))%kami.
  Definition fetchDecode :=
    fetchDecode fetch dec d2ePack
                f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                pcInit.
  Definition fetchNDecode :=
    ProcThreeStage.fetchDecode fetch dec d2ePack pcInit.

  #[local] Hint Unfold fetchDecode: ModuleDefs. (* for kinline_compute *)
  #[local] Hint Extern 1 (ModEquiv type typeUT fetchDecode) => unfold fetchDecode. (* for kequiv *)
  #[local] Hint Extern 1 (ModEquiv type typeUT fetchNDecode) => unfold fetchNDecode. (* for kequiv *)

  Definition fetchDecode_ruleMap (o: RegsT): string -> option string :=
    "pgmInitRq" |-> "pgmInitRq";
      "pgmInitRqEnd" |-> "pgmInitRqEnd";
      "pgmInitRs" |-> "pgmInitRs";
      "pgmInitRsEnd" |-> "pgmInitRsEnd";
      "modifyPc" |-> "modifyPc";
      "decodeLd" |-> "instFetchLd";
      "decodeSt" |-> "instFetchSt";
      "decodeTh" |-> "instFetchTh";
      "decodeNm" |-> "instFetchNm"; ||.
  #[local] Hint Unfold fetchDecode_ruleMap: MethDefs.

  Definition fetchDecode_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Pc addrSize) <- r |> "pc";
       mlet pinitv : Bool <- r |> "pinit";
       mlet pinitRqv : Bool <- r |> "pinitRq";
       mlet pinitRqOfsv : (Bit iaddrSize) <- r |> "pinitRqOfs";
       mlet pinitRsOfsv : (Bit iaddrSize) <- r |> "pinitRsOfs";
       mlet pgmv : (Vector (Data instBytes) iaddrSize) <- r |> "pgm";
       mlet fev : Bool <- r |> "fEpoch";
       mlet f2dfullv : Bool <- r |> "f2d"--"full";
       mlet f2deltv : f2dElt <- r |> "f2d"--"elt";
       (["fEpoch" <- existT _ _ fev]
        +["pgm" <- existT _ _ pgmv]
        +["pinitRsOfs" <- existT _ _ pinitRsOfsv]
        +["pinitRqOfs" <- existT _ _ pinitRqOfsv]
        +["pinitRq" <- existT _ _ pinitRqv]
        +["pinit" <- existT _ _ pinitv]
        +["pc" <- existT _ (SyntaxKind (Pc addrSize))
               (if f2dfullv then evalExpr (f2dCurPc _ f2deltv)
                else pcv)])%fmap)%mapping.
  #[local] Hint Unfold fetchDecode_regMap: MapDefs.

  Definition fetchDecodeInl := ProcFDInl.fetchDecodeInl
                                 fetch dec
                                 d2ePack f2dPack f2dRawInst f2dCurPc f2dNextPc f2dEpoch
                                 pcInit.

  Ltac f2d_abs_tac :=
    try rewrite Hf2dRawInst in *;
    try rewrite Hf2dCurPc in *;
    try rewrite Hf2dNextPc in *;
    try rewrite Hf2dEpoch in *;
    repeat
      match goal with
      | [H: ?pinitv = false -> true = false |- ?pinitv = true] =>
        destruct pinitv; [reflexivity|specialize (H eq_refl); discriminate]
      end.

  Ltac fetchDecode_dest_tac :=
    repeat match goal with
           | [H: context[fetchDecode_inv] |- _] => destruct H
           end;
    kinv_red.

  Definition fdConfig :=
    {| inlining := ITProvided fetchDecodeInl;
       decomposition := DTFunctional fetchDecode_regMap fetchDecode_ruleMap;
       invariants := IVCons fetchDecode_inv_ok IVNil
    |}.

  Theorem fetchDecode_refines_fetchNDecode:
    fetchDecode <<== fetchNDecode.
  Proof. (* SKIP_PROOF_ON

    (** inlining *)
    ketrans; [exact (projT2 fetchDecodeInl)|].

    (** decomposition *)
    kdecompose_nodefs fetchDecode_regMap fetchDecode_ruleMap.
    kinv_add fetchDecode_inv_ok.
    kinv_add_end.
    kinvert.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    - kinv_magic_with fetchDecode_dest_tac f2d_abs_tac.
    
      (* kami_ok fdConfig fetchDecode_dest_tac f2d_abs_tac. *)
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Theorem fetchICacheDecode_refines_fetchDecode:
    fetchICacheDecode <<== fetchDecode.
  Proof.
    intros.
    kmodular.
    - eapply fetchICache_refines_fetcher; eauto.
    - krefl.
  Qed.

  Theorem fetchICacheDecode_refines_fetchNDecode:
    fetchICacheDecode <<== fetchNDecode.
  Proof.
    ketrans.
    - exact fetchICacheDecode_refines_fetchDecode.
    - exact fetchDecode_refines_fetchNDecode.
  Qed.

End FetchDecode.

