Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAsync.
Require Import Ex.SC Ex.ProcDec Ex.ProcThreeStage Ex.ProcThreeStInl Ex.ProcThreeStInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcThreeStDec.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec iaddrSize instBytes dataBytes rfIdx).

  Variable predictNextPc: forall ty, fullType ty (SyntaxKind (Pc iaddrSize)) -> (* pc *)
                                     Expr ty (SyntaxKind (Pc iaddrSize)).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* val2 *)
                Expr ty (SyntaxKind (Data instBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Pc iaddrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data dataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data instBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Pc iaddrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Pc iaddrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  Hypotheses
    (Hd2eOpType: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eOpType _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr opType)
    (Hd2eDst: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eDst _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr dst)
    (Hd2eAddr: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eAddr _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr addr)
    (Hd2eVal1: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eVal1 _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr val1)
    (Hd2eVal2: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eVal2 _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr val2)
    (Hd2eRawInst: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eRawInst _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr rawInst)
    (Hd2eCurPc: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eCurPc _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr curPc)
    (Hd2eNextPc: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eNextPc _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr nextPc)
    (Hd2eEpoch: forall opType dst addr val1 val2 rawInst curPc nextPc epoch,
        evalExpr (d2eEpoch _ (evalExpr (d2ePack opType dst addr val1 val2 rawInst curPc nextPc epoch))) = evalExpr epoch).

  Variable (e2wElt: Kind).
  Variable (e2wPack:
              forall ty,
                Expr ty (SyntaxKind d2eElt) -> (* decInst *)
                Expr ty (SyntaxKind (Data dataBytes)) -> (* execVal *)
                Expr ty (SyntaxKind e2wElt)).
  Variables
    (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                            Expr ty (SyntaxKind d2eElt))
    (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Data dataBytes))).

  Hypotheses
    (He2wDecInst: forall decInst val,
        evalExpr (e2wDecInst _ (evalExpr (e2wPack decInst val))) = evalExpr decInst)
    (He2wVal: forall decInst val,
        evalExpr (e2wVal _ (evalExpr (e2wPack decInst val))) = evalExpr val).

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).

  Definition p3st := ProcThreeStage.p3st
                       fetch dec exec predictNextPc
                       d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                       d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                       e2wPack e2wDecInst e2wVal init.
  Definition pdec := ProcDec.pdec fetch dec exec init.
  
  Hint Unfold p3st: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT p3st) => unfold p3st. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)

  Definition p3st_pdec_ruleMap (o: RegsT): string -> option string :=
    "reqLd" |-> "reqLd";
      "reqLdZ" |-> "reqLdZ";
      "reqSt" |-> "reqSt";
      "repLd" |-> "repLd";
      "repSt" |-> "repSt";
      "execToHost" |-> "execToHost";
      "wbNm" |-> "execNm";
      "wbNmZ" |-> "execNmZ"; ||.
  Hint Unfold p3st_pdec_ruleMap: MethDefs.

  Definition p3st_pdec_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Pc iaddrSize) <- r |> "pc";
       mlet pgmv : (Vector (Data instBytes) iaddrSize) <- r |> "pgm";
       mlet rfv : (Vector (Data dataBytes) rfIdx) <- r |> "rf";
       mlet d2eeltv : d2eElt <- r |> "d2e"--"elt";
       mlet d2efv : Bool <- r |> "d2e"--"full";
       mlet e2weltv : e2wElt <- r |> "e2w"--"elt";
       mlet e2wfv : Bool <- r |> "e2w"--"full";
       mlet w2deltv : Pc iaddrSize <- r |> "w2d"--"elt";
       mlet w2dfv : Bool <- r |> "w2d"--"full";
       mlet eev : Bool <- r |> "eEpoch";
       mlet stallv : Bool <- r |> "stall";
       mlet stalledv : d2eElt <- r |> "stalled";

       (["stall" <- existT _ _ stallv]
        +["pgm" <- existT _ _ pgmv]
        +["rf" <- existT _ _ rfv]
        +["pc" <- existT _ (SyntaxKind (Pc iaddrSize))
               (if w2dfv then w2deltv
                else if stallv then evalExpr (d2eCurPc _ stalledv)
                     else if e2wfv then
                            (if Bool.eqb eev (evalExpr (d2eEpoch _ (evalExpr (e2wDecInst _ e2weltv))))
                             then evalExpr (d2eCurPc _ (evalExpr (e2wDecInst _ e2weltv)))
                             else
                               (if d2efv then
                                 (if Bool.eqb eev (evalExpr (d2eEpoch _ d2eeltv))
                                  then evalExpr (d2eCurPc _ d2eeltv)
                                  else pcv)
                                else pcv))
                          else if d2efv then
                                 (if Bool.eqb eev (evalExpr (d2eEpoch _ d2eeltv))
                                  then evalExpr (d2eCurPc _ d2eeltv)
                                  else pcv)
                               else pcv)])%fmap)%mapping.
  Hint Unfold p3st_pdec_regMap: MapDefs.

  Ltac is_not_ife t :=
    match t with
    | context [if _ then _ else _] => fail 1
    | _ => idtac
    end.
  
  Ltac dest_if :=
    match goal with
    | [ |- context[if ?x then _ else _] ] =>
      let c := fresh "c" in is_not_ife x; remember x as c; destruct c
    | [H: context[if ?x then _ else _] |- _] =>
      let c := fresh "c" in is_not_ife x; remember x as c; destruct c
    end.

  Ltac d2e_abs_tac :=
    try rewrite Hd2eOpType in *;
    try rewrite Hd2eDst in *;
    try rewrite Hd2eAddr in *;
    try rewrite Hd2eVal1 in *;
    try rewrite Hd2eVal2 in *;
    try rewrite Hd2eRawInst in *;
    try rewrite Hd2eCurPc in *;
    try rewrite Hd2eNextPc in *;
    try rewrite Hd2eEpoch in *;
    try rewrite He2wDecInst in *;
    try rewrite He2wVal in *.

  Ltac kinv_bool :=
    repeat
      (try match goal with
           | [H: ?t = true |- _] => rewrite H in *
           | [H: ?t = false |- _] => rewrite H in *
           | [H: true = ?t |- _] => rewrite <-H in *
           | [H: false = ?t |- _] => rewrite <-H in *
           end; dest_if; kinv_simpl; intuition idtac).

  Ltac p3st_inv_tac := d2e_abs_tac; kinv_bool.

  Ltac p3st_dest_tac :=
    repeat match goal with
           | [H: context[p3st_epochs_inv] |- _] => destruct H
           | [H: context[p3st_pc_inv] |- _] => destruct H
           | [H: context[p3st_decode_inv] |- _] => destruct H
           | [H: context[p3st_stalled_inv] |- _] => destruct H
           | [H: context[p3st_raw_inv] |- _] => destruct H
           | [H: context[p3st_scoreboard_waw_inv] |- _] => destruct H
           | [H: context[p3st_exec_inv] |- _] => destruct H
           end;
    kinv_red.

  Definition p3stInl := ProcThreeStInl.p3stInl
                          fetch dec exec predictNextPc
                          d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                          d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                          e2wPack e2wDecInst e2wVal init.

  Definition p3stConfig :=
    {| inlining := ITProvided p3stInl;
       decomposition := DTFunctional p3st_pdec_regMap p3st_pdec_ruleMap;
       invariants := IVCons p3st_inv_ok IVNil
    |}.

  Theorem p3st_refines_pdec:
    p3st <<== pdec.
  Proof. (* SKIP_PROOF_ON
    kami_ok p3stConfig p3st_dest_tac p3st_inv_tac.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End ProcThreeStDec.

