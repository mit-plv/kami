Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.SC Ex.ProcDec Ex.ProcTwoStage Ex.ProcTwoStInl Ex.ProcTwoStInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcTwoStDec.
  Variables addrSize lgDataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT lgDataBytes)
            (getLdDst: LdDstT lgDataBytes rfIdx)
            (getLdAddr: LdAddrT addrSize lgDataBytes)
            (getLdSrc: LdSrcT lgDataBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize lgDataBytes)
            (getStAddr: StAddrT addrSize lgDataBytes)
            (getStSrc: StSrcT lgDataBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize lgDataBytes)
            (getStVSrc: StVSrcT lgDataBytes rfIdx)
            (getSrc1: Src1T lgDataBytes rfIdx)
            (getSrc2: Src2T lgDataBytes rfIdx)
            (getDst: DstT lgDataBytes rfIdx)
            (exec: ExecT addrSize lgDataBytes)
            (getNextPc: NextPcT addrSize lgDataBytes rfIdx)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* rawInst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* curPc *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* nextPc *)
                Expr ty (SyntaxKind Bool) -> (* epoch *)
                Expr ty (SyntaxKind d2eElt)).
  Variables
    (d2eOpType: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit 2)))
    (d2eDst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Bit rfIdx)))
    (d2eAddr: forall ty, fullType ty (SyntaxKind d2eElt) ->
                         Expr ty (SyntaxKind (Bit addrSize)))
    (d2eVal: forall ty, fullType ty (SyntaxKind d2eElt) ->
                        Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
    (d2eEpoch: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind Bool)).

  Hypotheses (Hd2eOpType: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eOpType _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr opType)
             (Hd2eDst: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eDst _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr dst)
             (Hd2eAddr: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eAddr _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr addr)
             (Hd2eVal: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eVal _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr val)
             (Hd2eRawInst: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eRawInst _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr rawInst)
             (Hd2eCurPc: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eCurPc _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr curPc)
             (Hd2eNextPc: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eNextPc _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr nextPc)
             (Hd2eEpoch: forall opType dst addr val rawInst curPc nextPc epoch,
                 evalExpr (d2eEpoch _ (evalExpr (d2ePack opType dst addr val rawInst curPc nextPc epoch))) = evalExpr epoch).

  Definition p2st := ProcTwoStage.p2st
                       getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc predictNextPc
                       d2ePack d2eOpType d2eDst d2eAddr d2eVal
                       d2eRawInst d2eCurPc d2eNextPc d2eEpoch.
  Definition pdec := ProcDec.pdec
                       getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                       getStAddr getStSrc calcStAddr getStVSrc
                       getSrc1 getSrc2 getDst exec getNextPc.
  
  Hint Unfold p2st: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT p2st) => unfold p2st. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)

  Definition p2st_pdec_ruleMap (o: RegsT): string -> option string :=
    "reqLd" |-> "reqLd";
      "reqLdZ" |-> "reqLdZ";
      "reqSt" |-> "reqSt";
      "repLd" |-> "repLd";
      "repSt" |-> "repSt";
      "execToHost" |-> "execToHost";
      "execNm" |-> "execNm"; ||.
  Hint Unfold p2st_pdec_ruleMap: MethDefs.

  Definition p2st_pdec_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit addrSize) <- r |> "pc";
       mlet pgmv : (Vector (Data lgDataBytes) addrSize) <- r |> "pgm";
       mlet rfv : (Vector (Data lgDataBytes) rfIdx) <- r |> "rf";
       mlet d2eeltv : d2eElt <- r |> "d2e"--"elt";
       mlet d2efv : Bool <- r |> "d2e"--"full";
       mlet e2deltv : Bit addrSize <- r |> "e2d"--"elt";
       mlet e2dfv : Bool <- r |> "e2d"--"full";
       mlet eev : Bool <- r |> "eEpoch";
       mlet stallv : Bool <- r |> "stall";
       mlet stalledv : d2eElt <- r |> "stalled";

       (["stall" <- existT _ _ stallv]
        +["pgm" <- existT _ _ pgmv]
        +["rf" <- existT _ _ rfv]
        +["pc" <- existT _ (SyntaxKind (Bit addrSize))
               (if stallv then evalExpr (d2eCurPc _ stalledv)
                else if e2dfv then e2deltv
                     else if d2efv then
                            if eqb eev (evalExpr (d2eEpoch _ d2eeltv))
                            then evalExpr (d2eCurPc _ d2eeltv)
                            else pcv
                          else pcv)])%fmap)%mapping.
  Hint Unfold p2st_pdec_regMap: MapDefs.

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
    try rewrite Hd2eVal in *;
    try rewrite Hd2eRawInst in *;
    try rewrite Hd2eCurPc in *;
    try rewrite Hd2eNextPc in *;
    try rewrite Hd2eEpoch in *.

  Ltac kinv_bool :=
    repeat
      (try match goal with
           | [H: ?t = true |- _] => rewrite H in *
           | [H: ?t = false |- _] => rewrite H in *
           | [H: true = ?t |- _] => rewrite <-H in *
           | [H: false = ?t |- _] => rewrite <-H in *
           end; dest_if; kinv_simpl; intuition idtac).

  Ltac p2st_inv_tac :=
    repeat match goal with
           | [H: context[p2st_pc_epochs_inv] |- _] => destruct H
           | [H: context[p2st_decode_inv] |- _] => destruct H
           | [H: context[p2st_stalled_inv] |- _] => destruct H
           | [H: context[p2st_raw_inv] |- _] => destruct H
           | [H: context[p2st_scoreboard_inv] |- _] => destruct H
           end;
    kinv_red.

  Definition p2stInl := ProcTwoStInl.p2stInl getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                             getStAddr getStSrc calcStAddr getStVSrc
                                             getSrc1 getSrc2 getDst exec getNextPc predictNextPc
                                             d2ePack d2eOpType d2eDst d2eAddr d2eVal
                                             d2eRawInst d2eCurPc d2eNextPc d2eEpoch.

  Theorem p2st_refines_pdec:
    p2st <<== pdec.
  Proof. (* SKIP_PROOF_ON
    (* instead of: kinline_left im. *)
    ketrans; [exact (projT2 p2stInl)|].
    kdecompose_nodefs p2st_pdec_regMap p2st_pdec_ruleMap.

    kinv_add p2st_inv_ok.
    kinv_add_end.

    kinvert.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr; kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr; kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr; kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr; kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr; kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr; kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr;
        try (kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool; fail).
      Opaque evalExpr.
      kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
      Transparent evalExpr.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr;
        try (kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool; fail).
      meq; do 2 f_equal; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr;
        try (kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool; fail).
      Opaque evalExpr.
      kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
      Transparent evalExpr.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr;
        kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr;
        kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr;
        try (kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool; fail).
      meq; do 2 f_equal; kinv_finish_with kinv_bool.
    - kinv_action_dest;
        kinv_custom p2st_inv_tac;
        kinv_regmap_red;
        kinv_constr;
        try (kinv_eq; d2e_abs_tac; kinv_finish_with kinv_bool; fail).
      meq; do 2 f_equal; kinv_finish_with kinv_bool.

      END_SKIP_PROOF_ON *) admit.

  Qed.

End ProcTwoStDec.

