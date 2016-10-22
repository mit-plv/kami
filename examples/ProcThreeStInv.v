Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic Ex.ProcThreeStage Ex.ProcThreeStInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Section Invariants.
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
            (alignPc: AlignPcT addrSize)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Variable (d2eElt: Kind).
  Variable (d2ePack:
              forall ty,
                Expr ty (SyntaxKind (Bit 2)) -> (* opTy *)
                Expr ty (SyntaxKind (Bit rfIdx)) -> (* dst *)
                Expr ty (SyntaxKind (Bit addrSize)) -> (* addr *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val1 *)
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* val2 *)
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
    (d2eVal1 d2eVal2: forall ty, fullType ty (SyntaxKind d2eElt) ->
                                 Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eRawInst: forall ty, fullType ty (SyntaxKind d2eElt) ->
                            Expr ty (SyntaxKind (Data lgDataBytes)))
    (d2eCurPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                          Expr ty (SyntaxKind (Bit addrSize)))
    (d2eNextPc: forall ty, fullType ty (SyntaxKind d2eElt) ->
                           Expr ty (SyntaxKind (Bit addrSize)))
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
                Expr ty (SyntaxKind (Data lgDataBytes)) -> (* execVal *)
                Expr ty (SyntaxKind e2wElt)).
  Variables
    (e2wDecInst: forall ty, fullType ty (SyntaxKind e2wElt) ->
                            Expr ty (SyntaxKind d2eElt))
    (e2wVal: forall ty, fullType ty (SyntaxKind e2wElt) ->
                        Expr ty (SyntaxKind (Data lgDataBytes))).

  Hypotheses
    (He2wDecInst: forall decInst val,
        evalExpr (e2wDecInst _ (evalExpr (e2wPack decInst val))) = evalExpr decInst)
    (He2wVal: forall decInst val,
        evalExpr (e2wVal _ (evalExpr (e2wPack decInst val))) = evalExpr val).

  Definition p3stInl := projT1 (p3stInl getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                        getStAddr getStSrc calcStAddr getStVSrc
                                        getSrc1 getSrc2 getDst exec getNextPc alignPc predictNextPc
                                        d2ePack d2eOpType d2eDst d2eAddr d2eVal1 d2eVal2
                                        d2eRawInst d2eCurPc d2eNextPc d2eEpoch
                                        e2wPack e2wDecInst e2wVal).

  (** Now invariants are defined below *)

  Definition p3st_scoreboard_waw_inv_body
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2eeltv: fullType type (SyntaxKind d2eElt))
             (e2wfullv: fullType type (SyntaxKind Bool))
             (e2weltv: fullType type (SyntaxKind e2wElt))
             (stallv: fullType type (SyntaxKind Bool))
             (stalledv: fullType type (SyntaxKind d2eElt))
             (sbv: fullType type (SyntaxKind (Vector Bool rfIdx))) :=
    (d2efullv = true ->
     ((evalExpr (d2eOpType _ d2eeltv) = opLd ->
       sbv (evalExpr (d2eDst _ d2eeltv)) = true) /\
      (evalExpr (d2eOpType _ d2eeltv) = opNm ->
       sbv (evalExpr (d2eDst _ d2eeltv)) = true))) /\
    (e2wfullv = true ->
     let decInst := evalExpr (e2wDecInst _ e2weltv) in
     ((evalExpr (d2eOpType _ decInst) = opLd ->
       sbv (evalExpr (d2eDst _ decInst)) = true) /\
      (evalExpr (d2eOpType _ decInst) = opNm ->
       sbv (evalExpr (d2eDst _ decInst)) = true))) /\
    (stallv = true ->
     ((evalExpr (d2eOpType _ stalledv) = opLd ->
       sbv (evalExpr (d2eDst _ stalledv)) = true) /\
      (evalExpr (d2eOpType _ stalledv) = opNm ->
       sbv (evalExpr (d2eDst _ stalledv)) = true))) /\
    (d2efullv = true -> e2wfullv = true ->
     let decInst := evalExpr (e2wDecInst _ e2weltv) in
     (evalExpr (d2eOpType _ d2eeltv) = opLd \/ evalExpr (d2eOpType _ d2eeltv) = opNm) ->
     (evalExpr (d2eOpType _ decInst) = opLd \/ evalExpr (d2eOpType _ decInst) = opNm) ->
     evalExpr (d2eDst _ d2eeltv) <> evalExpr (d2eDst _ decInst)) /\
    (d2efullv = true -> stallv = true ->
     (evalExpr (d2eOpType _ d2eeltv) = opLd \/ evalExpr (d2eOpType _ d2eeltv) = opNm) ->
     (evalExpr (d2eOpType _ stalledv) = opLd \/ evalExpr (d2eOpType _ stalledv) = opNm) ->
     evalExpr (d2eDst _ d2eeltv) <> evalExpr (d2eDst _ stalledv)) /\
    (e2wfullv = true -> stallv = true ->
     let decInst := evalExpr (e2wDecInst _ e2weltv) in
     (evalExpr (d2eOpType _ decInst) = opLd \/ evalExpr (d2eOpType _ decInst) = opNm) ->
     (evalExpr (d2eOpType _ stalledv) = opLd \/ evalExpr (d2eOpType _ stalledv) = opNm) ->
     evalExpr (d2eDst _ decInst) <> evalExpr (d2eDst _ stalledv)).
  
  Record p3st_scoreboard_waw_inv (o: RegsT) : Prop :=
    { sbv0 : fullType type (SyntaxKind (Vector Bool rfIdx));
      Hsbv0 : M.find "sbFlags"%string o = Some (existT _ _ sbv0);
      
      d2eeltv0 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv0 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv0);
      d2efullv0 : fullType type (SyntaxKind Bool);
      Hd2efullv0 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv0);

      e2weltv0 : fullType type (SyntaxKind e2wElt);
      He2weltv0 : M.find "e2w"--"elt"%string o = Some (existT _ _ e2weltv0);
      e2wfullv0 : fullType type (SyntaxKind Bool);
      He2wfullv0 : M.find "e2w"--"full"%string o = Some (existT _ _ e2wfullv0);

      stallv0 : fullType type (SyntaxKind Bool);
      Hstallv0 : M.find "stall"%string o = Some (existT _ _ stallv0);
      stalledv0 : fullType type (SyntaxKind d2eElt);
      Hstalledv0 : M.find "stalled"%string o = Some (existT _ _ stalledv0);

      Hinv0 : p3st_scoreboard_waw_inv_body d2efullv0 d2eeltv0 e2wfullv0 e2weltv0
                                           stallv0 stalledv0 sbv0 }.

  (* NOTE: this invariant requires p3st_scoreboard_waw_inv *)
  Definition p3st_raw_inv_body
             (prevv nextv: fullType type (SyntaxKind Bool))
             (preveltv nexteltv: fullType type (SyntaxKind d2eElt)) :=
    prevv = true -> nextv = true ->
    (evalExpr (d2eOpType _ nexteltv) = opLd \/ evalExpr (d2eOpType _ nexteltv) = opNm) ->
    ((evalExpr (d2eOpType _ preveltv) = opSt ->
      (evalExpr (d2eDst _ nexteltv) <> evalExpr (getStSrc _ (evalExpr (d2eRawInst _ preveltv))) /\
       evalExpr (d2eDst _ nexteltv) <> evalExpr (getStVSrc _ (evalExpr (d2eRawInst _ preveltv))))) /\
     (evalExpr (d2eOpType _ preveltv) = opLd ->
      evalExpr (d2eDst _ nexteltv) <> evalExpr (getLdSrc _ (evalExpr (d2eRawInst _ preveltv)))) /\
     (evalExpr (d2eOpType _ preveltv) = opTh ->
      evalExpr (d2eDst _ nexteltv) <> evalExpr (getSrc1 _ (evalExpr (d2eRawInst _ preveltv)))) /\
     (evalExpr (d2eOpType _ preveltv) = opNm ->
      (evalExpr (d2eDst _ nexteltv) <> evalExpr (getSrc1 _ (evalExpr (d2eRawInst _ preveltv))) /\
       evalExpr (d2eDst _ nexteltv) <> evalExpr (getSrc2 _ (evalExpr (d2eRawInst _ preveltv)))))).
  
  Record p3st_raw_inv (o: RegsT) : Prop :=
    { d2eeltv1 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv1 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv1);
      d2efullv1 : fullType type (SyntaxKind Bool);
      Hd2efullv1 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv1);

      e2weltv1 : fullType type (SyntaxKind e2wElt);
      He2weltv1 : M.find "e2w"--"elt"%string o = Some (existT _ _ e2weltv1);
      e2wfullv1 : fullType type (SyntaxKind Bool);
      He2wfullv1 : M.find "e2w"--"full"%string o = Some (existT _ _ e2wfullv1);

      stallv1 : fullType type (SyntaxKind Bool);
      Hstallv1 : M.find "stall"%string o = Some (existT _ _ stallv1);
      stalledv1 : fullType type (SyntaxKind d2eElt);
      Hstalledv1 : M.find "stalled"%string o = Some (existT _ _ stalledv1);

      Hd2einv1 : p3st_raw_inv_body d2efullv1 stallv1 d2eeltv1 stalledv1;
      He2winv1 : p3st_raw_inv_body e2wfullv1 stallv1 (evalExpr (e2wDecInst _ e2weltv1)) stalledv1;
      Hd2winv1 : p3st_raw_inv_body d2efullv1 e2wfullv1 d2eeltv1 (evalExpr (e2wDecInst _ e2weltv1))
    }.

  (* NOTE: this invariant requires p3st_raw_inv *)
  Definition p3st_decode_inv_body
             (pgmv: fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize)))
             (rfv: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (d2eeltv: fullType type (SyntaxKind d2eElt))
             (d2efullv: fullType type (SyntaxKind Bool)) :=
    d2efullv = true ->
    let rawInst := evalExpr (d2eRawInst _ d2eeltv) in
    (rawInst = pgmv (evalExpr (alignPc _ (evalExpr (d2eCurPc _ d2eeltv)))) /\
     evalExpr (d2eOpType _ d2eeltv) = evalExpr (getOptype _ rawInst) /\
     (evalExpr (d2eOpType _ d2eeltv) = opLd ->
      (evalExpr (d2eDst _ d2eeltv) = evalExpr (getLdDst _ rawInst) /\
       evalExpr (d2eAddr _ d2eeltv) =
       evalExpr (calcLdAddr _ (evalExpr (getLdAddr _ rawInst))
                            (rfv (evalExpr (getLdSrc _ rawInst)))))) /\
     (evalExpr (d2eOpType _ d2eeltv) = opSt ->
      evalExpr (d2eAddr _ d2eeltv) =
      evalExpr (calcStAddr _ (evalExpr (getStAddr _ rawInst))
                           (rfv (evalExpr (getStSrc _ rawInst)))) /\
      evalExpr (d2eVal1 _ d2eeltv) = rfv (evalExpr (getStVSrc _ rawInst)))) /\
    (evalExpr (d2eOpType _ d2eeltv) = opTh ->
     evalExpr (d2eVal1 _ d2eeltv) = rfv (evalExpr (getSrc1 _ rawInst))) /\
    (evalExpr (d2eOpType _ d2eeltv) = opNm ->
     (evalExpr (d2eDst _ d2eeltv) = evalExpr (getDst _ rawInst) /\
      evalExpr (d2eVal1 _ d2eeltv) = rfv (evalExpr (getSrc1 _ rawInst)) /\
      evalExpr (d2eVal2 _ d2eeltv) = rfv (evalExpr (getSrc2 _ rawInst)))).

  Record p3st_decode_inv (o: RegsT) : Prop :=
    { pgmv2 : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv2 : M.find "pgm"%string o = Some (existT _ _ pgmv2);

      rfv2 : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv2 : M.find "rf"%string o = Some (existT _ _ rfv2);

      d2eeltv2 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv2 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv2);
      d2efullv2 : fullType type (SyntaxKind Bool);
      Hd2efullv2 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv2);

      e2weltv2 : fullType type (SyntaxKind e2wElt);
      He2weltv2 : M.find "e2w"--"elt"%string o = Some (existT _ _ e2weltv2);
      e2wfullv2 : fullType type (SyntaxKind Bool);
      He2wfullv2 : M.find "e2w"--"full"%string o = Some (existT _ _ e2wfullv2);

      Hd2einv2 : p3st_decode_inv_body pgmv2 rfv2 d2eeltv2 d2efullv2;
      He2winv2 : p3st_decode_inv_body pgmv2 rfv2 (evalExpr (e2wDecInst _ e2weltv2)) e2wfullv2
    }.

  (* NOTE: this invariant requires p3st_decode_inv *)
  Definition p3st_stalled_inv_body
             (pgmv: fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize)))
             (rfv: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (stallv: fullType type (SyntaxKind Bool))
             (stalledv: fullType type (SyntaxKind d2eElt)) :=
    stallv = true ->
    let rawInst := evalExpr (d2eRawInst _ stalledv) in
    evalExpr (d2eOpType _ stalledv) = evalExpr (getOptype _ rawInst) /\
    rawInst = pgmv (evalExpr (alignPc _ (evalExpr (d2eCurPc _ stalledv)))) /\
    (evalExpr (d2eOpType _ stalledv) = opLd ->
     evalExpr (d2eDst _ stalledv) = evalExpr (getLdDst _ rawInst)).

  Record p3st_stalled_inv (o: RegsT) : Prop :=
    { pgmv3 : fullType type (SyntaxKind (Vector (Data lgDataBytes) addrSize));
      Hpgmv3 : M.find "pgm"%string o = Some (existT _ _ pgmv3);

      rfv3 : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv3 : M.find "rf"%string o = Some (existT _ _ rfv3);

      stallv3 : fullType type (SyntaxKind Bool);
      Hstallv3 : M.find "stall"%string o = Some (existT _ _ stallv3);
      stalledv3 : fullType type (SyntaxKind d2eElt);
      Hstalledv3 : M.find "stalled"%string o = Some (existT _ _ stalledv3);

      Hinv3 : p3st_stalled_inv_body pgmv3 rfv3 stallv3 stalledv3 }.

  Definition p3st_exec_inv_body
             (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (rfv: fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx)))
             (e2wfullv: fullType type (SyntaxKind Bool))
             (e2weltv: fullType type (SyntaxKind e2wElt)) :=
    e2wfullv = true ->
    let d2eeltv := evalExpr (e2wDecInst _ e2weltv) in
    let rawInst := evalExpr (d2eRawInst _ d2eeltv) in
    evalExpr (d2eOpType _ d2eeltv) = opNm ->
    evalExpr (e2wVal _ e2weltv) =
    evalExpr (exec _ (rfv (evalExpr (getSrc1 _ rawInst))) (rfv (evalExpr (getSrc2 _ rawInst)))
                   (evalExpr (d2eCurPc _ d2eeltv)) rawInst).

  Record p3st_exec_inv (o: RegsT) : Prop :=
    { pcv4 : fullType type (SyntaxKind (Bit addrSize));
      Hpcv4 : M.find "pc"%string o = Some (existT _ _ pcv4);
      rfv4 : fullType type (SyntaxKind (Vector (Data lgDataBytes) rfIdx));
      Hrfv4 : M.find "rf"%string o = Some (existT _ _ rfv4);

      e2weltv4 : fullType type (SyntaxKind e2wElt);
      He2weltv4 : M.find "e2w"--"elt"%string o = Some (existT _ _ e2weltv4);
      e2wfullv4 : fullType type (SyntaxKind Bool);
      He2wfullv4 : M.find "e2w"--"full"%string o = Some (existT _ _ e2wfullv4);

      Hinv4 : p3st_exec_inv_body pcv4 rfv4 e2wfullv4 e2weltv4 }.

  Definition p3st_epochs_inv_body
             (fepochv eepochv d2efullv e2wfullv w2dfullv stallv: fullType type (SyntaxKind Bool))
             (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (d2eeltv: fullType type (SyntaxKind d2eElt))
             (e2weltv: fullType type (SyntaxKind e2wElt))
             (stalledv: fullType type (SyntaxKind d2eElt)) :=
    (fepochv = eepochv -> w2dfullv = false) /\ (w2dfullv = false -> fepochv = eepochv) /\
    (fepochv <> eepochv -> w2dfullv = true) /\ (w2dfullv = true -> fepochv <> eepochv) /\

    (* fepoch: w2d and {d2e, e2w} *)
    (w2dfullv = true ->
     ((d2efullv = true -> evalExpr (d2eEpoch _ d2eeltv) = fepochv) /\
      (e2wfullv = true -> evalExpr (d2eEpoch _ (evalExpr (e2wDecInst _ e2weltv))) = fepochv))) /\
    (d2efullv = true -> e2wfullv = true ->
     evalExpr (d2eEpoch _ (evalExpr (e2wDecInst _ e2weltv))) = fepochv ->
     evalExpr (d2eEpoch _ d2eeltv) = fepochv) /\
     
    (* w2d and stalled *)
    (w2dfullv = true -> stallv = false) /\ (stallv = true -> w2dfullv = false) /\
    (fepochv = eepochv -> stallv = true ->
     ((d2efullv = true -> evalExpr (d2eEpoch _ d2eeltv) = fepochv) /\
      (e2wfullv = true -> evalExpr (d2eEpoch _ (evalExpr (e2wDecInst _ e2weltv))) = fepochv))) /\

    (* eepoch: w2d and {d2e, e2w} *)
    (d2efullv = true -> evalExpr (d2eEpoch _ d2eeltv) = eepochv -> w2dfullv = false) /\
    (e2wfullv = true -> evalExpr (d2eEpoch _ (evalExpr (e2wDecInst _ e2weltv))) = eepochv ->
     w2dfullv = false).

  Record p3st_epochs_inv (o: RegsT) : Prop :=
    { pcv5 : fullType type (SyntaxKind (Bit addrSize));
      Hpcv5 : M.find "pc"%string o = Some (existT _ _ pcv5);
      fepochv5 : fullType type (SyntaxKind Bool);
      Hfepochv5 : M.find "fEpoch"%string o = Some (existT _ _ fepochv5);

      d2eeltv5 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv5 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv5);
      d2efullv5 : fullType type (SyntaxKind Bool);
      Hd2efullv5 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv5);

      (* NOTE: Don't remove w2dElt even if it's not used in the invariant body. *)
      w2deltv5 : fullType type (SyntaxKind (w2dElt addrSize));
      Hw2deltv5 : M.find "w2d"--"elt"%string o = Some (existT _ _ w2deltv5);
      w2dfullv5 : fullType type (SyntaxKind Bool);
      Hw2dfullv5 : M.find "w2d"--"full"%string o = Some (existT _ _ w2dfullv5);

      e2weltv5 : fullType type (SyntaxKind e2wElt);
      He2weltv5 : M.find "e2w"--"elt"%string o = Some (existT _ _ e2weltv5);
      e2wfullv5 : fullType type (SyntaxKind Bool);
      He2wfullv5 : M.find "e2w"--"full"%string o = Some (existT _ _ e2wfullv5);

      stallv5 : fullType type (SyntaxKind Bool);
      Hstallv5 : M.find "stall"%string o = Some (existT _ _ stallv5);
      stalledv5 : fullType type (SyntaxKind d2eElt);
      Hstalledv5 : M.find "stalled"%string o = Some (existT _ _ stalledv5);

      eepochv5 : fullType type (SyntaxKind Bool);
      Heepochv5 : M.find "eEpoch"%string o = Some (existT _ _ eepochv5);
      
      Hinv5 : p3st_epochs_inv_body fepochv5 eepochv5 d2efullv5 e2wfullv5 w2dfullv5 stallv5
                                   pcv5 d2eeltv5 e2weltv5 stalledv5 }.

  Definition p3st_pc_inv_body
             (fepochv eepochv d2efullv e2wfullv w2dfullv stallv: fullType type (SyntaxKind Bool))
             (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (d2eeltv: fullType type (SyntaxKind d2eElt))
             (e2weltv: fullType type (SyntaxKind e2wElt))
             (stalledv: fullType type (SyntaxKind d2eElt)) :=
    (* pc: d2e *)
    (d2efullv = true -> evalExpr (d2eEpoch _ d2eeltv) = fepochv ->
     evalExpr (d2eNextPc _ d2eeltv) = pcv) /\
    (* pc: e2w *)
    (e2wfullv = true ->
     ((d2efullv = true ->
       evalExpr (d2eEpoch _ (evalExpr (e2wDecInst _ e2weltv))) = evalExpr (d2eEpoch _ d2eeltv) ->
       evalExpr (d2eNextPc _ (evalExpr (e2wDecInst _ e2weltv))) = evalExpr (d2eCurPc _ d2eeltv)) /\
      (d2efullv = false ->
       evalExpr (d2eEpoch _ (evalExpr (e2wDecInst _ e2weltv))) = fepochv ->
       evalExpr (d2eNextPc _ (evalExpr (e2wDecInst _ e2weltv))) = pcv))) /\
    (* pc: stalled *)
    (stallv = true ->
     ((e2wfullv = true -> evalExpr (d2eNextPc _ stalledv) =
                          evalExpr (d2eCurPc _ (evalExpr (e2wDecInst _ e2weltv)))) /\
      (e2wfullv = false -> d2efullv = true ->
       evalExpr (d2eNextPc _ stalledv) = evalExpr (d2eCurPc _ d2eeltv)) /\
      (e2wfullv = false -> d2efullv = false -> evalExpr (d2eNextPc _ stalledv) = pcv))).

  Record p3st_pc_inv (o: RegsT) : Prop :=
    { pcv6 : fullType type (SyntaxKind (Bit addrSize));
      Hpcv6 : M.find "pc"%string o = Some (existT _ _ pcv6);
      fepochv6 : fullType type (SyntaxKind Bool);
      Hfepochv6 : M.find "fEpoch"%string o = Some (existT _ _ fepochv6);

      d2eeltv6 : fullType type (SyntaxKind d2eElt);
      Hd2eeltv6 : M.find "d2e"--"elt"%string o = Some (existT _ _ d2eeltv6);
      d2efullv6 : fullType type (SyntaxKind Bool);
      Hd2efullv6 : M.find "d2e"--"full"%string o = Some (existT _ _ d2efullv6);

      w2dfullv6 : fullType type (SyntaxKind Bool);
      Hw2dfullv6 : M.find "w2d"--"full"%string o = Some (existT _ _ w2dfullv6);

      e2weltv6 : fullType type (SyntaxKind e2wElt);
      He2weltv6 : M.find "e2w"--"elt"%string o = Some (existT _ _ e2weltv6);
      e2wfullv6 : fullType type (SyntaxKind Bool);
      He2wfullv6 : M.find "e2w"--"full"%string o = Some (existT _ _ e2wfullv6);

      stallv6 : fullType type (SyntaxKind Bool);
      Hstallv6 : M.find "stall"%string o = Some (existT _ _ stallv6);
      stalledv6 : fullType type (SyntaxKind d2eElt);
      Hstalledv6 : M.find "stalled"%string o = Some (existT _ _ stalledv6);

      eepochv6 : fullType type (SyntaxKind Bool);
      Heepochv6 : M.find "eEpoch"%string o = Some (existT _ _ eepochv6);
      
      Hinv6 : p3st_pc_inv_body fepochv6 eepochv6 d2efullv6 e2wfullv6 w2dfullv6 stallv6
                               pcv6 d2eeltv6 e2weltv6 stalledv6 }.

  Hint Unfold p3st_scoreboard_waw_inv_body p3st_raw_inv_body
       p3st_decode_inv_body p3st_stalled_inv_body
       p3st_exec_inv_body p3st_epochs_inv_body
       p3st_pc_inv_body : InvDefs.

  Ltac p3st_inv_old :=
    repeat match goal with
           | [H: p3st_scoreboard_waw_inv _ |- _] => destruct H
           | [H: p3st_raw_inv _ |- _] => destruct H
           | [H: p3st_decode_inv _ |- _] => destruct H
           | [H: p3st_stalled_inv _ |- _] => destruct H
           | [H: p3st_exec_inv _ |- _] => destruct H
           | [H: p3st_epochs_inv _ |- _] => destruct H
           | [H: p3st_pc_inv _ |- _] => destruct H
           end;
    kinv_red.

  Ltac p3st_inv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kregmap_clear; (* for improving performance *)
    kinv_red; (* unfolding invariant definitions *)
    repeat (* cheaper than "intuition" *)
      (match goal with
       | [ |- _ /\ _ ] => split
       end);
    try eassumption; intros; try reflexivity;
    intuition kinv_simpl; intuition idtac.

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
    try rewrite He2wVal in *;
    intuition idtac.

  Ltac p3st_inv_tac := p3st_inv_old; p3st_inv_new; d2e_abs_tac.
  
  Lemma p3st_epochs_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p3stInl) ->
      Multistep p3stInl init n ll ->
      p3st_epochs_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p3st_inv_old.
      unfold getRegInits, fst, p3stInl, ProcThreeStInl.p3stInl, projT1.
      p3st_inv_new; simpl in *; kinv_simpl.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p3st_inv_tac;
          try (destruct x0, eepochv5; intuition idtac; fail).
        rewrite H14 in H4; exfalso; eapply negb_eq_false; eauto.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
        rewrite H4 in H2; exfalso; eapply negb_eq_false; eauto.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
        rewrite H4 in H2; exfalso; eapply negb_eq_false; eauto.
      + kinv_dest_custom p3st_inv_tac.
        rewrite H4 in H2; exfalso; eapply negb_eq_false; eauto.
      + kinv_dest_custom p3st_inv_tac.
        rewrite H4 in H2; exfalso; eapply negb_eq_false; eauto.

        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma p3st_pc_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p3stInl) ->
      Multistep p3stInl init n ll ->
      p3st_pc_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p3st_inv_old.
      unfold getRegInits, fst, p3stInl, ProcThreeStInl.p3stInl, projT1.
      p3st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p3st_epochs_inv_ok' H H0).
      kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
        rewrite H10 in H8; intuition idtac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
        rewrite H10 in H8; intuition idtac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.

        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma p3st_scoreboard_waw_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p3stInl) ->
      Multistep p3stInl init n ll ->
      p3st_scoreboard_waw_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - p3st_inv_old.
      unfold getRegInits, p3stInl, ProcThreeStInl.p3stInl, projT1.
      p3st_inv_new; simpl in *; kinv_simpl.

    - kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac; try (find_if_inside; intuition idtac; fail);
          try (simpl in H7; rewrite H7 in H10; rewrite H10 in H9; inv H9; fail);
          try (simpl in H7; rewrite H7 in H10; rewrite H10 in H6; inv H6; fail).
      + kinv_dest_custom p3st_inv_tac; try (rewrite e in H2; inv H2; fail);
          try (rewrite e in H8; inv H8; fail).
      + kinv_dest_custom p3st_inv_tac; try (rewrite e in H2; inv H2; fail);
          try (rewrite e in H7; inv H7; fail).
      + kinv_dest_custom p3st_inv_tac; try (find_if_inside; intuition idtac; fail);
          try (simpl in H7; rewrite H7 in H10; rewrite H10 in H9; inv H9; fail);
          try (simpl in H7; rewrite H7 in H10; rewrite H10 in H6; inv H6; fail).
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac;
          try (apply eq_sym, orb_true_iff in Heqic; destruct Heqic;
               try (kinv_simpl; find_if_inside; intuition idtac)).
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac; try (find_if_inside; intuition idtac; fail).
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac; try (find_if_inside; intuition idtac; fail).
      + kinv_dest_custom p3st_inv_tac; try (find_if_inside; intuition idtac; fail).

        END_SKIP_PROOF_ON *) apply cheat.
  Qed.
  
  Lemma p3st_raw_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p3stInl) ->
      Multistep p3stInl init n ll ->
      p3st_raw_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p3st_inv_old.
      unfold getRegInits, fst, p3stInl, ProcThreeStInl.p3stInl, projT1.
      p3st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p3st_scoreboard_waw_inv_ok' H H0).
      kinvert.      
      + mred.
      + mred.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac; try (rewrite e in H7; inv H7; fail);
          try (rewrite e in H8; inv H8; fail);
          try (rewrite e in H9; inv H9; fail).
        * simpl in H9; rewrite H9 in H3; unfold LdSrcK in *; rewrite H3 in H4; inv H4.
        * simpl in H9; rewrite H9 in H3; unfold LdSrcK in *; rewrite H3 in H4; inv H4.
        * simpl in H12; rewrite H12 in H10; unfold LdSrcK in *; rewrite H10 in H4; inv H4.
        * simpl in H12; rewrite H12 in H10; unfold LdSrcK in *; rewrite H10 in H4; inv H4.
      + kinv_dest_custom p3st_inv_tac; try (rewrite e in H7; inv H7; fail);
          try (rewrite e in H8; inv H8; fail);
          try (rewrite e in H9; inv H9; fail).
        * simpl in H9; rewrite H9 in H3; unfold StSrcK in *; rewrite H3 in H4; inv H4.
        * simpl in H9; rewrite H9 in H3; unfold StVSrcK in *; rewrite H3 in H11; inv H11.
        * simpl in H9; rewrite H9 in H3; unfold StSrcK in *; rewrite H3 in H4; inv H4.
        * simpl in H9; rewrite H9 in H3; unfold StVSrcK in *; rewrite H3 in H11; inv H11.
        * simpl in H12; rewrite H12 in H10; unfold StSrcK in *; rewrite H10 in H4; inv H4.
        * simpl in H12; rewrite H12 in H10; unfold StVSrcK in *; rewrite H10 in H11; inv H11.
        * simpl in H12; rewrite H12 in H10; unfold StSrcK in *; rewrite H10 in H4; inv H4.
        * simpl in H12; rewrite H12 in H10; unfold StVSrcK in *; rewrite H10 in H11; inv H11.
      + kinv_dest_custom p3st_inv_tac; try (rewrite e in H7; inv H7; fail);
          try (rewrite e in H4; inv H4; fail);
          try (rewrite e in H8; inv H8; fail).
        * simpl in H9; rewrite H9 in H3; unfold Src1K in *; rewrite H3 in H13; inv H13.
        * simpl in H9; rewrite H9 in H3; unfold Src1K in *; rewrite H3 in H13; inv H13.
        * simpl in H10; rewrite H10 in H9; unfold Src1K in *; rewrite H9 in H13; inv H13.
        * simpl in H10; rewrite H10 in H9; unfold Src1K in *; rewrite H9 in H13; inv H13.
      + kinv_dest_custom p3st_inv_tac; try (rewrite e in H7; inv H7; fail);
          try (rewrite e in H8; inv H8; fail);
          try (rewrite e in H9; inv H9; fail).
        * simpl in H9; rewrite H9 in H3; unfold Src1K in *; rewrite H3 in H4; inv H4.
        * simpl in H9; rewrite H9 in H3; unfold Src2K in *; rewrite H3 in H15; inv H15.
        * simpl in H9; rewrite H9 in H3; unfold Src1K in *; rewrite H3 in H4; inv H4.
        * simpl in H9; rewrite H9 in H3; unfold Src2K in *; rewrite H3 in H15; inv H15.
        * simpl in H12; rewrite H12 in H10; unfold Src1K in *; rewrite H10 in H4; inv H4.
        * simpl in H12; rewrite H12 in H10; unfold Src2K in *; rewrite H10 in H15; inv H15.
        * simpl in H12; rewrite H12 in H10; unfold Src1K in *; rewrite H10 in H4; inv H4.
        * simpl in H12; rewrite H12 in H10; unfold Src2K in *; rewrite H10 in H15; inv H15.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.

        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma p3st_decode_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p3stInl) ->
      Multistep p3stInl init n ll ->
      p3st_decode_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p3st_inv_old.
      unfold getRegInits, fst, p3stInl, ProcThreeStInl.p3stInl, projT1.
      p3st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p3st_raw_inv_ok' H H0).
      kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p3st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p3st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p3st_inv_tac; try reflexivity; try (rewrite e in H1; inv H1; fail).
      + kinv_dest_custom p3st_inv_tac; try (simpl; intuition idtac).
      + kinv_dest_custom p3st_inv_tac; try (simpl; intuition idtac).
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac;
          try (find_if_inside; [exfalso; intuition auto|intuition idtac]; fail).
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac;
          try (find_if_inside; [exfalso; intuition auto|intuition idtac]; fail).
      + kinv_dest_custom p3st_inv_tac;
          try (find_if_inside; [exfalso; intuition auto|intuition idtac]; fail).

        END_SKIP_PROOF_ON *) apply cheat.
  Qed.
  
  Lemma p3st_stalled_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p3stInl) ->
      Multistep p3stInl init n ll ->
      p3st_stalled_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p3st_inv_old.
      unfold getRegInits, fst, p3stInl, ProcThreeStInl.p3stInl, projT1.
      p3st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p3st_decode_inv_ok' H H0).
      kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.

        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma p3st_exec_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits p3stInl) ->
      Multistep p3stInl init n ll ->
      p3st_exec_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2; intros.

    - p3st_inv_old.
      unfold getRegInits, fst, p3stInl, ProcThreeStInl.p3stInl, projT1.
      p3st_inv_new; simpl in *; kinv_simpl.

    - pose proof (p3st_decode_inv_ok' H H0).
      pose proof (p3st_raw_inv_ok' H H0).
      kinvert.
      + mred.
      + mred.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac; simpl; rewrite <-H6, <-H12; reflexivity.
      + kinv_dest_custom p3st_inv_tac; elim n0; assumption.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac;
          try (find_if_inside; [elim H21; auto|];
               find_if_inside; [elim H22; auto|];
               intuition idtac; fail).
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac.
      + kinv_dest_custom p3st_inv_tac;
          try (find_if_inside; [elim H21; auto|];
               find_if_inside; [elim H22; auto|];
               intuition idtac; fail).
      + kinv_dest_custom p3st_inv_tac;
          try (find_if_inside; [elim H21; auto|];
               find_if_inside; [elim H22; auto|];
               intuition idtac; fail).

        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma p3st_inv_ok:
    forall o,
      reachable o p3stInl ->
      p3st_scoreboard_waw_inv o /\ p3st_raw_inv o /\ p3st_decode_inv o /\
      p3st_stalled_inv o /\ p3st_exec_inv o /\ p3st_epochs_inv o /\ p3st_pc_inv o.
  Proof.
    intros; inv H; inv H0.
    repeat split.
    - eapply p3st_scoreboard_waw_inv_ok'; eauto.
    - eapply p3st_raw_inv_ok'; eauto.
    - eapply p3st_decode_inv_ok'; eauto.
    - eapply p3st_stalled_inv_ok'; eauto.
    - eapply p3st_exec_inv_ok'; eauto.
    - eapply p3st_epochs_inv_ok'; eauto.
    - eapply p3st_pc_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold p3st_scoreboard_waw_inv_body p3st_raw_inv_body
     p3st_decode_inv_body p3st_stalled_inv_body
     p3st_exec_inv_body p3st_epochs_inv_body p3st_pc_inv_body : InvDefs.

