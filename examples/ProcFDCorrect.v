Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.SC Ex.ProcDec Ex.ProcTwoStage Ex.ProcFetchDecode Ex.ProcFDInl.
Require Import Eqdep.

Set Implicit Arguments.

Section FetchDecode.
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
            (execState: ExecStateT addrSize lgDataBytes rfIdx)
            (execNextPc: ExecNextPcT addrSize lgDataBytes rfIdx)
            (predictNextPc: forall ty, fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                       Expr ty (SyntaxKind (Bit addrSize))).

  Definition fetchDecode := fetchDecode getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                        getStAddr getStSrc calcStAddr getStVSrc
                                        getSrc1 predictNextPc.
  Definition fetchNDecode := ProcTwoStage.decoder getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                                                  getStAddr getStSrc calcStAddr getStVSrc
                                                  getSrc1 predictNextPc.

  Hint Unfold fetchDecode: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT fetchDecode) => unfold fetchDecode. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT fetchNDecode) => unfold fetchNDecode. (* for kequiv *)

  Definition fetchDecode_ruleMap (o: RegsT): string -> option string :=
    "modifyPc" |-> "modifyPc";
      "decodeLd" |-> "instFetchLd";
      "decodeSt" |-> "instFetchSt";
      "decodeTh" |-> "instFetchTh";
      "decodeNm" |-> "instFetchNm"; ||.
  Hint Unfold fetchDecode_ruleMap: MethDefs.

  Definition fetchDecode_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit addrSize) <- r |> "pc";
       mlet pgmv : (Vector (Data lgDataBytes) addrSize) <- r |> "pgm";
       mlet fev : Bool <- r |> "fEpoch";
       mlet f2dfullv : Bool <- r |> "f2d"--"full";
       mlet f2deltv : (f2dElt addrSize lgDataBytes) <- r |> "f2d"--"elt";

       (["fEpoch" <- existT _ _ fev]
        +["pgm" <- existT _ _ pgmv]
        +["pc" <- existT _ (SyntaxKind (Bit addrSize))
               (if f2dfullv then f2deltv ``"curPc"
                else pcv)])%fmap)%mapping.
  Hint Unfold fetchDecode_regMap: MapDefs.

  (* Definition fetchDecodeInl := ProcFDInl.fetchDecodeInl *)
  (*                                getOptype getLdDst getLdAddr getLdSrc calcLdAddr *)
  (*                                getStAddr getStSrc calcStAddr getStVSrc *)
  (*                                getSrc1 predictNextPc. *)

  Theorem p2st_refines_pdec:
    fetchDecode <<== fetchNDecode.
  Proof.
    admit.
    (* (* instead of: kinline_left im. *) *)
    (* ketrans; [exact (projT2 fetchDecodeInl)|]. *)
    (* kdecompose_nodefs fetchDecode_regMap fetchDecode_ruleMap. *)

    (* kinv_add_end. *)

    (* kinvert. *)

    (* - kinv_action_dest. *)
    (*   kinv_red. *)
    (*   kinv_regmap_red. *)
  Qed.

End FetchDecode.

