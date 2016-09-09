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
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).
  Hypotheses (HldSt: (if weq (evalConstT opLd) (evalConstT opSt) then true else false) = false).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition p2st := ProcTwoStage.p2st dec execState execNextPc opLd opSt opTh.
  Definition pdec := ProcDec.pdec dec execState execNextPc opLd opSt opTh.

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
    (mlet pcv : (Bit addrSize) <- r of "pc";
       mlet pgmv : (Vector (Data lgDataBytes) addrSize) <- r of "pgm";
       mlet rfv : (Vector (Data lgDataBytes) rfIdx) <- r of "rf";
       mlet d2eeltv : d2eElt opIdx addrSize lgDataBytes rfIdx <- r of "d2e"--"elt";
       mlet d2efv : Bool <- r of "d2e"--"full";
       mlet e2deltv : Bit addrSize <- r of "e2d"--"elt";
       mlet e2dfv : Bool <- r of "e2d"--"full";
       mlet eev : Bool <- r of "eEpoch";
       mlet curv : d2eElt opIdx addrSize lgDataBytes rfIdx <- r of "curInfo";
       mlet stallv : Bool <- r of "stall";
       (["stall" <- existT _ _ stallv]
        +["pgm" <- existT _ _ pgmv]
        +["rf" <- existT _ _ rfv]
        +["pc" <- existT _ (SyntaxKind (Bit addrSize))
               (if d2efv
                then
                  if eqb eev (d2eeltv ``"epoch")
                  then d2eeltv ``"curPc"
                  else e2deltv
                else
                  if e2dfv then e2deltv else pcv)])%fmap)%mapping.
  Hint Unfold p2st_pdec_regMap: MapDefs.

  Theorem p2st_refines_pdec:
    p2st <<== pdec.
  Proof.
    (* kinline_left im. *)
    (* kdecompose_nodefs p2st_pdec_regMap p2st_pdec_ruleMap. *)

    (* kinv_add p2st_inv_ok. *)
    (* kinv_add_end. *)
    
    (* kinvert. *)
    admit.
  Qed.

End ProcTwoStDec.

