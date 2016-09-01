Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.SC Ex.ProcTwoStage Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
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
    "reqInstFetch" |-> "reqInstFetch";
      "repInstFetch" |-> "repInstFetch";
      "reqLd" |-> "reqLd";
      "reqLdZ" |-> "reqLdZ";
      "reqSt" |-> "reqSt";
      "repLd" |-> "repLd";
      "repSt" |-> "repSt";
      "execToHost" |-> "execToHost";
      "execNm" |-> "execNm"; ||.
  Hint Unfold p2st_pdec_ruleMap: MethDefs.

  (* TODO: p2st_pdec_regMap *)
  
  Theorem p2st_refines_pdec: p2st <<== pdec.
  Proof.
    admit.
  Qed.

End ProcTwoStDec.

