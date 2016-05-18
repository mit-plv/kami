Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Inline Lts.InlineFacts_2.
Require Import Lts.DecompositionZero Lts.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcDecSC.
  Variables addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdec := pdecf fifoSize dec execState execNextPc.
  Definition pinst := pinst dec execState execNextPc opLd opSt opHt.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT pinst) => unfold pinst. (* for kequiv *)

  Definition pdec_pinst_ruleMap (_: RegsT): string -> option string :=
    "execHt"    |-> "execHt";
    "execNm"    |-> "execNm";
    "processLd" |-> "execLd";
    "processSt" |-> "execSt"; ||.

  Definition pdec_pinst_regMap (r: RegsT): RegsT.
  Proof.
    kgetv "pc"%string pcv r (Bit addrSize) (M.empty (sigT (fullType type))).
    kgetv "rf"%string rfv r (Vector (Data lgDataBytes) rfIdx) (M.empty (sigT (fullType type))).
    kgetv "Outs".."empty"%string oev r Bool (M.empty (sigT (fullType type))).
    kgetv "Outs".."elt"%string oelv r (Vector RsToProc fifoSize)
          (M.empty (sigT (fullType type))).
    kgetv "Outs".."deqP"%string odv r (Bit fifoSize) (M.empty (sigT (fullType type))).

    pose proof (evalExpr (dec _ rfv pcv)) as inst.
    refine (
        if oev
        then (M.add "pc"%string (existT _ _ pcv)
                    (M.add "rf"%string (existT _ _ rfv)
                           (M.empty _)))
        else (M.add "pc"%string (existT _ _ (evalExpr (execNextPc _ rfv pcv inst)))
                    (M.add "rf"%string _ (M.empty _)))
      ).

    pose proof (inst ``"opcode") as opc.
    destruct (weq opc (evalConstT opLd)).
    - refine (existT _ (SyntaxKind (Vector (Data lgDataBytes) rfIdx)) _); simpl.
      exact (fun a => if weq a (inst ``"reg")
                      then (oelv odv) ``"data"
                      else rfv a).
    - refine (existT _ _ rfv).
  Defined.
  Hint Unfold pdec_pinst_regMap: MethDefs. (* for kdecompose_regMap_init *)

  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof.
    admit.
    (*
    kinline_left pdeci.
    kdecompose_nodefs pdec_pinst_regMap pdec_pinst_ruleMap.

    pose proof (procDec_inv_0_ok H).
    pose proof (procDec_inv_1_ok H).
    kinv_add_end.

    kinvert; kinv_magic_with kinv_or3.
     *)
  Qed.

End ProcDecSC.

