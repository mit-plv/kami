Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StructNotation Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcDecSC.
  Variables opIdx addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize lgDataBytes rfIdx.

  Variables opLd opSt opTh: ConstT (Bit opIdx).
  Hypotheses (HldSt: (if weq (evalConstT opLd) (evalConstT opSt) then true else false) = false).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdec := pdecf fifoSize dec execState execNextPc opLd opSt opTh.
  Definition pinst := pinst dec execState execNextPc opLd opSt opTh.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT pinst) => unfold pinst. (* for kequiv *)

  Definition pdec_pinst_ruleMap (o: RegsT): string -> option string :=
    "execToHost" |-> "execToHost";
      "execNm"     |-> "execNm";
      "processSt"  |-> "execSt";
      "reqLdZ"     |-> "execLdZ";
      "processLd"  |-> "execLd"; ||.
  Hint Unfold pdec_pinst_ruleMap: MethDefs.

  Definition pdec_pinst_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit addrSize) <- r of "pc";
       mlet rfv : (Vector (Data lgDataBytes) rfIdx) <- r of "rf";
       mlet pgmv : (Vector (Data lgDataBytes) addrSize) <- r of "pgm";
       mlet oev : Bool <- r of "rsToProc"--"empty";
       mlet oelv : (Vector RsToProc fifoSize) <- r of "rsToProc"--"elt";
       mlet odv : (Bit fifoSize) <- r of "rsToProc"--"deqP";
       if oev
       then (["pgm" <- (existT _ _ pgmv)]
             +["rf" <- (existT _ _ rfv)]
             +["pc" <- (existT _ _ pcv)])%fmap
       else
         let inst := evalExpr (dec _ rfv (pgmv pcv)) in
         (["pgm" <- (existT _ _ pgmv)]
          +["rf" <- (let opc := inst ``"opcode" in
                     if weq opc (evalConstT opLd)
                     then
                       (existT _ (SyntaxKind (Vector (Data lgDataBytes) rfIdx))
                               ((fun a : word rfIdx => if weq a (inst ``"reg")
                                                       then oelv odv ``"data"
                                                       else rfv a)
                                : (fullType type (SyntaxKind (Vector (Data lgDataBytes)
                                                                     rfIdx)))))
                     else
                       (existT _ _ rfv))]
          +["pc" <- (existT _ _ (evalExpr (execNextPc _ rfv pcv inst)))])%fmap
    )%mapping.
  Hint Unfold pdec_pinst_regMap: MapDefs.

  Definition decInstConfig :=
    {| inlining := true;
       decomposition := DTFunctional pdec_pinst_regMap pdec_pinst_ruleMap;
       invariants := IVCons procDec_inv_ok IVNil
    |}.

  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof. (* SKIP_PROOF_ON
    kami_ok decInstConfig procDec_inv_old.
    END_SKIP_PROOF_ON *) admit.
  Qed.

End ProcDecSC.

