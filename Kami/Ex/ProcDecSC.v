Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcDecSC.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT instBytes)
            (getLdDst: LdDstT instBytes rfIdx)
            (getLdAddr: LdAddrT addrSize instBytes)
            (getLdSrc: LdSrcT instBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize instBytes)
            (getStSrc: StSrcT instBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT instBytes rfIdx)
            (getSrc1: Src1T instBytes rfIdx)
            (getSrc2: Src2T instBytes rfIdx)
            (getDst: DstT instBytes rfIdx)
            (exec: ExecT addrSize instBytes dataBytes)
            (getNextPc: NextPcT addrSize instBytes dataBytes rfIdx)
            (alignPc: AlignPcT addrSize iaddrSize)
            (alignAddr: AlignAddrT addrSize).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Variable (init: ProcInit addrSize dataBytes rfIdx).

  Definition pdec := pdecf fifoSize getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                           getStAddr getStSrc calcStAddr getStVSrc
                           getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr init.
  Definition pinst := pinst getOptype getLdDst getLdAddr getLdSrc calcLdAddr
                            getStAddr getStSrc calcStAddr getStVSrc
                            getSrc1 getSrc2 getDst exec getNextPc alignPc alignAddr init.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT pinst) => unfold pinst. (* for kequiv *)

  Definition pdec_pinst_ruleMap (o: RegsT): string -> option string :=
    "execToHost" |-> "execToHost";
      "execNm"     |-> "execNm";
      "execNmZ"    |-> "execNmZ";
      "processSt"  |-> "execSt";
      "reqLdZ"     |-> "execLdZ";
      "processLd"  |-> "execLd"; ||.
  Hint Unfold pdec_pinst_ruleMap: MethDefs.

  Definition pdec_pinst_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit addrSize) <- r |> "pc";
       mlet rfv : (Vector (Data dataBytes) rfIdx) <- r |> "rf";
       mlet pgmv : (Vector (Data instBytes) iaddrSize) <- r |> "pgm";
       mlet oev : Bool <- r |> "rsToProc"--"empty";
       mlet oelv : (Vector (Struct RsToProc) fifoSize) <- r |> "rsToProc"--"elt";
       mlet odv : (Bit fifoSize) <- r |> "rsToProc"--"deqP";
       if oev
       then (["pgm" <- (existT _ _ pgmv)]
             +["rf" <- (existT _ _ rfv)]
             +["pc" <- (existT _ _ pcv)])%fmap
       else
         let rawInst := pgmv (evalExpr (alignPc _ pcv)) in
         (["pgm" <- (existT _ _ pgmv)]
          +["rf" <- (let opc := evalExpr (getOptype _ rawInst) in
                     if weq opc opLd
                     then
                       (existT _ (SyntaxKind (Vector (Data dataBytes) rfIdx))
                               ((fun a : word rfIdx => if weq a (evalExpr (getLdDst _ rawInst))
                                                       then oelv odv (RsToProc !! "data")
                                                       else rfv a)
                                : (fullType type (SyntaxKind (Vector (Data dataBytes)
                                                                     rfIdx)))))
                     else
                       (existT _ _ rfv))]
          +["pc" <- (existT _ _ (evalExpr (getNextPc _ rfv pcv rawInst)))])%fmap
    )%mapping.
  Hint Unfold pdec_pinst_regMap: MapDefs.

  Ltac procDec_inv_old :=
    try match goal with
        | [H: context[procDec_inv] |- _] => destruct H
        end;
    kinv_red; kinv_or3;
    (* decide the current state by giving contradictions for all other states *)
    kinv_red; kinv_contra;
    (* to simplity struct-related invariants *)
    repeat
      match goal with
      | [H: context[Vector_find] |- _] => unfold Vector_find in H; simpl in H
      end.

  Definition decInstConfig :=
    {| inlining := ITManual;
       decomposition := DTFunctional pdec_pinst_regMap pdec_pinst_ruleMap;
       invariants := IVCons procDec_inv_ok IVNil
    |}.

  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof. (* SKIP_PROOF_ON
    kami_ok decInstConfig procDec_inv_old idtac.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End ProcDecSC.

