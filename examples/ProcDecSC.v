Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Inline Lts.InlineFacts_2.
Require Import Lts.DecompositionZero Lts.Notations Lts.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcDecSC.
  Variables opIdx addrSize iaddrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT opIdx addrSize iaddrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT opIdx addrSize iaddrSize lgDataBytes rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).
  Hypotheses (HldSt: (if weq (evalConstT opLd) (evalConstT opSt) then true else false) = false).

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdec := pdecf fifoSize dec execState execNextPc opLd opSt opHt.
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
    kgetv "pc"%string pcv r (Bit iaddrSize) (M.empty (sigT (fullType type))).
    kgetv "rf"%string rfv r (Vector (Data lgDataBytes) rfIdx) (M.empty (sigT (fullType type))).
    kgetv "rsToProc"--"empty"%string oev r Bool (M.empty (sigT (fullType type))).
    kgetv "rsToProc"--"elt"%string oelv r (Vector RsToProc fifoSize)
          (M.empty (sigT (fullType type))).
    kgetv "rsToProc"--"deqP"%string odv r (Bit fifoSize) (M.empty (sigT (fullType type))).

    pose proof (evalExpr (dec _ rfv pcv)) as inst.
    refine (
        if oev
        then (M.add "pc"%string (existT _ _ pcv)
                    (M.add "rf"%string (existT _ _ rfv)
                           (M.empty _)))
        else (M.add "pc"%string (existT _ _ (evalExpr (execNextPc _ rfv pcv inst)))
                    (M.add "rf"%string _ (M.empty _)))
      ).

    pose proof (inst {| bindex := "opcode"%string |}) as opc.
    destruct (weq opc (evalConstT opLd)).
    - refine (existT _ (SyntaxKind (Vector (Data lgDataBytes) rfIdx)) _); simpl.
      exact (fun a => if weq a (inst {| bindex := "reg"%string |})
                      then (oelv odv) {| bindex := "data"%string |}
                      else rfv a).
    - refine (existT _ _ rfv).
  Defined.
  Hint Unfold pdec_pinst_regMap: MethDefs. (* for kdecompose_regMap_init *)

  Definition decInstConfig :=
    {| inlining := true;
       decomposition :=
         DTFunctional pdec_pinst_regMap pdec_pinst_ruleMap;
       invariants :=
         IVCons procDec_inv_0_ok (IVCons procDec_inv_1_ok IVNil)
    |}.

  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof. (* SKIP_PROOF_ON
    kami_ok decInstConfig kinv_or3.
    END_SKIP_PROOF_ON *) admit.
  Qed.

End ProcDecSC.

