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
  Variables addrSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Definition RqFromProc := MemTypes.RqFromProc lgDataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc lgDataBytes.

  Definition pdec := pdecf dec execState execNextPc.
  Definition pinst := pinst dec execState execNextPc opLd opSt opHt.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT pinst) => unfold pinst. (* for kequiv *)

  Definition pdec_pinst_ruleMap (_: RegsT): string -> option string :=
    "execHt"    |-> "execHt";
    "execNm"    |-> "execNm";
    "processLd" |-> "execLd";
    "processSt" |-> "execSt"; ||.

  Lemma pdec_pinst_regMap_type:
    forall ir (Hr: reachable ir (fst (ProcDecInl.pdecInl dec execState execNextPc))),
      match M.find "Outs"--"elt" ir with
      | Some s => projT1 s = @NativeKind (listEltT RsToProc type) nil
      | None => False
      end.
  Proof.
    abstract (
        intros; pose proof (procDec_inv_0_ok Hr);
        unfold procDec_inv_0 in H; dest;
        rewrite H3; reflexivity).
  Defined.

  Definition pdec_pinst_regMap (ir: RegsT)
             (Hr: reachable ir (fst (ProcDecInl.pdecInl dec execState execNextPc))): RegsT.
  Proof.
    kgetv "pc"%string pcv ir (Bit addrSize) (M.empty (sigT (fullType type))).
    kgetv "rf"%string rfv ir (Vector (Data lgDataBytes) rfIdx) (M.empty (sigT (fullType type))).

    pose proof (pdec_pinst_regMap_type Hr) as Hoeltv; clear Hr.
    destruct (M.find "Outs"--"elt" ir) as [oeltv|]; [|inv Hoeltv].
    destruct oeltv as [oeltk oeltv].
    simpl in Hoeltv; subst.

    pose proof (evalExpr (dec _ rfv pcv)) as inst.
    refine (match oeltv with
            | nil => M.add "pc"%string (existT _ _ pcv)
                           (M.add "rf"%string (existT _ _ rfv)
                                  (M.empty _))
            | _ => M.add "pc"%string (existT _ _ (evalExpr (execNextPc _ rfv pcv inst)))
                         (M.add "rf"%string _ (M.empty _))
            end).

    pose proof (inst ``"opcode") as opc.
    destruct (weq opc (evalConstT opLd)).
    - refine (existT _ (SyntaxKind (Vector (Data lgDataBytes) rfIdx)) _); simpl.
      exact (fun a => if weq a (inst ``"reg")
                      then hd (evalConstT Default) oeltv ``"data"
                      else rfv a).
    - refine (existT _ _ rfv).
  Defined.
  Hint Unfold pdec_pinst_regMap: MethDefs. (* for kdecompose_regMap_init *)

  Require Import ProofIrrelevance.

  Ltac pdec_refines_pinst_tac :=
    kinv_or3;
    repeat
      match goal with
      | [ |- context [pdec_pinst_regMap_type ?Hr] ] =>
        let Hpf := fresh "Hpf" in
        assert (Hpf: pdec_pinst_regMap_type Hr = eq_refl) by apply proof_irrelevance;
        simpl in Hpf; rewrite Hpf
      end.
  
  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof. (* SKIP_PROOF_ON
    kinline_left pdeci.

    subst.
    apply decompositionZeroE with (thetaE:= pdec_pinst_regMap) (ruleMap:= pdec_pinst_ruleMap);
      intros; subst.

    - unfold initRegs, getRegInits; simpl.
      kregmap_red.
      kinv_magic_light_with pdec_refines_pinst_tac.

    - auto.
    - auto.

    - pose proof (procDec_inv_0_ok Hreach).
      pose proof (procDec_inv_1_ok Hreach).

      admit.
      kinvert; kinv_magic_with kinv_or3.
      END_SKIP_PROOF_ON *) admit.
  Qed.

End ProcDecSC.

