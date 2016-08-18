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

  Definition pdec_pinst_ruleMap (o: RegsT): string -> option string.
    refine ("execToHost" |-> "execToHost";
            "execNm"     |-> "execNm";
            "processSt"  |-> "execSt"; _).
    kgetv "fetch"%string fetchv o Bool (fun _ : string => @None string).
    exact (if fetchv
           then "processLd" |-> "instFetch"; ||
           else "processLd" |-> "execLd"; ||).
  Defined.
  Hint Unfold pdec_pinst_ruleMap: MethDefs.

  Definition pdec_pinst_regMap (r: RegsT): RegsT.
  Proof.
    kgetv "pc"%string pcv r (Bit addrSize) (M.empty (sigT (fullType type))).
    kgetv "rf"%string rfv r (Vector (Data lgDataBytes) rfIdx) (M.empty (sigT (fullType type))).
    kgetv "fetch"%string fetchv r Bool (M.empty (sigT (fullType type))).
    kgetv "fetched"%string fetchedv r (Data lgDataBytes) (M.empty (sigT (fullType type))).
    kgetv "rsToProc"--"empty"%string oev r Bool (M.empty (sigT (fullType type))).
    kgetv "rsToProc"--"elt"%string oelv r (Vector RsToProc fifoSize)
          (M.empty (sigT (fullType type))).
    kgetv "rsToProc"--"deqP"%string odv r (Bit fifoSize) (M.empty (sigT (fullType type))).

    refine (if oev
            then (M.add "pc"%string (existT _ _ pcv)
                        (M.add "rf"%string (existT _ _ rfv)
                               (M.add "fetch"%string (existT _ _ fetchv)
                                      (M.add "fetched"%string (existT _ _ fetchedv)
                                             (M.empty _)))))
            else _).
    refine (if fetchv then _ else _).

    - refine (M.add "pc"%string (existT _ _ pcv)
                    (M.add "rf"%string (existT _ _ rfv)
                           (M.add "fetch"%string (existT _ (SyntaxKind Bool) false)
                                  (M.add "fetched"%string
                                         (existT _ (SyntaxKind (Data lgDataBytes))
                                                 (oelv odv ``"data"))
                                         (M.empty _))))).

    - pose proof (evalExpr (dec _ rfv fetchedv)) as inst.
      refine (M.add "pc"%string (existT _ _ (evalExpr (execNextPc _ rfv pcv inst)))
                    (M.add "rf"%string _
                           (M.add "fetch"%string (existT _ (SyntaxKind Bool) true)
                                  (M.add "fetched"%string (existT _ _ fetchedv)
                                         (M.empty _))))).
      pose proof (inst ``"opcode") as opc.
      destruct (weq opc (evalConstT opLd)).
      + refine (existT _ (SyntaxKind (Vector (Data lgDataBytes) rfIdx)) _); simpl.
        exact (fun a => if weq a (inst ``"reg")
                        then oelv odv ``"data"
                        else rfv a).
      + refine (existT _ _ rfv).
  Defined.
  Hint Unfold pdec_pinst_regMap: MethDefs. (* for kdecompose_regMap_init *)

  (* Definition decInstConfig := *)
  (*   {| inlining := true; *)
  (*      decomposition := DTFunctional pdec_pinst_regMap pdec_pinst_ruleMap; *)
  (*      invariants := IVCons procDec_inv_ok IVNil *)
  (*   |}. *)

  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof. (* SKIP_PROOF_ON

    kinline_left im.
    kdecompose_nodefs pdec_pinst_regMap pdec_pinst_ruleMap.

    kinv_add procDec_inv_ok.
    kinv_add_end.

    kinvert.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_magic_with kinv_or3.
    - kinv_action_dest;
        kinv_custom kinv_or3;
        kinv_regmap_red.
      + (* TODO: automation *)
        unfold IndexBound_head, IndexBound_tail, mapAttr, addFirstBoundedIndex, bindex in *.
        simpl in *.
        rewrite H17 in H25.
        kinv_contra.
      + kinv_constr;
          kinv_eq;
          kinv_finish.

        END_SKIP_PROOF_ON *) admit.
  Qed.

End ProcDecSC.

