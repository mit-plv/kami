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

  Definition pdec_pinst_regRel (ir sr: RegsT): Prop.
  Proof.
    kgetv "pc"%string pcv ir (Bit addrSize) False.
    kgetv "rf"%string rfv ir (Vector (Data lgDataBytes) rfIdx) False.
    refine (exists oeltv: fullType type (listEltK RsToProc type),
               M.find "Outs"--"elt" ir = Some (existT _ _ oeltv) /\ _).

    pose proof (evalExpr (dec _ rfv pcv)) as inst.
    refine (match oeltv with
            | nil => sr = M.add "pc"%string (existT _ _ pcv)
                                (M.add "rf"%string (existT _ _ rfv)
                                       (M.empty _))
            | _ => sr = M.add "pc"%string (existT _ _ (evalExpr (execNextPc _ rfv pcv inst)))
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
  Hint Unfold pdec_pinst_regRel: MethDefs. (* for kdecompose_regMap_init *)
  Hint Unfold evalConstT: MethDefs.
  
  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof. (* SKIP_PROOF_ON
    kinline_left pdeci.
    kdecomposeR_nodefs pdec_pinst_regRel pdec_pinst_ruleMap.

    pose proof (procDec_inv_0_ok Hreach).
    pose proof (procDec_inv_1_ok Hreach).
    kinv_add_end.

    kinvert.
    - kinv_magic_light_with kinv_or3.
    - kinv_magic_light_with kinv_or3.
    - kinv_magic_light_with kinv_or3.
      kinv_finish.
    - kinv_magic_light_with kinv_or3.
      kinv_finish.
    - kinv_magic_light_with kinv_or3.
      kinv_finish.
    - kinv_magic_light_with kinv_or3.
      kinv_finish.
    - kinv_red.
      invertActionRep.
      kinv_or3.
      + kinv_red.
        kregmap_red.
        kinv_contra.
      + kinv_magic_light_with kinv_or3.
        { kinv_finish. }
        { boundedMapTac; kinv_finish. }
        { kinv_finish. }
      + kinv_red.
        kregmap_red.
        kinv_contra.
    - kinv_magic_light_with kinv_or3.
      + kinv_finish.
      + boundedMapTac; kinv_finish.
      + kinv_finish.
        END_SKIP_PROOF_ON *) admit.
  Qed.

End ProcDecSC.

