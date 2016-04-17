Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Inline Lts.InlineFacts_2.
Require Import Lts.DecompositionZero Lts.Tactics.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcDecSC.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.
  Hypotheses (HdecEquiv: DecEquiv dec)
             (HexecEquiv_1: ExecEquiv_1 dec exec)
             (HexecEquiv_2: ExecEquiv_2 dec exec).

  Variable n: nat.

  Definition pdec := pdecf fifoSize dec exec.
  Definition pinst := pinst dec exec opLd opSt opHt.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)
  Hint Extern 1 (ModEquiv type typeUT pinst) => unfold pinst. (* for kequiv *)

  Definition pdec_pinst_ruleMap (_: RegsT) (s: string): option string :=
    if string_dec s "reqLd" then None
    else if string_dec s "reqSt" then None
    else if string_dec s "repLd" then None
    else if string_dec s "repSt" then None
    else if string_dec s "execHt" then Some "execHt"%string
    else if string_dec s "execNm" then Some "execNm"%string
    else if string_dec s "processLd" then Some "execLd"%string
    else if string_dec s "processSt" then Some "execSt"%string
    else None.

  Definition pdec_pinst_regMap (r: RegsT): RegsT.
  Proof.
    kgetv "pc"%string pcv r (Bit addrSize) (M.empty (sigT (fullType type))).
    kgetv "rf"%string rfv r (Vector (Bit valSize) rfIdx) (M.empty (sigT (fullType type))).
    kgetv "Outs.empty"%string oev r Bool (M.empty (sigT (fullType type))).
    kgetv "Outs.elt"%string oelv r (Vector (memAtomK addrSize valSize) fifoSize)
          (M.empty (sigT (fullType type))).
    kgetv "Outs.deqP"%string odv r (Bit fifoSize) (M.empty (sigT (fullType type))).
    refine (if oev then _ else _).

    - refine (M.add "pc"%string _
                    (M.add "rf"%string _
                           (M.empty _))).
      + exact (existT _ _ pcv).
      + exact (existT _ _ rfv).

    - refine (M.add "pc"%string _
                    (M.add "rf"%string _
                           (M.empty _))).
      + exact (existT _ _ (getNextPc exec _ pcv rfv (dec _ rfv pcv))).
      + pose proof (dec _ rfv pcv ``"opcode") as opc.
        destruct (weq opc (evalConstT opLd)).
        * refine (existT _ (SyntaxKind (Vector (Bit valSize) rfIdx)) _); simpl.
          exact (fun a => if weq a (dec _ rfv pcv ``"reg")
                          then (oelv odv) ``"value"
                          else rfv a).
        * refine (existT _ _ rfv).
  Defined.
  Hint Unfold pdec_pinst_regMap: MethDefs. (* for kdecompose_regMap_init *)

  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof.
    admit.
    (* kinline_left pdeci. *)
    (* kdecompose_nodefs pdec_pinst_regMap pdec_pinst_ruleMap. *)

    (* kinv_add procDec_inv_0_ok. *)
    (* kinv_add procDec_inv_1_ok. *)
    (* kinv_add_end. *)

    (* kinvert. *)
    (* - kinv_magic_with kinv_or3. *)
    (* - kinv_magic_with kinv_or3. *)
    (* - kinv_magic_with kinv_or3. *)
    (* - kinv_magic_with kinv_or3. *)
    (* - kinv_magic_with kinv_or3. *)
    (* - kinv_magic_with kinv_or3. *)
    (* - kinv_magic_with kinv_or3. *)
    (* - kinv_magic_with kinv_or3. *)
  Qed.

End ProcDecSC.

