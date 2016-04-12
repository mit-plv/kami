Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Inline Lts.InlineFacts_2.
Require Import Lts.DecompositionZero.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
Require Import Eqdep.

Set Implicit Arguments.

(** TODO: move to proper sites *)

Tactic Notation "brewrite" ident(H) :=
  match type of H with
  | context [{| bindex:= ?s; indexb:= ?ib1 |}] =>
    match goal with
    | [ |- context [{| bindex:= ?s; indexb:= ?ib2 |}] ] =>
      progress change {| bindex:= s; indexb:= ib2 |}
      with {| bindex:= s; indexb:= ib1 |}
    end
  end; rewrite H.

Tactic Notation "brewrite" ident(H1) "in" ident(H2) :=
  match type of H1 with
  | context [{| bindex:= ?s; indexb:= ?ib1 |}] =>
    match type of H2 with
    | context [{| bindex:= ?s; indexb:= ?ib2 |}] =>
      progress change {| bindex:= s; indexb:= ib2 |}
      with {| bindex:= s; indexb:= ib1 |} in H2
    end
  end; rewrite H1 in H2.

(** TODO end *)

Section ProcDecSC.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.
  Hypotheses (HdecEquiv: DecEquiv dec)
             (HexecEquiv_1: ExecEquiv_1 dec exec)
             (HexecEquiv_2: ExecEquiv_2 dec exec).

  Variable n: nat.

  (* Definition pdec := ProcDecInl.pdec fifoSize dec exec. *)
  Definition pdec := pdecf fifoSize dec exec.
  Definition pinst := pinst dec exec opLd opSt opHt.
  Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)
  Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for equiv_tac *)
  Hint Extern 1 (ModEquiv type typeUT pinst) => unfold pinst. (* for equiv_tac *)

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

    - (* Outs.empty = true *)
      refine (M.add "pc"%string _
                    (M.add "rf"%string _
                           (M.empty _))).
      + exact (existT _ _ pcv).
      + exact (existT _ _ rfv).

    - (* Outs.empty = false *)
      refine (M.add "pc"%string _
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

  Ltac regMap_red regMap :=
    unfold regMap;
    repeat
      (try match goal with
           | [H: M.find ?k ?m = _ |- context[M.find ?k ?m] ] => rewrite H
           | [ |- context[decKind ?k ?k] ] =>
             rewrite kind_eq; unfold eq_rect_r, eq_rect, eq_sym
           end;
       dest; try subst;
       try findReify).

  Ltac regMap_init regMap :=
    unfold initRegs, getRegInits; simpl; clear;
    regMap_red regMap; reflexivity.
  
  Ltac kinline_left im :=
    match goal with
    | [ |- traceRefines _ ?lm _ ] =>
      apply traceRefines_inlining_left; auto;
      let Heq := fresh "Heq" in
      remember (inlineF lm) as im eqn:Heq;
      kinline_compute_in Heq;
      split; [|subst; reflexivity]
    end.

  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof.
    admit.
    (* kinline_left pdeci. *)
    (* kdecompose_nodefs pdec_pinst_regMap pdec_pinst_ruleMap; *)
    (*   subst; [regMap_init pdec_pinst_regMap|auto|auto|]. *)

    (* intros. *)
    (* pose proof (procDec_inv_0_ok H). *)
    (* pose proof (procDec_inv_1_ok H). *)
    (* clear H. *)
    (* inv H0; CommonTactics.dest_in. *)

    (* - invertActionRep. *)
    (*   eexists; split. *)
    (*   + econstructor. *)
    (*   + inv_red; simpl_find. *)
    (*     dest_or3; inv_contra. *)
    (*     regMap_red pdec_pinst_regMap. *)
    (*     mred. *)

    (* - invertActionRep. *)
    (*   eexists; split. *)
    (*   + econstructor. *)
    (*   + inv_red; simpl_find. *)
    (*     dest_or3; inv_contra. *)
    (*     regMap_red pdec_pinst_regMap. *)
    (*     mred. *)

    (* - invertActionRep. *)
    (*   eexists; split. *)
    (*   + econstructor. *)
    (*   + inv_red; simpl_find. *)
    (*     dest_or3; inv_contra; inv_red. *)
    (*     regMap_red pdec_pinst_regMap. *)

    (*     brewrite e. *)
    (*     reflexivity. *)
        
    (* - invertActionRep. *)
    (*   eexists; split. *)
    (*   + econstructor. *)
    (*   + inv_red; simpl_find. *)
    (*     dest_or3; inv_contra; inv_red. *)
    (*     regMap_red pdec_pinst_regMap. *)

    (*     brewrite e. *)
    (*     reflexivity. *)
        
    (* - invertActionRep. *)
    (*   eexists; split. *)
    (*   + inv_red; simpl_find. *)
    (*     dest_or3; inv_contra; inv_red. *)
    (*     regMap_red pdec_pinst_regMap. *)

    (*     econstructor; [simpl; tauto|]. *)
    (*     repeat econstructor; auto. *)
    (*     simpl; rewrite e; reflexivity. *)
        
    (*   + meqReify. *)

    (* - invertActionRep. *)
    (*   inv_red; simpl_find. *)
    (*   dest_or3; inv_contra; inv_red. *)
    (*   regMap_red pdec_pinst_regMap. *)
      
    (*   eexists; split. *)
    (*   + econstructor; [simpl; tauto|]. *)
    (*     repeat econstructor. *)
    (*     simpl; apply negb_true_iff; auto. *)
    (*   + meqReify. *)

    (* - invertActionRep. *)
    (*   inv_red; simpl_find. *)
    (*   dest_or3; inv_contra. *)
    (*   unfold memAtomK, atomK in *; inv_red. *)
    (*   regMap_red pdec_pinst_regMap. *)
      
    (*   eexists; split. *)
    (*   + econstructor; [simpl; tauto|]. *)
    (*     repeat econstructor. *)
    (*     * clear -H0 e; simpl in *. *)
    (*       find_if_inside; intuition idtac. *)
    (*       brewrite H0 in e; auto. *)
    (*     * rewrite idElementwiseId; unfold id. *)
    (*       meqReify. *)
    (*       simpl; boundedMapTac. *)
    (*       clear -H3 e. *)
    (*       brewrite e in H3; simpl in H3. *)
    (*       auto. *)
    (*   + meqReify. *)

    (*     clear -H0 e; simpl in *. *)
    (*     brewrite H0 in e. *)
    (*     rewrite e; simpl. *)
    (*     repeat f_equal. *)
    (*     destruct (weq x9 x9); [|elim n; reflexivity]. *)
    (*     reflexivity. *)

    (* - invertActionRep. *)
    (*   inv_red; simpl_find. *)
    (*   dest_or3; inv_contra; inv_red. *)
    (*   unfold memAtomK, atomK in *. *)
    (*   regMap_red pdec_pinst_regMap. *)

    (*   eexists; split. *)
    (*   + econstructor; [simpl; tauto|]. *)
    (*     repeat econstructor. *)
    (*     * clear -H0 e; simpl in *. *)
    (*       brewrite H0 in e. *)
    (*       brewrite e. *)
    (*       auto. *)
    (*     * rewrite idElementwiseId; unfold id. *)
    (*       meqReify. *)
    (*       simpl; boundedMapTac. *)
    (*       clear -H3 e; simpl in *. *)
    (*       brewrite e in H3; simpl in H3. *)
    (*       auto. *)
    (*   + meqReify. *)

    (*     clear -H0 e; simpl in *. *)
    (*     brewrite H0 in e. *)
    (*     rewrite e; simpl. *)
    (*     reflexivity. *)
  Qed.

End ProcDecSC.

