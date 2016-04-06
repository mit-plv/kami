Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2.
Require Import Lts.DecompositionZero.
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

  Definition pdecN := procDecM fifoSize dec exec n.
  Definition scN := sc dec exec opLd opSt opHt n.

  Section SingleCore.
    Definition pdec := ProcDecInl.pdec fifoSize dec exec.
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

    Ltac regMap_red :=
      unfold pdec_pinst_regMap;
      repeat
        (try match goal with
             | [H: M.find ?k ?m = _ |- context[M.find ?k ?m] ] => rewrite H
             | [ |- context[decKind ?k ?k] ] =>
               rewrite kind_eq; unfold eq_rect_r, eq_rect, eq_sym
             end;
         dest; try subst;
         try findReify).

    Tactic Notation "brewrite" ident(H1) "in" ident(H2) :=
      match type of H1 with
      | context [{| bindex:= ?s; indexb:= ?ib1 |}] =>
        match type of H2 with
        | context [{| bindex:= ?s; indexb:= ?ib2 |}] =>
          progress change {| bindex:= s; indexb:= ib2 |}
          with {| bindex:= s; indexb:= ib1 |} in H2
        end
      end; rewrite H1 in H2.

    Lemma pdec_refines_pinst: pdec <<== pinst.
    Proof.
      admit.
      (* apply traceRefines_inlining_left; auto. *)
      (* unfold pdec; rewrite <-pdecInl_equal. *)
      (* split; [|reflexivity]. *)

      (* kdecompose_nodefs pdec_pinst_regMap pdec_pinst_ruleMap. *)

      (* - unfold initRegs, getRegInits; simpl; clear. *)
      (*   regMap_red. *)
      (*   reflexivity. *)
      (* - auto. *)
      (* - auto. *)
      (* - intros. *)
      (*   pose proof (procDec_inv_0_ok H). *)
      (*   pose proof (procDec_inv_1_ok H). *)
      (*   clear H. *)
      (*   inv H0; CommonTactics.dest_in. *)

      (*   + inv H; invertActionRep. *)
      (*     eexists; split. *)
      (*     * econstructor. *)
      (*     * inv_red; simpl_find. *)
      (*       dest_or3; inv_contra. *)
      (*       regMap_red. *)
      (*       mred. *)

      (*   + inv H0; invertActionRep. *)
      (*     eexists; split. *)
      (*     * econstructor. *)
      (*     * inv_red; simpl_find. *)
      (*       dest_or3; inv_contra. *)
      (*       regMap_red. *)
      (*       mred. *)

      (*   + inv H; invertActionRep. *)
      (*     eexists; split. *)
      (*     * econstructor. *)
      (*     * inv_red; simpl_find. *)
      (*       dest_or3; inv_contra. *)
      (*       regMap_red. *)

      (*       destruct (weq (x2 ^+ $ (1)) (x2 ^+ $ (1))); [|elim n0; reflexivity]. *)
      (*       clear -H9; meq. *)
          
      (*   + inv H0; invertActionRep. *)
      (*     eexists; split. *)
      (*     * econstructor. *)
      (*     * inv_red; simpl_find. *)
      (*       dest_or3; inv_contra. *)
      (*       regMap_red. *)

      (*       destruct (weq (x2 ^+ $ (1)) (x2 ^+ $ (1))); [|elim n0; reflexivity]. *)
      (*       clear -H9; meq. *)

      (*       brewrite e in e0. *)
      (*       inv e0. *)
          
      (*   + inv H; invertActionRep. *)
      (*     eexists; split. *)
      (*     * inv_red; simpl_find. *)
      (*       dest_or3; inv_contra. *)
      (*       regMap_red. *)

      (*       eapply SingleRule; [simpl; tauto|]. *)
      (*       repeat econstructor. *)
      (*       auto. *)
      (*     * meq. *)

      (*   + inv H0; invertActionRep. *)
      (*     inv_red; simpl_find. *)
      (*     dest_or3; inv_contra. *)
      (*     regMap_red. *)
          
      (*     eexists; split. *)
      (*     * eapply SingleRule; [simpl; tauto|]. *)
      (*       repeat econstructor. *)
      (*       simpl; apply negb_true_iff; auto. *)
      (*     * meq. *)

      (*   + inv H; invertActionRep. *)
      (*     inv_red; simpl_find. *)
      (*     dest_or3; inv_contra. *)
      (*     unfold memAtomK, atomK in *. *)
      (*     regMap_red. *)
              
      (*     eexists; split. *)
      (*     * eapply SingleRule; [simpl; tauto|]. *)
      (*       repeat econstructor. *)
      (*       { simpl in *; clear -H0 H7. *)
      (*         repeat find_if_inside; intuition idtac. *)
      (*         elim n; clear n; rewrite <-e; auto. *)
      (*       } *)
      (*       { rewrite idElementwiseId; unfold id. *)
      (*         do 3 f_equal. *)
      (*         simpl; boundedMapTac. *)
      (*         { clear -H7. *)
      (*           find_if_inside; auto; inv H7. *)
      (*         } *)
      (*         { clear -H3 H7. *)
      (*           repeat find_if_inside; intuition idtac; inv H7. *)
      (*         } *)
      (*       } *)
      (*     * clear -H0 H7; meq. *)
      (*       elim n; clear n. *)
      (*       simpl; rewrite <-e; auto. *)

      (*   + inv H0; invertActionRep. *)
      (*     inv_red; simpl_find. *)
      (*     dest_or3; inv_contra. *)
      (*     unfold memAtomK, atomK in *. *)
      (*     regMap_red. *)

      (*     eexists; split. *)
      (*     * eapply SingleRule; [simpl; tauto|]. *)
      (*       repeat econstructor. *)
      (*       { simpl in *; clear -H0 H7. *)
      (*         repeat find_if_inside; intuition idtac. *)
      (*         elim n; clear n; rewrite <-e; auto. *)
      (*       } *)
      (*       { rewrite idElementwiseId; unfold id. *)
      (*         do 3 f_equal. *)
      (*         simpl; boundedMapTac. *)
      (*         { clear -H7. *)
      (*           find_if_inside; intuition idtac. *)
      (*           inv H7. *)
      (*         } *)
      (*         { clear -H3 H7. *)
      (*           repeat find_if_inside; intuition idtac. *)
      (*           { brewrite e0 in e; inv e. } *)
      (*           { inv H7. } *)
      (*           { inv H7. } *)
      (*         } *)
      (*       } *)
      (*     * clear -H0 H7; meq. *)
      (*       rewrite e0 in H0. *)
      (*       brewrite e in H0. *)
      (*       inv H0. *)
    Qed.

  End SingleCore.

  Lemma pdecN_refines_scN: traceRefines (liftToMap1 (@idElementwise _)) pdecN scN.
  Proof.
    apply traceRefines_modular_interacting with (vp:= (@idElementwise _)); auto.
    - admit.
    - admit.
    - admit. 
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - apply duplicate_defCallSub.
      vm_compute; split; intros; intuition idtac.
    - apply DefCallSub_refl.
    - repeat split.
    - (* TODO: a general lemma for duplication-refinement: implement in Specialize.v *)
      induction n; simpl; intros.
      + apply specialized_2.
        * intros; vm_compute.
          (* intro; dest. *)
          (* repeat *)
          (*   match goal with *)
          (*   | [H: _ \/ _ |- _] => destruct H *)
          (*   end; subst; try discriminate; auto. *)
          (* TODO: takes a time ... *)
          admit.
        * intros; vm_compute; admit.
        * apply traceRefines_label_map with (p:= liftToMap1 (@idElementwise _)); auto.
          { admit. }
          { admit. (* apply pdec_refines_pinst. *) }
      + admit. (* apply traceRefines_modular_noninteracting. *)
    - rewrite idElementwiseId; apply traceRefines_refl.

  Qed.

End ProcDecSC.

