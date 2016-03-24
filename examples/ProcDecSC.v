Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Inline Lts.InlineFacts_2 Lts.Decomposition.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.
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
    Definition pdec := pdecf fifoSize dec exec.
    Definition pinst := pinst dec exec opLd opSt opHt.
    Hint Unfold pdec pinst: ModuleDefs. (* for kinline_compute *)
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
      destruct (M.find "pc"%string r) as [[pck pcv]|]; [|exact (M.empty _)].
      destruct pck as [pck|]; [|exact (M.empty _)].
      destruct (decKind pck (Bit addrSize)); [subst|exact (M.empty _)].
      
      destruct (M.find "rf"%string r) as [[rfk rfv]|]; [|exact (M.empty _)].
      destruct rfk as [rfk|]; [|exact (M.empty _)].
      destruct (decKind rfk (Vector (Bit valSize) rfIdx)); [subst|exact (M.empty _)].
      
      destruct (M.find "Outs.empty"%string r) as [[oek oev]|]; [|exact (M.empty _)].
      destruct oek as [oek|]; [|exact (M.empty _)].
      destruct (decKind oek Bool); [subst|exact (M.empty _)].

      destruct (M.find "Outs.elt"%string r) as [[oelk oelv]|]; [|exact (M.empty _)].
      destruct oelk as [oelk|]; [|exact (M.empty _)].
      destruct (decKind oelk (Vector (memAtomK addrSize valSize) fifoSize));
        [subst|exact (M.empty _)].

      destruct (M.find "Outs.deqP"%string r) as [[odk odv]|]; [|exact (M.empty _)].
      destruct odk as [odk|]; [|exact (M.empty _)].
      destruct (decKind odk (Bit fifoSize)); [subst|exact (M.empty _)].
      
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

    Lemma pdec_decompose_rule:
      forall (oImp : RegsT) (uImp : UpdatesT) (rule : string) (csImp : MethsT),
        Substep (fst (inlineF pdec)) oImp uImp (Rle (Some rule)) csImp ->
        {uSpec : UpdatesT |
         Substep pinst (pdec_pinst_regMap oImp) uSpec (Rle (pdec_pinst_ruleMap oImp rule))
                 (liftToMap1 (@idElementwise _) csImp) /\
         (forall o : RegsT, M.union uSpec (pdec_pinst_regMap o) =
                            pdec_pinst_regMap (M.union uImp o))}.
    Proof.
      admit.
    Qed.

    Lemma pdec_decompose_meth:
      forall (oImp : RegsT) (uImp : UpdatesT) 
             (meth : Attribute (sigT SignT)) 
             (csImp : MethsT),
        Substep (fst (inlineF pdec)) oImp uImp (Meth (Some meth)) csImp ->
        {uSpec : UpdatesT |
         Substep pinst (pdec_pinst_regMap oImp) uSpec (Meth (liftP (@idElementwise _) meth))
                 (liftToMap1 (@idElementwise _) csImp) /\
         (forall o : RegsT, M.union uSpec (pdec_pinst_regMap o) =
                            pdec_pinst_regMap (M.union uImp o))}.
    Proof.
      admit.
    Qed.

    Lemma pdec_refines_pinst: pdec <<== pinst.
    Proof.
      kinline_left.

      (* haha this is so tricky :P *)
      match goal with
      | [ |- ?lm' <<== ?rm' ] =>
        (let Hlm := fresh "Hlm" in
         let lm := fresh "lm" in
         pose (lm := lm'); assert (Hlm: lm = lm') by reflexivity;
         rewrite <-Hlm; clear Hlm);
          (let Hrm := fresh "Hrm" in
           let rm := fresh "rm" in
           pose (rm := rm'); assert (Hrm: rm = rm') by reflexivity;
           rewrite <-Hrm; clear Hrm)
      end.

      match goal with
      | [ |- ?lm <<== ?rm ] =>
        assert (forall (oImp : RegsT) (uImp : UpdatesT) (rule : string) (csImp : MethsT),
                   Substep lm oImp uImp (Rle (Some rule)) csImp ->
                   {uSpec : UpdatesT |
                    Substep rm (pdec_pinst_regMap oImp) uSpec (Rle (pdec_pinst_ruleMap oImp rule))
                            (liftToMap1 (@idElementwise _) csImp) /\
                    (forall o : RegsT, M.union uSpec (pdec_pinst_regMap o) =
                                       pdec_pinst_regMap (M.union uImp o))})
          as HssRuleMap
      end.
      { admit.
        (* intros; eexists. *)
        (* inv H. *)
        (* CommonTactics.dest_in. *)
        (* { clear lm. inv H. *)
        (*   invertActionRep. *)
      }

      match goal with
      | [ |- ?lm <<== ?rm ] =>
        assert (forall (oImp : RegsT) (uImp : UpdatesT) 
                       (meth : Attribute (sigT SignT)) 
                       (csImp : MethsT),
                   Substep lm oImp uImp (Meth (Some meth)) csImp ->
                   {uSpec : UpdatesT |
                    Substep rm (pdec_pinst_regMap oImp) uSpec (Meth (liftP (@idElementwise _) meth))
                            (liftToMap1 (@idElementwise _) csImp) /\
                    (forall o : RegsT, M.union uSpec (pdec_pinst_regMap o) =
                                       pdec_pinst_regMap (M.union uImp o))})
          as HssMethMap
      end.
      { admit. }

      (* kdecompose pdec_pinst_regMap pdec_pinst_ruleMap HssRuleMap HssMethMap. *)
      
      (* - admit. *)
      (* - admit. *)
      (* - admit. *)
      (* - admit. *)

      admit.
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
          { apply pdec_refines_pinst. }
      + admit. (* apply traceRefines_modular_noninteracting. *)
    - rewrite idElementwiseId; apply traceRefines_refl.

  Qed.

End ProcDecSC.

