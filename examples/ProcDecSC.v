Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Inline Lts.InlineFacts_2 Lts.Cycles.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.

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
    Hint Unfold pdec pinst : ModuleDefs.
    
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

    (* Eval vm_compute in (getRegInits pdec). *)
    (* = ["pc"%string; "rf"%string; "stall"%string; "Ins.elt"%string; "Ins.enqP"%string; *)
    (*    "Ins.deqP"%string; "Ins.empty"%string; "Ins.full"%string; "Outs.elt"%string; *)
    (*    "Outs.enqP"%string; "Outs.deqP"%string; "Outs.empty"%string; "Outs.full"%string] *)
    (*   : list string *)
    
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

    Ltac dest_rules :=
      repeat
        match goal with
        | [H: In _ _ |- _] => inv H
        | [H: (_ :: _)%struct = (_ :: _)%struct |- _] => inv H
        end.
    
    Lemma attribute_invert:
      forall {k: Type} n1 n2 (a1 a2: k),
        (n1 :: a1)%struct = (n2 :: a2)%struct -> a1 = a2.
    Proof. intros; inv H; auto. Qed.

    Ltac invert_call :=
      (* Figure out if the call is internal or not *)
      repeat
        match goal with
        | [H: (_ /\ _) \/ (_ /\ _) |- _] => destruct H; dest; subst; simpl in *
        | [H: ~ (_ \/ _) |- _] => try (elim H; tauto; fail)
        end;
      (* Find the call body *)
      repeat
        match goal with
        | [H: ((_ :: _)%struct = (_ :: _)%struct \/ _) |- _] => destruct H 
        | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
          try (inv H; fail);
          try (apply attribute_invert in H; destruct_existT)
        | [H: False |- _] => elim H
        end.

    (* TODO: seems too arbitrary *)
    Ltac mred_concrete :=
      repeat
        match goal with
        | [ |- context[M.find _ (M.add _ _ _)] ] =>
          (rewrite M.find_add_1 by auto)
          || (rewrite M.find_add_2 by auto)
        | [ |- context[decKind ?k1 ?k2] ] =>
          let Hneq := fresh "Hneq" in
          destruct (decKind k1 k2) as [|Hneq];
          [|elim Hneq; reflexivity]
        | [ |- context[eq_rect_r _ _ _ _] ] =>
          unfold eq_rect_r
        | [ |- context[eq_rect _ _ _ _ _ _] ] =>
          rewrite <-Eqdep.Eq_rect_eq.eq_rect_eq
        end.

    Lemma pdec_noCycleModules: NoModulesCycle pdec.
    Proof.
      unfold NoModulesCycle; intros; dest_in; simpl.

      - econstructor; eauto; [simpl; tauto|].
        intros; simpl.
        repeat constructor.
      - econstructor; eauto; [simpl; tauto|].
        intros; simpl.
        repeat constructor.
      - econstructor; eauto; [simpl; tauto|].
        intros; simpl.
        repeat constructor.
      - econstructor; eauto; [simpl; tauto|].
        intros; simpl.
        repeat constructor.

    Qed.

    Lemma pdec_refines_pinst_op: pdec <<== pinst.
    Proof.
      admit.
    Qed.

  End SingleCore.

  Lemma pdecN_refines_scN: traceRefines id pdecN scN.
  Proof.
    apply traceRefines_modular_interacting with (vp:= (@idElementwise _)).

    - apply pdecfs_ModEquiv; auto.
    - apply pinsts_ModEquiv; auto.
    - apply memInst_ModEquiv; auto.
    - apply memInst_ModEquiv; auto.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - repeat split.
    - induction n; simpl; intros.
      + admit.
      + admit. (* apply traceRefines_modular_noninteracting. *)
    - rewrite idElementwiseId; apply traceRefines_refl.

  Qed.

End ProcDecSC.

