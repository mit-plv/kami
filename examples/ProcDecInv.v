Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.

Require Import Program.Equality. (* For dependent induction *)

Set Implicit Arguments.

Section Xor3.
  Definition Xor3 (P Q R: Prop) := P /\ ~Q /\ ~R \/ ~P /\ Q /\ ~R \/ ~P /\ ~Q /\ R.

  Lemma xor_1: forall (P Q R: Prop), P -> ~Q -> ~R -> Xor3 P Q R.
  Proof. intros; left; intuition. Qed.

  Lemma xor_2: forall (P Q R: Prop), ~P -> Q -> ~R -> Xor3 P Q R.
  Proof. intros; right; left; intuition. Qed.

  Lemma xor_3: forall (P Q R: Prop), ~P -> ~Q -> R -> Xor3 P Q R.
  Proof. intros; right; right; intuition. Qed.

End Xor3.

Section Invariants.
  Variables addrSize valSize rfIdx: nat.
  Variable i: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition pdecfi := pdecfi dec exec i.
  Hint Unfold pdecfi : ModuleDefs.
  
  Lemma pdecfi_none:
    forall or nr dmMap cmMap (Hstep: LtsStep pdecfi None or nr dmMap cmMap),
      nr = empty /\ dmMap = empty /\ cmMap = empty.
  Proof.
    admit.
  Qed.
  (*   intros; invStep. *)

  (*   invertSemMod Hltsmod2. (* proc *) *)
  (*   invertSemMod Hltsmod1. (* mid *) *)

  (*   invertSemMod Hltsmod0; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*   invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*   invertSemMod HSemMod0. (* outs *) *)

  (*   invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*   invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*   invertSemMod HSemMod0. (* ins *) *)

  (*   filt_dest. *)
  (*   repeat split; auto. *)
  (* Qed. *)

  Definition procDec_inv_1 stallv iemptyv oemptyv :=
    Xor3 (stallv = false) (iemptyv = false) (oemptyv = false).

  Definition procDec_inv_2 (oenqPv odeqPv: type (Bit O)) :=
    oenqPv = odeqPv.

  Definition procDec_inv_3
             (stv: type (Vector (Bit valSize) rfIdx))
             (pcv: type (Bit addrSize))
             (iemptyv: type Bool)
             (insv: type (Vector (atomK addrSize (Bit valSize)) O))
             (ideqPv: type (Bit O)) :=
    iemptyv = false ->
    dec stv pcv ``"opcode" = insv ideqPv ``"type" /\
    insv ideqPv ``"addr" = dec stv pcv ``"addr" /\    
    insv ideqPv ``"value" = if (weq (dec stv pcv ``"opcode") (evalConstT opLd)) then
                              evalConstT (getDefaultConst (Bit valSize))
                            else
                              dec stv pcv ``"value".

  Lemma procDec_inv:
    forall or l (Hclos: LtsStepClosure pdecfi or l),
    exists pcv stv stallv iemptyv insv ideqPv oemptyv oenqPv odeqPv,
      (find ("pc"__ i) or = Some {| objType := SyntaxKind (Bit addrSize); objVal := pcv |} /\
       find ("rf"__ i) or = Some {| objType := SyntaxKind (Vector (Bit valSize) rfIdx); objVal := stv |} /\
       find ("stall"__ i) or = Some {| objType := SyntaxKind Bool; objVal := stallv |} /\
       find ("Ins"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool; objVal := iemptyv |} /\
       find ("Ins"__ i -n- "elt") or = Some {| objType := SyntaxKind (Vector (atomK addrSize (Bit valSize)) O);
                                               objVal := insv |} /\
       find ("Ins"__ i -n- "deqP") or = Some {| objType := SyntaxKind (Bit O); objVal := ideqPv |} /\
       find ("Outs"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool; objVal := oemptyv |} /\
       find ("Outs"__ i -n- "enqP") or = Some {| objType := SyntaxKind (Bit O); objVal := oenqPv |} /\
       find ("Outs"__ i -n- "deqP") or = Some {| objType := SyntaxKind (Bit O); objVal := odeqPv |}) /\

      (procDec_inv_1 stallv iemptyv oemptyv /\
       procDec_inv_2 oenqPv odeqPv /\
       procDec_inv_3 stv pcv iemptyv insv ideqPv).
  Proof.
    admit.
  Qed.
  (*   intros; dependent induction Hclos; intros; subst. *)
  (*   { do 9 eexists; split. *)
  (*     { repeat split; simpl; find_eq. } *)
  (*     { split; [|split]. *)
  (*       { apply xor_1; intuition. } *)
  (*       { reflexivity. } *)
  (*       { unfold procDec_inv_3; intros; inv H. } *)
  (*     } *)
  (*   } *)

  (*   specialize (IHHclos eq_refl). *)
  (*   destruct rm. *)

  (*   - inv Hlts; inv Hlts2; inv Hlts0. *)
  (*     destConcatLabel. *)
  (*     repeat match goal with *)
  (*              | [H: find _ _ = Some _ |- _] => progress map_simpl H *)
  (*            end. *)
  (*     destRuleRep; repeat combRule. *)

  (*     + (** processLd *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod1. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod; *)
  (*         [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* outs *) *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* ins *) *)

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)
        
  (*       * (* invariant 1 *) *)
  (*         (* simpl in H17; destruct x11; [discriminate|]. *) *)
  (*         simpl in H21; destruct x15; [discriminate|]. *)
  (*         assert (x1 = true) *)
  (*           by (clear -H0; destruct x1; destruct x5; inv H0; dest; intuition); subst. *)
  (*         rewrite (shatter_word_0 x17); rewrite (shatter_word_0 x18); simpl. *)
  (*         apply xor_3; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         rewrite (shatter_word_0 x17); rewrite (shatter_word_0 x18); simpl. *)
  (*         unfold procDec_inv_3; intros; inv H11. *)

  (*     + (** processSt *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod1. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod; *)
  (*         [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* outs *) *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* ins *) *)

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H21; destruct x15; [discriminate|]. *)
  (*         assert (x1 = true) *)
  (*           by (clear -H0; destruct x1; destruct x5; inv H0; dest; intuition); subst. *)
  (*         rewrite (shatter_word_0 x17); rewrite (shatter_word_0 x18); simpl. *)
  (*         apply xor_3; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         rewrite (shatter_word_0 x17); rewrite (shatter_word_0 x18); simpl. *)
  (*         unfold procDec_inv_3; intros; inv H11. *)

  (*     + (* reqLd *) *)
  (*       invertActionRep. *)

  (*       invertSemMod Hltsmod1. (* proc *) *)
  (*       invertSemMod HSemMod. (* mid *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod0; [|invertSemMod HSemMod; invertSemMod HSemMod0; *)
  (*                                fconn_tac ("Ins"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)
  (*       filt_dest; invertActionRep. *)

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H14; destruct x8; [discriminate|]. *)
  (*         assert (x5 = true) *)
  (*           by (clear -H0; destruct x2; destruct x5; inv H0; dest; intuition); subst. *)
  (*         apply xor_2; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         unfold procDec_inv_3; intros. *)
  (*         rewrite (shatter_word_0 x14); rewrite (shatter_word_0 x15); simpl. *)
  (*         conn_tac ("Ins"__ i -n- "enq"). *)
  (*         repeat split; try reflexivity. *)
  (*         { destruct (weq _ _) in H17; [|discriminate]. *)
  (*           sassumption. *)
  (*         } *)
  (*         { destruct (weq _ _) in H17; [|discriminate]. *)
  (*           find_if_inside; [|elim n; assumption]. *)
  (*           reflexivity. *)
  (*         } *)

  (*     + (** reqSt *) *)
  (*       invertActionRep. *)

  (*       invertSemMod HSemMod. (* proc *) *)
  (*       invertSemMod Hltsmod1. (* mid *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod0; [|invertSemMod HSemMod; invertSemMod HSemMod0; *)
  (*                                fconn_tac ("Ins"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)
  (*       filt_dest; invertActionRep. *)

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H14; destruct x8; [discriminate|]. *)
  (*         assert (x5 = true) *)
  (*           by (clear -H0; destruct x2; destruct x5; inv H0; dest; intuition); subst. *)
  (*         apply xor_2; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         unfold procDec_inv_3; intros. *)
  (*         rewrite (shatter_word_0 x14); rewrite (shatter_word_0 x15); simpl. *)
  (*         conn_tac ("Ins"__ i -n- "enq"). *)
  (*         repeat split; try reflexivity. *)
  (*         { destruct (weq _ _) in H17; [|discriminate]. *)
  (*           sassumption. *)
  (*         } *)
  (*         { destruct (weq _ _) in H17; [|discriminate]. *)
  (*           match goal with *)
  (*             | [ |- context [if weq ?w _ then _ else _] ] => *)
  (*               progress replace w with WO~0~1 by assumption *)
  (*           end. *)
  (*           reflexivity. *)
  (*         } *)
        
  (*     + (** repLd *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod1. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)
  (*       invertActionRep. *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         destruct x9; [discriminate|]. *)
  (*         assert (x2 = true) *)
  (*           by (clear -H0; destruct x1; destruct x2; inv H0; dest; intuition); subst. *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); simpl. *)
  (*         apply xor_1; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         destruct x9; [discriminate|]. *)
  (*         assert (x2 = true) *)
  (*           by (clear -H0; destruct x1; destruct x2; inv H0; dest; intuition); subst. *)
  (*         unfold procDec_inv_3; intros; inv H11. *)

  (*     + (* repSt *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod1. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)
  (*       invertActionRep. *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)
        
  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         destruct x9; [discriminate|]. *)
  (*         assert (x2 = true) *)
  (*           by (clear -H0; destruct x1; destruct x2; inv H0; dest; intuition); subst. *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); simpl. *)
  (*         apply xor_1; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         destruct x9; [discriminate|]. *)
  (*         assert (x2 = true) *)
  (*           by (clear -H0; destruct x1; destruct x2; inv H0; dest; intuition); subst. *)
  (*         unfold procDec_inv_3; intros; inv H11. *)
        
  (*     + (** execHt *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod1. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         assumption. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         assumption. *)

  (*     + (** execNm *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod1. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         assumption. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         destruct x8; [discriminate|]. *)
  (*         assert (x2 = true) *)
  (*           by (clear -H0; destruct x2; destruct x5; inv H0; dest; intuition); subst. *)
  (*         unfold procDec_inv_3; intros; inv H11. *)

  (*     + inv H11. *)
        
  (*   - (* should be an empty step *) *)
  (*     pose proof (pdecfi_none Hlts); dest; subst. *)
  (*     map_simpl_G. *)

  (*     do 9 eexists; split; [repeat split; find_eq; sassumption|]. *)
  (*     split; [|split]; assumption. *)
      
  (* Qed. *)

  Variables (l: list RuleLabelT) (or nr: RegsT) (dmMap cmMap: CallsT) (rm: option string).
  
  Lemma proc_reqLd_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("reqLd"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H8; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H4. *)
  (*     invStep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H. *)
  (*     invertActionRep. *)
  (*     map_simpl H4. clear -H H1 H4. *)
  (*     destruct x; [discriminate|]. *)
  (*     simpl in H, H4; rewrite H in H4. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H0; inv H0; dest; intuition. *)
  (*   destruct x5; intuition. *)
  (* Qed. *)

  Lemma proc_reqSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("reqSt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H8; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H4. *)
  (*     invStep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H0. *)
  (*     invertActionRep. *)
  (*     map_simpl H4. clear -H H1 H4. *)
  (*     destruct x; [discriminate|]. *)
  (*     simpl in H, H4; rewrite H in H4. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H0; inv H0; dest; intuition. *)
  (*   destruct x5; intuition. *)
  (* Qed. *)

  Lemma proc_execHt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execHt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H8; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H4. *)
  (*     invStep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H. *)
  (*     invertActionRep. *)
  (*     map_simpl H4. clear -H H1 H4. *)
  (*     destruct x; [discriminate|]. *)
  (*     simpl in H, H4; rewrite H in H4. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H0; inv H0; dest; intuition. *)
  (*   destruct x5; intuition. *)
  (* Qed. *)

  Lemma proc_execNm_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execNm"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H8; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H4. *)
  (*     invStep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H0. *)
  (*     invertActionRep. *)
  (*     map_simpl H4. clear -H H1 H4. *)
  (*     destruct x; [discriminate|]. *)
  (*     simpl in H, H4; rewrite H in H4. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H0; inv H0; dest; intuition. *)
  (*   destruct x5; intuition. *)
  (* Qed. *)

  Lemma mid_processLd_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("Mid"__ i -n- "processLd")),
      exists pcv stv insv ideqPv oemptyv oenqPv odeqPv,
        find ("pc"__ i) or = Some {| objType := SyntaxKind (Bit addrSize); objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := SyntaxKind (Vector (Bit valSize) rfIdx);
                                     objVal := stv |} /\
        find ("Ins"__ i -n- "elt") or =
        Some {| objType := SyntaxKind (Vector (atomK addrSize (Bit valSize)) O);
                objVal := insv |} /\
        find ("Ins"__ i -n- "deqP") or = Some {| objType := SyntaxKind (Bit O);
                                                 objVal := ideqPv |} /\
        find ("Outs"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool;
                                                   objVal := oemptyv |} /\
        find ("Outs"__ i -n- "enqP") or = Some {| objType := SyntaxKind (Bit O);
                                                  objVal := oenqPv |} /\
        find ("Outs"__ i -n- "deqP") or = Some {| objType := SyntaxKind (Bit O);
                                                  objVal := odeqPv |} /\
        dec stv pcv ``"opcode" = evalConstT opLd /\
        insv ideqPv ``"addr" = dec stv pcv ``"addr" /\
        insv ideqPv ``"value" = evalConstT (getDefaultConst (Bit valSize)) /\
        oemptyv = true /\ oenqPv = odeqPv.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   do 7 eexists. *)
  (*   do 7 (split; [eassumption|]). *)

  (*   invStep. *)
  (*   invertSemMod Hltsmod1. (* mid *) *)
  (*   in_tac_H; vdiscriminate; *)
  (*   [|exfalso; clear -H12; *)
  (*     match goal with *)
  (*       | [H: ?l = ?r |- _] => assert (attrName l = attrName r) by (rewrite H; reflexivity) *)
  (*     end; *)
  (*     apply appendName_neq in H; inv H]. *)
  (*   inv H11. *)
  (*   invertSemMod HSemMod. *)
  (*   invertActionRep. *)
    
  (*   invertSemMod Hltsmod2. (* proc *) *)

  (*   invertSemMod Hltsmod0; *)
  (*     [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")]. *)
  (*   invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*   invertSemMod HSemMod0. *)
  (*   invertActionRep. (* outs *) *)

  (*   invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*   invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")]. *)
  (*   invertSemMod HSemMod0. *)
  (*   invertActionRep. (* ins *) *)

  (*   invariant_tac; basic_dest. *)

  (*   callIffDef_dest; filt_dest. *)
  (*   pred_dest ("Ins"__ i -n- "deq"). *)
  (*   invariant_tac; basic_dest. *)

  (*   destruct x15; [discriminate|]. *)
  (*   specialize (H2 eq_refl); dest. *)
  (*   destruct (weq _ _) in H12; [|discriminate]. *)
  (*   assert (Hopc: dec x0 x ``("opcode") = evalConstT opLd) by (rewrite H2; assumption). *)

  (*   repeat split. *)

  (*   - assumption. *)
  (*   - assumption. *)
  (*   - rewrite Hopc in H25. assumption. *)
  (*   - clear -H0; inv H0; dest; intuition. *)
  (*     destruct x5; intuition. *)
  (*   - assumption. *)

  (* Qed. *)

  Lemma mid_processSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("Mid"__ i -n- "processSt")),
      exists pcv stv insv ideqPv oemptyv oenqPv odeqPv,
        find ("pc"__ i) or = Some {| objType := SyntaxKind (Bit addrSize); objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := SyntaxKind (Vector (Bit valSize) rfIdx);
                                     objVal := stv |} /\
        find ("Ins"__ i -n- "elt") or =
        Some {| objType := SyntaxKind (Vector (atomK addrSize (Bit valSize)) O);
                objVal := insv |} /\
        find ("Ins"__ i -n- "deqP") or = Some {| objType := SyntaxKind (Bit O);
                                                 objVal := ideqPv |} /\
        find ("Outs"__ i -n- "empty") or = Some {| objType := SyntaxKind Bool;
                                                   objVal := oemptyv |} /\
        find ("Outs"__ i -n- "enqP") or = Some {| objType := SyntaxKind (Bit O);
                                                  objVal := oenqPv |} /\
        find ("Outs"__ i -n- "deqP") or = Some {| objType := SyntaxKind (Bit O);
                                                  objVal := odeqPv |} /\
        dec stv pcv ``"opcode" = evalConstT opSt /\
        insv ideqPv ``"addr" = dec stv pcv ``"addr" /\
        insv ideqPv ``"value" = dec stv pcv ``"value" /\
        oemptyv = true /\ oenqPv = odeqPv.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   do 7 eexists. *)
  (*   do 7 (split; [eassumption|]). *)

  (*   invStep. *)
  (*   invertSemMod Hltsmod1. (* mid *) *)
  (*   in_tac_H; vdiscriminate; *)
  (*   [exfalso; clear -H11; *)
  (*    match goal with *)
  (*      | [H: ?l = ?r |- _] => assert (attrName l = attrName r) by (rewrite H; reflexivity) *)
  (*    end; *)
  (*    apply appendName_neq in H; inv H|]. *)
  (*   inv H12. *)
  (*   invertSemMod HSemMod. *)
  (*   invertActionRep. *)

  (*   invertSemMod Hltsmod2. (* proc *) *)

  (*   invertSemMod Hltsmod0; *)
  (*     [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")]. *)
  (*   invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*   invertSemMod HSemMod0. *)
  (*   invertActionRep. (* outs *) *)

  (*   invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*   invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")]. *)
  (*   invertSemMod HSemMod0. *)
  (*   invertActionRep. (* ins *) *)

  (*   invariant_tac; basic_dest. *)

  (*   callIffDef_dest; filt_dest. *)
  (*   pred_dest ("Ins"__ i -n- "deq"). *)
  (*   invariant_tac; basic_dest. *)

  (*   destruct x15; [discriminate|]. *)
  (*   specialize (H2 eq_refl); dest. *)
  (*   destruct (weq _ _) in H12; [|discriminate]. *)
  (*   assert (Hopc: dec x0 x ``("opcode") = evalConstT opSt) by (rewrite H2; assumption). *)

  (*   repeat split. *)

  (*   - assumption. *)
  (*   - assumption. *)
  (*   - rewrite Hopc in H25; assumption. *)
  (*   - clear -H0; inv H0; dest; intuition. *)
  (*     destruct x5; intuition. *)
  (*   - assumption. *)

  (* Qed. *)

End Invariants.

