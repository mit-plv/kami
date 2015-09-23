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
  (*   intros; invStep Hstep. *)

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

  Lemma procRef_inv_1:
    forall or l (Hclos: LtsStepClosure pdecfi or l),
    exists stallv iemptyv oemptyv,
      find ("stall"__ i) or = Some {| objType := Bool; objVal := stallv |} /\
      find ("Ins"__ i -n- "empty") or = Some {| objType := Bool; objVal := iemptyv |} /\
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := oemptyv |} /\
      (Xor3 (stallv = false) (iemptyv = false) (oemptyv = false)).
  Proof.
    admit.
  Qed.
  (*   intros; dependent induction Hclos; intros; subst. *)
  (*   { repeat eexists; try (simpl; find_eq; fail). *)
  (*     apply xor_1; intuition. *)
  (*   } *)

  (*   specialize (IHHclos eq_refl). *)
  (*   destruct rm. *)

  (*   - inv Hlts; inv Hlts2; inv Hlts0. *)
  (*     destConcatLabel. *)
  (*     map_simpl H; map_simpl H0; map_simpl H1. *)
  (*     destRule Hlts1; destRule Hlts2; destRule Hlts3; destRule Hlts4; repeat combRule. *)

  (*     + (** reqLd *) *)
  (*       invertActionRep. *)

  (*       invertSemMod HSemMod. (* proc *) *)
  (*       invertSemMod Hltsmod0. (* mid *) *)

  (*       invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod; [|invertSemMod HSemMod; invertSemMod HSemMod0; *)
  (*                               fconn_tac ("Ins"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)
  (*       filt_dest; invertActionRep. *)

  (*       simpl in H6; destruct x2; [discriminate|]. *)
  (*       invariant_tac; basic_dest. *)
  (*       assert (x0 = true /\ x1 = true) *)
  (*         by (clear -H2; destruct x0; destruct x1; inv H2; dest; intuition); dest; subst. *)

  (*       repeat eexists; eauto. *)
  (*       simpl; apply xor_2; intuition. *)

  (*     + (** reqSt *) *)
  (*       invertActionRep. *)

  (*       invertSemMod HSemMod. (* proc *) *)
  (*       invertSemMod Hltsmod0. (* mid *) *)

  (*       invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod; [|invertSemMod HSemMod; invertSemMod HSemMod0; *)
  (*                               fconn_tac ("Ins"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)
  (*       filt_dest; invertActionRep. *)

  (*       simpl in H7; destruct x2; [discriminate|]. *)
  (*       invariant_tac; basic_dest. *)
  (*       assert (x0 = true /\ x1 = true) *)
  (*         by (clear -H2; destruct x0; destruct x1; inv H2; dest; intuition); dest; subst. *)

  (*       repeat eexists; eauto. *)
  (*       simpl; apply xor_2; intuition. *)
        
  (*     + (** repLd *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod0. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)
  (*       invertActionRep. *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)

  (*       simpl in H10; destruct x3; [discriminate|]. *)
  (*       invariant_tac; basic_dest. *)
  (*       assert (x = true /\ x0 = true) *)
  (*         by (clear -H2; destruct x; destruct x0; inv H2; dest; intuition); dest; subst. *)
        
  (*       repeat eexists; eauto. *)
  (*       rewrite (shatter_word_0 x7); rewrite (shatter_word_0 x8); simpl. *)
  (*       simpl; apply xor_1; intuition. *)

  (*     + (* repSt *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod0. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)
  (*       invertActionRep. *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)

  (*       simpl in H10; destruct x3; [discriminate|]. *)
  (*       invariant_tac; basic_dest. *)
  (*       assert (x = true /\ x0 = true) *)
  (*         by (clear -H2; destruct x; destruct x0; inv H2; dest; intuition); dest; subst. *)

  (*       repeat eexists; eauto. *)
  (*       rewrite (shatter_word_0 x7); rewrite (shatter_word_0 x8); simpl. *)
  (*       simpl; apply xor_1; intuition. *)
        
  (*     + (** execHt *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod0. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)

  (*       invariant_tac; basic_dest. *)

  (*       repeat eexists; eauto. *)

  (*     + (** execNm *) *)
  (*       invertActionRep. *)
  (*       invertSemMod Hltsmod0. (* mid *) *)
  (*       invertSemMod HSemMod. (* proc *) *)

  (*       invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* outs *) *)

  (*       invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. (* ins *) *)

  (*       invariant_tac; basic_dest. *)

  (*       repeat eexists; eauto. *)

  (*     + (** processLd *) *)
  (*       invertActionRep. *)
  (*       invertSemMod HSemMod. (* mid *) *)
  (*       invertSemMod Hltsmod. (* proc *) *)

  (*       invertSemMod Hltsmod1; *)
  (*         [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* outs *) *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* ins *) *)

  (*       simpl in H8; destruct x5; [discriminate|]. *)
  (*       simpl in H13; destruct x9; [discriminate|]. *)
  (*       invariant_tac; basic_dest. *)
  (*       assert (x = true /\ x1 = true) *)
  (*         by (clear -H2; destruct x; destruct x1; inv H2; dest; intuition); dest; subst. *)

  (*       repeat eexists; eauto. *)
  (*       rewrite (shatter_word_0 x11); rewrite (shatter_word_0 x12); simpl. *)
  (*       simpl; apply xor_3; intuition. *)

  (*     + (** processSt *) *)
  (*       invertActionRep. *)
  (*       invertSemMod HSemMod. (* mid *) *)
  (*       invertSemMod Hltsmod. (* proc *) *)

  (*       invertSemMod Hltsmod1; *)
  (*         [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")]. *)
  (*       invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* outs *) *)

  (*       invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|]. *)
  (*       invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")]. *)
  (*       invertSemMod HSemMod0. *)
  (*       invertActionRep. (* ins *) *)

  (*       simpl in H8; destruct x5; [discriminate|]. *)
  (*       simpl in H13; destruct x9; [discriminate|]. *)
  (*       invariant_tac; basic_dest. *)
  (*       assert (x = true /\ x1 = true) *)
  (*         by (clear -H2; destruct x; destruct x1; inv H2; dest; intuition); dest; subst. *)

  (*       repeat eexists; eauto. *)
  (*       rewrite (shatter_word_0 x11); rewrite (shatter_word_0 x12); simpl. *)
  (*       simpl; apply xor_3; intuition. *)

  (*     + inv H3. *)
        
  (*   - (* should be an empty step *) *)
  (*     pose proof (pdecfi_none Hlts); dest; subst. *)
  (*     map_simpl_G. *)
  (*     repeat eexists; eauto. *)
      
  (* Qed. *)

  Variables (l: list RuleLabelT) (or nr: RegsT) (dmMap cmMap: CallsT) (rm: option string).
  
  Lemma proc_reqLd_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("reqLd"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procRef_inv_1 Hclos) as Hinv; dest; subst. *)
  (*   rewrite H1; repeat f_equal. *)

  (*   assert (x = false); subst. *)
  (*   { clear -Hstep H. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H0. *)
  (*     invertActionRep. *)
  (*     map_simpl H; clear -H H0 H3. *)
  (*     simpl in H3; destruct x0; intuition. *)
  (*     simpl in H, H0; rewrite H in H0. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H2; inv H2; dest; intuition. *)
  (*   destruct x1; intuition. *)
  (* Qed. *)

  Lemma proc_reqSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("reqSt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procRef_inv_1 Hclos) as Hinv; dest; subst. *)
  (*   rewrite H1; repeat f_equal. *)

  (*   assert (x = false); subst. *)
  (*   { clear -Hstep H. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H1. *)
  (*     invertActionRep. *)
  (*     map_simpl H; clear -H H0 H3. *)
  (*     simpl in H3; destruct x0; intuition. *)
  (*     simpl in H, H0; rewrite H in H0. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H2; inv H2; dest; intuition. *)
  (*   destruct x1; intuition. *)
  (* Qed. *)

  Lemma proc_execHt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execHt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procRef_inv_1 Hclos) as Hinv; dest; subst. *)
  (*   rewrite H1; repeat f_equal. *)

  (*   assert (x = false); subst. *)
  (*   { clear -Hstep H. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H0. *)
  (*     invertActionRep. *)
  (*     map_simpl H; clear -H H0 H3. *)
  (*     simpl in H3; destruct x0; intuition. *)
  (*     simpl in H, H0; rewrite H in H0. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H2; inv H2; dest; intuition. *)
  (*   destruct x1; intuition. *)
  (* Qed. *)

  Lemma proc_execNm_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execNm"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procRef_inv_1 Hclos) as Hinv; dest; subst. *)
  (*   rewrite H1; repeat f_equal. *)

  (*   assert (x = false); subst. *)
  (*   { clear -Hstep H. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H1. *)
  (*     invertActionRep. *)
  (*     map_simpl H; clear -H H0 H3. *)
  (*     simpl in H3; destruct x0; intuition. *)
  (*     simpl in H, H0; rewrite H in H0. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H2; inv H2; dest; intuition. *)
  (*   destruct x1; intuition. *)
  (* Qed. *)

  Lemma mid_processLd_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("Mid"__ i -n- "processLd")),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |} /\
      exists pcv stv insv ideqPv oenqPv odeqPv,
        find ("pc"__ i) or = Some {| objType := Bit addrSize; objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := Vector (Bit valSize) rfIdx;
                                     objVal := stv |} /\
        find ("Ins"__ i -n- "elt") or = Some {| objType := Vector (atomK addrSize (Bit valSize)) O;
                                                objVal := insv |} /\
        find ("Ins"__ i -n- "deqP") or = Some {| objType := Bit O;
                                                 objVal := ideqPv |} /\
        find ("Outs"__ i -n- "enqP") or = Some {| objType := Bit O;
                                                  objVal := oenqPv |} /\
        find ("Outs"__ i -n- "deqP") or = Some {| objType := Bit O;
                                                  objVal := odeqPv |} /\
        dec stv pcv ``"opcode" = evalConstT opLd /\
        insv ideqPv ``"addr" = dec stv pcv ``"addr" /\
        insv ideqPv ``"value" = evalConstT (getDefaultConst (Bit valSize)) /\
        oenqPv = odeqPv.
  Proof.
    admit.
  Qed.

  Lemma mid_processSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("Mid"__ i -n- "processSt")),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |} /\
      exists pcv stv insv ideqPv oenqPv odeqPv,
        find ("pc"__ i) or = Some {| objType := Bit addrSize; objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := Vector (Bit valSize) rfIdx;
                                     objVal := stv |} /\
        find ("Ins"__ i -n- "elt") or = Some {| objType := Vector (atomK addrSize (Bit valSize)) O;
                                                objVal := insv |} /\
        find ("Ins"__ i -n- "deqP") or = Some {| objType := Bit O;
                                                 objVal := ideqPv |} /\
        find ("Outs"__ i -n- "enqP") or = Some {| objType := Bit O;
                                                  objVal := oenqPv |} /\
        find ("Outs"__ i -n- "deqP") or = Some {| objType := Bit O;
                                                  objVal := odeqPv |} /\
        dec stv pcv ``"opcode" = evalConstT opSt /\
        insv ideqPv ``"addr" = dec stv pcv ``"addr" /\
        insv ideqPv ``"value" = dec stv pcv ``"value" /\
        oenqPv = odeqPv.
  Proof.
    admit.
  Qed.

End Invariants.

