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

  Ltac fconn_tac meth := admit.

  Lemma procDec_inv:
    forall or l (Hclos: LtsStepClosure pdecfi or l),
    exists pcv stv stallv iemptyv insv ideqPv oemptyv oenqPv odeqPv,
      find ("pc"__ i) or = Some {| objType := Bit addrSize; objVal := pcv |} /\
      find ("rf"__ i) or = Some {| objType := Vector (Bit valSize) rfIdx; objVal := stv |} /\
      find ("stall"__ i) or = Some {| objType := Bool; objVal := stallv |} /\
      find ("Ins"__ i -n- "empty") or = Some {| objType := Bool; objVal := iemptyv |} /\
      find ("Ins"__ i -n- "elt") or = Some {| objType := Vector (atomK addrSize (Bit valSize)) O;
                                              objVal := insv |} /\
      find ("Ins"__ i -n- "deqP") or = Some {| objType := Bit O; objVal := ideqPv |} /\
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := oemptyv |} /\
      find ("Outs"__ i -n- "enqP") or = Some {| objType := Bit O; objVal := oenqPv |} /\
      find ("Outs"__ i -n- "deqP") or = Some {| objType := Bit O; objVal := odeqPv |} /\
      procDec_inv_1 stallv iemptyv oemptyv /\
      procDec_inv_2 oenqPv odeqPv /\
      procDec_inv_3 stv pcv iemptyv insv ideqPv.
  Proof.
    admit.
  Qed.
  (*   intros; dependent induction Hclos; intros; subst. *)
  (*   { do 9 eexists. *)
  (*     do 9 (split; [simpl; find_eq|]). *)
  (*     split. *)
  (*     { apply xor_1; intuition. } *)
  (*     { split; [reflexivity|]. *)
  (*       unfold procDec_inv_3; intros; inv H. *)
  (*     } *)
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

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H15; destruct x8; [discriminate|]. *)
  (*         assert (x5 = true) *)
  (*           by (clear -H8; destruct x2; destruct x5; inv H8; dest; intuition); subst. *)
  (*         apply xor_2; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)

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

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H15; destruct x8; [discriminate|]. *)
  (*         assert (x2 = true /\ x5 = true) *)
  (*           by (clear -H8; destruct x2; destruct x5; inv H8; dest; intuition); dest; subst. *)
  (*         apply xor_2; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)
        
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

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H18; destruct x9; [discriminate|]. *)
  (*         assert (x1 = true /\ x2 = true) *)
  (*           by (clear -H8; destruct x1; destruct x2; inv H8; dest; intuition); dest; subst. *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); simpl. *)
  (*         simpl; apply xor_1; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)
          
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

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H18; destruct x9; [discriminate|]. *)
  (*         assert (x1 = true /\ x2 = true) *)
  (*           by (clear -H8; destruct x1; destruct x2; inv H8; dest; intuition); dest; subst. *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); simpl. *)
  (*         simpl; apply xor_1; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)
        
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

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         assumption. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)

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

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         assumption. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x6); rewrite (shatter_word_0 x7); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)

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

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)
        
  (*       * (* invariant 1 *) *)
  (*         simpl in H17; destruct x11; [discriminate|]. *)
  (*         simpl in H22; destruct x15; [discriminate|]. *)
  (*         assert (x1 = true /\ x5 = true) *)
  (*           by (clear -H8; destruct x1; destruct x5; inv H8; dest; intuition); dest; subst. *)
          
  (*         rewrite (shatter_word_0 x17); rewrite (shatter_word_0 x18); simpl. *)
  (*         simpl; apply xor_3; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)

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

  (*       invariant_tac; basic_dest. *)

  (*       do 9 eexists. *)
  (*       do 9 (split; [find_eq; sassumption|]). *)
  (*       split; [|split]. *)

  (*       * (* invariant 1 *) *)
  (*         simpl in H17; destruct x11; [discriminate|]. *)
  (*         simpl in H22; destruct x15; [discriminate|]. *)
  (*         assert (x1 = true /\ x5 = true) *)
  (*           by (clear -H8; destruct x1; destruct x5; inv H8; dest; intuition); dest; subst. *)
          
  (*         rewrite (shatter_word_0 x17); rewrite (shatter_word_0 x18); simpl. *)
  (*         simpl; apply xor_3; intuition. *)

  (*       * (* invariant 2 *) *)
  (*         rewrite (shatter_word_0 x13); rewrite (shatter_word_0 x14); reflexivity. *)

  (*       * (* invariant 3 *) *)
  (*         admit. *)

  (*     + inv H11. *)
        
  (*   - (* should be an empty step *) *)
  (*     pose proof (pdecfi_none Hlts); dest; subst. *)
  (*     map_simpl_G. *)

  (*     do 9 eexists. *)
  (*     do 9 (split; [find_eq; sassumption|]). *)
  (*     split; [|split]; assumption. *)
      
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
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H5; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H1. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H. *)
  (*     invertActionRep. *)
  (*     map_simpl H1. clear -H H1 H2. *)
  (*     destruct x; intuition. *)
  (*     simpl in H, H1; rewrite H in H1. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H8; inv H8; dest; intuition. *)
  (*   destruct x5; intuition. *)
  (* Qed. *)

  Lemma proc_reqSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("reqSt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H5; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H1. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H0. *)
  (*     invertActionRep. *)
  (*     map_simpl H1. clear -H H1 H2. *)
  (*     simpl in H2; destruct x; intuition. *)
  (*     simpl in H, H1; rewrite H in H1. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H8; inv H8; dest; intuition. *)
  (*   destruct x5; intuition. *)
  (* Qed. *)

  Lemma proc_execHt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execHt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H5; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H1. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H. *)
  (*     invertActionRep. *)
  (*     map_simpl H1. clear -H H1 H2. *)
  (*     simpl in H2; destruct x; intuition. *)
  (*     simpl in H, H1; rewrite H in H1. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H8; inv H8; dest; intuition. *)
  (*   destruct x5; intuition. *)
  (* Qed. *)

  Lemma proc_execNm_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execNm"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)
  (*   rewrite H5; repeat f_equal. *)

  (*   assert (x1 = false); subst. *)
  (*   { clear -Hstep H1. *)
  (*     invStep Hstep. *)
  (*     invertSemMod Hltsmod2. *)
  (*     in_tac_H; vdiscriminate; inv H0. *)
  (*     invertActionRep. *)
  (*     map_simpl H1. clear -H H1 H2. *)
  (*     simpl in H2; destruct x; intuition. *)
  (*     simpl in H, H1; rewrite H in H1. *)
  (*     basic_dest; reflexivity. *)
  (*   } *)

  (*   clear -H8; inv H8; dest; intuition. *)
  (*   destruct x5; intuition. *)
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
  (*   intros; pose proof (procDec_inv Hclos) as Hinv; dest; subst. *)

  (*   assert (x2 = false /\ x3 x4 ``("type") = evalConstT opLd); dest; subst. *)
  (*   { clear -Hstep H2. *)
  (*     admit. *)
  (*   } *)

  (*   split. *)

  (*   - rewrite H5; repeat f_equal. *)
  (*     clear -H8; inv H8; dest; intuition. *)
  (*     destruct x5; intuition. *)

  (*   - do 6 eexists. *)
  (*     do 6 (split; [sassumption|]). *)
  (*     specialize (H10 eq_refl); dest. *)
  (*     repeat split; auto. *)
  (*     + rewrite H12 in H10; assumption. *)
  (* Qed. *)

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

