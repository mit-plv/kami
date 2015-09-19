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
  
  Lemma pdecfi_none:
    forall or nr dmMap cmMap (Hstep: LtsStep pdecfi None or nr dmMap cmMap),
      nr = empty /\ dmMap = empty /\ cmMap = empty.
  Proof.
    intros.
    inv Hstep.
    inv Hlts2.
    inv Hlts0.
    destConcatLabel.

    assert (rm1 = None /\ rm2 = None); dest; subst.
    { clear -Hcrm1; unfold CombineRm in Hcrm1; simpl in Hcrm1.
      destruct rm1, rm2; intuition; inversion H1.
    }
    assert (rm0 = None /\ rm3 = None); dest; subst.
    { clear -Hcrm0; unfold CombineRm in Hcrm0; simpl in Hcrm0.
      destruct rm0, rm3; intuition; inversion H1.
    }
    assert (rm4 = None /\ rm5 = None); dest; subst.
    { clear -Hcrm; unfold CombineRm in Hcrm; simpl in Hcrm.
      destruct rm4, rm5; intuition; inversion H1.
    }

    inv Hlts1; inv Hltsmod. (* proc *)
    inv Hlts3; inv Hltsmod. (* mid *)

    inv Hlts4.
    invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
    invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
    invertSemMod HSemMod0. (* outs *)

    inv Hlts2.
    invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|].
    invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
    invertSemMod HSemMod0. (* ins *)

    filt_dest.
    repeat split; auto.
  Qed.

  Variables or nr: RegsT.
  Variable l: list RuleLabelT.
  Variables (rm: option string) (dmMap cmMap: CallsT).

  Lemma procRef_inv_1:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm <> None),
    exists stallv iemptyv oemptyv,
      find ("stall"__ i) or = Some {| objType := Bool; objVal := stallv |} /\
      find ("Ins"__ i -n- "empty") or = Some {| objType := Bool; objVal := iemptyv |} /\
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := oemptyv |} /\
      (Xor3 (stallv = false) (iemptyv = false) (oemptyv = false)).
  Proof.
    intros.
    generalize dependent nr; generalize dependent rm;
    generalize dependent dmMap; generalize dependent cmMap.
    dependent induction Hclos; intros; subst.
    { repeat eexists.
      { simpl. find_eq. }
      { simpl. find_eq. }
      { simpl. find_eq. }
      { apply xor_1; intuition. }
    }

    specialize (IHHclos eq_refl).
    destruct rm0.
      
    - assert (Hsn: Some s <> None) by discriminate.
      specialize (IHHclos _ _ _ Hsn _ Hlts); clear Hsn.
      destruct rm1; [|elim Hrm; reflexivity].

      inv Hlts.
      inv Hlts2.
      inv Hlts0.
      destConcatLabel.
      map_simpl H; map_simpl H0; map_simpl H1.
      destRule Hlts1; destRule Hlts2; destRule Hlts3; destRule Hlts4; repeat combRule.

      + (** reqLd *)
        inv H3.
        invertActionRep.

        invertSemMod HSemMod. (* proc *)
        invertSemMod Hltsmod0. (* mid *)

        invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod; [|invertSemMod HSemMod; invertSemMod HSemMod0;
                                fconn_tac ("Ins"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)
        filt_dest; invertActionRep.

        simpl in H6; destruct x2; [discriminate|].
        invariant_tac; basic_dest.
        assert (x0 = true /\ x1 = true)
          by (clear -H2; destruct x0; destruct x1; inv H2; dest; intuition); dest; subst.

        repeat eexists.
        { find_eq. }
        { find_eq. }
        { find_eq; sassumption. }
        { simpl; apply xor_2; intuition. }
        
      + (** reqSt *)
        invertActionRep.

        invertSemMod HSemMod. (* proc *)
        invertSemMod Hltsmod0. (* mid *)

        invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod; [|invertSemMod HSemMod; invertSemMod HSemMod0;
                                fconn_tac ("Ins"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)
        filt_dest; invertActionRep.

        simpl in H7; destruct x2; [discriminate|].
        invariant_tac; basic_dest.
        assert (x0 = true /\ x1 = true)
          by (clear -H2; destruct x0; destruct x1; inv H2; dest; intuition); dest; subst.

        repeat eexists.
        { find_eq. }
        { find_eq. }
        { find_eq; sassumption. }
        { simpl; apply xor_2; intuition. }
        
      + (** repLd *)
        invertActionRep.
        invertSemMod Hltsmod0. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")].
        invertSemMod HSemMod0. (* outs *)
        invertActionRep.

        invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0.

        simpl in H10; destruct x3; [discriminate|].
        invariant_tac; basic_dest.
        assert (x = true /\ x0 = true)
          by (clear -H2; destruct x; destruct x0; inv H2; dest; intuition); dest; subst.

        repeat eexists.
        { find_eq. }
        { find_eq; sassumption. }
        { find_eq. }
        { rewrite (shatter_word_0 x7); rewrite (shatter_word_0 x8); simpl.
          simpl; apply xor_1; intuition.
        }

      + (* repSt *)
        invertActionRep.
        invertSemMod Hltsmod0. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")].
        invertSemMod HSemMod0. (* outs *)
        invertActionRep.

        invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0.

        simpl in H10; destruct x3; [discriminate|].
        invariant_tac; basic_dest.
        assert (x = true /\ x0 = true)
          by (clear -H2; destruct x; destruct x0; inv H2; dest; intuition); dest; subst.

        repeat eexists.
        { find_eq. }
        { find_eq; sassumption. }
        { find_eq. }
        { rewrite (shatter_word_0 x7); rewrite (shatter_word_0 x8); simpl.
          simpl; apply xor_1; intuition.
        }
        
      + (** execHt *)
        invertActionRep.
        invertSemMod Hltsmod0. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)

        invariant_tac; basic_dest.

        repeat eexists.
        { find_eq; sassumption. }
        { find_eq; sassumption. }
        { find_eq; sassumption. }
        { assumption. }

      + (** execNm *)
        invertActionRep.
        invertSemMod Hltsmod0. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod1; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)

        invariant_tac; basic_dest.

        repeat eexists.
        { find_eq; sassumption. }
        { find_eq; sassumption. }
        { find_eq; sassumption. }
        { assumption. }

      + (** processLd *)
        invertActionRep.
        invertSemMod HSemMod. (* mid *)
        invertSemMod Hltsmod. (* proc *)

        invertSemMod Hltsmod1;
          [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0.
        invertActionRep. (* outs *)

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")].
        invertSemMod HSemMod0.
        invertActionRep. (* ins *)

        simpl in H8; destruct x5; [discriminate|].
        simpl in H13; destruct x9; [discriminate|].
        invariant_tac; basic_dest.
        assert (x = true /\ x1 = true)
          by (clear -H2; destruct x; destruct x1; inv H2; dest; intuition); dest; subst.

        repeat eexists.
        { find_eq; sassumption. }
        { find_eq. }
        { find_eq. }
        { rewrite (shatter_word_0 x11); rewrite (shatter_word_0 x12); simpl.
          simpl; apply xor_3; intuition.
        }

      + (** processSt *)
        invertActionRep.
        invertSemMod HSemMod. (* mid *)
        invertSemMod Hltsmod. (* proc *)

        invertSemMod Hltsmod1;
          [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0.
        invertActionRep. (* outs *)

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")].
        invertSemMod HSemMod0.
        invertActionRep. (* ins *)

        simpl in H8; destruct x5; [discriminate|].
        simpl in H13; destruct x9; [discriminate|].
        invariant_tac; basic_dest.
        assert (x = true /\ x1 = true)
          by (clear -H2; destruct x; destruct x1; inv H2; dest; intuition); dest; subst.

        repeat eexists.
        { find_eq; sassumption. }
        { find_eq. }
        { find_eq. }
        { rewrite (shatter_word_0 x11); rewrite (shatter_word_0 x12); simpl.
          simpl; apply xor_3; intuition.
        }

      + inv H3.
        
    - (* should be an empty step *)
      pose proof (pdecfi_none Hlts); dest; subst.
      map_simpl Hstep.
      eapply IHHclos; eauto.
      
  Qed.

  Lemma proc_reqLd_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("reqLd"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.

  Lemma proc_reqSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("reqSt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.

  Lemma proc_execHt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execHt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.

  Lemma proc_execNm_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("execNm"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |}.
  Proof.
    admit.
  Qed.

  Lemma proc_repLd_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("repLd"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := false |} /\
      exists pcv stv,
        find ("pc"__ i) or = Some {| objType := Bit addrSize; objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := Vector (Bit valSize) rfIdx;
                                     objVal := stv |} /\
        dec stv pcv ``"opcode" = evalConstT opLd.
  Proof.
    admit.
  Qed.
  
  Lemma proc_repSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("repSt"__ i)),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := false |} /\
      exists pcv stv,
        find ("pc"__ i) or = Some {| objType := Bit addrSize; objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := Vector (Bit valSize) rfIdx;
                                     objVal := stv |} /\
        dec stv pcv ``"opcode" = evalConstT opSt.
  Proof.
    admit.
  Qed.

  Lemma mid_processLd_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("Mid"__ i -n- "processLd")),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |} /\
      exists pcv stv insv deqPv,
        find ("pc"__ i) or = Some {| objType := Bit addrSize; objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := Vector (Bit valSize) rfIdx;
                                     objVal := stv |} /\
        find ("Ins"__ i -n- "elt") or = Some {| objType := Vector (atomK addrSize (Bit valSize)) O;
                                                objVal := insv |} /\
        find ("Ins"__ i -n- "deqP") or = Some {| objType := Bit O;
                                                 objVal := deqPv |} /\
        dec stv pcv ``"opcode" = evalConstT opLd /\
        insv deqPv ``"type" = evalConstT memLd /\
        insv deqPv ``"addr" = dec stv pcv ``"addr" /\
        insv deqPv ``"value" = evalConstT (getDefaultConst (Bit valSize)).
  Proof.
    admit.
  Qed.

  Lemma mid_processSt_prop:
    forall (Hclos: LtsStepClosure pdecfi or l)
           (Hstep: LtsStep pdecfi rm or nr dmMap cmMap)
           (Hrm: rm = Some ("Mid"__ i -n- "processSt")),
      find ("Outs"__ i -n- "empty") or = Some {| objType := Bool; objVal := true |} /\
      exists pcv stv insv deqPv,
        find ("pc"__ i) or = Some {| objType := Bit addrSize; objVal := pcv |} /\
        find ("rf"__ i) or = Some {| objType := Vector (Bit valSize) rfIdx;
                                     objVal := stv |} /\
        find ("Ins"__ i -n- "elt") or = Some {| objType := Vector (atomK addrSize (Bit valSize)) O;
                                                objVal := insv |} /\
        find ("Ins"__ i -n- "deqP") or = Some {| objType := Bit O;
                                                 objVal := deqPv |} /\
        dec stv pcv ``"opcode" = evalConstT opSt /\
        insv deqPv ``"type" = evalConstT memSt /\
        insv deqPv ``"addr" = dec stv pcv ``"addr" /\
        insv deqPv ``"value" = dec stv pcv ``"value".
  Proof.
    admit.
  Qed.

End Invariants.

