Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec Ex.ProcDecInv.

Require Import FunctionalExtensionality.

Section ProcDecSC.
  Variables addrSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition procDecM (n: nat) := procDecM dec exec n.
  Definition sc (n: nat) := sc 2 _ _ _ dec exec opLd opSt opHt n.

  Hint Unfold procDecM sc : ModuleDefs.

  Section SingleCore.
    Variable i: nat. (* i-th core *)

    Definition pdecfi := ProcDec.pdecfi dec exec i.
    Definition pinsti := pinsti 2 _ _ _ dec exec opLd opSt opHt i.

    Hint Unfold pdecfi pinsti.
    
    Definition regRel: RegsT -> RegsT -> Prop.
    Proof.
      intros ir sr.
      refine (exists pcv: type (Bit addrSize),
                find ("pc"__ i) ir = Some {| objVal := pcv |} /\
                _).
      refine (exists rfv: type (Vector (Bit valSize) rfIdx),
                find ("rf"__ i) ir = Some {| objVal := rfv |} /\
                _).
      refine (exists stv: type Bool,
                find ("stall"__ i) ir = Some {| objVal := stv |} /\
                _).
      refine (exists outv: type (Vector (atomK addrSize (Bit valSize)) O),
                find ("Outs"__ i -n- "elt") ir = Some {| objVal := outv |} /\
                _).
      refine (exists deqPv: type (Bit O),
                find ("Outs"__ i -n- "deqP") ir = Some {| objVal := deqPv |} /\
                _).
      refine (exists emptyv: type Bool,
                find ("Outs"__ i -n- "empty") ir = Some {| objVal := emptyv |} /\
                _).
      destruct emptyv.
      - refine (sr =
                add ("pc"__ i) {| objVal := pcv |}
                    (add ("rf"__ i) {| objType := Vector (Bit valSize) rfIdx;
                                       objVal := rfv |} empty)).
      - pose proof (outv deqPv ``"type") as opc; unfold GetAttrType in opc; simpl in opc.
        destruct (weq opc (evalConstT opLd)).
        + refine (sr =
                  add ("pc"__ i) {| objVal := fst (exec rfv pcv (dec rfv pcv)) |}
                      (add ("rf"__ i) {| objType := Vector (Bit valSize) rfIdx;
                                         objVal := _ |} empty)).
          exact (fun a => if weq a (dec rfv pcv ``"reg")
                          then outv deqPv ``"value"
                          else rfv a).
        + refine (sr =
                  add ("pc"__ i) {| objVal := fst (exec rfv pcv (dec rfv pcv)) |}
                      (add ("rf"__ i) {| objType := Vector (Bit valSize) rfIdx;
                                         objVal := rfv |} empty)).
    Defined.
    Hint Unfold regRel.

    Ltac regRel_tac :=
      repeat
        match goal with
          | [H: regRel _ _ |- _] =>
            unfold regRel in H; dest; invariant_tac; basic_dest; subst
          | [ |- regRel _ _] =>
            unfold regRel; repeat esplit
          | [ |- find ?k ?m = ?rhs] =>
            find_eq; sassumption
        end.

    Definition cmMap: CallsT -> CallsT := id.
    Definition dmMap: CallsT -> CallsT := id.
    Hint Unfold cmMap dmMap id.

    Lemma Ht2t : t2t {dmMap, cmMap}.
    Proof.
      unfold t2t; intros.
      destruct x as [[ ]]; simpl in *; subst; reflexivity.
    Qed.

    Definition ruleMap: string -> string :=
      fun r =>
        if string_eq r ("reqLd"__ i) then ("voidRule"__ i)
        else if string_eq r ("reqSt"__ i) then ("voidRule"__ i)
        else if string_eq r ("repLd"__ i) then ("voidRule"__ i)
        else if string_eq r ("repSt"__ i) then ("voidRule"__ i)
        else if string_eq r ("execHt"__ i) then ("execHt"__ i)
        else if string_eq r ("execNm"__ i) then ("execNm"__ i)
        else if string_eq r ("Mid"__ i -n- "processLd") then ("execLd"__ i)
        else if string_eq r ("Mid"__ i -n- "processSt") then ("execSt"__ i)
        else ("voidRule"__ i).
    Hint Unfold ruleMap.

    Definition f := f _ _ Ht2t.

    Lemma procDec_SC_i: pdecfi <<=[f] pinsti.
    Proof.
      apply transMap with (regRel:=regRel) (ruleMap:=ruleMap);
      [repeat (eexists; split); simpl; find_eq|].

      intros.
      (* collect invariants before inversions *)
      pose proof (proc_reqLd_prop H H0) as HreqLdInv.
      pose proof (proc_reqSt_prop H H0) as HreqStInv.
      pose proof (proc_execHt_prop H H0) as HexecHtInv.
      pose proof (proc_execNm_prop H H0) as HexecNmInv.
      pose proof (mid_processLd_prop H H0) as HprocessLdInv.
      pose proof (mid_processSt_prop H H0) as HprocessStInv.

      (* inversions for combined module step *)
      inv H0.
      inv Hlts2.
      inv Hlts0.
      destConcatLabel; destRuleRep; repeat combRule; invertActionRep.

      - (** processLd *)
        invertSemMod HSemMod. (* mid *)
        invertSemMod Hltsmod1. (* proc *)

        invertSemMod Hltsmod;
          [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0.
        invertActionRep. (* outs *)

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")].
        invertSemMod HSemMod0.
        invertActionRep. (* ins *)

        (* Need to get the values for old registers and defined/called method labels *)
        filt_dest; regRel_tac.

        (* Handling invariants for "processLd" *)
        specialize (HprocessLdInv eq_refl); dest.
        invariant_tac; basic_dest; subst.
        
        eexists; split.

        { econstructor; eauto.
          econstructor.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor; eauto.
            econstructor; eauto.
            econstructor; [simpl; find_if_inside; [reflexivity|intuition]|].
            econstructor; eauto.
            econstructor; eauto.
            econstructor; eauto.
          }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { callIffDef_dest; filt_dest.
            pred_dest ("Outs"__ i -n- "enq").
            pred_dest ("Ins"__ i -n- "deq").
            pred_dest ("exec"__ i).
            invariant_tac; basic_dest.
            map_eq.

            (* invariant *)
            simpl in H2; destruct (weq _ _) in H2; [|discriminate].
            simpl; repeat f_equal; boundedMapTac.
          }
        }
        { regRel_tac.
          callIffDef_dest; filt_dest.
          pred_dest ("Ins"__ i -n- "deq").
          pred_dest ("exec"__ i).
          pred_dest ("Outs"__ i -n- "enq").
          repeat (invariant_tac; basic_dest); subst.

          (* invariant *)
          rewrite (rewrite_weq eq_refl).
          destruct (weq _ _) in H3; [|discriminate].
          find_if_inside; [|elim n; assumption].
          map_eq.
        }

      - (** processSt *)
        invertSemMod HSemMod. (* mid *)
        invertSemMod Hltsmod1. (* proc *)

        invertSemMod Hltsmod;
          [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0.
        invertActionRep. (* outs *)

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "deq")].
        invertSemMod HSemMod0.
        invertActionRep. (* ins *)
        
        (* Need to get the values for old registers and defined/called method labels *)
        filt_dest; regRel_tac.

        (* Handling invariants for "processSt" *)
        specialize (HprocessStInv eq_refl); dest.
        invariant_tac; basic_dest; subst.
        
        eexists; split.

        { econstructor; eauto.
          econstructor.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor; eauto.
            econstructor; eauto.
            econstructor; [simpl; find_if_inside; [reflexivity|intuition]|].
            econstructor; eauto.
            econstructor; eauto.
          }
          { eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { callIffDef_dest; filt_dest.
            pred_dest ("Outs"__ i -n- "enq").
            pred_dest ("Ins"__ i -n- "deq").
            pred_dest ("exec"__ i).
            invariant_tac; basic_dest.
            map_eq.

            (* invariant *)
            simpl in H2; destruct (weq _ _) in H2; [|discriminate].
            simpl; repeat f_equal; boundedMapTac.
          }
        }
        { regRel_tac.
          callIffDef_dest; filt_dest.
          pred_dest ("Outs"__ i -n- "enq").
          pred_dest ("Ins"__ i -n- "deq").
          pred_dest ("exec"__ i).
          repeat (invariant_tac; basic_dest); subst.

          (* invariant *)
          rewrite (rewrite_weq eq_refl).
          destruct (weq _ _) in H3; [|discriminate].
          match goal with
            | [ |- context [weq ?w (evalConstT opLd)] ] =>
              replace w with WO~0~1 by assumption
          end.
          map_eq.
        }

      - (** reqLd *)
        invertSemMod HSemMod. (* proc *)
        invertSemMod Hltsmod1. (* mid *)

        invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod0;
          [|invertSemMod HSemMod; invertSemMod HSemMod0; fconn_tac ("Ins"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)
        filt_dest; invertActionRep.

        (* Handling invariants for "reqLd" *)
        specialize (HreqLdInv eq_refl); dest.
        invariant_tac; basic_dest; subst.

        eexists; split.

        { econstructor; eauto.
          econstructor; eauto.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor. reflexivity. }
          { eauto. }
          { eauto. }
        }
        { regRel_tac.
          map_eq.
        }

      - (** reqSt *)
        invertSemMod HSemMod. (* proc *)
        invertSemMod Hltsmod1. (* mid *)

        invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod0; [|invertSemMod HSemMod; invertSemMod HSemMod0;
                                 fconn_tac ("Ins"__ i -n- "enq")].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)
        filt_dest; invertActionRep.

        (* Handling invariants for "reqSt" *)
        specialize (HreqStInv eq_refl); dest.
        invariant_tac; basic_dest; subst.

        eexists; split.

        { econstructor; eauto.
          econstructor; eauto.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor. reflexivity. }
          { eauto. }
          { eauto. }
        }
        { regRel_tac; map_eq. }

      - (** repLd *)
        invertSemMod Hltsmod1. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")].
        invertSemMod HSemMod0. (* outs *)
        invertActionRep.

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0.

        filt_dest; regRel_tac.
        repeat (invariant_tac; basic_dest); subst.

        eexists; split.

        { econstructor; eauto.
          econstructor; eauto.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor. reflexivity. }
          { eauto. }
          { eauto. }
        }
        { regRel_tac.
          conn_tac ("Outs"__ i -n- "deq").

          (* invariant *)
          simpl in H6; apply negb_true_iff in H6; subst.
          assert (x3 x5 ``"type" = WO~0~0)
            by (clear -H4; simpl in H4; destruct (weq _ _); [assumption|inv H4]).
          destruct (weq _ _) in H14; [|elim n; assumption]; subst.
          rewrite (shatter_word_0 x4); rewrite (shatter_word_0 x5); simpl.
          
          map_eq.
        }

      - (** repSt *)
        invertSemMod Hltsmod1. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [|invertSemMod HSemMod0; fconn_tac ("Outs"__ i -n- "deq")].
        invertSemMod HSemMod0. (* outs *)
        invertActionRep.

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0.

        filt_dest; regRel_tac.
        repeat (invariant_tac; basic_dest); subst.

        eexists; split.

        { econstructor; eauto.
          econstructor; eauto.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor. reflexivity. }
          { eauto. }
          { eauto. }
        }
        { regRel_tac.
          conn_tac ("Outs"__ i -n- "deq").

          (* invariant *)
          simpl in H6; apply negb_true_iff in H6; subst.
          destruct (weq _ _) in H4; [|discriminate].
          match type of H14 with
            | context [weq ?w (evalConstT opLd)] =>
              progress replace w with WO~0~1 in H14 by assumption
          end; simpl in H14; subst.
          rewrite (shatter_word_0 x4); rewrite (shatter_word_0 x5); simpl.
          
          map_eq.
        }

      - (** execHt *)
        invertSemMod Hltsmod1. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)

        filt_dest; regRel_tac.
        specialize (HexecHtInv eq_refl); dest.
        repeat (invariant_tac; basic_dest); subst.

        eexists; split.

        { econstructor; eauto.
          econstructor; eauto.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor; eauto.
            econstructor; eauto.
            econstructor; eauto.
            econstructor; eauto.
          }
          { eauto. }
          { eauto. }
          { eauto. }
        }
        { regRel_tac.
          map_eq.
        }

      - (** execNm *)
        invertSemMod Hltsmod1. (* mid *)
        invertSemMod HSemMod. (* proc *)

        invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)

        filt_dest; regRel_tac.
        specialize (HexecNmInv eq_refl); dest.
        repeat (invariant_tac; basic_dest); subst.

        eexists; split.

        { econstructor; eauto.
          econstructor; eauto.
          { repeat autounfold; ssimpl_G; in_tac. }
          { econstructor; eauto.
            econstructor; eauto.
            econstructor; eauto.
            econstructor; eauto.
            econstructor; eauto.
          }
          { eauto. }
          { eauto. }
        }
        { regRel_tac.
          map_eq.
        }
        
      - (** None *)
        invertSemMod Hltsmod1. (* mid *)
        invertSemMod Hltsmod2. (* proc *)

        invertSemMod Hltsmod; [fconn_tac ("Outs"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Outs"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* outs *)

        invertSemMod Hltsmod0; [fconn_tac ("Ins"__ i -n- "enq")|].
        invertSemMod HSemMod; [fconn_tac ("Ins"__ i -n- "deq")|].
        invertSemMod HSemMod0. (* ins *)

        filt_dest.
        eexists; split.

        { econstructor; eauto. }
        { map_simpl_G; assumption. }

    Qed.

  End SingleCore.

  Theorem procDecM_SC: forall n, exists f, (procDecM n) <<=[f] (sc n).
  Proof.
    intros; exists id.
    pose proof (procDec_SC_i).
    unfold f, Refinement.f, dmMap, cmMap in H; rewrite <-id_idTrs in H by reflexivity.
    repeat autounfold with ModuleDefs.

    apply tr_comb.
    - induction n; [apply H|]; simpl.
      apply tr_comb; [apply H|assumption].
    - apply tr_refl.
  Qed.

End ProcDecSC.

