Require Import Bool String List Lia.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.
Require Import Kami.Decomposition Kami.Notations Kami.Tactics.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAsync.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv.
Require Import Eqdep.

Set Implicit Arguments.

Section ProcDecSC.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Variable (init: ProcInit addrSize dataBytes rfIdx).

  Definition pdec := pdecf fetch dec exec init.
  Definition pinst := pinst fetch dec exec init.
  #[local] Hint Unfold pdec: ModuleDefs. (* for kinline_compute *)
  #[local] Hint Extern 1 (ModEquiv type typeUT pdec) => unfold pdec. (* for kequiv *)
  #[local] Hint Extern 1 (ModEquiv type typeUT pinst) => unfold pinst. (* for kequiv *)

  Definition drainInst (elt: type (Struct RsToProc))
             (ofs: type (Bit iaddrSize))
             (pgmv: type (Vector (Data instBytes) iaddrSize))
    : fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize)) :=
    fun w =>
      if weq w ofs
      then evalExpr (alignInst _ (elt (RsToProc!!"data")%kami_expr))
      else pgmv w.

  Fixpoint drainInsts (elts: listEltT (Struct RsToProc) type)
           (ofs: type (Bit iaddrSize))
           (pgmv: type (Vector (Data instBytes) iaddrSize))
    : fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize)) :=
    match elts with
    | nil => pgmv
    | elt :: elts' =>
      drainInsts elts' (ofs ^+ $1) (drainInst elt ofs pgmv)
    end.

  Definition pdec_pinst_regRel: RegsT -> RegsT -> Prop.
  Proof.
    intros ir sr.
    kexistv "pc"%string pcv ir (Pc addrSize).
    kexistv "rf"%string rfv ir (Vector (Data dataBytes) rfIdx).
    kexistv "pinit"%string pinitv ir Bool.
    kexistv "pgm"%string pgmv ir (Vector (Data instBytes) iaddrSize).
    kexistnv "rsToProc"--"elt" oeltv ir (listEltK (Struct RsToProc) type).
    kexistv "pinitRsOfs"%string pinitRsOfsv ir (Bit iaddrSize).

    refine (if pinitv
            then (match oeltv with
                  | nil => _
                  | rs :: oeltv => _
                  end)
            else _).
    - exact (sr = (["pgm" <- (existT _ _ pgmv)]
                   +["pinitOfs" <- (existT _ _ pinitRsOfsv)]
                   +["pinit" <- (existT _ _ pinitv)]
                   +["rf" <- (existT _ _ rfv)]
                   +["pc" <- (existT _ _ pcv)])%fmap).
    - set (rawInst := pgmv (evalExpr (toIAddr _ pcv))).
      exact (sr = (["pgm" <- existT _ _ pgmv]
                   +["pinitOfs" <- (existT _ _ pinitRsOfsv)]
                   +["pinit" <- (existT _ _ pinitv)]
                   +["rf" <- let opc := evalExpr (getOptype _ rawInst) in
                             if weq opc opLd
                             then if weq (evalExpr (getLdDst _ rawInst)) $0
                                  then (existT _ _ rfv)
                                  else
                                    (existT
                                       _ _
                                       ((fun a => if weq a (evalExpr (getLdDst _ rawInst))
                                                  then
                                                    evalExpr
                                                      (calcLdVal
                                                         _ (evalExpr
                                                              (calcLdAddr
                                                                 _ (evalExpr (getLdAddr type rawInst))
                                                                 (rfv (evalExpr (getLdSrc type rawInst))))) 
                                                         (rs Fin.F1)
                                                         (evalExpr (getLdType _ rawInst)))
                                                  else rfv a)
                                        : fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx))))
                             else (existT _ _ rfv)]
                   +["pc" <- (existT _ _ (evalExpr (getNextPc _ rfv pcv rawInst)))])%fmap).

    - exact (sr = (["pgm" <- (existT _ _ (drainInsts oeltv pinitRsOfsv pgmv))]
                   +["pinitOfs" <- (existT _ (SyntaxKind (Bit iaddrSize))
                                           (pinitRsOfsv ^+ $(List.length oeltv)))]
                   +["pinit" <- (existT _ (SyntaxKind Bool)
                                        (if Peano_dec.eq_nat_dec
                                              (#pinitRsOfsv + List.length oeltv)
                                              (NatLib.pow2 iaddrSize)
                                         then true else false))]
                   +["rf" <- (existT _ _ rfv)]
                   +["pc" <- (existT _ _ pcv)])%fmap).
  Defined.
  #[local] Hint Unfold pdec_pinst_regRel: MapDefs.

  Ltac procDec_inv_old :=
    try match goal with
        | [H: context[procDec_inv] |- _] => destruct H
        end;
    kinv_red; kinv_or3;
    (* decide the current state by giving contradictions for all other states *)
    kinv_red; kinv_contra;
    (* to simplity struct-related invariants *)
    repeat
      match goal with
      | [H: context[Vector_find] |- _] => unfold Vector_find in H; simpl in H
      end.

  Definition pdecInl := ProcDecInl.pdecInl fetch dec exec init.

  Lemma drainInsts_enq:
    forall rss rs rsOfs pgmv,
      drainInsts (listEnq rs rss) rsOfs pgmv =
      (fun w => if weq w (rsOfs ^+ $ (Datatypes.length rss))
                then evalExpr (alignInst type (rs Fin.F1))
                else drainInsts rss rsOfs pgmv w).
  Proof.
    unfold listEnq; induction rss; simpl; intros;
      [rewrite wplus_wzero_1; reflexivity|].
    rewrite IHrss.
    rewrite <-wplus_assoc, <-natToWord_plus; reflexivity.
  Qed.
  
  Lemma pdec_refines_pinst: pdec <<== pinst.
  Proof. (* SKIP_PROOF_ON

    (** inlining *)
    ketrans; [exact (projT2 pdecInl)|].

    (** decomposition *)
    apply decompositionZeroR_NoRuleMap with (thetaR:= pdec_pinst_regRel);
      try reflexivity.
    1: {
      kdecompose_regrel_init.
      cbn; rewrite wplus_wzero_1.
      meq.
      exfalso; rewrite wordToNat_wzero in e.
      pose proof (NatLib.pow2_zero iaddrSize); lia.
    }

    intros.
    kinv_add procDec_inv_ok.
    kinvert.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.
      kinv_eq.
      + destruct x1; [discriminate|reflexivity].
      + rewrite wnot_not_zero_wplusone by assumption.
        destruct x1; [discriminate|].
        simpl; rewrite <-PeanoNat.Nat.add_assoc; reflexivity.
      + destruct x1; [discriminate|].
        simpl; rewrite <-wplus_assoc, <-natToWord_S.
        reflexivity.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.
      apply wnot_zero_wones in e; subst.
      rewrite wones_pow2_minus_one in H1.
      simpl; destruct x1 as [|rs ?]; [discriminate|].
      assert (x1 = nil); subst.
      { destruct x1; [reflexivity|].
        destruct pinitRqv; simpl in H1;
          pose proof (wordToNat_bound pinitRqOfsv); lia.
      }
      simpl; kinv_eq.
      + rewrite wones_pow2_minus_one.
        find_if_inside; [reflexivity|].
        elim n; pose proof (NatLib.pow2_zero iaddrSize); lia.
      + rewrite wones_wneg_one, wplus_comm, wminus_inv; reflexivity.
        
    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.
      destruct x; [discriminate|].
      destruct x; [|discriminate].
      simpl; subst; kinv_eq; kinv_finish.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.
      destruct x; [discriminate|].
      destruct x; [|discriminate].
      simpl; subst; kinv_eq; kinv_finish.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists None; kinv_constr.
      destruct x; [discriminate|].
      destruct x; [|discriminate].
      simpl; subst; kinv_eq; kinv_finish.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists (Some "execNm"%string); kinv_constr;
        kinv_eq; kinv_finish.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red.
      exists (Some "execNmZ"%string); kinv_constr;
        kinv_eq; kinv_finish.

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red; kinv_red.
      destruct pinitv.
      + specialize (H9 eq_refl); clear H8.
        kinv_custom procDec_inv_old.
        kinv_regmap_red.
        unfold type, ilist_to_fun_m in *; simpl in *.
        destruct x; [discriminate|].
        destruct x; [|discriminate].
        destruct (weq (evalExpr (getLdDst _ (pgmv (evalExpr (toIAddr _ pcv))))) $0).
        * exists (Some "execLdZ"%string); kinv_constr; kinv_eq; kinv_finish.
        * exists (Some "execLd"%string); kinv_constr; kinv_eq; kinv_finish.
        
      + specialize (H8 eq_refl); clear H9; kinv_red.
        unfold type, ilist_to_fun_m in *; simpl in *.
        destruct (Peano_dec.eq_nat_dec (#pinitRsOfsv + Datatypes.length x3)
                                       (NatLib.pow2 iaddrSize - 1)).
        * exists (Some "pgmInitEnd"%string); kinv_constr; kinv_eq.
          { simpl; rewrite e.
            destruct (PeanoNat.Nat.eq_dec _ _); [|reflexivity].
            pose proof (NatLib.pow2_zero iaddrSize); lia.
          }
          { cbn; find_if_inside; [reflexivity|].
            elim n.
            replace (pinitRsOfsv ^+ $(Datatypes.length x3)) with (wones iaddrSize).
            { apply wnot_ones. }
            { rewrite <-natToWord_wordToNat with (w:= pinitRsOfsv).
              rewrite <-natToWord_plus.
              rewrite e.
              apply wones_natToWord.
            }
          }
          { destruct x; [discriminate|].
            simpl; simpl in H; dest; subst.
            kinv_eq.
            unfold type, ilist_to_fun_m in *; simpl in *.
            do 2 f_equal.
            rewrite H0; simpl.
            rewrite <-natToWord_wordToNat with (w:= pinitRsOfsv) at 2.
            rewrite <-natToWord_plus.
            f_equal; lia.
          }
          { apply eq_sym, drainInsts_enq. }
          { rewrite e.
            find_if_inside; [pose proof (NatLib.pow2_zero iaddrSize); lia|].
            find_if_inside; [reflexivity|].
            elim n0; unfold listEnq; rewrite app_length; simpl; lia.
          }
          { pose proof (NatLib.pow2_zero iaddrSize).
            rewrite <-natToWord_wordToNat with (w:= pinitRsOfsv).
            rewrite <-natToWord_plus.
            unfold listEnq; rewrite app_length; simpl.
            replace (#pinitRsOfsv + (Datatypes.length x3 + 1))
              with (NatLib.pow2 iaddrSize) by lia.
            apply eq_sym, natToWord_pow2.
          }
        * assert (#pinitRsOfsv + Datatypes.length x3 < NatLib.pow2 iaddrSize - 1)%nat.
          { assert (#pinitRsOfsv + Datatypes.length x3 < NatLib.pow2 iaddrSize)%nat.
            { rewrite <-PeanoNat.Nat.add_assoc, PeanoNat.Nat.add_comm with (n:= Datatypes.length x) in H0.
              simpl in H0; rewrite PeanoNat.Nat.add_assoc in H0.
              destruct x; [discriminate|simpl in H0].
              destruct pinitRqv; simpl in H0;
                pose proof (wordToNat_bound pinitRqOfsv); lia.
            }
            lia.
          }
          exists (Some "pgmInit"%string); kinv_constr; kinv_eq.
          { simpl; destruct (PeanoNat.Nat.eq_dec _ _); [lia|reflexivity]. }
          { cbn; find_if_inside; [|reflexivity].
            apply wnot_zero_wones in e.
            rewrite <-natToWord_wordToNat with (w:= pinitRsOfsv) in e.
            rewrite <-natToWord_plus, wones_natToWord in e.
            apply natToWord_inj in e; lia.
          }
          { destruct x; [discriminate|].
            simpl; simpl in H; dest; subst.
            kinv_eq.
            unfold type, ilist_to_fun_m in *; simpl in *.
            do 2 f_equal.
            rewrite H0; simpl.
            rewrite <-natToWord_wordToNat with (w:= pinitRsOfsv) at 2.
            rewrite <-natToWord_plus.
            f_equal; lia.
          }
          { apply eq_sym, drainInsts_enq. }
          { find_if_inside; [lia|].
            unfold listEnq; rewrite app_length; simpl.
            find_if_inside; [lia|].
            reflexivity.
          }
          { unfold listEnq; rewrite app_length; simpl.
            rewrite <-wplus_assoc.
            rewrite <-natToWord_plus.
            reflexivity.
          }

    - kinv_action_dest.
      kinv_custom procDec_inv_old.
      kinv_regmap_red; kinv_red.
      unfold type, ilist_to_fun_m in *; simpl in *.
      destruct pinitv.
      + specialize (H9 eq_refl); clear H8.
        kinv_custom procDec_inv_old.
        kinv_regmap_red.
        destruct x; [discriminate|].
        destruct x; [|discriminate].
        exists (Some "execSt"%string); kinv_constr; kinv_eq; kinv_finish.
      + exfalso.
        specialize (H8 eq_refl); clear H9; kinv_red.
        destruct x as [|rq ?]; [discriminate|].
        simpl in H; dest; subst.
        simpl in H4; discriminate.
        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End ProcDecSC.

