Require Import Bool String List BinNums Omega.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAsync Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Lemma wnot_not_zero_wplusone:
  forall {sz} (w2: word sz),
    wnot w2 <> $0 ->
    #(w2 ^+ $1) = #w2 + 1.
Proof.
  intros.
  assert (w2 < wones _).
  { apply lt_wlt.
    rewrite wones_pow2_minus_one.
    pose proof (wordToNat_bound w2).
    pose proof (NatLib.pow2_zero sz).
    assert (#w2 = NatLib.pow2 sz - 1 \/ (#w2 < NatLib.pow2 sz - 1)%nat) by omega.
    destruct H2; [|assumption].
    assert (natToWord sz (#w2) = natToWord sz (NatLib.pow2 sz - 1)) by congruence.
    rewrite natToWord_wordToNat, <-wones_natToWord in H3; subst.
    rewrite wnot_ones in H.
    exfalso; auto.
  }
  erewrite wordToNat_plusone; [|eassumption].
  omega.
Qed.

Lemma wminus_wplus_transpose:
  forall {sz} (w1 w2 w3: word sz),
    w1 ^- w2 = w3 -> w1 = w3 ^+ w2.
Proof.
  intros.
  replace (w3 ^+ w2) with (w1 ^- w2 ^+ w2).
  - rewrite wminus_def, <-wplus_assoc.
    rewrite wplus_comm with (x:= ^~ w2), wminus_inv.
    rewrite wplus_wzero_1; reflexivity.
  - congruence.
Qed.

Lemma wnot_zero_wones:
  forall {sz} (w: word sz), wnot w = $0 -> w = wones _.
Proof.
  intros.
  rewrite wneg_wnot in H.
  apply wminus_wplus_transpose in H.
  rewrite wplus_unit in H.
  rewrite <-wneg_idempotent with (w0:= w), H.
  apply eq_sym, wones_wneg_one.
Qed.

Section Invariants.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize iaddrSize instBytes dataBytes rfIdx).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).

  Definition pdecInl := pdecInl fifoSize fetch dec exec init.

  Definition fifoLength (emptyv fullv: bool)
             (enqpv deqpv: type (Bit fifoSize)) :=
    if emptyv then 0
    else if fullv then NatLib.pow2 fifoSize
         else #(enqpv ^- deqpv).

  Definition fifo_inv (emptyv fullv: bool)
             (enqpv deqpv: type (Bit fifoSize)): Prop :=
    (emptyv || fullv = true <-> enqpv = deqpv).

  Definition fifo_rq_rs_inv
             (pinitRqv: type Bool)
             (pinitRqOfsv pinitRsOfsv: type (Bit iaddrSize))
             (iemptyv ifullv oemptyv ofullv: type Bool)
             (ienqpv ideqpv oenqpv odeqpv: type (Bit fifoSize)) :=
    fifo_inv iemptyv ifullv ienqpv ideqpv /\
    fifo_inv oemptyv ofullv oenqpv odeqpv /\
    (if pinitRqv then NatLib.pow2 iaddrSize
     else #pinitRqOfsv) =
    #pinitRsOfsv +
    fifoLength iemptyv ifullv ienqpv ideqpv +
    fifoLength oemptyv ofullv oenqpv odeqpv.

  Definition fifo_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = true /\ fifoEnqP = fifoDeqP.
  
  Definition fifo_not_empty_inv (fifoEmpty: bool) (fifoEnqP fifoDeqP: type (Bit fifoSize)): Prop :=
    fifoEmpty = false /\ fifoEnqP = fifoDeqP ^+ $1.

  Definition mem_request_inv
             (rawInst: fullType type (SyntaxKind (Data instBytes)))
             (rf: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx)))
             (insEmpty: bool) (insElt: type (Vector (Struct RqFromProc) fifoSize))
             (insDeqP: type (Bit fifoSize)): Prop.
  Proof.
    refine (if insEmpty then True else _).
    refine (_ /\ _).
    - exact ((insElt insDeqP (RqFromProc !! "op") = false ->
              evalExpr (getOptype _ rawInst) = opLd) /\
             (evalExpr (getOptype _ rawInst) = opLd ->
              (insElt insDeqP (RqFromProc !! "op") = false /\
               insElt insDeqP (RqFromProc !! "addr") =
               evalExpr
                 (alignLdAddr
                    _ (evalExpr
                         (calcLdAddr
                            _ (evalExpr (getLdAddr _ rawInst))
                            (evalExpr (#rf@[getLdSrc _ rawInst])%kami_expr)))) /\
               insElt insDeqP (RqFromProc !! "data") =
               evalConstT (getDefaultConst (Data dataBytes))))).
    - exact ((insElt insDeqP (RqFromProc !! "op") = true ->
              evalExpr (getOptype _ rawInst) = opSt) /\
             (evalExpr (getOptype _ rawInst) = opSt ->
              (insElt insDeqP (RqFromProc !! "op") = true /\
               insElt insDeqP (RqFromProc !! "addr") =
               evalExpr (calcStAddr
                           _ (evalExpr (getStAddr _ rawInst))
                           (evalExpr (#rf@[getStSrc _ rawInst])%kami_expr)) /\
               insElt insDeqP (RqFromProc !! "data") =
               evalExpr (#rf@[getStVSrc _ rawInst ])%kami_expr))).
  Defined.
  Hint Unfold fifo_rq_rs_inv fifo_inv fifo_empty_inv fifo_not_empty_inv
       mem_request_inv: InvDefs.

  Record procDec_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Pc iaddrSize));
      Hpcv : M.find "pc"%string o = Some (existT _ _ pcv);
      rfv : fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx));
      Hrfv : M.find "rf"%string o = Some (existT _ _ rfv);

      pinitv : fullType type (SyntaxKind Bool);
      Hpinitv : M.find "pinit"%string o = Some (existT _ _ pinitv);
      pinitRqv : fullType type (SyntaxKind Bool);
      HpinitRqv : M.find "pinitRq"%string o = Some (existT _ _ pinitRqv);
      pinitRqOfsv : fullType type (SyntaxKind (Bit iaddrSize));
      HpinitRqOfsv : M.find "pinitRqOfs"%string o = Some (existT _ _ pinitRqOfsv);
      pinitRsOfsv : fullType type (SyntaxKind (Bit iaddrSize));
      HpinitRsOfsv : M.find "pinitRsOfs"%string o = Some (existT _ _ pinitRsOfsv);
      
      pgmv : fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize));
      Hpgmv : M.find "pgm"%string o = Some (existT _ _ pgmv);
      stallv : fullType type (SyntaxKind Bool);
      Hstallv : M.find "stall"%string o = Some (existT _ _ stallv);
      iev : fullType type (SyntaxKind Bool);
      Hiev : M.find "rqFromProc"--"empty"%string o = Some (existT _ _ iev);
      ifv : fullType type (SyntaxKind Bool);
      Hifv : M.find "rqFromProc"--"full"%string o = Some (existT _ _ ifv);
      ienqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hienqpv : M.find "rqFromProc"--"enqP"%string o = Some (existT _ _ ienqpv);
      ideqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hideqpv : M.find "rqFromProc"--"deqP"%string o = Some (existT _ _ ideqpv);
      ieltv : fullType type (SyntaxKind (Vector (Struct RqFromProc) fifoSize));
      Hieltv : M.find "rqFromProc"--"elt"%string o = Some (existT _ _ ieltv);
      oev : fullType type (SyntaxKind Bool);
      Hoev : M.find "rsToProc"--"empty"%string o = Some (existT _ _ oev);
      ofv : fullType type (SyntaxKind Bool);
      Hofv : M.find "rsToProc"--"full"%string o = Some (existT _ _ ofv);
      oenqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hoenqpv : M.find "rsToProc"--"enqP"%string o = Some (existT _ _ oenqpv);
      odeqpv : fullType type (SyntaxKind (Bit fifoSize));
      Hodeqpv : M.find "rsToProc"--"deqP"%string o = Some (existT _ _ odeqpv);
      oeltv : fullType type (SyntaxKind (Vector (Struct RsToProc) fifoSize));
      Hoeltv : M.find "rsToProc"--"elt"%string o = Some (existT _ _ oeltv);

      Hinv :
        (pinitv = false ->
         fifo_rq_rs_inv pinitRqv pinitRqOfsv pinitRsOfsv
                        iev ifv oev ofv ienqpv ideqpv oenqpv odeqpv /\
         stallv = false) /\
        (pinitv = true ->
         or3 (stallv = false /\
              fifo_empty_inv iev ienqpv ideqpv /\
              fifo_empty_inv oev oenqpv odeqpv)
             ((stallv = true /\
               fifo_not_empty_inv iev ienqpv ideqpv /\
               fifo_empty_inv oev oenqpv odeqpv) /\
              (mem_request_inv (pgmv (split2 _ _ pcv)) rfv iev ieltv ideqpv))
             (stallv = true /\
              fifo_empty_inv iev ienqpv ideqpv /\
              fifo_not_empty_inv oev oenqpv odeqpv))
        }.

  Ltac procDec_inv_old :=
    try match goal with
        | [H: procDec_inv _ |- _] => destruct H
        end;
    kinv_red; kinv_or3;
    (* decide the current state by giving contradictions for all other states *)
    kinv_red; kinv_contra.
    
  Ltac procDec_inv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kregmap_clear. (* for improving performance *)

  Ltac procDec_inv_tac := procDec_inv_old; procDec_inv_new.

  Ltac procDec_inv_next ph :=
    match ph with
    | 0 => or3_fst (* intact *)
    | 1 => or3_snd (* requested *)
    | 2 => or3_thd (* responded *)
    end; intuition idtac.

  Lemma fifoLength_enq:
    forall emptyv enqpv deqpv,
      fifo_inv emptyv false enqpv deqpv ->
      fifoLength emptyv false enqpv deqpv + 1 =
      fifoLength false (if weq deqpv (enqpv ^+ $1) then true else false)
                 (enqpv ^+ $1) deqpv.
  Proof.
    unfold fifo_inv, fifoLength; intros.
    destruct H.
    destruct emptyv; simpl in *.
    - specialize (H eq_refl); subst.
      destruct (weq deqpv (deqpv ^+ $1)).
      + destruct fifoSize; [reflexivity|].
        exfalso; eapply wplus_one_neq; eauto.
      + rewrite wminus_def, <-wplus_assoc.
        rewrite wplus_comm with (x:= $1).
        rewrite wplus_assoc.
        rewrite wminus_inv, wplus_wzero_2.
        destruct fifoSize.
        * elim n.
          rewrite (word0 deqpv); reflexivity.
        * rewrite roundTrip_1; reflexivity.
    - destruct (weq deqpv (enqpv ^+ $1)); subst.
      + rewrite wminus_def, wneg_wplus_distr.
        rewrite wplus_assoc, wminus_inv, wplus_wzero_2.
        destruct fifoSize; [reflexivity|].
        rewrite <-wones_wneg_one.
        rewrite wones_pow2_minus_one.
        pose proof (NatLib.pow2_zero (S n)); omega.
      + rewrite wminus_def with (x:= enqpv ^+ _).
        rewrite <-wplus_assoc, wplus_comm with (x:= $1).
        rewrite wplus_assoc, <-wminus_def.
        erewrite wordToNat_plusone with (w':= wones _).
        * omega.
        * apply lt_wlt.
          pose proof (wordToNat_bound (enqpv ^- deqpv)).
          rewrite wones_pow2_minus_one.
          assert (#(enqpv ^- deqpv) <> NatLib.pow2 fifoSize - 1).
          { intro Hx.
            rewrite <-wones_pow2_minus_one in Hx.
            assert (enqpv ^- deqpv = wones fifoSize).
            { rewrite <-natToWord_wordToNat, <-Hx.
              rewrite natToWord_wordToNat; reflexivity.
            }
            assert (^~ (enqpv ^- deqpv) = $1).
            { rewrite H2, <-wneg_idempotent with (w:= $1).
              rewrite wones_wneg_one; reflexivity.
            }
            elim n.
            rewrite <-H3.
            rewrite wminus_def, wneg_wplus_distr.
            rewrite wplus_assoc, wneg_idempotent.
            rewrite wminus_inv, wplus_wzero_2.
            reflexivity.
          }
          omega.
  Qed.

  Lemma fifoLength_deq:
    forall fullv enqpv deqpv,
      fifo_inv false fullv enqpv deqpv ->
      fifoLength false fullv enqpv deqpv =
      fifoLength (if weq enqpv (deqpv ^+ $1) then true else false) false 
                 enqpv (deqpv ^+ $1) + 1.
  Proof.
    unfold fifo_inv, fifoLength; intros.
    destruct H.
    destruct fullv; simpl in *.
    - specialize (H eq_refl); subst.
      destruct (weq deqpv (deqpv ^+ $1)).
      + destruct fifoSize; [reflexivity|].
        exfalso; eapply wplus_one_neq; eauto.
      + rewrite wminus_def, wneg_wplus_distr.
        rewrite wplus_assoc, wminus_inv, wplus_wzero_2.
        rewrite <-wones_wneg_one.
        rewrite wones_pow2_minus_one.
        pose proof (NatLib.pow2_zero fifoSize); omega.
    - destruct (weq enqpv (deqpv ^+ $1)).
      + subst.
        rewrite wminus_def, <-wplus_assoc.
        rewrite wplus_comm with (x:= $1).
        rewrite wplus_assoc.
        rewrite wminus_inv, wplus_wzero_2.
        destruct fifoSize.
        * rewrite (word0 deqpv) in H0.
          specialize (H0 eq_refl); discriminate.
        * rewrite roundTrip_1; reflexivity.
      + rewrite wminus_plus_distr.
        rewrite <-wordToNat_minus_one'.
        * omega.
        * intro Hx.
          apply sub_0_eq in Hx; subst.
          specialize (H0 eq_refl); discriminate.
  Qed.

  Lemma fifoLength_zero:
    forall emptyv fullv enqpv deqpv,
      fifo_inv emptyv fullv enqpv deqpv ->
      fifoLength emptyv fullv enqpv deqpv = 0 ->
      emptyv = true /\ enqpv = deqpv.
  Proof.
    unfold fifo_inv, fifoLength; intros.
    destruct emptyv.
    - destruct H; specialize (H eq_refl); subst; auto.
    - destruct fullv.
      + pose proof (NatLib.pow2_zero fifoSize); omega.
      + exfalso.
        rewrite <-wordToNat_wzero with (sz:= fifoSize) in H0.
        assert (enqpv ^- deqpv = wzero fifoSize).
        { rewrite <-natToWord_wordToNat, <-H0.
          rewrite natToWord_wordToNat.
          reflexivity.
        }
        apply sub_0_eq in H1; subst.
        destruct H; specialize (H1 eq_refl); discriminate.
  Qed.

  Lemma fifoLength_one:
    forall fullv enqpv deqpv,
      fifo_inv false fullv enqpv deqpv ->
      fifoLength false fullv enqpv deqpv = 1 ->
      fifoSize = 0 \/ enqpv = deqpv ^+ $1.
  Proof.
    unfold fifo_inv, fifoLength; intros.
    destruct fifoSize; [left; reflexivity|].
    destruct fullv.
    - exfalso; pose proof (NatLib.one_lt_pow2 n); omega.
    - right.
      rewrite wplus_comm.
      apply wminus_wplus_transpose.
      rewrite <-natToWord_wordToNat with (w:= enqpv ^- deqpv).
      congruence.
  Qed.

  Lemma fifoLength_not_empty:
    forall fullv enqpv deqpv,
      fifo_inv false fullv enqpv deqpv ->
      (fifoLength false fullv enqpv deqpv > 0)%nat.
  Proof.
    unfold fifo_inv, fifoLength; intros.
    destruct fullv.
    - apply NatLib.pow2_zero.
    - apply gt0_wneq0.
      intro Hx.
      apply wminus_wplus_transpose in Hx.
      rewrite wplus_wzero_2 in Hx; subst.
      destruct H; specialize (H0 eq_refl).
      discriminate.
  Qed.

  Lemma fifo_rq_rs_inv_last:
    forall (pinitRqv: type Bool) (pinitRqOfsv: type (Bit iaddrSize))
           iev ifv ienqpv ideqpv ofv oenqpv odeqpv,
      fifo_inv iev ifv ienqpv ideqpv ->
      fifo_inv false ofv oenqpv odeqpv ->
      (if pinitRqv then NatLib.pow2 iaddrSize else # (pinitRqOfsv)) =
      (NatLib.pow2 iaddrSize - 1) +
      fifoLength iev ifv ienqpv ideqpv +
      fifoLength false ofv oenqpv odeqpv ->
      pinitRqv = true /\
      iev = true /\ (* ifv = false /\ *) ienqpv = ideqpv /\
      oenqpv = odeqpv ^+ $1.
  Proof.
    intros.
    pose proof (fifoLength_not_empty H0).
    find_if_inside;
      [|exfalso; pose proof (wordToNat_bound pinitRqOfsv); omega].

    assert (fifoLength iev ifv ienqpv ideqpv = 0) by omega.
    apply fifoLength_zero in H3; [|assumption].
    dest; subst.

    assert (fifoLength false ofv oenqpv odeqpv = 1) by omega.
    apply fifoLength_one in H3; [|assumption].
    destruct H3.
    - clear -H3; subst.
      repeat split.
      rewrite (word0 oenqpv), (word0 odeqpv); reflexivity.
    - subst; repeat split.
  Qed.

  Lemma procDec_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits (fst pdecInl)) ->
      Multistep (fst pdecInl) init n ll ->
      procDec_inv n.
  Proof. (* SKIP_PROOF_OFF *)
    induction 2.

    - kinv_dest_custom procDec_inv_tac.
      kinv_constr.
      + cbn; repeat rewrite wordToNat_wzero; split; intros; reflexivity.
      + cbn; repeat rewrite wordToNat_wzero; split; intros; reflexivity.
      + cbn; repeat rewrite wordToNat_wzero; reflexivity.
      + procDec_inv_next 0.

    - kinvert; [mred|mred|..].
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * split; intros.
          { rewrite orb_false_l in H2; find_if_inside; [auto|discriminate]. }
          { rewrite orb_false_l; find_if_inside; [reflexivity|exfalso; auto]. }
        * assumption.
        * rewrite wnot_not_zero_wplusone by assumption.
          erewrite <-fifoLength_enq with (emptyv:= iev) by (apply H; auto).
          omega.

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * split; intros.
          { rewrite orb_false_l in H2; find_if_inside; [auto|discriminate]. }
          { rewrite orb_false_l; find_if_inside; [reflexivity|exfalso; auto]. }
        * assumption.
        * erewrite <-fifoLength_enq with (emptyv:= iev) by (apply H; auto).
          replace #x1 with (NatLib.pow2 iaddrSize - 1) in H4.
          { pose proof (NatLib.pow2_zero iaddrSize); omega. }
          { replace x1 with (wones iaddrSize).
            { apply eq_sym, wones_pow2_minus_one. }
            { apply wnot_zero_wones in e; auto. }
          }

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * assumption.
        * split; intros.
          { rewrite orb_false_r in H2; find_if_inside; [auto|discriminate]. }
          { rewrite orb_false_r; find_if_inside; [reflexivity|exfalso; auto]. }
        * rewrite wnot_not_zero_wplusone by assumption.
          rewrite fifoLength_deq in H4 by (apply H3; auto).
          omega.
          
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        apply wnot_zero_wones in e; subst.
        rewrite wones_pow2_minus_one in H4.
        eapply fifo_rq_rs_inv_last in H4; [|assumption|assumption].
        dest; subst.
        procDec_inv_next 0; kinv_finish.

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 1; kinv_eq; kinv_finish.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 1; kinv_eq; kinv_finish.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * split; intros.
          { rewrite orb_false_r in H2; find_if_inside; [assumption|discriminate]. }
          { rewrite orb_false_r; find_if_inside; [reflexivity|exfalso; auto]. }
        * split; intros.
          { rewrite orb_false_l in H2; find_if_inside; [auto|discriminate]. }
          { rewrite orb_false_l; find_if_inside; [reflexivity|exfalso; auto]. }
        * erewrite <-fifoLength_enq with (emptyv:= oev) by assumption.
          rewrite Nat.add_comm with (m:= 1), Nat.add_assoc.
          rewrite <-Nat.add_assoc with (n:= #pinitRsOfsv).
          erewrite <-fifoLength_deq with (fullv:= ifv) by assumption.
          assumption.
        * procDec_inv_old; procDec_inv_next 2.
          (* END_SKIP_PROOF_OFF *)
  Qed.

  Lemma procDec_inv_ok:
    forall o,
      reachable o (fst pdecInl) ->
      procDec_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_ok'; eauto.
  Qed.

End Invariants.

Hint Unfold RqFromProc RsToProc: MethDefs.
Hint Unfold fifo_rq_rs_inv fifo_inv fifo_empty_inv fifo_not_empty_inv
       mem_request_inv: InvDefs.
    
