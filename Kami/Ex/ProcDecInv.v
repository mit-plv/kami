Require Import Bool String List BinNums Lia.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.
Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.
Require Import Kami.Renaming Kami.Specialize Kami.Inline Kami.InlineFacts Kami.Decomposition.
Require Import Kami.Tactics Kami.Notations.
Require Import Ex.MemTypes Ex.SC Ex.NativeFifo Ex.MemAsync Ex.ProcDec Ex.ProcDecInl.
Require Import Eqdep ProofIrrelevance.

Set Implicit Arguments.

Local Hint Unfold listIsEmpty listEnq listDeq listFirstElt: MethDefs.

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
    assert (#w2 = NatLib.pow2 sz - 1 \/ (#w2 < NatLib.pow2 sz - 1)%nat) by lia.
    destruct H2; [|assumption].
    assert (natToWord sz (#w2) = natToWord sz (NatLib.pow2 sz - 1)) by congruence.
    rewrite natToWord_wordToNat, <-wones_natToWord in H3; subst.
    rewrite wnot_ones in H.
    exfalso; auto.
  }
  erewrite wordToNat_plusone; [|eassumption].
  lia.
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
  rewrite <- @wneg_idempotent with (w:= w), H.
  apply eq_sym, wones_wneg_one.
Qed.

Section Invariants.
  Variables addrSize iaddrSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx).

  Definition RqFromProc := MemTypes.RqFromProc dataBytes (Bit addrSize).
  Definition RsToProc := MemTypes.RsToProc dataBytes.

  Variable (init: ProcInit addrSize dataBytes rfIdx).

  Definition pdecInl := projT1 (pdecInl fetch dec exec init).

  Fixpoint pgm_init_rq_inv
           (pinitRqv: type Bool)
           (pinitRqOfsv: type (Bit iaddrSize))
           (ieltv: listEltT (Struct RqFromProc) type) :=
    match ieltv with
    | nil => True
    | rq :: rqs =>
      rq = evalExpr
             (STRUCT { "addr" ::=
                         toAddr _ (natToWord _ ((if pinitRqv
                                                 then NatLib.pow2 iaddrSize
                                                 else wordToNat pinitRqOfsv)
                                                - List.length ieltv));
                       "op" ::= $$false;
                       "byteEn" ::= $$Default;
                       "data" ::= $0 })%kami_expr /\
      pgm_init_rq_inv pinitRqv pinitRqOfsv rqs
    end.

  Definition pgm_init_rq_rs_inv
             (pinitRqv: type Bool)
             (pinitRqOfsv pinitRsOfsv: type (Bit iaddrSize))
             (ieltv: listEltT (Struct RqFromProc) type)
             (oeltv: listEltT (Struct RsToProc) type) :=
    (if pinitRqv then NatLib.pow2 iaddrSize else #pinitRqOfsv) =
    #pinitRsOfsv + List.length ieltv + List.length oeltv.

  Definition fifo_empty_inv {k: Kind} (eltv: listEltT k type) :=
    eltv = nil.
  
  Definition fifo_not_empty_inv {k: Kind} (eltv: listEltT k type) :=
    List.length eltv = 1.

  Definition mem_request_inv
             (rawInst: fullType type (SyntaxKind (Data instBytes)))
             (rf: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx)))
             (insElt: listEltT (Struct RqFromProc) type): Prop.
  Proof.
    destruct insElt as [|rq rqs]; [exact True|].
    refine (_ /\ _).
    - exact ((rq (RqFromProc !! "op") = false ->
              evalExpr (getOptype _ rawInst) = opLd) /\
             (evalExpr (getOptype _ rawInst) = opLd ->
              (rq (RqFromProc !! "op") = false /\
               rq (RqFromProc !! "addr") =
               evalExpr
                 (calcLdAddr
                    _ (evalExpr (getLdAddr _ rawInst))
                    (evalExpr (#rf@[getLdSrc _ rawInst])%kami_expr)) /\
               rq (RqFromProc !! "data") =
               evalConstT (getDefaultConst (Data dataBytes)) /\
               rq (RqFromProc !! "byteEn") =
               evalConstT (getDefaultConst (Array Bool dataBytes)))))%kami_expr.
    - exact ((rq (RqFromProc !! "op") = true ->
              evalExpr (getOptype _ rawInst) = opSt) /\
             (evalExpr (getOptype _ rawInst) = opSt ->
              (rq (RqFromProc !! "op") = true /\
               rq (RqFromProc !! "addr") =
               evalExpr (calcStAddr
                           _ (evalExpr (getStAddr _ rawInst))
                           (evalExpr (#rf@[getStSrc _ rawInst]))) /\
               rq (RqFromProc !! "data") =
               evalExpr (#rf@[getStVSrc _ rawInst ]) /\
               rq (RqFromProc !! "byteEn") =
               evalExpr (calcStByteEn _ rawInst))))%kami_expr.
  Defined.
  #[local] Hint Unfold pgm_init_rq_rs_inv fifo_empty_inv fifo_not_empty_inv
       mem_request_inv: InvDefs.

  Record procDec_inv (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Pc addrSize));
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

      ieltv : fullType type (listEltK (Struct RqFromProc) type);
      Hieltv : M.find "rqFromProc"--"elt"%string o = Some (existT _ _ ieltv);
      oeltv : fullType type (listEltK (Struct RsToProc) type);
      Hoeltv : M.find "rsToProc"--"elt"%string o = Some (existT _ _ oeltv);

      Hinv :
        (pinitv = false ->
         pgm_init_rq_inv pinitRqv pinitRqOfsv ieltv /\
         pgm_init_rq_rs_inv pinitRqv pinitRqOfsv pinitRsOfsv ieltv oeltv /\
         stallv = false) /\
        (pinitv = true ->
         or3 (stallv = false /\ fifo_empty_inv ieltv /\ fifo_empty_inv oeltv)
             ((stallv = true /\ fifo_not_empty_inv ieltv /\ fifo_empty_inv oeltv) /\
              (mem_request_inv (pgmv (evalExpr (toIAddr _ pcv))) rfv ieltv))
             (stallv = true /\ fifo_empty_inv ieltv /\ fifo_not_empty_inv oeltv))
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

  Lemma pgm_init_rq_inv_enq_not_last:
    forall elts rqOfs,
      wnot rqOfs <> $0 ->
      pgm_init_rq_inv false rqOfs elts ->
      forall elt,
        elt = evalExpr
                (STRUCT { "addr" ::= toAddr _ rqOfs;
                          "op" ::= $$false;
                          "byteEn" ::= $$Default;
                          "data" ::= $0})%kami_expr ->
        pgm_init_rq_inv false (rqOfs ^+ $1) (listEnq elt elts).
  Proof.
    induction elts; intros.
    - simpl; split; auto.
      rewrite H1; simpl; kinv_eq.
      rewrite wnot_not_zero_wplusone by assumption.
      rewrite PeanoNat.Nat.add_sub.
      rewrite natToWord_wordToNat.
      reflexivity.
    - simpl in H0; dest; subst.
      split.
      + simpl; kinv_eq.
        rewrite app_length; simpl.
        rewrite wnot_not_zero_wplusone by assumption.
        unfold type, ilist_to_fun_m; simpl.
        do 3 f_equal; lia.
      + apply IHelts; auto.
  Qed.

  Lemma pgm_init_rq_inv_enq_last:
    forall elts rqOfs,
      wnot rqOfs = $0 ->
      pgm_init_rq_inv false rqOfs elts ->
      forall elt,
        elt = evalExpr
                (STRUCT { "addr" ::= toAddr _ rqOfs;
                          "op" ::= $$false;
                          "byteEn" ::= $$Default;
                          "data" ::= $0})%kami_expr ->
        pgm_init_rq_inv true $0 (listEnq elt elts).
  Proof.
    induction elts; intros.
    - simpl; split; auto.
      rewrite H1; simpl; kinv_eq.
      rewrite wnot_zero_wones with (w:= rqOfs) by assumption.
      rewrite wones_natToWord; reflexivity.
    - simpl in H0; dest; subst.
      split.
      + simpl; kinv_eq.
        rewrite app_length; simpl.
        rewrite wnot_zero_wones with (w:= rqOfs) by assumption.
        rewrite wones_natToWord.
        unfold type, ilist_to_fun_m; simpl.
        do 3 f_equal.
        pose proof (NatLib.pow2_zero iaddrSize).
        rewrite wordToNat_natToWord_2; lia.
      + apply IHelts; auto.
  Qed.

  Lemma pgm_init_rq_inv_deq:
    forall elts rqf rqOfs,
      pgm_init_rq_inv rqf rqOfs elts ->
      pgm_init_rq_inv rqf rqOfs (listDeq elts).
  Proof.
    induction elts; intros; auto.
    simpl in H; dest; subst.
    simpl; assumption.
  Qed.

  Lemma pgm_init_rq_rs_inv_last:
    forall (pinitRqv: type Bool) (pinitRqOfsv: type (Bit iaddrSize))
           (ieltv: listEltT (Struct RqFromProc) type)
           (oeltv: listEltT (Struct RsToProc) type),
      oeltv <> nil ->
      (if pinitRqv then NatLib.pow2 iaddrSize else # (pinitRqOfsv)) =
      NatLib.pow2 iaddrSize - 1 + Datatypes.length ieltv + Datatypes.length oeltv ->
      pinitRqv = true /\ ieltv = nil /\ List.length oeltv = 1.
  Proof.
    intros.
    find_if_inside.
    - destruct oeltv; [exfalso; auto|].
      destruct ieltv; simpl in H0; [|lia].
      destruct oeltv; simpl in H0; [|lia].
      auto.
    - destruct oeltv; [exfalso; auto|].
      simpl in H0.
      exfalso.
      pose proof (wordToNat_bound pinitRqOfsv); lia.
  Qed.

  Lemma procDec_inv_ok':
    forall init n ll,
      init = initRegs (getRegInits pdecInl) ->
      Multistep pdecInl init n ll ->
      procDec_inv n.
  Proof. (* SKIP_PROOF_ON
    induction 2.

    - kinv_dest_custom procDec_inv_tac.
      kinv_constr.
      + simpl; auto.
      + cbn; repeat rewrite wordToNat_wzero; split; intros; reflexivity.
      + procDec_inv_next 0.

    - kinvert; [mred|mred|..].
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * kinv_regmap_red.
          apply pgm_init_rq_inv_enq_not_last; auto.
        * kinv_regmap_red.
          rewrite app_length; simpl in *.
          rewrite wnot_not_zero_wplusone by assumption.
          unfold type in *; simpl in *.
          lia.

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * eapply pgm_init_rq_inv_enq_last; eauto.
        * kinv_regmap_red.
          rewrite app_length; simpl in *.
          replace #x1 with (NatLib.pow2 iaddrSize - 1) in H2.
          { pose proof (NatLib.pow2_zero iaddrSize).
            unfold type in *; simpl in *; lia.
          }
          { replace x1 with (wones iaddrSize).
            { apply eq_sym, wones_pow2_minus_one. }
            { apply wnot_zero_wones in e; auto. }
          }

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * assumption.
        * kinv_regmap_red.
          rewrite wnot_not_zero_wplusone by assumption.
          destruct x1; [discriminate|].
          simpl in *; lia.

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        apply wnot_zero_wones in e; subst.
        rewrite wones_pow2_minus_one in H2.
        eapply pgm_init_rq_rs_inv_last in H2; [|destruct x1; discriminate].
        dest; subst.
        destruct x1; [discriminate|].
        destruct x1; [|discriminate].
        procDec_inv_next 0.

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 1; kinv_eq.
        simpl; kinv_constr; kinv_finish.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 1; kinv_eq.
        simpl; kinv_constr; kinv_finish.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
        destruct x; [discriminate|].
        destruct x; [reflexivity|discriminate].
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
        destruct x; [discriminate|].
        destruct x; [reflexivity|discriminate].
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
        destruct x; [discriminate|].
        destruct x; [reflexivity|discriminate].
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        procDec_inv_next 0.

      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * apply pgm_init_rq_inv_deq; assumption.
        * rewrite H2.
          destruct x; [discriminate|].
          kinv_regmap_red.
          unfold type in *; simpl in *.
          rewrite app_length; simpl; lia.
        * procDec_inv_old; procDec_inv_next 2.
          destruct x; [discriminate|].
          destruct x; [reflexivity|discriminate].
      + kinv_dest_custom procDec_inv_tac; kinv_constr.
        * apply pgm_init_rq_inv_deq; assumption.
        * rewrite H2.
          destruct x; [discriminate|].
          kinv_regmap_red.
          unfold type in *; simpl in *.
          rewrite app_length; simpl; lia.
        * procDec_inv_old; procDec_inv_next 2.
          destruct x; [discriminate|].
          destruct x; [reflexivity|discriminate].
          END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma procDec_inv_ok:
    forall o,
      reachable o pdecInl ->
      procDec_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply procDec_inv_ok'; eauto.
  Qed.

End Invariants.

#[global] Hint Unfold RqFromProc RsToProc: MethDefs.
#[global] Hint Unfold pgm_init_rq_rs_inv fifo_empty_inv fifo_not_empty_inv
       mem_request_inv: InvDefs.

