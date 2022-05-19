Require Import Bool String List Lia.
Require Import Lib.CommonTactics Lib.NatLib Lib.Indexer
        Lib.Struct Lib.DepEq Lib.Word Lib.FMap Lib.Reflection.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.SemFacts Kami.Tactics.

Require Import ZArith Eqdep Program.Equality.

Set Implicit Arguments.

Open Scope string.

Lemma evalExprRewrite K (e: Expr type (SyntaxKind K))
  : evalExpr (#(evalExpr e))%kami_expr = evalExpr e.
Proof.
  induction e; simpl in *; auto.
Qed.

(* Below implements non-restoring division for _unsigned_ integers.
 * Operands should be made unsigned first and the signs should be re-applied
 * after the division.
 *)
Section Divider64.
  Definition DivLogNumPhases := 3.
  Definition DivNumBitsPerPhase := 8.

  Local Definition DivNumPhases := wordToNat (wones DivLogNumPhases) + 1.
  Local Definition DivNumBits := DivNumPhases * DivNumBitsPerPhase.
  Local Definition DivBits := DivNumBits + (2 * DivNumBits).

  (* "dividend" and "divisor" each should be an unsigned integer. *)
  Definition DivInStr := STRUCT { "dividend" :: Bit DivNumBits;
                                  "divisor" :: Bit DivNumBits }.

  (* "quotient" and "remainder" each should be an unsigned integer. *)
  Definition DivOutStr := STRUCT { "quotient" :: Bit DivNumBits;
                                   "remainder" :: Bit DivNumBits }.

  Definition divRegister := MethodSig "divRegister"(Struct DivInStr): Void.
  Definition divGetResult := MethodSig "divGetResult"(Void): Struct DivOutStr.

  Definition nrDivStep {ty}
             (xq: fullType ty (SyntaxKind (Bit DivBits)))
             (d_pos d_neg: fullType ty (SyntaxKind (Bit (2 * DivNumBits))))
    : Expr ty (SyntaxKind (Bit DivBits)) :=
    ((* Step 1: shift 1-bit *)
      let pq_shift := BinBit (Sll (DivNumBits + (pred (2 * DivNumBits)) + 1) _)
                             #xq $$(natToWord 1 1) in
      (* Step 2: add or subtract *)
      (* Step 3: set the quotient bit, which is a LSB here *)
      let pq_shift_msb := UniBit (TruncLsb _ 1) pq_shift in
      pq_shift +
      (IF (pq_shift_msb == $0)
       then BinBit (Concat (2 * DivNumBits) DivNumBits) #d_neg $1
       else BinBit (Concat (2 * DivNumBits) DivNumBits) #d_pos $0)
    )%kami_expr.

  Definition nrDivNextQBit (xq: word DivBits): word 1 :=
    if weq (split2 (DivNumBits + (pred (2 * DivNumBits))) 1 (wlshift xq 1)) $0
    then $1 else $0.

  Definition nrDivNextAdder (xq: word DivBits) (d_pos d_neg: word (2 * DivNumBits)) :=
    if weq (split2 (DivNumBits + (pred (2 * DivNumBits))) 1 (wlshift xq 1)) $0
    then d_neg else d_pos.

  Lemma nrDivNextAdder_wmsb:
    forall xq d_pos d_neg,
      wmsb (nrDivNextAdder xq d_pos d_neg) false =
      if wmsb (wlshift xq 1) false then wmsb d_pos false else wmsb d_neg false.
  Proof.
    unfold nrDivNextAdder; intros.
    change DivBits with (pred DivBits + 1) in xq.
    pose proof (wmsb_split2 _ (wlshift xq 1) false).
    destruct (weq _ _);
      try (change (pred DivBits + 1) with DivBits in H;
           rewrite H; reflexivity).
  Qed.

  Lemma nrDivNextAdder_Z_value:
    forall xq (d: word DivNumBits) n,
      wordToZ (extz (nrDivNextAdder xq (zext d DivNumBits) (^~ (zext d DivNumBits))) n) =
      ((if wmsb (wlshift xq 1) false then 1 else -1)
       * (Z.of_nat (wordToNat d) * Z.of_nat (pow2 n)))%Z.
  Proof.
    change DivBits with (pred DivBits + 1).
    unfold nrDivNextAdder; intros.
    rewrite wmsb_split2.
    destruct (weq _ _).
    - rewrite extz_pow2_wordToZ.
      change (DivNumBits + DivNumBits) with (S (pred DivNumBits + DivNumBits)).
      change (2 * DivNumBits) with (S (pred DivNumBits + DivNumBits)).
      rewrite wneg_wordToZ.
      + change (S (pred DivNumBits + DivNumBits)) with (DivNumBits + DivNumBits).
        rewrite zext_wordToNat_equal_Z by discriminate.
        rewrite <-Z.mul_opp_l.
        reflexivity.
      + intro Hx.
        assert (wmsb (zext d DivNumBits) false =
                wmsb (wpow2 (Init.Nat.pred DivNumBits + DivNumBits)) false)
          by (rewrite Hx; reflexivity).
        rewrite wmsb_zext in H by discriminate.
        rewrite wpow2_wmsb in H; discriminate.
    - rewrite extz_pow2_wordToZ.
      change (2 * DivNumBits) with (DivNumBits + DivNumBits).
      rewrite zext_wordToNat_equal_Z by discriminate.
      lia.
  Qed.

  Lemma nrDivNextAdder_bound:
    forall sz (pq: word sz) (na d: Z),
      (d > 0)%Z ->
      (Z.abs (wordToZ pq) <= 2 * d)%Z ->
      (na = (if wmsb pq false then 1 else -1) * d)%Z ->
      (Z.abs (wordToZ pq + na) <= d)%Z.
  Proof.
    intros; subst.
    remember (wmsb pq false) as pqb; destruct pqb.
    - apply eq_sym, wmsb_true_neg in Heqpqb.
      rewrite Z.abs_neq in H0 by lia.
      destruct (wordToZ pq).
      + cbn; lia.
      + replace (1 * d)%Z with d by lia.
        apply Z.abs_le; split; lia.
      + replace (1 * d)%Z with d by lia.
        apply Z.abs_le; split; lia.
    - apply eq_sym, wmsb_false_pos in Heqpqb.
      rewrite Z.abs_eq in H0 by lia.
      destruct (wordToZ pq).
      + replace (0 + -1 * d)%Z with (-d)%Z by lia.
        destruct d; cbn; try lia.
      + replace (-1 * d)%Z with (-d)%Z by lia.
        apply Z.abs_le; split; lia.
      + replace (-1 * d)%Z with (-d)%Z by lia.
        apply Z.abs_le; split; lia.
  Qed.

  Lemma nrDivStep_eval:
    forall xq d_pos d_neg,
      evalExpr (nrDivStep xq d_pos d_neg) =
      (wlshift xq 1)
        ^+ (if weq (split2 (DivNumBits + (pred (2 * DivNumBits))) 1 (wlshift xq 1)) $0
            then combine $1 d_neg
            else combine $0 d_pos).
  Proof.
    intros.
    unfold nrDivStep, evalExpr, evalUniBit, evalBinBit, isEq, evalConstT.
    rewrite roundTrip_1.
    destruct (weq _ _); reflexivity.
  Qed.

  Opaque nrDivStep.

  Fixpoint nrDivSteps (cnt: nat)
           {ty} (xq: fullType ty (SyntaxKind (Bit (DivNumBits + 2 * DivNumBits))))
           (d_pos d_neg: fullType ty (SyntaxKind (Bit (2 * DivNumBits))))
           (cont: fullType ty (SyntaxKind (Bit (DivNumBits + 2 * DivNumBits))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont xq)%kami_action
    | S n => (LET npq <- nrDivStep xq d_pos d_neg;
              nrDivSteps n npq d_pos d_neg cont)%kami_action
    end.

  Definition nrDivPull := MethodSig "nrDivPull"(): Struct DivInStr.
  Definition nrDivPush := MethodSig "nrDivPush"(Struct DivOutStr): Void.

  (* Positive-negative digit {0 |-> -1, 1 |-> 1} number 
   * to the corresponding binary number. *)
  Definition pn2bin {ty n} (w: fullType ty (SyntaxKind (Bit n)))
    : Expr ty (SyntaxKind (Bit (S n))) :=
    ((UniBit (ZeroExtendTrunc _ (S n)) #w)
     - (UniBit (ZeroExtendTrunc _ (S n)) (UniBit (Neg _) #w - $1)))%kami_expr.

  Definition pn2binE {n} (w: word n) :=
    (zext w 1) ^- (zext (wnot w) 1).

  Lemma pn2bin_eval:
    forall n (w: fullType type (SyntaxKind (Bit n))),
      existT word _ (evalExpr (pn2bin w)) = existT word _ (pn2binE w).
  Proof.
    unfold pn2binE; intros; cbn.
    cbv [evalZeroExtendTrunc].
    destruct (lt_dec _ _); [|lia].
    apply existT_wminus.
    - unfold zext, eq_rec.
      change (fun n2 => word n2) with word.
      rewrite existT_eq_rect.
      match goal with
      | [ |- existT _ (n + ?mn) _ = _ ] =>
        replace mn with 1 by (clear; induction n; auto)
      end.
      reflexivity.
    - unfold zext, eq_rec.
      change (fun n2 => word n2) with word.
      rewrite existT_eq_rect.
      match goal with
      | [ |- existT _ (n + ?mn) _ = _ ] =>
        replace mn with 1 by (clear; induction n; auto)
      end.
      rewrite wneg_wnot.
      reflexivity.
  Qed.

  Definition pn2binBool (b: bool): Z := if b then 1 else -1.

  Fixpoint pn2binBitwise {n} (w: word n): Z :=
    match w with
    | WO => 0
    | WS b w' => pn2binBool b + 2 * (pn2binBitwise w')
    end.

  Lemma pn2bin_bitwise_eq:
    forall sz (w: word sz), wordToZ (pn2binE w) = pn2binBitwise w.
  Proof.
    dependent induction w; [reflexivity|].
    unfold pn2binE.
    destruct b; cbn.
    - rewrite wminus_WS_pos'.
      rewrite <-IHw.
      cbn; unfold pn2binE, zext; cbn.
      destruct (wordToZ _); reflexivity.
    - rewrite wminus_wordToZ.
      + rewrite wminus_WS_pos'.
        rewrite wminus_wordToZ'.
        * rewrite <-IHw.
          cbn; unfold pn2binE, zext; cbn.
          destruct (wordToZ _); reflexivity.
        * clear; intro Hx.
          apply existT_wordToZ in Hx.
          dependent destruction w.
          { cbn in Hx; discriminate. }
          { destruct b; unfold wminus in Hx; simpl in Hx.
            { rewrite wneg_WS_0 in Hx.
              rewrite <-wplus_WS_0 in Hx.
              rewrite wordToZ_WS_0 in Hx.
              rewrite wordToZ_WS_1' in Hx.
              lia.
            }
            { rewrite wneg_WS_1 in Hx.
              rewrite wplus_comm in Hx.
              rewrite <-wplus_WS_0 in Hx.
              rewrite wordToZ_WS_0 in Hx.
              rewrite wordToZ_WS_1' in Hx.
              lia.
            }
          }
      + unfold wminus.
        rewrite wneg_WS_0.
        rewrite <-wplus_WS_0.
        remember (combine (wnot w) WO~0 ^+ ^~ (combine w WO~0)) as ww.
        clear; induction n; discriminate.
  Qed.

  Corollary pn2binE_lsb_0:
    forall sz (w: word sz),
      wordToZ (pn2binE (combine (natToWord 1 0) w)) =
      (2 * wordToZ (pn2binE w) - 1)%Z.
  Proof.
    intros.
    do 2 rewrite pn2bin_bitwise_eq; simpl.
    destruct (pn2binBitwise w); reflexivity.
  Qed.

  Corollary pn2binE_lsb_1:
    forall sz (w: word sz),
      wordToZ (pn2binE (combine (natToWord 1 1) w)) =
      (2 * wordToZ (pn2binE w) + 1)%Z.
  Proof.
    intros.
    do 2 rewrite pn2bin_bitwise_eq; simpl.
    destruct (pn2binBitwise w); reflexivity.
  Qed.
  
  Variable n: nat.

  Definition finalRestoringQ {ty}
             (rem: fullType ty (SyntaxKind (Bit (pred (2 * DivNumBits) + 1))))
             (q_bin: fullType ty (SyntaxKind (Bit (DivNumBits + 1))))
             (d_pos: fullType ty (SyntaxKind (Bit (2 * DivNumBits))))
    : Expr ty (SyntaxKind (Bit (DivNumBits + 1))) :=
    (IF (UniBit (TruncLsb _ 1) #rem) == $1
     then #q_bin - $1
     else (IF #rem == #d_pos
           then #q_bin + $1
           else #q_bin))%kami_expr.

  Definition finalRestoringR {ty}
             (rem: fullType ty (SyntaxKind (Bit (pred (2 * DivNumBits) + 1))))
             (d_pos: fullType ty (SyntaxKind (Bit (2 * DivNumBits))))
    : Expr ty (SyntaxKind (Bit DivNumBits)) :=
    (UniBit (Trunc DivNumBits DivNumBits)
            (IF (UniBit (TruncLsb _ 1) #rem) == $1
             then #rem + #d_pos
             else (IF #rem == #d_pos
                   then $0
                   else #rem)))%kami_expr.

  Lemma finalRestoringQ_eval:
    forall rem q_bin d_pos,
      evalExpr (finalRestoringQ rem q_bin d_pos) =
      if weq (split2 _ 1 rem) WO~1
      then q_bin ^- $1
      else if weq rem d_pos
           then q_bin ^+ $1
           else q_bin.
  Proof.
    intros.
    Opaque split1 split2.
    cbn.
    destruct (weq _ _); [reflexivity|].
    destruct (weq _ _); reflexivity.
    Transparent split1 split2.
  Qed.

  Lemma finalRestoringR_eval:
    forall rem d_pos,
      evalExpr (finalRestoringR rem d_pos) =
      split1 DivNumBits DivNumBits
             (if weq (split2 _ 1 rem) WO~1
              then rem ^+ d_pos
              else if weq rem d_pos
                   then $0
                   else rem).
  Proof.
    intros.
    Opaque split1 split2.
    cbn.
    destruct (weq _ _); [reflexivity|].
    destruct (weq _ _); reflexivity.
    Transparent split1 split2.
  Qed.

  Definition nrDividerImpl :=
    MODULE {
      Register "xq" : Bit DivBits <- Default
      with Register "x" : Bit DivNumBits <- Default
      with Register "d" : Bit DivNumBits <- Default
      with Register "d_pos" : Bit (2 * DivNumBits) <- Default
      with Register "d_neg" : Bit (2 * DivNumBits) <- Default
      with Register "cnt" : Bit (S DivLogNumPhases) <- Default

      with Rule "nrDivRegister" :=
        Call src <- nrDivPull();
        
        LET dividend : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET divisor : Bit DivNumBits <- #src!DivInStr@."divisor";
        Assert (#divisor != $0);
        
        Write "xq" : Bit (DivNumBits + 2 * DivNumBits) <- UniBit (ZeroExtendTrunc _ _) #dividend;
        Write "x" <- #dividend;
        Write "d" <- #divisor;

        LET d_pos <- UniBit (ZeroExtendTrunc _ (2 * DivNumBits)) #divisor;
        LET d_neg <- UniBit (Neg _) #d_pos;
        Write "d_pos" <- #d_pos;
        Write "d_neg" <- #d_neg;
        Write "cnt" : Bit (S DivLogNumPhases) <- $(DivNumPhases);
        Retv

      with Rule "nrDivGetResult" :=
        Read cnt : Bit (S DivLogNumPhases) <- "cnt";
        Assert (#cnt == $0);

        Read xq : Bit (DivNumBits + 2 * DivNumBits) <- "xq";
        Read d_pos : Bit (2 * DivNumBits) <- "d_pos";
        Assert (#d_pos != $0);
        
        LET rem : Bit (pred (2 * DivNumBits) + 1) <- UniBit (TruncLsb _ _) #xq;
        
        LET q_pn : Bit DivNumBits <- UniBit (Trunc _ _) #xq;
        LET q_bin : Bit (DivNumBits + 1) <- pn2bin q_pn;

        (* A final restoring, if necessary *)
        LET rem_rst : Bit DivNumBits <- finalRestoringR rem d_pos;
        LET q_rst : Bit (DivNumBits + 1) <- finalRestoringQ rem q_bin d_pos;
        LET q_rst_cut : Bit DivNumBits <- UniBit (Trunc _ _) #q_rst;

        Call nrDivPush(STRUCT { "quotient" ::= #q_rst_cut;
                                "remainder" ::= #rem_rst });
        Retv
            
      with Rule "nrDivStep" :=
        Read cnt : Bit (S DivLogNumPhases) <- "cnt";
        Assert (#cnt != $0);

        Read xq : Bit (DivNumBits + 2 * DivNumBits) <- "xq";
        Read d_pos : Bit (2 * DivNumBits) <- "d_pos";
        Read d_neg : Bit (2 * DivNumBits) <- "d_neg";

        Write "cnt" <- #cnt - $1;

        nrDivSteps
          DivNumBitsPerPhase xq d_pos d_neg
          (fun npq => Write "xq" <- #npq; Retv)
    }.

  Definition dividerSpec :=
    MODULE {
      Register "x" : Bit DivNumBits <- Default
      with Register "d" : Bit DivNumBits <- Default

      with Rule "divRegister" :=
        Call src <- nrDivPull();
        LET x : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET d : Bit DivNumBits <- #src!DivInStr@."divisor";
        Assert (#d != $0);
        
        Write "x" <- #x;
        Write "d" <- #d;
        Retv

      with Rule "divGetResult" :=
        Read x : Bit DivNumBits <- "x";
        Read d : Bit DivNumBits <- "d";
        Assert (#d != $0);

        LET quotient <- BinBit (Div _ false) #x #d;
        LET remainder <- BinBit (Rem _ false) #x #d;

        Call nrDivPush(STRUCT { "quotient" ::= #quotient;
                                "remainder" ::= #remainder });
        Retv
    }.

  (*! Correctness of the divider *)

  Inductive NrDivInv (x: word DivNumBits) (* as an unsigned number *)
            (d: nat) (* also as an unsigned number *)
    : forall sr, word sr -> forall sq, word sq -> Prop :=
  | NDInv: forall sr (prem: word sr) sq (pq: word sq),
      (* x = d * (partial quotient) + (partial remainder) *)
      (wordToZ prem =
       Z.of_nat (wordToNat x) - (Z.of_nat d)
                                * (wordToZ (pn2binE pq))
                                * (Z.of_nat (pow2 (DivNumBits - sq))))%Z ->
      (* boundary of the partial remainder; cf. [Z.rem_bound_abs] *)
      (Z.abs (wordToZ prem) <= (Z.of_nat d) * (Z.of_nat (pow2 (DivNumBits - sq))))%Z ->
      NrDivInv x d prem pq.

  Lemma nrDivInv_inv:
    forall x d sr (prem: word sr) sq (pq: word sq),
      NrDivInv x d prem pq ->
      (wordToZ prem =
       Z.of_nat (wordToNat x) - (Z.of_nat d)
                                * (wordToZ (pn2binE pq))
                                * (Z.of_nat (pow2 (DivNumBits - sq))))%Z /\
      (Z.abs (wordToZ prem) <= (Z.of_nat d) * (Z.of_nat (pow2 (DivNumBits - sq))))%Z.
  Proof.
    intros; inv H.
    destruct_existT.
    eauto.
  Qed.

  Lemma nrDivInv_init:
    forall x d, d <> 0 -> NrDivInv x d (zext x (2 * DivNumBits)) WO.
  Proof.
    intros.
    econstructor.
    - rewrite zext_wordToNat_equal_Z by discriminate.
      replace (wordToZ (pn2binE WO)) with 0%Z by reflexivity.
      rewrite Z.mul_0_r, Z.mul_0_l.
      lia.
    - apply Z.le_trans with (m:= (1 * Z.of_nat (pow2 DivNumBits))%Z).
      + rewrite zext_wordToNat_equal_Z by discriminate.
        rewrite Z.mul_1_l.
        rewrite Zabs_of_nat.
        apply Nat2Z.inj_le.
        apply Nat.lt_le_incl.
        apply wordToNat_bound.
      + rewrite Nat.sub_0_r.
        apply Z.mul_le_mono_pos_r.
        * pose proof (pow2_zero DivNumBits); lia.
        * lia.
  Qed.

  Lemma nrDivInv_finish:
    forall x d (prem: word (2 * DivNumBits)) (pq: word DivNumBits),
      d <> 0 -> NrDivInv x d prem pq ->
      (Z.of_nat (wordToNat x) = Z.of_nat d * wordToZ (pn2binE pq) + wordToZ prem)%Z /\
      (Z.abs (wordToZ prem) <= Z.of_nat d)%Z.
  Proof.
    intros; inv H0.
    destruct_existT.
    replace (Z.of_nat (pow2 (DivNumBits - DivNumBits))) with 1%Z in * by reflexivity.
    rewrite Z.mul_1_r in *.
    split; [|assumption].
    lia.
  Qed.

  Lemma nat_div_modulo_unique:
    forall (x d q r: nat),
      (r < d)%nat -> x = d * q + r ->
      q = Nat.div x d /\ r = Nat.modulo x d.
  Proof.
    intros; subst; split.
    - eauto using Nat.div_unique.
    - eauto using Nat.mod_unique.
  Qed.

  Lemma nrDivInv_final_restoring':
    forall (x d: word DivNumBits)
           (Hd: wordToNat d <> 0)
           (d_pos: word (2 * DivNumBits)) (Hdpos: d_pos = zext d DivNumBits)
           (prem: word (pred (2 * DivNumBits) + 1))
           (pq: word (DivNumBits + 1)) (* as a normal binary number *),
      Z.of_nat (wordToNat x) = (Z.of_nat (wordToNat d) * wordToZ pq + wordToZ prem)%Z ->
      (Z.abs (wordToZ prem) <= Z.of_nat (wordToNat d))%Z ->
      wordToNat (split1 DivNumBits 1 (evalExpr (finalRestoringQ prem pq d_pos))) =
      Nat.div (wordToNat x) (wordToNat d) /\
      wordToNat (evalExpr (finalRestoringR prem d_pos)) =
      Nat.modulo (wordToNat x) (wordToNat d).
  Proof.
    intros.
    rewrite finalRestoringQ_eval.
    rewrite finalRestoringR_eval.
    apply nat_div_modulo_unique.

    - subst.
      pose proof (wmsb_split2 _ prem false).
      destruct (weq _ _).
      + destruct (weq _ _); [rewrite e in e0; discriminate|clear e n].
        destruct (weq _ _); subst.
        * change (#(split1 DivNumBits DivNumBits $0)) with 0; Lia.lia.
        * change (pred (2 * DivNumBits) + 1) with (DivNumBits + DivNumBits) in *.
          apply zext_size in H1; dest; subst.
          { unfold zext; rewrite split1_combine.
            apply Nat.le_neq; split.
            { rewrite zext_wordToNat_equal_Z in H0 by discriminate.
              rewrite Zabs_of_nat in H0.
              apply Nat2Z.inj_le; auto.
            }
            { intro Hx.
              apply wordToNat_inj in Hx; subst.
              elim n; reflexivity.
            }
          }
          { apply wordToZ_bound_weakened.
            eapply Z.le_lt_trans; [eassumption|].
            apply Nat2Z.inj_lt.
            apply wordToNat_bound.
          }
      + change (pred (2 * DivNumBits) + 1) with (DivNumBits + DivNumBits) in *.
        destruct (weq _ _);
          [|remember (split2 _ _ _) as w; clear Heqw;
            do 2 dependent destruction w;
            destruct b; intuition idtac].

        assert (Z.abs (wordToZ (prem ^+ zext d DivNumBits)) < wordToZ (zext d DivNumBits))%Z.
        { rewrite wordToZ_distr_diff_wmsb
            by (rewrite H1; apply eq_sym, negb_true_iff;
                rewrite wmsb_zext by discriminate; reflexivity).
          rewrite zext_wordToNat_equal_Z by discriminate.
          apply wmsb_true_neg in H1.
          apply Z.abs_le in H0; dest.
          apply Z.abs_lt; split; lia.
        }

        assert (Z.abs (wordToZ (prem ^+ zext d DivNumBits)) < Z.of_nat (pow2 DivNumBits))%Z.
        { eapply Z.lt_le_trans; [eassumption|].
          rewrite zext_wordToNat_equal_Z by discriminate.
          apply Nat2Z.inj_le.
          apply Nat.lt_le_incl.
          apply wordToNat_bound.
        }

        assert (wordToZ (prem ^+ zext d DivNumBits) >= 0)%Z.
        { rewrite wordToZ_distr_diff_wmsb
            by (rewrite H1; apply eq_sym, negb_true_iff;
                rewrite wmsb_zext by discriminate; reflexivity).
          apply Z.abs_le in H0; dest.
          rewrite zext_wordToNat_equal_Z by discriminate.
          lia.
        }

        apply wmsb_false_pos in H4.
        apply zext_size in H4; [|apply wordToZ_bound_weakened; assumption].
        dest; rewrite H4 in *.
        do 2 rewrite zext_wordToNat_equal_Z in H2 by discriminate.
        rewrite Zabs_of_nat in H2.
        unfold zext; rewrite split1_combine.
        apply Nat2Z.inj_lt; assumption.

    - subst.
      pose proof (wmsb_split2 _ prem false).
      destruct (weq _ _).
      + change (pred (2 * DivNumBits) + 1) with (DivNumBits + DivNumBits) in *.
        destruct (weq _ _); [rewrite e in e0; discriminate|clear e n].
        destruct (weq _ _); subst.
        * clear H0 H1 n0.
          rewrite zext_wordToNat_equal_Z in H by discriminate.
          assert (wordToZ pq + 1 = Z.of_nat (wordToNat (split1 DivNumBits 1 (pq ^+ $1))))%Z.
          { rewrite <-Z.mul_succ_r, <-Z.add_1_r in H.
            assert (Z.of_nat (wordToNat d) > 0)%Z by lia.
            assert (wordToZ pq + 1 >= 0)%Z.
            { pose proof (Zle_0_nat (wordToNat x)).
              rewrite H in H1.
              apply Z.mul_nonneg_cancel_l in H1; [|lia].
              lia.
            }
            assert (wordToZ pq + 1 < Z.of_nat (pow2 DivNumBits))%Z.
            { destruct (Z_lt_ge_dec (wordToZ pq + 1) (Z.of_nat (pow2 DivNumBits))); auto.
              apply Zmult_ge_compat_l with (p:= Z.of_nat (wordToNat d)) in g; [|lia].
              rewrite <-H in g.
              assert (Z.of_nat (pow2 DivNumBits) <=
                      Z.of_nat (wordToNat d) * Z.of_nat (pow2 DivNumBits))%Z.
              { rewrite Z.mul_comm.
                apply (Z.le_mul_diag_r _ (Z.of_nat (wordToNat d))); [|lia].
                change 0%Z with (Z.of_nat 0).
                apply Nat2Z.inj_lt.
                pose proof (pow2_zero DivNumBits); lia.
              }
              apply Z.ge_le_iff in g.
              pose proof (Z.le_trans _ _ _ H2 g).
              assert (Z.of_nat (pow2 DivNumBits) > Z.of_nat (wordToNat x))%Z.
              { apply Z.gt_lt_iff.
                apply Nat2Z.inj_lt.
                apply wordToNat_bound.
              }
              lia.
            }

            assert (wordToZ pq + 1 = wordToZ (pq ^+ $1))%Z.
            { assert (- Z.of_nat (pow2 DivNumBits) <=
                      wordToZ pq + wordToZ (natToWord (DivNumBits + 1) 1) <
                      Z.of_nat (pow2 DivNumBits))%Z.
              { change (wordToZ (natToWord _ _)) with 1%Z.
                split; lia.
              }
              apply wordToZ_wplus_bound in H3.
              assumption.
            }

            remember (wordToZ pq + 1)%Z as pqa; clear Heqpqa; subst.
            apply wmsb_false_pos in H1.
            apply zext_size_1 in H1; dest.
            rewrite H1 in *.
            rewrite zext_wordToNat_equal_Z by discriminate.
            unfold zext; rewrite split1_combine.
            reflexivity.
          }
          rewrite Zred_factor3 in H.
          rewrite Z.add_comm in H.
          rewrite H0 in H.
          rewrite <-Nat2Z.inj_mul in H.
          apply Nat2Z.inj in H.
          rewrite <-H.
          change #(split1 DivNumBits DivNumBits $0) with 0.
          lia.
        * assert (wmsb pq false = false).
          { apply wmsb_false_pos.
            destruct (Z_ge_lt_dec (wordToZ pq) 0%Z); auto.
            exfalso.
            assert (wordToZ pq <= -1)%Z by lia.
            assert (Z.of_nat (wordToNat d) * wordToZ pq <= Z.abs (wordToZ prem) * (-1))%Z.
            { etransitivity.
              { eapply Z.mul_le_mono_nonpos_r; [lia|eassumption]. }
              { eapply Z.mul_le_mono_nonneg_l; [apply Z.abs_nonneg|lia]. }
            }
            assert (Z.of_nat (wordToNat x) <= 0)%Z.
            { rewrite H.
              rewrite wmsb_Zabs_pos in H3 by assumption.
              lia.
            }
            pose proof (Nat2Z.is_nonneg (wordToNat x)).
            assert (x = $0) by (apply wordToNat_inj; simpl; lia); subst.
            elim n; clear n.
            simpl in H.

            apply eq_sym, Z.add_move_0_l in H.
            cbn in H, H0; rewrite H in H0.
            rewrite Z.abs_opp, Z.abs_mul, Zabs_of_nat in H0.

            replace (Z.of_nat (wordToNat d)) with (Z.of_nat (wordToNat d) * 1)%Z
              in H0 at 2 by lia.
            apply Z.mul_le_mono_pos_l in H0;
              [|change 0%Z with (Z.of_nat 0); apply Nat2Z.inj_lt; lia].
            apply Z.abs_le in H0; dest.
            assert (wordToZ pq = -1)%Z by (cbn; cbn in H0, H2; lia).
            cbn in H7; rewrite H7 in H.
            change (-1)%Z with (- (1))%Z in H.
            rewrite Z.mul_opp_r, Z.opp_involutive, Z.mul_1_r in H.
            rewrite <-wordToZ_wordToNat_pos in H by assumption.
            apply Nat2Z.inj in H.
            cbn in d.
            replace (wordToNat d) with (wordToNat (zext d DivNumBits)) in H
              by apply wordToNat_zext.
            apply wordToNat_inj; assumption.
          }
          rewrite <-wordToZ_wordToNat_pos with (w:= pq) in H by assumption.
          rewrite <-wordToZ_wordToNat_pos with (w:= prem) in H by assumption.
          rewrite <-Nat2Z.inj_mul in H.
          rewrite <-Nat2Z.inj_add in H.

          assert (exists spq, pq = zext spq 1).
          { apply zext_size; [|assumption].
            apply wordToZ_size'.
          }
          assert (exists sprem, prem = zext sprem DivNumBits).
          { apply zext_size; [|assumption].
            apply wordToZ_bound_weakened.
            eapply Z.le_lt_trans; [eassumption|].
            apply Nat2Z.inj_lt.
            apply wordToNat_bound.
          }
          dest; subst.
          unfold zext; do 2 rewrite split1_combine.
          do 2 rewrite wordToNat_zext in H.
          auto using Nat2Z.inj.
          
      + change (pred (2 * DivNumBits) + 1) with (DivNumBits + DivNumBits) in *.
        destruct (weq _ _);
          [|remember (split2 _ _ _) as w; clear Heqw;
            do 2 dependent destruction w;
            destruct b; intuition idtac].
        clear e n0.

        assert (Z.of_nat (wordToNat d) > 0)%Z by lia.
        assert (wordToZ pq - 1 = Z.of_nat (wordToNat (split1 DivNumBits 1 (pq ^- $ (1)))))%Z.
        { assert (wordToZ pq - 1 >= 0)%Z.
          { apply wmsb_true_neg in H1.
            assert (Z.of_nat (wordToNat d) * wordToZ pq + wordToZ prem >= 0)%Z.
            { rewrite <-H.
              pose proof (Nat2Z.is_nonneg (wordToNat x)); lia.
            }
            assert (Z.of_nat (wordToNat d) * wordToZ pq >= -(wordToZ prem))%Z by lia.
            assert (Z.of_nat (wordToNat d) * wordToZ pq > 0)%Z by lia.
            assert (wordToZ pq > 0)%Z.
            { apply Z.gt_lt_iff in H5.
              rewrite Z.mul_comm in H5.
              apply Zmult_gt_0_lt_0_reg_r in H5; lia.
            }
            lia.
          }

          assert (wordToZ pq - 1 < Z.of_nat (pow2 DivNumBits))%Z.
          { remember (wmsb pq false) as pqmsb; destruct pqmsb.
            { apply eq_sym, wmsb_true_neg in Heqpqmsb; lia. }
            { apply eq_sym, zext_size_1 in Heqpqmsb; dest; subst.
              rewrite zext_wordToNat_equal_Z by discriminate.
              assert (Z.of_nat (wordToNat x0) < Z.of_nat (pow2 DivNumBits))%Z
                by (apply Nat2Z.inj_lt, wordToNat_bound).
              lia.
            }
          }

          assert (wordToZ pq - 1 = wordToZ (pq ^- $1))%Z.
          { assert (- Z.of_nat (pow2 DivNumBits) <=
                    wordToZ pq + wordToZ (wneg (natToWord (DivNumBits + 1) 1)) <
                    Z.of_nat (pow2 DivNumBits))%Z.
            { change (DivNumBits + 1) with (S DivNumBits).
              rewrite wneg_wordToZ by discriminate.
              change (S DivNumBits) with (DivNumBits + 1).
              change (wordToZ (natToWord _ _)) with 1%Z.
              split; lia.
            }
            apply wordToZ_wplus_bound in H5.
            assumption.
          }

          remember (wordToZ pq - 1)%Z as pqa; clear Heqpqa; subst.
          apply wmsb_false_pos in H3.
          apply zext_size_1 in H3; dest.
          rewrite H3 in *.
          rewrite zext_wordToNat_equal_Z by discriminate.
          unfold zext; rewrite split1_combine.
          reflexivity.
        }

        assert (wordToZ prem + Z.of_nat (wordToNat d) =
                Z.of_nat (wordToNat (split1 DivNumBits DivNumBits (prem ^+ zext d DivNumBits))))%Z.
        { assert (wordToZ (prem ^+ zext d DivNumBits) =
                  wordToZ prem + wordToZ (zext d DivNumBits))%Z.
          { apply wordToZ_distr_diff_wmsb.
            rewrite wmsb_zext by discriminate.
            assumption.
          }
          rewrite zext_wordToNat_equal_Z in H4 by discriminate.

          assert (exists sr, prem ^+ zext d DivNumBits = zext sr DivNumBits); dest.
          { apply Z.abs_le in H0; dest.
            assert (wordToZ prem + Z.of_nat (wordToNat d) >= 0)%Z by lia.
            assert (wordToZ prem + Z.of_nat (wordToNat d) < Z.of_nat (pow2 DivNumBits))%Z.
            { apply wmsb_true_neg in H1.
              assert (Z.of_nat (wordToNat d) < Z.of_nat (pow2 DivNumBits))%Z.
              { apply Nat2Z.inj_lt.
                apply wordToNat_bound.
              }
              lia.
            }
            rewrite <-H4 in *.
            apply zext_size.
            { apply wordToZ_bound_weakened.
              apply Z.abs_lt; split; lia.
            }
            { apply wmsb_false_pos; assumption. }
          }
          
          rewrite H5.
          unfold zext; rewrite split1_combine.
          rewrite <-H4, H5.
          rewrite zext_wordToNat_equal_Z by discriminate.
          reflexivity.
        }

        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
        rewrite <-H3, <-H4.
        rewrite Z.mul_sub_distr_l; lia.
        
  Qed.

  Lemma nrDivInv_final_restoring:
    forall (x d: word DivNumBits)
           (Hd: wordToNat d <> 0)
           (d_pos: word (2 * DivNumBits)) (Hdpos: d_pos = zext d DivNumBits)
           (prem: word (pred (2 * DivNumBits) + 1))
           (pq: word (DivNumBits + 1)) (* as a normal binary number *),
      Z.of_nat (wordToNat x) = (Z.of_nat (wordToNat d) * wordToZ pq + wordToZ prem)%Z ->
      (Z.abs (wordToZ prem) <= Z.of_nat (wordToNat d))%Z ->
      split1 DivNumBits 1 (evalExpr (finalRestoringQ prem pq d_pos)) = wdivN x d /\
      evalExpr (finalRestoringR prem d_pos) = wremN x d.
  Proof.
    unfold wdivN, wremN, wordBinN; intros.
    eapply nrDivInv_final_restoring' in H; eauto; dest.
    split.
    - apply wordToNat_inj.
      rewrite wordToNat_natToWord_2.
      + assumption.
      + clear -Hd.
        remember (wordToNat x) as xn; destruct xn;
          [rewrite Nat.div_0_l by assumption; apply zero_lt_pow2|].
        remember (wordToNat d) as dn; destruct dn; [elim Hd; reflexivity|].
        destruct dn; [rewrite Nat.div_1_r, Heqxn; apply wordToNat_bound|].
        etransitivity.
        * apply Nat.div_lt; lia.
        * rewrite Heqxn; apply wordToNat_bound.
    - apply wordToNat_inj.
      rewrite wordToNat_natToWord_2.
      + assumption.
      + etransitivity.
        * auto using Nat.mod_upper_bound.
        * apply wordToNat_bound.
  Qed.
  
  Lemma nrDivInv_nrDivStep:
    forall x (d: word DivNumBits) (Hd: wordToNat d <> 0) (xq: word DivBits)
           sr srr (prem: word (sr + 1)) sq (pq: word sq)
           (d_pos d_neg: word (2 * DivNumBits)),
      srr + 2 * DivNumBits = sr ->
      (sq < DivNumBits)%nat ->
      d_pos = zext d DivNumBits -> d_neg = wneg d_pos ->
      existT word _ xq = existT word _ (combine pq prem) ->
      NrDivInv x (wordToNat d) prem pq ->
      forall nxq,
        nxq = evalExpr (nrDivStep xq d_pos d_neg) ->
        exists (nprem: word sr) (npq: word (S sq)),
          existT word _ nxq = existT word _ (combine npq nprem) /\
          NrDivInv x (wordToNat d) nprem npq.
  Proof.
    intros; subst.
    apply nrDivInv_inv in H4; dest.

    eexists ((split1 _ 1 prem)
               ^+ (extz (nrDivNextAdder xq (zext d DivNumBits) (^~ (zext d DivNumBits))) _)).
    eexists (combine (nrDivNextQBit xq) pq).
    split.

    - rewrite nrDivStep_eval.
      unfold nrDivNextQBit, nrDivNextAdder.

      change (S sq) with (1 + sq).
      rewrite <-combine_assoc_existT.
      rewrite combine_wplus_1.
      rewrite combine_wplus_2 with (w1:= if weq _ _ then _ else _).
      apply existT_wplus.
      + apply existT_wlshift with (n:= 1) in H3; rewrite H3.
        change (S (srr + S DivNumBits)) with (1 + (srr + S DivNumBits)) in *.
        apply wlshift_combine_extz.
      + destruct (weq _ _).
        { repeat rewrite extz_combine.
          do 2 rewrite combine_assoc_existT.
          replace (combine (combine $1 $0) $0) with (natToWord (1 + sq + srr) 1).
          { replace (1 + sq + srr) with DivNumBits; [reflexivity|].
            apply EqdepFacts.eq_sigT_fst in H3.
            cbn; cbn in H3; lia.
          }
          { rewrite combine_one; reflexivity. }
        }
        { do 2 rewrite <-extz_combine.
          repeat rewrite extz_extz.
          replace (1 + sq + srr) with DivNumBits; [reflexivity|].
          apply EqdepFacts.eq_sigT_fst in H3.
          cbn; cbn in H3; lia.
        }

    - assert (Hxq: wmsb xq false = wmsb (wlshift xq 1) false).
      { assert (exists sprem, prem = sext sprem 1).
        { apply sext_size; [lia|].
          apply Z.abs_le in H1; destruct H1.
          assert (Z.of_nat (wordToNat d) * Z.of_nat (pow2 (DivNumBits - sq)) <
                  Z.of_nat (pow2 (srr + 2 * DivNumBits - 1)))%Z.
          { replace (DivNumBits - sq) with (S srr)
              by (apply EqdepFacts.eq_sigT_fst in H3;
                  assert (DivNumBits = S srr + sq) by (cbn; cbn in H3; lia);
                  lia).
            eapply Z.le_lt_trans.
            { apply Z.mul_le_mono_pos_r.
              { change 0%Z with (Z.of_nat 0).
                apply Nat2Z.inj_lt.
                apply pow2_zero.
              }
              { apply Nat2Z.inj_le.
                apply Nat.lt_le_incl.
                apply wordToNat_bound.
              }
            }
            { rewrite <-Nat2Z.inj_mul.
              rewrite <-pow2_add_mul.
              apply Nat2Z.inj_lt.
              apply pow2_inc; [lia|].
              replace (srr + 2 * DivNumBits - 1) with (srr + (2 * DivNumBits - 1)) by lia.
              replace (DivNumBits + S srr) with (srr + S DivNumBits) by lia.
              apply Nat.add_lt_mono_l.
              cbn; lia.
            }
          }
          split.
          { etransitivity; [|exact H1].
            rewrite <-Z.opp_le_mono.
            lia.
          }
          { eapply Z.le_lt_trans; [exact H2|].
            lia.
          }
        }
        dest; subst.
        clear -H3; change DivBits with (pred DivBits + 1) in *.
        apply sext_combine in H3; [|destruct srr; discriminate].
        dest; subst.
        apply wmsb_wlshift_sext.
      }
      
      assert (Hprem1: wmsb prem false = wmsb (split1 _ 1 prem) false).
      { clear -H3 Hxq.
        pose proof (eq_sigT_fst H3).
        generalize dependent xq.
        rewrite H; clear H; intros.
        destruct_existT.
        pose proof (wlshift_combine_extz 1 pq _ prem).
        apply wmsb_existT with (b:= false) in H.
        rewrite wmsb_extz in H.
        rewrite wmsb_combine with (b2:= false) in H by (rewrite Nat.add_comm; discriminate).
        rewrite <-H, <-Hxq.
        apply eq_sym, wmsb_combine; lia.
      }
      assert (Hprem2: wordToZ prem = wordToZ (split1 _ 1 prem)).
      { apply wmsb_split1_sext in Hprem1; dest; subst.
        rewrite sext_split1.
        apply sext_wordToZ.
      }

      assert (Hmsb: wmsb (split1 (srr + 2 * DivNumBits) 1 prem) false =
                    negb (wmsb (extz (nrDivNextAdder xq (zext d DivNumBits)
                                                     (^~ (zext d DivNumBits))) srr) false)).
      { rewrite <-Hprem1.
        rewrite wmsb_extz.
        apply wmsb_combine_existT with (b1:= false) (b2:= false) in H3; [|lia].
        rewrite <-H3.
        rewrite nrDivNextAdder_wmsb.
        change (2 * DivNumBits) with (DivNumBits + DivNumBits).
        rewrite wmsb_wneg_zext; [|discriminate|assumption].
        rewrite wmsb_zext by discriminate.
        rewrite <-Hxq.
        destruct (wmsb xq false); reflexivity.
      }

      econstructor.

      + rewrite wordToZ_distr_diff_wmsb at 1 by assumption.
        rewrite <-Hprem2.
        rewrite H; clear H.
        rewrite <-Z.sub_sub_distr.
        rewrite Z.sub_cancel_l.
        unfold nrDivNextAdder, nrDivNextQBit.
        
        assert (Hsq1: DivNumBits - sq = S srr).
        { apply EqdepFacts.eq_sigT_fst in H3.
          assert (DivNumBits = S srr + sq) by (cbn; cbn in H3; lia).
          lia.
        }
        assert (Hsq2: DivNumBits - S sq = srr) by lia.
        rewrite Hsq1, Hsq2.
        destruct (weq _ _).
        * rewrite extz_pow2_wordToZ.
          change (DivNumBits + DivNumBits) with (S (pred DivNumBits + DivNumBits)).
          change (2 * DivNumBits) with (S (pred DivNumBits + DivNumBits)).
          rewrite wneg_wordToZ.
          { change (S (pred DivNumBits + DivNumBits)) with (DivNumBits + DivNumBits).
            rewrite zext_wordToNat_equal_Z by discriminate.
            rewrite Z.mul_opp_l.
            rewrite Z.sub_opp_r.
            rewrite <-Z.mul_assoc.
            rewrite <-Z.mul_add_distr_l.
            rewrite <-Z.mul_assoc.
            rewrite Z.mul_cancel_l by (destruct (wordToNat d); auto; discriminate).
            rewrite pow2_S_z.
            rewrite pn2binE_lsb_1.
            ring.
          }
          { intro Hx.
            assert (wmsb (zext d DivNumBits) false =
                    wmsb (wpow2 (Init.Nat.pred DivNumBits + DivNumBits)) false)
              by (rewrite Hx; reflexivity).
            rewrite wmsb_zext in H by discriminate.
            rewrite wpow2_wmsb in H; discriminate.
          }
        * rewrite extz_pow2_wordToZ.
          change (2 * DivNumBits) with (DivNumBits + DivNumBits).
          rewrite zext_wordToNat_equal_Z by discriminate.
          rewrite <-Z.mul_assoc.
          rewrite <-Z.mul_sub_distr_l.
          rewrite <-Z.mul_assoc.
          rewrite Z.mul_cancel_l by (destruct (wordToNat d); auto; discriminate).
          rewrite pow2_S_z.
          rewrite pn2binE_lsb_0.
          ring.

      + rewrite wordToZ_distr_diff_wmsb by assumption.
        rewrite <-Hprem1 in Hmsb.
        rewrite <-Hprem2.
        replace (Z.of_nat (pow2 (DivNumBits - sq)))
          with (2 * Z.of_nat (pow2 (DivNumBits - S sq)))%Z in H1
          by (replace (DivNumBits - sq) with (S (DivNumBits - S sq)) by lia;
              apply eq_sym, pow2_S_z).

        apply nrDivNextAdder_bound.
        * apply Zmult_gt_0_compat.
          { lia. }
          { clear.
            induction (DivNumBits - S sq).
            { cbn; lia. }
            { cbn; do 2 rewrite Nat2Z.inj_add; lia. }
          }
        * rewrite Z.mul_assoc, Z.mul_comm with (n:= 2%Z).
          rewrite <-Z.mul_assoc.
          assumption.
        * assert (Hsq1: DivNumBits - sq = S srr).
          { apply EqdepFacts.eq_sigT_fst in H3.
            assert (DivNumBits = S srr + sq) by (cbn; cbn in H3; lia).
            lia.
          }
          assert (Hsq2: DivNumBits - S sq = srr) by lia.
          rewrite Hsq2.
          replace (wmsb prem false) with (wmsb (wlshift xq 1) false)
            by (rewrite <-Hxq; eapply wmsb_combine_existT; eauto; lia).
          apply nrDivNextAdder_Z_value.
  Qed.

  Record NrDividerInv (o: RegsT): Prop :=
    { ndiXq : fullType type (SyntaxKind (Bit DivBits));
      HndiXq : M.find "xq" o = Some (existT _ _ ndiXq);
      ndiX : fullType type (SyntaxKind (Bit DivNumBits));
      HndiX : M.find "x" o = Some (existT _ _ ndiX);
      ndiD : fullType type (SyntaxKind (Bit DivNumBits));
      HndiD : M.find "d" o = Some (existT _ _ ndiD);

      ndiDp : fullType type (SyntaxKind (Bit (2 * DivNumBits)));
      HndiDp : M.find "d_pos" o = Some (existT _ _ ndiDp);
      ndiDn : fullType type (SyntaxKind (Bit (2 * DivNumBits)));
      HndiDn : M.find "d_neg" o = Some (existT _ _ ndiDn);

      ndiCnt : fullType type (SyntaxKind (Bit (S DivLogNumPhases)));
      HndiCnt : M.find "cnt" o = Some (existT _ _ ndiCnt);

      HndiDdp : ndiDp = zext ndiD DivNumBits;
      HndiDdn : ndiDn = wneg ndiDp;

      HndiInv :
        ndiD <> $0 ->
        exists sr srr (prem: word sr) sq (pq: word sq),
          sr = 2 * DivNumBits + (wordToNat ndiCnt) * DivNumBitsPerPhase /\
          sr = srr + 2 * DivNumBits /\
          existT word _ ndiXq = existT word _ (combine pq prem) /\
          NrDivInv ndiX (wordToNat ndiD) prem pq
    }.

  Ltac nr_split := split; [|split; [|split]].
  
  Ltac nrDividerInv_old :=
    repeat match goal with
           | [H: NrDividerInv _ |- _] => destruct H
           end;
    kinv_red.

  Ltac nrDividerInv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kinv_red; (* unfolding invariant definitions *)
    repeat (* cheaper than "intuition" *)
      (match goal with
       | [ |- _ /\ _ ] => split
       end);
    try eassumption; intros; try reflexivity;
    intuition kinv_simpl; intuition idtac.

  Lemma nrDividerInv_ok':
    forall init n ll,
      init = initRegs (getRegInits nrDividerImpl) ->
      Multistep nrDividerImpl init n ll ->
      NrDividerInv n.
  Proof.
    induction 2; intros.
    
    - nrDividerInv_old.
      unfold getRegInits, fst, nrDividerImpl, projT1.
      nrDividerInv_new.

    - kinvert; [mred|mred| | |].
      + (* nrDivRegister *)
        Opaque evalExpr.
        kinv_action_dest.
        Transparent evalExpr.
        kinv_custom nrDividerInv_old.
        nrDividerInv_new;
          cbn; eq_rect_simpl; [reflexivity|].

        eexists; eexists; exists (zext (x Fin.F1) 128).
        eexists; exists WO.
        nr_split.
        * reflexivity.
        * reflexivity.
        * reflexivity.
        * apply nrDivInv_init.
          simpl in H4.
          remember (x (Fin.FS Fin.F1)) as w.
          simpl in w; clear -H4.
          destruct (weq _ _).
          { subst; simpl; discriminate. }
          { intro Hx.
            change DivNumBits with 64 in *.
            assert (natToWord DivNumBits (wordToNat w) = natToWord _ 0)
              by (rewrite Hx; reflexivity).
            rewrite natToWord_wordToNat in H; subst.
            elim n; reflexivity.
          }
        
      + (* nrDivGetResult *)
        Opaque evalExpr.
        kinv_action_dest.
        mred.
        Transparent evalExpr.

      + (* nrDivStep *)
        Opaque evalExpr.
        kinv_action_dest.
        Transparent evalExpr.
        kinv_custom nrDividerInv_old.
        nrDividerInv_new.
        kinv_regmap_red.

        assert (HndiDz: wordToNat ndiD <> 0)
          by (intro Hx; elim H; apply wordToNat_inj; assumption).
        assert (Hxz: wordToNat x <> 0).
        { simpl in H3; destruct (weq x _); [discriminate|].
          intro Hx; elim n1.
          apply wordToNat_inj; rewrite Hx; reflexivity.
        }
        assert (x4 + 8 <= DivNumBits)%nat.
        { apply eq_sigT_fst in H6.
          clear -Hxz H6.
          unfold DivNumBitsPerPhase in *.
          cbn in *; lia.
        }

        rewrite evalExprRewrite.
        rename x3 into nprem0.
        rename H10 into Hinv0.

        generalize dependent nprem0.
        replace (2 * DivNumBits + wordToNat x * DivNumBitsPerPhase)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 7 + 2 * DivNumBits + 1)
          by (unfold DivNumBitsPerPhase; cbn; lia); intros.
        eapply nrDivInv_nrDivStep in Hinv0; try reflexivity; try eassumption; try lia.
        destruct Hinv0 as [nprem1 [npq1 [Heq1 Hinv1]]].

        generalize dependent nprem1.
        replace ((pred (wordToNat x) * DivNumBitsPerPhase) + 7 + 2 * DivNumBits)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 6 + 2 * DivNumBits + 1)
          by lia; intros.
        eapply nrDivInv_nrDivStep in Hinv1; try reflexivity; try eassumption; try lia.
        clear Heq1 nprem1 npq1; destruct Hinv1 as [nprem2 [npq2 [Heq2 Hinv2]]].

        generalize dependent nprem2.
        replace ((pred (wordToNat x) * DivNumBitsPerPhase) + 6 + 2 * DivNumBits)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 5 + 2 * DivNumBits + 1)
          by lia; intros.
        eapply nrDivInv_nrDivStep in Hinv2; try reflexivity; try eassumption; try lia.
        clear Heq2 nprem2 npq2; destruct Hinv2 as [nprem3 [npq3 [Heq3 Hinv3]]].

        generalize dependent nprem3.
        replace ((pred (wordToNat x) * DivNumBitsPerPhase) + 5 + 2 * DivNumBits)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 4 + 2 * DivNumBits + 1)
          by lia; intros.
        eapply nrDivInv_nrDivStep in Hinv3; try reflexivity; try eassumption; try lia.
        clear Heq3 nprem3 npq3; destruct Hinv3 as [nprem4 [npq4 [Heq4 Hinv4]]].

        generalize dependent nprem4.
        replace ((pred (wordToNat x) * DivNumBitsPerPhase) + 4 + 2 * DivNumBits)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 3 + 2 * DivNumBits + 1)
          by lia; intros.
        eapply nrDivInv_nrDivStep in Hinv4; try reflexivity; try eassumption; try lia.
        clear Heq4 nprem4 npq4; destruct Hinv4 as [nprem5 [npq5 [Heq5 Hinv5]]].

        generalize dependent nprem5.
        replace ((pred (wordToNat x) * DivNumBitsPerPhase) + 3 + 2 * DivNumBits)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 2 + 2 * DivNumBits + 1)
          by lia; intros.
        eapply nrDivInv_nrDivStep in Hinv5; try reflexivity; try eassumption; try lia.
        clear Heq5 nprem5 npq5; destruct Hinv5 as [nprem6 [npq6 [Heq6 Hinv6]]].

        generalize dependent nprem6.
        replace ((pred (wordToNat x) * DivNumBitsPerPhase) + 2 + 2 * DivNumBits)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 1 + 2 * DivNumBits + 1)
          by lia; intros.
        eapply nrDivInv_nrDivStep in Hinv6; try reflexivity; try eassumption; try lia.
        clear Heq6 nprem6 npq6; destruct Hinv6 as [nprem7 [npq7 [Heq7 Hinv7]]].

        generalize dependent nprem7.
        replace ((pred (wordToNat x) * DivNumBitsPerPhase) + 1 + 2 * DivNumBits)
          with ((pred (wordToNat x) * DivNumBitsPerPhase) + 2 * DivNumBits + 1)
          by lia; intros.
        eapply nrDivInv_nrDivStep in Hinv7; try reflexivity; try eassumption; try lia.
        clear Heq7 nprem7 npq7; destruct Hinv7 as [nprem8 [npq8 [Heq8 Hinv8]]].

        generalize dependent nprem8.
        replace (pred (wordToNat x) * DivNumBitsPerPhase + 2 * DivNumBits)
          with (2 * DivNumBits + pred (wordToNat x) * DivNumBitsPerPhase)
          by lia; intros.

        replace (wordToNat (evalExpr (_ - _)%kami_expr)) with (pred (wordToNat x))
          by (clear -Hxz; simpl;
              rewrite wordToNat_natToWord_pred; [reflexivity|];
              intro Hx; elim Hxz; subst; reflexivity).
        
        do 5 eexists; split; [reflexivity|].
        split; [|split]; try eassumption.
        apply Nat.add_comm.
  Qed.
  
  Lemma nrDividerInv_ok:
    forall o,
      reachable o nrDividerImpl ->
      NrDividerInv o.
  Proof.
    intros; inv H; inv H0.
    eapply nrDividerInv_ok'; eauto.
  Qed.
  
  Local Definition thetaR (ir sr: RegsT): Prop.
  Proof.
    kexistv "xq" xq ir (Bit DivBits).
    kexistv "x" x ir (Bit DivNumBits).
    kexistv "d" d ir (Bit DivNumBits).
    kexistv "cnt" m ir (Bit (S DivLogNumPhases)).
    exact (sr = ["d" <- existT _ _ d]
                +["x" <- existT _ _ x])%fmap.
  Defined.
  #[local] Hint Unfold thetaR: MapDefs.

  Local Definition ruleMap (o: RegsT): string -> option string :=
    "nrDivRegister" |-> "divRegister";
      "nrDivGetResult" |-> "divGetResult"; ||.
  #[local] Hint Unfold ruleMap: MethDefs.

  Theorem divider_ok: nrDividerImpl <<== dividerSpec.
  Proof.
    kdecomposeR_nodefs thetaR ruleMap.
    kinv_add nrDividerInv_ok.
    kinvert.

    - (* "nrDivRegister" |-> "divRegister" *)
      Opaque evalExpr.
      kinv_action_dest.
      Transparent evalExpr.
      kinv_custom nrDividerInv_old.
      kinv_regmap_red.
      simpl; eq_rect_simpl.
      eexists; split; kinv_constr.
      + assumption.
      + kinv_eq.

    - (* "nrDivGetResult" |-> "divGetResult" *)
      Opaque evalExpr.
      kinv_action_dest.
      Transparent evalExpr.
      kinv_custom nrDividerInv_old.
      kinv_regmap_red.
      kinv_red.

      eexists; split; kinv_constr.
      + cbn; cbn in H5.
        destruct (weq _ _); [discriminate|].
        destruct (weq _ _); [|reflexivity].
        subst; elim n0; reflexivity.
      + rewrite idElementwiseId; unfold id.
        do 3 f_equal.

        assert (x = $0) by (cbn; cbn in H2; destruct (weq _ _); [auto|discriminate]).
        subst; clear x2 H2 H6.
        assert (HndiDz: ndiD <> $0).
        { cbn; cbn in H5.
          destruct (weq _ _); [discriminate|].
          intro Hx; subst; elim n0; reflexivity.
        }
        specialize (HndiInv HndiDz); clear H5; dest; subst.
        progress change #($0) with 0 in *.
        assert (x1 = 0) by (lia); subst; clear H0.
        assert (x3 = 64) by (apply eq_sigT_fst in H1; cbn in H1; lia); subst.
        cbn in x2, H1; destruct_existT.

        apply nrDivInv_finish in H2;
          [|intro Hx; elim HndiDz; apply wordToNat_inj; rewrite Hx; reflexivity];
          dest.
        eapply nrDivInv_final_restoring in H; try reflexivity; try eassumption;
          [|intro Hx; elim HndiDz; apply wordToNat_inj; assumption].
        dest.

        unfold evalExpr; fold evalExpr.
        fin_func_eq.
        * Opaque zext split1 split2 pn2bin finalRestoringQ finalRestoringR.
          simpl; eq_rect_simpl.
          rewrite split1_combine, split2_combine.
          Transparent zext split1 split2 pn2bin finalRestoringQ finalRestoringR.
          pose proof (pn2bin_eval x4); destruct_existT.
          change DivNumBits with 64; rewrite H2; clear H2.
          assumption.
        * Opaque zext split1 split2 pn2bin finalRestoringQ finalRestoringR.
          simpl; eq_rect_simpl.
          rewrite split2_combine.
          Transparent zext split1 split2 pn2bin finalRestoringQ finalRestoringR.
          assumption.

    - (* "nrDivStep" |-> . *)
      Opaque evalExpr.
      kinv_action_dest.
      Transparent evalExpr.
      kinv_regmap_red.
      eexists; split; kinv_constr.
    
  Qed.

End Divider64.

