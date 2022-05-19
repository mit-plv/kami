Require Import Bool String List Lia.
Require Import Lib.CommonTactics Lib.NatLib Lib.Indexer
        Lib.Struct Lib.DepEq Lib.Word Lib.FMap Lib.Reflection.
Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.SemFacts Kami.Tactics.

Require Import ZArith Eqdep Program.Equality.

Set Implicit Arguments.
Open Scope string.

(* Some useful facts about [word], only for the multiplier implementation. *)
Section WordEx.

  Definition rtrunc1 sz (w: word (S sz)): word sz:=
    match w with
    | WO => idProp
    | WS _ w' => w'
    end.

  Definition rtrunc2 sz (w: word (S (S sz))): word sz :=
    match w with
    | WO => idProp
    | WS _ w' =>
      match w' with
      | WO => idProp
      | WS _ w'' => w''
      end
    end.

  Lemma wordToNat_rtrunc1:
    forall sz (w: word (S sz)),
      wordToNat (rtrunc1 w) = wordToNat w / 2.
  Proof.
    dependent destruction w.
    unfold rtrunc1, wordToNat; fold wordToNat.
    destruct b.
    - change (S (wordToNat w * 2)) with (1 + wordToNat w * 2).
      rewrite Nat.div_add by discriminate.
      reflexivity.
    - apply eq_sym, Nat.div_mul; discriminate.
  Qed.

  Lemma combine_wrshifta_rtrunc1_sext:
    forall s (w: word s) sl (wl: word (S (S sl))) su (wu: word (S su)),
      existT word s w =
      existT word ((S (S sl)) + S su) (combine wl wu) ->
      existT word s (wrshifta w 1) =
      existT word ((S sl) + (S su + 1)) (combine (rtrunc1 wl) (sext wu 1)).
  Proof.
    intros.
    pose proof (eq_sigT_fst H); subst.
    destruct_existT.
    apply wordToNat_existT; [lia|].

    rewrite wordToNat_wrshifta.
    change (pow2 1) with 2.
    rewrite wordToNat_combine.
    pose proof (combine_sext wl wu 1).
    apply existT_wordToNat in H; rewrite <-H.
    rewrite wordToNat_combine.
    change (pow2 (S (S sl))) with (2 * pow2 (S sl)).
    rewrite <-Nat.mul_assoc.
    rewrite Nat.mul_comm with (n:= 2).
    rewrite Nat.div_add by discriminate.
    rewrite wordToNat_rtrunc1.
    reflexivity.
  Qed.

  Lemma wordToNat_rtrunc2:
    forall sz (w: word (S (S sz))),
      wordToNat (rtrunc2 w) = wordToNat w / 4.
  Proof.
    do 2 dependent destruction w.
    unfold rtrunc2, wordToNat; fold wordToNat.
    destruct b, b0.
    - replace (S (S (wordToNat w * 2) * 2))
        with (3 + wordToNat w * 4) by lia.
      rewrite Nat.div_add by discriminate.
      reflexivity.
    - replace (S (wordToNat w * 2 * 2))
        with (1 + wordToNat w * 4) by lia.
      rewrite Nat.div_add by discriminate.
      reflexivity.
    - replace (S (wordToNat w * 2) * 2)
        with (2 + wordToNat w * 4) by lia.
      rewrite Nat.div_add by discriminate.
      reflexivity.
    - replace (wordToNat w * 2 * 2)
        with (wordToNat w * 4) by lia.
      apply eq_sym, Nat.div_mul; discriminate.
  Qed.

  Lemma combine_wrshifta_rtrunc2_sext:
    forall s (w: word s) sl (wl: word (S (S (S sl)))) su (wu: word (S su)),
      existT word s w =
      existT word ((S (S (S sl))) + S su) (combine wl wu) ->
      existT word s (wrshifta w 2) =
      existT word ((S sl) + (S su + 2)) (combine (rtrunc2 wl) (sext wu 2)).
  Proof.
    intros.
    pose proof (eq_sigT_fst H); subst.
    destruct_existT.
    apply wordToNat_existT; [lia|].

    rewrite wordToNat_wrshifta.
    change (pow2 2) with 4.
    rewrite wordToNat_combine.
    pose proof (combine_sext wl wu 2).
    apply existT_wordToNat in H; rewrite <-H.
    rewrite wordToNat_combine.
    replace (pow2 (S (S (S sl)))) with (4 * pow2 (S sl)) by (simpl; lia).
    rewrite <-Nat.mul_assoc.
    rewrite Nat.mul_comm with (n:= 4).
    rewrite Nat.div_add by discriminate.
    rewrite wordToNat_rtrunc2.
    reflexivity.
  Qed.

End WordEx.

(** A radix-4 Booth Multiplier.*)

(* Note that the Booth multiplication algorithm is naturally designed
 * for signed integers, so we need to add sign bits (0) for unsigned integers
 * and their multiplication. It means we have to deal with 65 bits for 64-bit
 * unsigned multiplication.
 *
 * Here we assume the multiplier always takes _65-bit signed integers_ as
 * arguments.
 *)
Section Multiplier64.
  (* NOTE: it's hard to declare [LogNumPhases] and [NumBitsPerPhase] as 
   * variables, since truncation and extension require certain equation 
   * w.r.t. bit-lengths.
   *)
  (* Variable MultLogNumPhases MultNumStepsPerPhase: nat. *)
  Definition MultLogNumPhases := 3.
  Definition MultNumStepsPerPhase := 4.
  (* 2*4 = 8 bits are calculated per a phase. *)
  Definition MultNumBitsPerPhase := 2 * MultNumStepsPerPhase. 

  Definition MultNumPhases := wordToNat (wones MultLogNumPhases) + 1. (* 2^3 = 8 *)
  Definition MultNumBits := MultNumPhases * MultNumBitsPerPhase. (* 8*8 = 64 *)
  Definition MultNumBitsExt := MultNumBits + 1. (* 8*8 + 1 = 65 *)
  Definition MultBits := 2 * MultNumBitsExt + 2.

  Definition MultInStr := STRUCT { "multiplicand" :: Bit MultNumBitsExt;
                                   "multiplier" :: Bit MultNumBitsExt }.
  Definition MultOutStr := STRUCT { "high" :: Bit MultNumBits;
                                    "low" :: Bit MultNumBits }.

  (* NOTE: must use shirt-right-arithmetic to preserve the sign bit. *)
  Definition boothStep' {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit MultBits)))
             (pr: Expr ty (SyntaxKind (Bit 2))) :=
    let pSra := (p ~>> $$(WO~1))%kami_expr in
    (IF (pr == $$(WO~0~1)) then pSra + (#m_pos ~>> $$(WO~1))
     else IF (pr == $$(WO~1~0)) then pSra + (#m_neg ~>> $$(WO~1))
     else pSra)%kami_expr.

  Definition boothStep {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit ((MultBits - 2) + 2))))
    : Expr ty (SyntaxKind (Bit MultBits)) :=
    (boothStep' m_pos m_neg p (UniBit (Trunc 2 _) p))%kami_expr.

  Lemma boothStep'_eval:
    forall m_pos m_neg p pr,
      evalExpr (boothStep' m_pos m_neg p pr) =
      if weq (evalExpr pr) WO~0~1 then (wrshifta (evalExpr p) 1) ^+ (wrshifta m_pos 1)
      else if weq (evalExpr pr) WO~1~0 then (wrshifta (evalExpr p) 1) ^+ (wrshifta m_neg 1)
           else wrshifta (evalExpr p) 1.
  Proof.
    intros; simpl.
    destruct (weq _ _); try reflexivity.
    destruct (weq _ _); reflexivity.
  Qed.

  Definition boothStepEvalM (m_pos m_neg: word MultBits)
             (p: Expr type (SyntaxKind (Bit (MultBits - 2 + 2)))) :=
    wrshifta
      (if weq (split1 2 (MultBits - 2) (evalExpr p)) WO~0~1
       then m_pos
       else
         if weq (split1 2 (MultBits - 2) (evalExpr p)) WO~1~0
         then m_neg
         else $0) 1.

  Lemma boothStep_eval:
    forall m_pos m_neg p,
      evalExpr (boothStep m_pos m_neg p) =
      wrshifta (evalExpr p) 1 ^+ boothStepEvalM m_pos m_neg p.
  Proof.
    intros; unfold boothStep, boothStepEvalM.
    rewrite boothStep'_eval.
    repeat destruct (weq _ _); try reflexivity.
    rewrite wrshifta_wzero, wplus_comm, wplus_unit; reflexivity.
  Qed.

  Opaque boothStep.

  Definition booth4Step' {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit MultBits)))
             (pr: Expr ty (SyntaxKind (Bit 3))) :=
    let pSra := (p ~>> $$(WO~1~0))%kami_expr in
    (IF (pr == $$(WO~0~0~1)) then pSra + (#m_pos ~>> $$(WO~1~0))
     else IF (pr == $$(WO~0~1~0)) then pSra + (#m_pos ~>> $$(WO~1~0))
     else IF (pr == $$(WO~0~1~1)) then pSra + ((#m_pos << $$(WO~1)) ~>> $$(WO~1~0))
     else IF (pr == $$(WO~1~0~0)) then pSra + ((#m_neg << $$(WO~1)) ~>> $$(WO~1~0))
     else IF (pr == $$(WO~1~0~1)) then pSra + (#m_neg ~>> $$(WO~1~0))
     else IF (pr == $$(WO~1~1~0)) then pSra + (#m_neg ~>> $$(WO~1~0))
     else pSra)%kami_expr.

  (* NOTE: must use shirt-right-arithmetic to preserve the sign bit. *)
  Definition booth4Step {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
    : Expr ty (SyntaxKind (Bit MultBits)) :=
    (booth4Step' m_pos m_neg p (UniBit (Trunc 3 _) p))%kami_expr.

  Lemma booth4Step'_eval:
    forall m_pos m_neg p pr,
      evalExpr (booth4Step' m_pos m_neg p pr) =
      if weq (evalExpr pr) WO~0~0~1 then wrshifta (evalExpr p) 2 ^+ wrshifta m_pos 2
      else if weq (evalExpr pr) WO~0~1~0 then wrshifta (evalExpr p) 2 ^+ wrshifta m_pos 2
      else if weq (evalExpr pr) WO~0~1~1 then wrshifta (evalExpr p) 2 ^+ wrshifta (wlshift m_pos 1) 2
      else if weq (evalExpr pr) WO~1~0~0 then wrshifta (evalExpr p) 2 ^+ wrshifta (wlshift m_neg 1) 2
      else if weq (evalExpr pr) WO~1~0~1 then wrshifta (evalExpr p) 2 ^+ wrshifta m_neg 2
      else if weq (evalExpr pr) WO~1~1~0 then wrshifta (evalExpr p) 2 ^+ wrshifta m_neg 2
      else wrshifta (evalExpr p) 2.
  Proof.
    intros; simpl.
    repeat destruct (weq _ _); reflexivity.
  Qed.

  Definition booth4StepEvalM (m_pos m_neg: word MultBits)
             (p: Expr type (SyntaxKind (Bit (MultBits - 3 + 3)))) :=
    wrshifta
      (if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~0~1
       then m_pos
       else
         if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~1~0
         then m_pos
         else
           if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~1~1
           then (wlshift m_pos 1)
           else
             if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~0~0
             then (wlshift m_neg 1)
             else
               if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~0~1
               then m_neg
               else
                 if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~1~0
                 then m_neg
                 else $0) 2.

  Lemma booth4Step_eval:
    forall m_pos m_neg p,
      evalExpr (booth4Step m_pos m_neg p) =
      wrshifta (evalExpr p) 2 ^+ (booth4StepEvalM m_pos m_neg p).
  Proof.
    intros; unfold booth4Step, booth4StepEvalM.
    rewrite booth4Step'_eval.

    repeat destruct (weq _ _); try reflexivity.
    rewrite wrshifta_wzero, wplus_comm, wplus_unit; reflexivity.
  Qed.

  Opaque booth4Step.
  
  Fixpoint booth4Steps (cnt: nat)
           {ty} (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
           (p: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
           (cont: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont p)%kami_action
    | S n => (LET np <- booth4Step m_pos m_neg #p;
              booth4Steps n m_pos m_neg np cont)%kami_action
    end.

  Definition multPull := MethodSig "multPull"(): Struct MultInStr.
  Definition multPush := MethodSig "multPush"(Struct MultOutStr): Void.

  Definition boothMultiplierImpl :=
    MODULE {
      Register "m_pos" : Bit MultBits <- Default
      with Register "m_neg" : Bit MultBits <- Default
      with Register "p" : Bit MultBits <- Default
      with Register "m" : Bit MultNumBitsExt <- Default
      with Register "r" : Bit MultNumBitsExt <- Default
      with Register "cnt" : Bit (S MultLogNumPhases) <- Default

      with Rule "boothMultRegister" :=
        Call src <- multPull();

        LET m : Bit (pred MultNumBitsExt + 1) <- #src!MultInStr@."multiplicand";

        (* Make sure msb(m) = 0 *)
        Assert (UniBit (TruncLsb _ 1) #m == $0);
      
        LET m_neg <- UniBit (Neg _) #m;

        LET m_pos : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt))
                 (UniBit (SignExtendTrunc _ (S MultNumBitsExt)) #m) $0;
        LET m_neg : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt))
                 (UniBit (SignExtendTrunc _ (S MultNumBitsExt)) #m_neg) $0;

        Write "m_pos" <- #m_pos;
        Write "m_neg" <- #m_neg;
        Write "m" <- #m;

        LET r <- #src!MultInStr@."multiplier";
        Write "r" <- #r;

        LET p : Bit MultBits <-
          BinBit (Concat (S MultNumBitsExt) _) $0 (BinBit (Concat _ 1) #r $0);
        
        (* Handle one bit in advance, in order to deal with other 64 bits 
         * consistently in a rule [boothStep].
         *)
        LET np : Bit MultBits <- boothStep m_pos m_neg #p;
        Write "p" <- #np;

        Write "cnt" : Bit (S MultLogNumPhases) <- $(MultNumPhases);
        Retv

      with Rule "boothMultGetResult" :=
        Read cnt : Bit (S MultLogNumPhases) <- "cnt";
        Assert (#cnt == $0);

        Read p : Bit MultBits <- "p";
        LET highlowe : Bit (2 * MultNumBitsExt) <-
          UniBit (ConstExtract 1 (2 * MultNumBitsExt) 1) #p;
        LET highlow : Bit (2 * MultNumBits) <-
          UniBit (SignExtendTrunc _ _) #highlowe;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        Call multPush(STRUCT { "high" ::= #high; "low" ::= #low });

        Retv
            
      with Rule "boothStep" :=
        Read cnt : Bit (S MultLogNumPhases) <- "cnt";
        Assert (#cnt != $0);

        Read m_pos : Bit MultBits <- "m_pos";
        Read m_neg : Bit MultBits <- "m_neg";
        Read p : Bit MultBits <- "p";

        Write "cnt" <- #cnt - $1;
        
        booth4Steps
          MultNumStepsPerPhase m_pos m_neg p
          (fun np => Write "p" <- #np; Retv)
    }.

  Definition multiplierSpec :=
    MODULE {
      Register "m" : Bit MultNumBitsExt <- Default
      with Register "r" : Bit MultNumBitsExt <- Default

      with Rule "multRegister" :=
        Call src <- multPull();
        LET m : Bit MultNumBitsExt <- #src!MultInStr@."multiplicand";
        LET r : Bit MultNumBitsExt <- #src!MultInStr@."multiplier";

        Write "m" <- #m;
        Write "r" <- #r;
        Retv

      with Rule "multGetResult" :=
        Read m : Bit MultNumBitsExt <- "m";
        LET m_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #m;
        Read r : Bit MultNumBitsExt <- "r";
        LET r_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #r;

        LET p : Bit (2 * MultNumBitsExt) <- #m_ext *s #r_ext;
        LET highlow : Bit (2 * MultNumBits) <- UniBit (SignExtendTrunc _ _) #p;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        Call multPush(STRUCT { "high" ::= #high; "low" ::= #low });

        Retv
    }.

  (*! Correctness of the multiplier *)

  Section BoothEncoding.

    Inductive Booth := BZero | BPlus | BMinus.

    Definition boothToZ (b: Booth): Z :=
      match b with
      | BZero => 0
      | BPlus => 1
      | BMinus => -1
      end.

    Definition bbToZ (bb: Booth * Booth): Z :=
      match bb with
      | (BZero, b) => boothToZ b
      | (BPlus, b) => boothToZ b + 2
      | (BMinus, b) => boothToZ b - 2
      end.

    Inductive bword: nat -> Set :=
    | BWO: bword 0
    | BWS: Booth -> forall n, bword n -> bword (S n).

    Fixpoint bwordToZ sz (bw: bword sz): Z :=
      match bw with
      | BWO => 0
      | BWS BZero bw' => bwordToZ bw' * 2
      | BWS BPlus bw' => (bwordToZ bw' * 2) + 1
      | BWS BMinus bw' => (bwordToZ bw' * 2) - 1
      end.

    Declare Scope bword_scope.
    Notation "w ~ 0" := (BWS BZero w) (at level 7, left associativity,
                                       format "w '~' '0'"): bword_scope.
    Notation "w ~ 'P'" := (BWS BPlus w) (at level 7, left associativity,
                                         format "w '~' 'P'"): bword_scope.
    Notation "w ~ 'N'" := (BWS BMinus w) (at level 7, left associativity,
                                          format "w '~' 'N'"): bword_scope.
    Delimit Scope bword_scope with bword.

    Definition encodeB2 (mst lst: bool) :=
      match mst, lst with
      | false, true => BPlus
      | true, false => BMinus
      | _, _ => BZero
      end.

    Definition wencodeB2 (w: word 2): Booth.
    Proof.
      dependent destruction w.
      dependent destruction w.
      exact (encodeB2 b0 b).
    Defined.

    Fixpoint wordToB2' sz (w: word sz) (p: bool): bword sz :=
      match w with
      | WO => BWO
      | WS b w' => BWS (encodeB2 b p) (wordToB2' w' b)
      end.

    Lemma wordToB2'_rtrunc1_wlsb:
      forall sz (w: word (S sz)) p,
        wordToB2' w p = BWS (encodeB2 (wlsb w) p) (wordToB2' (rtrunc1 w) (wlsb w)).
    Proof.
      intros; dependent destruction w; simpl; reflexivity.
    Qed.

    Definition wordToB2 sz (w: word (S sz)): bword sz :=
      match w with
      | WO => idProp
      | WS b w' => wordToB2' w' b
      end.

    Lemma wordToB2_one:
      forall (w: word 1), bwordToZ (wordToB2 w) = 0%Z.
    Proof.
      dependent destruction w.
      dependent destruction w.
      simpl; reflexivity.
    Qed.

    Lemma wordToB2_bwordToZ':
      forall sz (w: word (S sz)) b,
        bwordToZ (wordToB2 (WS b w)) = (wordToZ w + (if b then 1 else 0))%Z.
    Proof.
      dependent induction w; simpl; intros.
      dependent destruction w.
      - destruct b, b0; cbn; reflexivity.
      - specialize (IHw _ _ eq_refl JMeq_refl).
        unfold wordToB2 in IHw; rewrite IHw; clear IHw.
        destruct b, b1, b0; cbn;
          repeat (rewrite wordToZ_WS_0 || rewrite wordToZ_WS_1); lia.
    Qed.

    Lemma wordToB2_bwordToZ:
      forall sz (w: word sz),
        bwordToZ (wordToB2 w~0) = wordToZ w.
    Proof.
      dependent destruction w; [reflexivity|].
      rewrite wordToB2_bwordToZ'; lia.
    Qed.

    Lemma wordToB2_bwordToZ_step:
      forall sz (w: word (S (S sz))),
        bwordToZ (wordToB2 w) =
        (2 * bwordToZ (wordToB2 (rtrunc1 w)) +
         boothToZ (wencodeB2 (split1 2 _ w)))%Z.
    Proof.
      do 2 dependent destruction w; cbn.
      remember (bwordToZ (wordToB2' w b0)) as ww; clear Heqww.
      destruct ww.
      - destruct b, b0; cbn; reflexivity.
      - rewrite Pos2Z.inj_xO with (p:= p).
        rewrite Z.mul_comm; remember (2 * Z.pos p)%Z as tp; clear Heqtp.
        destruct b, b0; cbn; lia.
      - rewrite Pos2Z.neg_xO with (p:= p).
        rewrite Z.mul_comm; remember (2 * Z.neg p)%Z as tp; clear Heqtp.
        destruct b, b0; cbn; lia.
    Qed.

    Definition encodeB4 (b1 b2 b3: bool) :=
      match b1, b2, b3 with
      | false, false, true
      | false, true, false => (BZero, BPlus)
      | false, true, true => (BPlus, BZero)
      | true, false, false => (BMinus, BZero)
      | true, false, true
      | true, true, false => (BZero, BMinus)
      | _, _, _ => (BZero, BZero)
      end.

    Definition wencodeB4 (w: word 3): Booth * Booth.
    Proof.
      dependent destruction w.
      dependent destruction w.
      dependent destruction w.
      exact (encodeB4 b1 b0 b).
    Defined.

    Fixpoint wordToB4' sz (w: word sz) (p1 p2: bool): bword (S sz).
    Proof.
      dependent destruction w.
      - exact (BWS (encodeB2 p1 p2) BWO).
      - dependent destruction w.
        + exact (BWS (snd (encodeB4 b p1 p2)) (BWS (fst (encodeB4 b p1 p2)) BWO)).
        + refine (BWS (snd (encodeB4 b p1 p2)) (BWS (fst (encodeB4 b p1 p2)) _)).
          exact (wordToB4' _ w b0 b).
    Defined.

    Definition wordToB4 sz (w: word (S sz)): bword sz.
    Proof.
      dependent destruction w.
      dependent destruction w.
      - exact BWO.
      - exact (wordToB4' w b0 b).
    Defined.

    Lemma wordToB2_wordToB4:
      forall sz (w: word (S sz)),
        bwordToZ (wordToB2 w) = bwordToZ (wordToB4 w).
    Proof.
      dependent destruction w.
      move b at bottom.
      dependent induction w; [reflexivity|].
      cbn; cbn in IHw; rewrite IHw; clear IHw.
      move b at bottom.
      dependent induction w.
      - destruct b, b0; cbn; reflexivity.
      - rewrite <-IHw; clear IHw.
        dependent destruction w.
        + destruct b, b0, b1; cbn; reflexivity.
        + cbn; remember (bwordToZ (wordToB4' w b0 b)) as ww; clear Heqww.
          destruct b, b0, b1, b2; cbn; lia.
    Qed.

    Lemma wordToB4_bwordToZ_step:
      forall sz (w: word (S (S (S sz)))),
        bwordToZ (wordToB4 w) =
        (4 * bwordToZ (wordToB4 (rtrunc2 w)) +
         bbToZ (wencodeB4 (split1 3 _ w)))%Z.
    Proof.
      do 3 dependent destruction w; cbn.
      dependent destruction w.
      - destruct b, b0, b1; cbn; reflexivity.
      - cbn; remember (bwordToZ (wordToB4' w b2 b1)) as ww; clear Heqww.
        destruct ww.
        + destruct b, b0, b1; cbn; reflexivity.
        + rewrite Pos2Z.inj_xO with (p:= (p~0)%positive).
          rewrite Pos2Z.inj_xO with (p:= p).
          rewrite Z.mul_comm with (n:= Z.pos p); remember (2 * Z.pos p)%Z as tp; clear Heqtp.
          Opaque Z.mul.
          destruct b, b0, b1; cbn; lia.
          Transparent Z.mul.
        + rewrite Pos2Z.neg_xO with (p:= (p~0)%positive).
          rewrite Pos2Z.neg_xO with (p:= p).
          rewrite Z.mul_comm with (n:= Z.neg p); remember (2 * Z.neg p)%Z as tp; clear Heqtp.
          Opaque Z.mul.
          destruct b, b0, b1; cbn; lia.
          Transparent Z.mul.
    Qed.

  End BoothEncoding.

  Inductive BoothStepInv {sz} (m p: word sz)
    : forall sl, word sl -> forall su, word su -> Prop :=
  | BSInv: forall sl su (wl: word (S sl)) (wu: word su) u,
      (sl = 0 -> exists tsu (twu: word tsu), existT word _ wu = existT word _ (sext twu 1)) ->
      wordToZ wu = (wordToZ m * u)%Z ->
      (u + bwordToZ (wordToB2 wl) * Z.of_nat (pow2 (su - sz - 1)))%Z = wordToZ p ->
      BoothStepInv m p wl wu.

  Lemma boothStepInv_inv:
    forall {sz} (m p: word sz) sl su (wl: word (S sl)) (wu: word su),
      BoothStepInv m p wl wu ->
      (sl = 0 -> exists tsu (twu: word tsu), existT word _ wu = existT word _ (sext twu 1)) /\
      exists u,
        wordToZ wu = (wordToZ m * u)%Z /\
        (u + bwordToZ (wordToB2 wl) * Z.of_nat (pow2 (su - sz - 1)))%Z = wordToZ p.
  Proof.
    intros.
    inv H; destruct_existT.
    split; auto.
    eexists; repeat (split; try eassumption).
  Qed.

  Lemma natToWord_ZToWord_zero:
    forall sz, natToWord sz 0 = ZToWord sz 0%Z.
  Proof.
    intros; simpl.
    induction sz; simpl; auto.
    rewrite IHsz; reflexivity.
  Qed.

  Lemma wmsb_wzero'_false:
    forall sz, wmsb (wzero' sz) false = false.
  Proof.
    induction sz; simpl; intros; auto.
  Qed.

  Lemma boothStepInv_init:
    forall sz m p,
      BoothStepInv m (p: word sz)
                   (combine (natToWord 1 0) p)
                   (natToWord (S sz) 0).
  Proof.
    intros; econstructor; try reflexivity.
    - intros; subst.
      eexists; exists WO.
      reflexivity.
    - instantiate (1:= 0%Z).
      rewrite <-Zmult_0_r_reverse.
      rewrite natToWord_ZToWord_zero.
      rewrite wordToZ_wzero'.
      reflexivity.
    - rewrite Z.add_0_l.
      replace (S sz - sz - 1) with 0 by lia.
      simpl; rewrite <-wordToB2_bwordToZ.
      rewrite Z.mul_1_r.
      reflexivity.
  Qed.

  Lemma boothStepInv_finish:
    forall {sz} (m p: word sz) (wl: word 1) su (wu: word su),
      BoothStepInv m p wl wu ->
      exists tsu (twu: word tsu),
        existT word _ wu = existT word _ (sext twu 1) /\
        wordToZ wu = (wordToZ m * wordToZ p)%Z.
  Proof.
    intros.
    apply boothStepInv_inv in H; dest.
    specialize (H eq_refl); destruct H as [tsu [twu ?]].
    rewrite wordToB2_one in H1.
    rewrite Z.add_0_r in H1; subst.
    repeat eexists; eassumption.
  Qed.

  Definition booth2AddM (m: word MultNumBitsExt) (wl: word 2) {sus}
    : word (S sus + MultNumBitsExt).
  Proof.
    assert (Hsu: sus + MultNumBitsExt + 1 = S sus + MultNumBitsExt)
      by (abstract lia).
    refine (if weq wl WO~0~1 then _
            else if weq wl WO~1~0 then _
                 else _).
    - exact (eq_rect _ word (sext (extz m sus) 1) _ Hsu).
    - exact (eq_rect _ word (sext (extz (wneg m) sus) 1) _ Hsu).
    - exact $0.
  Defined.

  Definition booth4AddM (m: word MultNumBitsExt) (wl: word 3) {sus}
    : word (S sus + MultNumBitsExt).
  Proof.
    assert (Hsu: sus + (MultNumBitsExt + 1) = S sus + MultNumBitsExt)
      by (abstract lia).
    refine (if weq wl WO~0~0~1 then _
            else if weq wl WO~0~1~0 then _
                 else if weq wl WO~0~1~1 then _
                      else if weq wl WO~1~0~0 then _
                           else if weq wl WO~1~0~1 then _
                                else if weq wl WO~1~1~0 then _
                                     else _).
    - exact (eq_rect _ word (extz (sext m 1) sus) _ Hsu).
    - exact (eq_rect _ word (extz (sext m 1) sus) _ Hsu).
    - exact (extz m (S sus)).
    - exact (extz (wneg m) (S sus)).
    - exact (eq_rect _ word (extz (sext (wneg m) 1) sus) _ Hsu).
    - exact (eq_rect _ word (extz (sext (wneg m) 1) sus) _ Hsu).
    - exact $0.
  Defined.

  Definition booth2AddU (wl: word 2) (sus: nat) :=
    (if weq wl WO~0~1 then (Z.of_nat (pow2 sus))
     else if weq wl WO~1~0 then -(Z.of_nat (pow2 sus))
          else 0)%Z.

  Definition booth4AddU (wl: word 3) (sus: nat) :=
    (if weq wl WO~0~0~1 then (Z.of_nat (pow2 sus))
     else if weq wl WO~0~1~0 then (Z.of_nat (pow2 sus))
          else if weq wl WO~0~1~1 then (Z.of_nat (pow2 (S sus)))
               else if weq wl WO~1~0~0 then -(Z.of_nat (pow2 (S sus)))
                    else if weq wl WO~1~0~1 then -(Z.of_nat (pow2 sus))
                         else if weq wl WO~1~1~0 then -(Z.of_nat (pow2 sus))
                              else 0)%Z.

  Lemma wencodeB2_zero:
    forall (wl: word 2),
      wl <> WO~0~1 -> wl <> WO~1~0 ->
      wencodeB2 wl = BZero.
  Proof.
    intros.
    dependent destruction wl.
    dependent destruction wl.
    dependent destruction wl.
    destruct b, b0; intuition idtac.
  Qed.

  Lemma wencodeB4_zero:
    forall (wl: word 3),
      wl <> WO~0~0~1 -> wl <> WO~0~1~0 -> wl <> WO~0~1~1 ->
      wl <> WO~1~0~0 -> wl <> WO~1~0~1 -> wl <> WO~1~1~0 ->
      wencodeB4 wl = (BZero, BZero).
  Proof.
    intros.
    dependent destruction wl.
    dependent destruction wl.
    dependent destruction wl.
    dependent destruction wl.
    destruct b, b0, b1; intuition idtac.
  Qed.

  Ltac wordToZ_red :=
    repeat (first [rewrite extz_pow2_wordToZ
                  |rewrite sext_wordToZ
                  |rewrite wordToZ_eq_rect]).

  Lemma boothStepEvalM_booth2AddM:
    forall (m: word MultNumBitsExt) we sl sus,
      MultBits - 2 + 2 = S (S sl) + (S sus + MultNumBitsExt) ->
      existT word (1 + S MultNumBitsExt + MultNumBitsExt)
             (boothStepEvalM
                (extz (sext m 1) (S MultNumBitsExt))
                (extz (sext (^~ m) 1) (S MultNumBitsExt)) we) =
      existT word (S sl + (S sus + MultNumBitsExt + 1))
             (extz (sext (booth2AddM m (split1 2 (MultBits - 2) (evalExpr we))) 1)
                   (S sl)).
  Proof.
    unfold boothStepEvalM, booth2AddM; intros.
    repeat destruct (weq _ _).

    - change (1 + S MultNumBitsExt + MultNumBitsExt)
        with (1 + MultNumBitsExt + S MultNumBitsExt).
      rewrite wrshifta_extz_sext.
      apply wordToZ_existT; [cbn; cbn in H; lia|].
      wordToZ_red.
      rewrite <-Z.mul_assoc, <-Nat2Z.inj_mul.
      rewrite <-pow2_add_mul.
      replace MultNumBitsExt with (sus + S sl) at 2 by (cbn; cbn in H; lia).
      reflexivity.
    - change (1 + S MultNumBitsExt + MultNumBitsExt)
        with (1 + MultNumBitsExt + S MultNumBitsExt).
      rewrite wrshifta_extz_sext.
      apply wordToZ_existT; [cbn; cbn in H; lia|].
      wordToZ_red.
      rewrite <-Z.mul_assoc, <-Nat2Z.inj_mul.
      rewrite <-pow2_add_mul.
      replace MultNumBitsExt with (sus + S sl) at 3 by (cbn; cbn in H; lia).
      reflexivity.

    - rewrite wrshifta_wzero, sext_wzero, extz_zero.
      replace (S sl + (S sus + MultNumBitsExt + 1)) with MultBits by lia.
      reflexivity.
  Qed.

  Lemma booth4StepEvalM_booth4AddM:
    forall (m: word MultNumBitsExt) we sl sus,
      MultBits - 3 + 3 = S (S (S sl)) + (S sus + MultNumBitsExt) ->
      existT word (2 + (MultNumBitsExt - 1) + S MultNumBitsExt)
             (booth4StepEvalM (extz (sext m 1) (S MultNumBitsExt))
                              (extz (sext (^~ m) 1) (S MultNumBitsExt)) we) =
      existT word (S sl + (S sus + MultNumBitsExt + 2))
             (extz (sext (booth4AddM m (split1 3 (MultBits - 3) (evalExpr we))) 2) (S sl)).
  Proof.
    unfold booth4StepEvalM, booth4AddM; intros.
    repeat destruct (weq _ _).

    - rewrite wrshifta_extz_sext.
      apply wordToZ_existT; [cbn; cbn in H; lia|].
      wordToZ_red.
      rewrite <-Z.mul_assoc, <-Nat2Z.inj_mul.
      rewrite <-pow2_add_mul.
      replace (MultNumBitsExt - 1) with (sus + S sl) by (cbn; cbn in H; lia).
      reflexivity.
    - rewrite wrshifta_extz_sext.
      apply wordToZ_existT; [cbn; cbn in H; lia|].
      wordToZ_red.
      rewrite <-Z.mul_assoc, <-Nat2Z.inj_mul.
      rewrite <-pow2_add_mul.
      replace (MultNumBitsExt - 1) with (sus + S sl) by (cbn; cbn in H; lia).
      reflexivity.

    - erewrite existT_wrshifta
        by (erewrite existT_wlshift
             by (change MultBits with ((S MultNumBitsExt) + (MultNumBitsExt + 1));
                 apply extz_sext);
            apply wlshift_sext_extz).
      erewrite existT_wrshifta by apply extz_extz.
      change (1 + S MultNumBitsExt) with (2 + MultNumBitsExt).
      rewrite wrshifta_extz_sext.
      rewrite extz_sext.
      apply existT_sext.
      rewrite extz_extz.
      replace (S sl + S sus) with MultNumBitsExt by (cbn; cbn in H; lia).
      reflexivity.
    - erewrite existT_wrshifta
        by (erewrite existT_wlshift
             by (change MultBits with ((S MultNumBitsExt) + (MultNumBitsExt + 1));
                 apply extz_sext);
            apply wlshift_sext_extz).
      erewrite existT_wrshifta by apply extz_extz.
      change (1 + S MultNumBitsExt) with (2 + MultNumBitsExt).
      rewrite wrshifta_extz_sext.
      rewrite extz_sext.
      apply existT_sext.
      rewrite extz_extz.
      replace (S sl + S sus) with MultNumBitsExt by (cbn; cbn in H; lia).
      reflexivity.
      
    - rewrite wrshifta_extz_sext.
      apply wordToZ_existT; [cbn; cbn in H; lia|].
      wordToZ_red.
      rewrite <-Z.mul_assoc, <-Nat2Z.inj_mul.
      rewrite <-pow2_add_mul.
      replace (MultNumBitsExt - 1) with (sus + S sl) by (cbn; cbn in H; lia).
      reflexivity.
    - rewrite wrshifta_extz_sext.
      apply wordToZ_existT; [cbn; cbn in H; lia|].
      wordToZ_red.
      rewrite <-Z.mul_assoc, <-Nat2Z.inj_mul.
      rewrite <-pow2_add_mul.
      replace (MultNumBitsExt - 1) with (sus + S sl) by (cbn; cbn in H; lia).
      reflexivity.

    - rewrite wrshifta_wzero, sext_wzero, extz_zero.
      replace (S sl + (S sus + MultNumBitsExt + 2)) with MultBits by lia.
      reflexivity.
  Qed.

  Lemma booth2AddM_booth2AddU:
    forall sus (m: word MultNumBitsExt) (Hm: m <> wpow2 MultNumBits)
           wu w,
      wordToZ (sext wu 1 ^+ sext (booth2AddM (sus:= sus) m (split1 2 (MultBits - 2) w)) 1) =
      (wordToZ wu + wordToZ m * booth2AddU (split1 2 (MultBits - 2) w) sus)%Z.
  Proof.
    unfold booth2AddM, booth2AddU; intros.
    repeat destruct (weq _ _).
    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite sext_wordToZ.
      rewrite extz_pow2_wordToZ.
      reflexivity.
    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite sext_wordToZ.
      rewrite extz_pow2_wordToZ.
      change MultNumBitsExt with (S MultNumBits).
      rewrite wneg_wordToZ by assumption.
      ring.
    - rewrite sext_wzero, wplus_wzero_1.
      rewrite Z.mul_0_r.
      rewrite sext_wordToZ.
      lia.
  Qed.
  
  Lemma booth4AddM_booth4AddU:
    forall sus (m: word MultNumBitsExt) (Hm: m <> wpow2 MultNumBits)
           wu w,
      wordToZ (sext wu 2 ^+ sext (booth4AddM (sus:= sus) m (split1 3 (MultBits - 3) w)) 2) =
      (wordToZ wu + wordToZ m * booth4AddU (split1 3 (MultBits - 3) w) sus)%Z.
  Proof.
    unfold booth4AddM, booth4AddU; intros.
    repeat destruct (weq _ _).

    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      reflexivity.
    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      reflexivity.

    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite extz_pow2_wordToZ.
      reflexivity.
    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite extz_pow2_wordToZ.
      change MultNumBitsExt with (S MultNumBits).
      rewrite wneg_wordToZ by assumption.
      ring.

    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      change MultNumBitsExt with (S MultNumBits).
      rewrite wneg_wordToZ by assumption.
      ring.
    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      change MultNumBitsExt with (S MultNumBits).
      rewrite wneg_wordToZ by assumption.
      ring.
    - rewrite sext_wzero.
      rewrite wplus_comm, wplus_unit.
      rewrite sext_wordToZ.
      rewrite Z.mul_0_r.
      ring.
  Qed.

  Lemma booth2AddU_boothToZ:
    forall wl n,
      booth2AddU wl n =
      (boothToZ (wencodeB2 wl) * Z.of_nat (pow2 n))%Z.
  Proof.
    unfold booth2AddU, boothToZ; intros.
    repeat destruct (weq _ _); subst.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - rewrite wencodeB2_zero by assumption.
      reflexivity.
  Qed.

  Lemma booth4AddU_bbToZ:
    forall wl n,
      booth4AddU wl n =
      (bbToZ (wencodeB4 wl) * Z.of_nat (pow2 n))%Z.
  Proof.
    unfold booth4AddU, bbToZ; intros.
    repeat destruct (weq _ _); subst.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - rewrite pow2_S_z; simpl; reflexivity.
    - rewrite pow2_S_z; simpl.
      destruct (Z.of_nat (pow2 n)); reflexivity.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - rewrite wencodeB4_zero by assumption.
      reflexivity.
  Qed.

  Lemma wordToZ_sext_wplus_distr:
    forall (sz: nat) (w1 w2: word (S sz)) n,
      (- Z.of_nat (pow2 sz) <= wordToZ w1 + wordToZ w2 < Z.of_nat (pow2 sz))%Z ->
      wordToZ (sext (w1 ^+ w2) n) = wordToZ (sext w1 n ^+ sext w2 n).
  Proof.
    intros.
    rewrite sext_wordToZ.
    rewrite <-wordToZ_wplus_bound by assumption.
    change (S sz + n) with (S (sz + n)).
    rewrite <-wordToZ_wplus_bound; change (S (sz + n)) with (S sz + n).
    - do 2 rewrite sext_wordToZ.
      reflexivity.
    - do 2 rewrite sext_wordToZ.
      destruct H; split.
      + etransitivity; [|eassumption].
        rewrite <-Z.opp_le_mono.
        apply Nat2Z.inj_le.
        rewrite pow2_add_mul.
        pose proof (zero_lt_pow2 n).
        replace (pow2 sz) with (pow2 sz * 1)%nat at 1 by lia.
        apply mult_le_compat_l; lia.
      + eapply Z.lt_le_trans; [eassumption|].
        apply Nat2Z.inj_le.
        rewrite pow2_add_mul.
        pose proof (zero_lt_pow2 n).
        replace (pow2 sz) with (pow2 sz * 1)%nat at 1 by lia.
        apply mult_le_compat_l; lia.
  Qed.

  Lemma boothStepInv_booth4Step:
    forall (m: word MultNumBitsExt) (Hm: m <> wpow2 MultNumBits)
           mp mn p we nwe,
      mp = extz (sext m 1) (S MultNumBitsExt) ->
      mn = extz (sext (wneg m) 1) (S MultNumBitsExt) ->
      booth4Step mp mn we = nwe ->
      forall sl su (wl: word (S (S (S sl)))) (wu: word su) sus,
        (S sus) + MultNumBitsExt = su ->
        existT word _ (evalExpr we) = existT word _ (combine wl wu) ->
        BoothStepInv m p wl wu ->
        exists (nwl: word (S sl)) (nwu: word (su + 2)),
          existT word _ (evalExpr nwe) = existT word _ (combine nwl nwu) /\
          BoothStepInv m p nwl nwu.
  Proof.
    intros; subst.
    apply boothStepInv_inv in H4; destruct H4 as [_ H4].
    rewrite wordToB2_wordToB4 in H4.
    destruct H4 as [u ?]; dest.

    exists (rtrunc2 wl).
    exists (sext wu 2 ^+ sext (booth4AddM m (split1 3 (MultBits - 3) (evalExpr we))) 2).
    split.

    - rewrite booth4Step_eval.
      rewrite combine_wplus_1.
      apply existT_wplus.
      + apply combine_wrshifta_rtrunc2_sext; assumption.
      + apply booth4StepEvalM_booth4AddM.
        apply eq_sigT_fst in H3; assumption.

    - pose proof (sext_wplus_exist wu (booth4AddM m (split1 3 (MultBits - 3) (evalExpr we))) 1).
      destruct H1 as [twu ?].
      eapply @BSInv
        with (u:= (u + booth4AddU (split1 3 (MultBits - 3) (evalExpr we)) sus)%Z).
      + intros; rewrite H1; do 2 eexists; reflexivity.
      + rewrite Z.mul_add_distr_l, <-H.
        apply booth4AddM_booth4AddU; assumption.
      + rewrite wordToB2_wordToB4.
        rewrite <-H0, <-Z.add_assoc.
        replace (S sus + MultNumBitsExt + 2 - MultNumBitsExt - 1)
          with (S (S sus)) by lia.
        apply Z.add_cancel_l.
        replace (S sus + MultNumBitsExt - MultNumBitsExt - 1) with sus by lia.
        rewrite wordToB4_bwordToZ_step.
        rewrite Z.mul_add_distr_r.
        rewrite Z.add_comm.
        f_equal.
        * replace (Z.of_nat (pow2 (S (S sus)))) with (4 * Z.of_nat (pow2 sus))%Z
            by (do 2 rewrite pow2_S_z; ring).
          rewrite Z.mul_assoc; f_equal; lia.
        * replace (split1 3 (MultBits - 3) (evalExpr we)) with (split1 3 sl wl)
            by (apply eq_sym; eauto using split1_combine_existT).
          apply booth4AddU_bbToZ.
  Qed.

  Lemma boothStepInv_boothStep:
    forall (m: word MultNumBitsExt) (Hm: m <> wpow2 MultNumBits)
           mp mn p we nwe,
      mp = extz (sext m 1) (S MultNumBitsExt) ->
      mn = extz (sext (wneg m) 1) (S MultNumBitsExt) ->
      boothStep mp mn we = nwe ->
      forall sl su (wl: word (S (S sl))) (wu: word su) sus,
        sl <> 0 ->
        (S sus) + MultNumBitsExt = su ->
        existT word _ (evalExpr we) = existT word _ (combine wl wu) ->
        BoothStepInv m p wl wu ->
        exists (nwl: word (S sl)) (nwu: word (su + 1)),
          existT word _ (evalExpr nwe) = existT word _ (combine nwl nwu) /\
          BoothStepInv m p nwl nwu.
  Proof.
    intros; subst.
    apply boothStepInv_inv in H5; destruct H5 as [_ H5].
    destruct H5 as [u ?]; dest.

    exists (rtrunc1 wl).
    exists (sext wu 1 ^+ sext (booth2AddM m (split1 2 (MultBits - 2) (evalExpr we))) 1).
    split.

    - rewrite boothStep_eval.
      rewrite combine_wplus_1.
      apply existT_wplus.
      + apply combine_wrshifta_rtrunc1_sext; assumption.
      + apply boothStepEvalM_booth2AddM.
        apply eq_sigT_fst in H4; assumption.

    - eapply @BSInv
        with (u:= (u + booth2AddU (split1 2 (MultBits - 2) (evalExpr we)) sus)%Z).
      + intros; subst.
        elim H2; reflexivity.
      + rewrite Z.mul_add_distr_l, <-H.
        apply booth2AddM_booth2AddU; assumption.
      + rewrite <-H0, <-Z.add_assoc.
        replace (S sus + MultNumBitsExt + 1 - MultNumBitsExt - 1) with (S sus) by lia.
        apply Z.add_cancel_l.
        replace (S sus + MultNumBitsExt - MultNumBitsExt - 1) with sus by lia.
        rewrite wordToB2_bwordToZ_step.
        rewrite Z.mul_add_distr_r.
        rewrite Z.add_comm.
        f_equal.
        * replace (Z.of_nat (pow2 (S sus))) with (2 * Z.of_nat (pow2 sus))%Z
            by (rewrite pow2_S_z; ring).
          rewrite Z.mul_assoc; f_equal; lia.
        * replace (split1 2 (MultBits - 2) (evalExpr we)) with (split1 2 sl wl)
            by (apply eq_sym; eauto using split1_combine_existT).
          apply booth2AddU_boothToZ.
  Qed.

  Lemma booth4Step_evalExpr_var:
    forall m_pos m_neg e,
      evalExpr (booth4Step m_pos m_neg (Var _ _ (evalExpr e))) =
      evalExpr (booth4Step m_pos m_neg e).
  Proof.
    intros; do 2 rewrite booth4Step_eval; reflexivity.
  Qed.

  Record BoothMultiplierInv (o: RegsT): Prop :=
    { bsiM : fullType type (SyntaxKind (Bit MultNumBitsExt));
      HbsiM : M.find "m" o = Some (existT _ _ bsiM);
      bsiR : fullType type (SyntaxKind (Bit MultNumBitsExt));
      HbsiR : M.find "r" o = Some (existT _ _ bsiR);

      bsiMp : fullType type (SyntaxKind (Bit MultBits));
      HbsiMp : M.find "m_pos" o = Some (existT _ _ bsiMp);
      bsiMn : fullType type (SyntaxKind (Bit MultBits));
      HbsiMn : M.find "m_neg" o = Some (existT _ _ bsiMn);

      bsiP : fullType type (SyntaxKind (Bit MultBits));
      HbsiP : M.find "p" o = Some (existT _ _ bsiP);

      bsiCnt : fullType type (SyntaxKind (Bit (S MultLogNumPhases)));
      HbsiCnt : M.find "cnt" o = Some (existT _ _ bsiCnt);

      HbsiMmp : bsiMp = extz (sext bsiM 1) (S MultNumBitsExt);
      HbsiMmn : bsiMn = extz (sext (wneg bsiM) 1) (S MultNumBitsExt);

      HmInv : bsiM <> wpow2 MultNumBits;
      HbsiInv :
        exists sl (wl: word sl) sus su (wu: word su),
          sl = 8 * (wordToNat bsiCnt) + 1 /\
          su = S sus + MultNumBitsExt /\
          existT word _ bsiP = existT word _ (combine wl wu) /\
          BoothStepInv bsiM bsiR wl wu
    }.

  Ltac boothMultiplierInv_old :=
    repeat match goal with
           | [H: BoothMultiplierInv _ |- _] => destruct H
           end;
    kinv_red.

  Ltac boothMultiplierInv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kinv_red; (* unfolding invariant definitions *)
    repeat (* cheaper than "intuition" *)
      (match goal with
       | [ |- _ /\ _ ] => split
       end);
    try eassumption; intros; try reflexivity;
    intuition kinv_simpl; intuition idtac.

  Variable n: nat.
  
  Lemma boothMultiplierInv_ok':
    forall init n ll,
      init = initRegs (getRegInits boothMultiplierImpl) ->
      Multistep boothMultiplierImpl init n ll ->
      BoothMultiplierInv n.
  Proof.
    induction 2; intros.
 
    - boothMultiplierInv_old.
      unfold getRegInits, fst, boothMultiplierImpl, projT1.
      boothMultiplierInv_new; [discriminate|].
      eexists; exists (natToWord 1 0).
      eexists; eexists; exists (natToWord (2 * MultNumBitsExt + 1) 0).
      split; [|split; [|split]].
      + reflexivity.
      + instantiate (1:= MultNumBitsExt); reflexivity.
      + reflexivity.
      + econstructor.
        * intros.
          eexists; exists (wzero (2 * MultNumBitsExt)).
          reflexivity.
        * instantiate (1:= 0%Z); reflexivity.
        * reflexivity.

    - kinvert; [mred|mred| | |].
      + (* boothMultRegister *)
        Opaque natToWord evalExpr combine.
        kinv_action_dest.
        Transparent natToWord evalExpr.
        kinv_custom boothMultiplierInv_old.
        boothMultiplierInv_new.
        
        * cbn; unfold eq_rec; eq_rect_simpl.
          reflexivity.
        * cbn; unfold eq_rec; eq_rect_simpl.
          reflexivity.
        * clear -H4 H12.
          Opaque split2.
          simpl in *.
          Transparent split2.
          find_if_inside; [|discriminate].
          assert (wmsb (x Fin.F1) false = true) by (rewrite H12; reflexivity).
          remember (x Fin.F1) as x1; simpl in x1; clear Heqx1 x.
          change MultNumBitsExt with (MultNumBits + 1) in *.
          rewrite wmsb_split2 in H.
          find_if_inside; [discriminate|].
          elim n; assumption.

        * simpl; unfold eq_rec; eq_rect_simpl.

          assert (Hx1: x Fin.F1 <> wpow2 MultNumBits).
          { intro Hx.
            clear -Hx H4.
            Opaque split2.
            simpl in H4.
            Transparent split2.
            find_if_inside; [|discriminate].
            assert (wmsb (x Fin.F1) false = true) by (rewrite Hx; reflexivity).
            remember (x Fin.F1) as x1; simpl in x1; clear Heqx1 x.
            change MultNumBitsExt with (MultNumBits + 1) in *.
            rewrite wmsb_split2 in H.
            find_if_inside; [discriminate|].
            elim n; assumption.
          }

          set (extz (combine (x (Fin.FS Fin.F1)) (natToWord (MultNumBitsExt + 1) 0)) 1) as ww.
          pose proof (boothStepInv_init (x Fin.F1) (x (Fin.FS Fin.F1))) as Hinv0.

          assert (pred MultNumBitsExt <> 0) by (cbn; lia).
          eapply (boothStepInv_boothStep
                    (we:= Var type (SyntaxKind (Bit MultBits)) ww) (sus:= O)
                    Hx1 eq_refl eq_refl eq_refl H12 eq_refl) in Hinv0; [|reflexivity].
          simpl in Hinv0.
          destruct Hinv0 as [nwl [nwu [? ?]]].

          eexists; exists nwl.
          exists 1; eexists; exists nwu.

          repeat split.
          { subst ww.
            cbv [evalSignExtendTrunc].
            simpl; unfold eq_rec; eq_rect_simpl.
            rewrite <-H13.
            reflexivity.
          }
          { assumption. }
        
      + (* boothMultGetResult *)
        Opaque MultNumBits.
        kinv_action_dest.
        mred.
        Transparent MultNumBits.

      + (* boothStep *)
        kinv_action_dest.
        kinv_custom boothMultiplierInv_old.
        boothMultiplierInv_new.

        remember (8 * wordToNat x + 1) as psl.
        assert (psl >= 9)%nat.
        { subst; clear -n1.
          unfold type in x.
          do 5 (dependent destruction x).
          destruct b, b0, b1, b2; cbn; try lia.
          elim n1; reflexivity.
        }
        do 9 (destruct psl as [|psl]; [lia|]); clear H.

        rename H12 into Hinv0.
        eapply (boothStepInv_booth4Step
                  (we:= Var type (SyntaxKind (Bit MultBits)) x2)
                  HmInv eq_refl eq_refl eq_refl eq_refl) in Hinv0; [|eassumption].
        replace (S x5 + MultNumBitsExt + 2)
          with ((S (S (S x5))) + MultNumBitsExt) in Hinv0 by lia.
        destruct Hinv0 as [nwl1 [nwu1 [Heq1 Hinv1]]].
        
        eapply (boothStepInv_booth4Step
                  HmInv eq_refl eq_refl eq_refl eq_refl) in Hinv1; [|eassumption].
        replace (S (S (S x5)) + MultNumBitsExt + 2)
          with (S (S (S (S (S x5)))) + MultNumBitsExt) in Hinv1 by lia.
        destruct Hinv1 as [nwl2 [nwu2 [Heq2 Hinv2]]].

        eapply (boothStepInv_booth4Step
                  HmInv eq_refl eq_refl eq_refl eq_refl) in Hinv2; [|eassumption].
        replace (S (S (S (S (S x5)))) + MultNumBitsExt + 2)
          with (S (S (S (S (S (S (S x5)))))) + MultNumBitsExt) in Hinv2 by lia.
        destruct Hinv2 as [nwl3 [nwu3 [Heq3 Hinv3]]].

        eapply (boothStepInv_booth4Step
                  HmInv eq_refl eq_refl eq_refl eq_refl) in Hinv3; [|eassumption].
        replace (S (S (S (S (S (S (S x5)))))) + MultNumBitsExt + 2)
          with (S (S (S (S (S (S (S (S (S x5)))))))) + MultNumBitsExt) in Hinv3 by lia.
        destruct Hinv3 as [nwl4 [nwu4 [Heq4 Hinv4]]].

        eexists; exists nwl4.
        eexists; eexists; exists nwu4.

        repeat split.
        * intros.
          match goal with
          | [ |- context [_ ^- ?w] ] =>
            replace w with (natToWord (S MultLogNumPhases) 1) by reflexivity
          end.
          rewrite <-wordToNat_natToWord_pred by assumption.
          lia.
        * rewrite booth4Step_evalExpr_var with (e:= booth4Step _ _ (#x2)%kami_expr).
          rewrite booth4Step_evalExpr_var with (e:= booth4Step _ _ (booth4Step _ _ _)).
          rewrite booth4Step_evalExpr_var.
          assumption.
        * assumption.

  Qed.

  Lemma boothMultiplierInv_ok:
    forall o,
      reachable o boothMultiplierImpl ->
      BoothMultiplierInv o.
  Proof.
    intros; inv H; inv H0.
    eapply boothMultiplierInv_ok'; eauto.
  Qed.
  
  Local Definition thetaR (ir sr: RegsT): Prop.
  Proof.
    kexistv "m_pos" m_pos ir (Bit MultBits).
    kexistv "m_neg" m_neg ir (Bit MultBits).
    kexistv "p" p ir (Bit MultBits).
    kexistv "m" m ir (Bit MultNumBitsExt).
    kexistv "r" r ir (Bit MultNumBitsExt).
    kexistv "cnt" cnt ir (Bit (S MultLogNumPhases)).

    exact (sr = ["r" <- existT _ _ r]
                +["m" <- existT _ _ m])%fmap.
  Defined.
  #[local] Hint Unfold thetaR: MapDefs.

  Local Definition ruleMap (o: RegsT): string -> option string :=
    "boothMultRegister" |-> "multRegister";
      "boothMultGetResult" |-> "multGetResult"; ||.
  #[local] Hint Unfold ruleMap: MethDefs.
  
  Theorem multiplier_ok: boothMultiplierImpl <<== multiplierSpec.
  Proof.
    kdecomposeR_nodefs thetaR ruleMap.
    kinv_add boothMultiplierInv_ok.
    kinvert.

    - (* "boothMultRegister" |-> "multRegister" *)
      Opaque natToWord evalExpr combine.
      kinv_action_dest.
      kinv_custom boothMultiplierInv_old.
      kinv_regmap_red.
      eexists; split; kinv_constr.
      kinv_eq.
      Transparent natToWord evalExpr combine.

    - (* "boothMultGetResult" |-> "multGetResult" *)
      Opaque MultNumBits.
      kinv_action_dest.
      kinv_custom boothMultiplierInv_old.
      kinv_regmap_red.
      Transparent MultNumBits.

      eexists; split; kinv_constr.
      apply boothStepInv_finish in H7; dest.
      assert (x3 = MultNumBitsExt) by (apply eq_sigT_fst in H6; cbn; cbn in H6; lia).
      subst; destruct_existT.
      rewrite idElementwiseId; unfold id.
      do 3 f_equal.
      fin_func_eq.

      + Opaque split1 split2 wordToZ.
        simpl.
        unfold eq_rec_r, eq_rec; repeat rewrite <-eq_rect_eq.
        unfold ilist.ilist_to_fun_m; simpl.
        repeat f_equal.
        rewrite wtl_combine.
        unfold wmultZ, wordBinZ.
        pose proof (sext_wordToZ 65 bsiM).
        cbv [evalSignExtendTrunc]; cbn.
        unfold eq_rec; eq_rect_simpl.
        cbn in H1; rewrite H1.
        pose proof (sext_wordToZ 65 bsiR).
        cbn; cbn in H2; rewrite H2.
        cbn in H0; rewrite <-H0.
        assert (x = 2 * MultNumBitsExt) by (apply eq_sigT_fst in H; lia); subst.
        destruct_existT.
        pose proof (sext_wordToZ 1 x4); cbn; cbn in H; rewrite H.
        rewrite sext_split1.
        rewrite ZToWord_wordToZ.
        reflexivity.
        Transparent split1 split2 wordToZ.

      + Opaque split1 split2 wordToZ.
        simpl.
        unfold eq_rec_r, eq_rec; repeat rewrite <-eq_rect_eq.
        unfold ilist.ilist_to_fun_m; simpl.
        repeat f_equal.
        rewrite wtl_combine.
        unfold wmultZ, wordBinZ.
        pose proof (sext_wordToZ 65 bsiM).
        cbv [evalSignExtendTrunc]; cbn.
        unfold eq_rec; eq_rect_simpl.
        cbn in H1; rewrite H1.
        pose proof (sext_wordToZ 65 bsiR).
        cbn; cbn in H2; rewrite H2.
        cbn in H0; rewrite <-H0.
        assert (x = 2 * MultNumBitsExt) by (apply eq_sigT_fst in H; lia); subst.
        destruct_existT.
        pose proof (sext_wordToZ 1 x4); cbn; cbn in H; rewrite H.
        rewrite sext_split1.
        rewrite ZToWord_wordToZ.
        reflexivity.
        Transparent split1 split2 wordToZ.

    - (* "boothStep" |-> . *)
      kinv_action_dest.
      kinv_custom boothMultiplierInv_old.
      kinv_regmap_red.
      eexists; split; kinv_constr.
      
  Qed.

End Multiplier64.

