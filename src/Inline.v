Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FnMap.
Require Import Syntax.

Set Implicit Arguments.

Section Phoas.
  Variable type: Kind -> Type.
  Variable getDefault: forall (k: Kind), type k.

  Definition inlineArg {argT retT} (a: Expr type argT)
             (m: type argT -> Action type retT): Action type retT :=
    Let_ a m.

  Fixpoint getMethod (n: string) (dms: list (DefMethT type)) :=
    match dms with
      | nil => None
      | {| attrName := mn; attrType := mb |} :: dms' =>
        if string_dec n mn then Some mb else getMethod n dms'
    end.

  Fixpoint appendAction {retT1 retT2} (a1: Action type retT1)
           (a2: type retT1 -> Action type retT2): Action type retT2 :=
    match a1 with
      | MCall name sig ar cont => MCall name sig ar (fun a => appendAction (cont a) a2)
      | Let_ _ ar cont => Let_ ar (fun a => appendAction (cont a) a2)
      | ReadReg reg k cont => ReadReg reg k (fun a => appendAction (cont a) a2)
      | WriteReg reg _ e cont => WriteReg reg e (appendAction cont a2)
      | IfElse ce _ ta fa cont => IfElse ce ta fa (fun a => appendAction (cont a) a2)
      | Assert_ ae cont => Assert_ ae (appendAction cont a2)
      | Return e => Let_ e a2
    end.

  Fixpoint inlineActionOnce {retT} (a: Action type retT)
           (dms: list (DefMethT type)): Action type retT :=
    match a with
      | MCall name sig ar cont =>
        match getMethod name dms with
          | Some dm =>
            match SignatureT_dec (objType dm) sig with
              | left e => appendAction (inlineArg ar (eq_rect _ _ (objVal dm) _ e)) cont
              | right _ =>
                MCall name sig ar (fun ak => inlineActionOnce (cont ak) dms)
            end
          | None =>
            MCall name sig ar (fun ak => inlineActionOnce (cont ak) dms)
        end
      | Let_ _ ar cont => Let_ ar (fun a => inlineActionOnce (cont a) dms)
      | ReadReg reg k cont => ReadReg reg k (fun a => inlineActionOnce (cont a) dms)
      | WriteReg reg _ e cont => WriteReg reg e (inlineActionOnce cont dms)
      | IfElse ce _ ta fa cont => IfElse ce (inlineActionOnce ta dms)
                                         (inlineActionOnce fa dms)
                                         (fun a => inlineActionOnce (cont a) dms)
      | Assert_ ae cont => Assert_ ae (inlineActionOnce cont dms)
      | Return e => Return e
    end.

  Fixpoint inlineAction {retT} (a: Action type retT) (dms: list (DefMethT type))
           (countdown: nat): Action type retT :=
    match countdown with
      | O => a
      | S cd => inlineAction (inlineActionOnce a dms) dms cd
    end.

  Definition inlineRule (r: Attribute (Action type (Bit 0)))
             (dms: list (DefMethT type)): Attribute (Action type (Bit 0)) :=
    match r with
      | {| attrName := rn; attrType := ra |} =>
        {| attrName := rn;
           attrType := inlineAction ra dms (List.length dms) |}
    end.

  Fixpoint inlineRules (rules: list (Attribute (Action type (Bit 0))))
           (dms: list (DefMethT type)): list (Attribute (Action type (Bit 0))) :=
    match rules with
      | nil => nil
      | r :: rules' => (inlineRule r dms) :: (inlineRules rules' dms)
    end.

  Lemma inlineRules_In:
    forall r rules dms, In r rules -> In (inlineRule r dms) (inlineRules rules dms).
  Proof.
    induction rules; intros; inv H.
    - left; reflexivity.
    - right; apply IHrules; auto.
  Qed.

  Definition inlineMethod (n: string) {argT retT} (m: type argT -> Action type retT)
             (dms: list (DefMethT type)): type argT -> Action type retT :=
    fun a => inlineAction (m a) dms (List.length dms).

  Fixpoint inlineDms (dms: list (DefMethT type)): list (DefMethT type) :=
    match dms with
      | nil => nil
      | {| attrName := n; attrType := {| objType := s; objVal := a |} |} :: dms' =>
        {| attrName := n; attrType := {| objType := s; objVal := inlineMethod n a dms |} |}
          :: (inlineDms dms')
    end.

  Definition inlineMod (m1 m2: Modules type): Modules type :=
    match m1, m2 with
      | Mod regs1 r1 dms1, Mod regs2 r2 dms2 =>
        Mod (regs1 ++ regs2) (inlineRules (r1 ++ r2) (dms1 ++ dms2)) (inlineDms (dms1 ++ dms2))
      | _, _ => m1 (* undefined *)
    end.

  (* necessary condition *)
  Fixpoint noCalls {retT} (a: Action type retT) :=
    match a with
      | MCall _ _ _ _ => false
      | Let_ _ ar cont => noCalls (cont (getDefault _))
      | ReadReg reg k cont => noCalls (cont (getDefault _))
      | WriteReg reg _ e cont => noCalls cont
      | IfElse ce _ ta fa cont => (noCalls ta) && (noCalls fa) && (noCalls (cont (getDefault _)))
      | Assert_ ae cont => noCalls cont
      | Return e => true
    end.

  Fixpoint noCallsRules (rules: list (Attribute (Action type (Bit 0)))) :=
    match rules with
      | nil => true
      | {| attrType := r |} :: rules' => (noCalls r) && (noCallsRules rules')
    end.

  Fixpoint noCallsDms (dms: list (DefMethT type)) :=
    match dms with
      | nil => true
      | {| attrType := {| objVal := dm |} |} :: dms' =>
        (noCalls (dm (getDefault _))) && (noCallsDms dms')
    end.

  Fixpoint noCallsMod (m: Modules type) :=
    match m with
      | Mod _ rules dms => (noCallsRules rules) && (noCallsDms dms)
      | ConcatMod m1 m2 => (noCallsMod m1) && (noCallsMod m2)
    end.

End Phoas.

Require Import Semantics.

Section Preliminaries.

  Lemma action_olds_ext:
    forall retK olds1 olds2 a news calls (retV: type retK),
      FnMap.Sub olds1 olds2 ->
      SemAction olds1 a news calls retV ->
      SemAction olds2 a news calls retV.
  Proof.
    admit.
  Qed.

  Lemma appendAction_prop:
    forall retK1 retK2 a1 a2 olds1 olds2 news1 news2 calls1 calls2
           (retV1: type retK1) (retV2: type retK2),
      Disj olds1 olds2 ->
      SemAction olds1 a1 news1 calls1 retV1 ->
      SemAction olds2 (a2 retV1) news2 calls2 retV2 ->
      SemAction (union olds1 olds2) (appendAction a1 a2)
                (union news1 news2) (union calls1 calls2) retV2.
  Proof.
    induction a1; intros.

    - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2); econstructor; eauto.
    - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2); econstructor; eauto.
    - invertAction H1; specialize (H _ _ _ _ _ _ _ _ _ _ H0 H3 H2); econstructor; eauto.
      repeat autounfold with MapDefs; repeat autounfold with MapDefs in H1.
      rewrite H1; reflexivity.
    - invertAction H0; specialize (IHa1 _ _ _ _ _ _ _ _ _ H H0 H1); econstructor; eauto.

    - invertAction H1.
      simpl; remember (evalExpr e) as cv; destruct cv; dest; subst.
      + eapply SemIfElseTrue.
        * eauto.
        * eapply action_olds_ext.
          { instantiate (1:= olds1); apply Sub_union. }
          { exact H1. }
        * eapply H; eauto.
        * rewrite union_assoc; reflexivity.
        * rewrite union_assoc; reflexivity.
      + eapply SemIfElseFalse.
        * eauto.
        * eapply action_olds_ext.
          { instantiate (1:= olds1); apply Sub_union. }
          { exact H1. }
        * eapply H; eauto.
        * rewrite union_assoc; reflexivity.
        * rewrite union_assoc; reflexivity.

    - invertAction H0; specialize (IHa1 _ _ _ _ _ _ _ _ _ H H0 H1); econstructor; eauto.
    - invertAction H0; map_simpl_G; econstructor.
      eapply action_olds_ext; eauto.
      rewrite Disj_union_unionR; auto.
      apply Sub_unionR.
      
  Qed.

End Preliminaries.

Section Facts.
  Variables (regs1 regs2: list RegInitT)
            (r1 r2: list (Attribute (Action type (Bit 0))))
            (dms1 dms2: list (DefMethT type)).

  Definition getDefault := (fun k: Kind => evalConstT (getDefaultConst k)).

  Definition m1 := Mod regs1 r1 dms1.
  Definition m2 := Mod regs2 r2 dms2.

  Definition cm := ConcatMod m1 m2.
  Definition im := @inlineMod type m1 m2.

  Lemma inline_correct_rule:
    forall r or nr cmMap,
      noCallsMod getDefault im = true ->
      LtsStep cm (Some r) or nr empty cmMap -> LtsStep im (Some r) or nr empty cmMap.
  Proof.
    intros; unfold im, inlineMod; simpl.
    inv H0; destConcatLabel.
    unfold CombineRm in Hcrm; dest.
    inv H0; [destruct rm2; inv H1|destruct rm1; inv H1].

    - inv Hlts1; inv Hlts2; constructor.
      + unfold InDomain in *; intros.
        rewrite map_app; apply in_or_app.
        apply InMap_disjUnion in H0; destruct H0.
        * specialize (HOldRegs _ H0); left; assumption.
        * specialize (HOldRegs0 _ H0); right; assumption.
      + inv Hltsmod0.
        eapply SemAddRule.
        * assert (Hin: In (s :: ruleBody)%struct (r1 ++ r2)) by
              (apply in_or_app; right; assumption); clear HInRule.
          pose proof (inlineRules_In _ _ (dms1 ++ dms2) Hin).
          exact H0.
        * instantiate (3:= disjUnion news1 (union news news0)
                                     (map (attrName (Kind:=Typed ConstT)) (getRegInits m1))).
          instantiate (2:= disjUnion
                             (complement cmMap1 (map (@attrName _) dms2))
                             (complement (union calls cm2)
                                         (map (@attrName _) dms1))
                             (listSub (getCmsR r1 ++ getCmsM dms1)
                                      (map (@attrName _) dms2))).
          instantiate (1:= retV).

          

          unfold FiltDm in Hfd; simpl in Hfd.
          clear Hfc.
          

          

            
          admit.
        * instantiate (2:= empty); instantiate (1:= empty).
          apply SemMod_empty.
        * eauto.
        * eauto.
        * rewrite union_empty_2; reflexivity.
        * unfold FiltCm in Hfc; simpl in Hfc; subst.
          rewrite union_empty_2; reflexivity.

    - admit.

  Qed.

End Facts.
    
    