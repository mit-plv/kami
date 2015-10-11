Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FnMap.
Require Import Syntax.

Set Implicit Arguments.

Ltac destruct_existT :=
  repeat match goal with
           | [H: existT _ _ _ = existT _ _ _ |- _] =>
             (apply Eqdep.EqdepTheory.inj_pair2 in H; subst)
         end.

Section Phoas.
  Variable type: Kind -> Type.

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

  Fixpoint inlineDm {retT} (a: Action type retT)
           (dm: DefMethT type): Action type retT :=
    match a with
      | MCall name sig ar cont =>
        if string_dec name (attrName dm) then
          match SignatureT_dec (objType (attrType dm)) sig with
            | left e => appendAction (inlineArg ar (eq_rect _ _ (objVal (attrType dm)) _ e))
                                     (* (fun ak => inlineDm (cont ak) dm) *) cont
            | right _ =>
              MCall name sig ar (fun ak => inlineDm (cont ak) dm)
          end
        else
          MCall name sig ar (fun ak => inlineDm (cont ak) dm)
      | Let_ _ ar cont => Let_ ar (fun a => inlineDm (cont a) dm)
      | ReadReg reg k cont => ReadReg reg k (fun a => inlineDm (cont a) dm)
      | WriteReg reg _ e cont => WriteReg reg e (inlineDm cont dm)
      | IfElse ce _ ta fa cont => IfElse ce (inlineDm ta dm) (inlineDm fa dm)
                                         (fun a => inlineDm (cont a) dm)
      | Assert_ ae cont => Assert_ ae (inlineDm cont dm)
      | Return e => Return e
    end.

  Fixpoint inlineDms {retT} (a: Action type retT)
           (dms: list (DefMethT type)): Action type retT :=
    match dms with
      | nil => a
      | dm :: dms' => inlineDms (inlineDm a dm) dms'
    end.

  Fixpoint inlineDmsRep {retT} (a: Action type retT) (dms: list (DefMethT type))
           (countdown: nat): Action type retT :=
    match countdown with
      | O => a
      | S cd => inlineDmsRep (inlineDms a dms) dms cd
    end.

  Section Countdown.
    Variable countdown: nat.

    Definition inlineToRule (r: Attribute (Action type (Bit 0)))
               (dms: list (DefMethT type)): Attribute (Action type (Bit 0)) :=
      match r with
        | {| attrName := rn; attrType := ra |} =>
          {| attrName := rn;
             attrType := inlineDmsRep ra dms countdown |}
      end.

    Fixpoint inlineToRules (rules: list (Attribute (Action type (Bit 0))))
             (dms: list (DefMethT type)): list (Attribute (Action type (Bit 0))) :=
      match rules with
        | nil => nil
        | r :: rules' => (inlineToRule r dms) :: (inlineToRules rules' dms)
      end.

    Lemma inlineToRules_In:
      forall r rules dms, In r rules -> In (inlineToRule r dms) (inlineToRules rules dms).
    Proof.
      induction rules; intros; inv H.
      - left; reflexivity.
      - right; apply IHrules; auto.
    Qed.

    Definition inlineToDm (n: string) {argT retT} (m: type argT -> Action type retT)
               (dms: list (DefMethT type)): type argT -> Action type retT :=
      fun a => inlineDmsRep (m a) dms countdown.

    Fixpoint inlineToDms (dms: list (DefMethT type)): list (DefMethT type) :=
      match dms with
        | nil => nil
        | {| attrName := n; attrType := {| objType := s; objVal := a |} |} :: dms' =>
          {| attrName := n; attrType := {| objType := s; objVal := inlineToDm n a dms |} |}
            :: (inlineToDms dms')
      end.

    Definition inlineMod (m1 m2: Modules type): Modules type :=
      match m1, m2 with
        | Mod regs1 r1 dms1, Mod regs2 r2 dms2 =>
          Mod (regs1 ++ regs2) (inlineToRules (r1 ++ r2) (dms1 ++ dms2))
              (inlineToDms (dms1 ++ dms2))
        | _, _ => m1 (* undefined *)
      end.

  End Countdown.

End Phoas.

Section PhoasTT.

  Definition typeTT (k: Kind): Type :=
    match k with
      | _ => unit
    end.

  (* Well-formedness w.r.t. method calls *)
  Section Wfm.
    Fixpoint nodupString (l: list string): bool :=
      match l with
        | nil => true
        | hd :: tl => if in_dec string_dec hd tl then false else nodupString tl
      end.

    Fixpoint collectCalls (calls: list (list string)) {retT} (a: Action typeTT retT)
    : list (list string) :=
      match a with
        | MCall name _ _ cont =>
          collectCalls (map (fun l => name :: l) calls) (cont tt)
        | Let_ _ ar cont => collectCalls calls (cont tt)
        | ReadReg reg k cont => collectCalls calls (cont tt)
        | WriteReg reg _ e cont => collectCalls calls cont
        | IfElse ce _ ta fa cont =>
          app (collectCalls (collectCalls calls ta) (cont tt))
              (collectCalls (collectCalls calls fa) (cont tt))
        | Assert_ _ cont => collectCalls calls cont
        | Return _ => calls
      end.

    Definition wfmAction {retT} (a: Action typeTT retT) :=
      forallb (fun l => nodupString l) (collectCalls ((@nil string) :: nil) a).

    Inductive WfmAction: list string -> forall {retT}, Action typeTT retT -> Prop :=
    | WfmMCall:
        forall ll name sig ar {retT} cont t (Hnin: ~ In name ll),
          WfmAction (name :: ll) (cont t) ->
          WfmAction ll (MCall (lretT:= retT) name sig ar cont)
    | WfmLet:
        forall ll {argT retT} ar cont t,
          WfmAction ll (cont t) ->
          WfmAction ll (Let_ (lretT':= argT) (lretT:= retT) ar cont)
    | WfmReadReg:
        forall ll {retT} reg k cont t,
          WfmAction ll (cont t) ->
          WfmAction ll (ReadReg (lretT:= retT) reg k cont)
    | WfmWriteReg:
        forall ll {writeT retT} reg e cont,
          WfmAction ll cont ->
          WfmAction ll (WriteReg (k:= writeT) (lretT:= retT) reg e cont)
    | WfmIfElse:
        forall ll {retT1 retT2} ce ta fa cont,
          WfmAction ll (appendAction (retT1:= retT1) (retT2:= retT2) ta cont) ->
          WfmAction ll (appendAction (retT1:= retT1) (retT2:= retT2) fa cont) ->
          WfmAction ll (IfElse ce ta fa cont)
    | WfmAssert:
        forall ll {retT} e cont,
          WfmAction ll cont ->
          WfmAction ll (Assert_ (lretT:= retT) e cont)
    | WfmReturn:
        forall ll {retT} (e: Expr typeTT retT), WfmAction ll (Return e).

    Lemma wfmAction_WfmAction:
      forall {retT} (a: Action typeTT retT), wfmAction a = true -> WfmAction nil a.
    Proof.
      admit.
    Qed.

  End Wfm.

  Section NoCalls.
    (* Necessary condition for inlining correctness *)
    Fixpoint noCalls {retT} (a: Action typeTT retT) :=
      match a with
        | MCall _ _ _ _ => false
        | Let_ _ ar cont => noCalls (cont tt)
        | ReadReg reg k cont => noCalls (cont tt)
        | WriteReg reg _ e cont => noCalls cont
        | IfElse ce _ ta fa cont => (noCalls ta) && (noCalls fa) && (noCalls (cont tt))
        | Assert_ ae cont => noCalls cont
        | Return e => true
      end.

    Fixpoint noCallsRules (rules: list (Attribute (Action typeTT (Bit 0)))) :=
      match rules with
        | nil => true
        | {| attrType := r |} :: rules' => (noCalls r) && (noCallsRules rules')
      end.

    Fixpoint noCallsDms (dms: list (DefMethT typeTT)) :=
      match dms with
        | nil => true
        | {| attrType := {| objVal := dm |} |} :: dms' =>
          (noCalls (dm tt)) && (noCallsDms dms')
      end.

    Fixpoint noCallsMod (m: Modules typeTT) :=
      match m with
        | Mod _ rules dms => (noCallsRules rules) && (noCallsDms dms)
        | ConcatMod m1 m2 => (noCallsMod m1) && (noCallsMod m2)
      end.

  End NoCalls.

End PhoasTT.

Require Import Semantics.

Inductive WfmActionSem: list string -> forall {retT}, Action type retT -> list string -> Prop :=
| WfmMCallSem:
    forall ll rl name sig ar {retT} cont (Hnin: ~ In name ll),
      (forall t, WfmActionSem (name :: ll) (cont t) rl) ->
      WfmActionSem ll (MCall (lretT:= retT) name sig ar cont) rl
| WfmLetSem:
    forall ll rl {argT retT} ar cont,
      (forall t, WfmActionSem ll (cont t) rl) ->
      WfmActionSem ll (Let_ (lretT':= argT) (lretT:= retT) ar cont) rl
| WfmReadRegSem:
    forall ll rl {retT} reg k cont,
      (forall t, WfmActionSem ll (cont t) rl) ->
      WfmActionSem ll (ReadReg (lretT:= retT) reg k cont) rl
| WfmWriteRegSem:
    forall ll rl {writeT retT} reg e cont,
      WfmActionSem ll cont rl ->
      WfmActionSem ll (WriteReg (k:= writeT) (lretT:= retT) reg e cont) rl
| WfmIfElseSem:
    forall ll trl frl rl {retT1 retT2} ce ta fa cont,
      WfmActionSem (retT:= retT1) ll ta trl ->
      WfmActionSem (retT:= retT1) ll fa frl ->
      (forall t, WfmActionSem (retT:= retT2) (trl ++ frl) (cont t) rl) ->
      (* WfmActionSem ll (appendAction (retT1:= retT1) (retT2:= retT2) ta cont) -> *)
      (* WfmActionSem ll (appendAction (retT1:= retT1) (retT2:= retT2) fa cont) -> *)
      WfmActionSem ll (IfElse ce ta fa cont) rl
| WfmAssertSem:
    forall ll rl {retT} e cont,
      WfmActionSem ll cont rl ->
      WfmActionSem ll (Assert_ (lretT:= retT) e cont) rl
| WfmReturnSem:
    forall ll rl {retT} (e: Expr type retT), ll = rl -> WfmActionSem ll (Return e) rl.

Definition WfmActionSem' {retT} (a: Action type retT) := exists rl, WfmActionSem nil a rl.

Lemma WfmActionSem_init:
  forall {retK} (a: Action type retK) ll rl
         (Hwfm: WfmActionSem ll a rl),
    WfmActionSem' a.
Proof.
  admit.
Qed.

Lemma WfmActionSem_MCall:
  forall {retK} olds a news calls (retV: type retK) dmn rl
         (Hsem: SemAction olds a news calls retV)
         (Hwfm: WfmActionSem [dmn] a rl),
    complement calls [dmn] = calls.
Proof.
  induction a; intros; invertAction Hsem; inv Hwfm; destruct_existT.

  - admit.
  - eapply H; eauto.
  - eapply H; eauto.
  - eapply IHa; eauto.
  - admit.
  - eapply IHa; eauto.
  - map_simpl_G; reflexivity.
Qed.

Section Preliminaries.

  Lemma action_olds_ext:
    forall retK a olds1 olds2 news calls (retV: type retK),
      FnMap.Sub olds1 olds2 ->
      SemAction olds1 a news calls retV ->
      SemAction olds2 a news calls retV.
  Proof.
    induction a; intros.
    - invertAction H1; econstructor; eauto.
    - invertAction H1; econstructor; eauto.
    - invertAction H1; econstructor; eauto.
      repeat autounfold with MapDefs; repeat autounfold with MapDefs in H1.
      rewrite <-H1; symmetry; apply H0; unfold InMap, find; rewrite H1; discriminate.
    - invertAction H0; econstructor; eauto.
    - invertAction H1.
      remember (evalExpr e) as cv; destruct cv; dest.
      + eapply SemIfElseTrue; eauto.
      + eapply SemIfElseFalse; eauto.
    - invertAction H0; econstructor; eauto.
    - invertAction H0; econstructor; eauto.
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

  Lemma SemMod_singleton:
    forall rules olds news dm dmMap cmMap,
      SemMod rules olds None news (dm :: nil) dmMap cmMap ->
      DomainOf dmMap ((attrName dm) :: nil) ->
      exists argV retV,
        dm = {| attrName := attrName dm;
                attrType := {| objType := {| arg := arg (objType (attrType dm));
                                             ret := ret (objType (attrType dm)) |};
                               objVal := objVal (attrType dm) |} |} /\
        dmMap = add (attrName dm) {| objVal := (argV, retV) |} empty /\
        SemAction olds (objVal (attrType dm) argV) news cmMap retV.
  Proof.
    intros.
    invertSemMod H.

    - invertSemMod HSemMod.
      exists argV; exists retV.
      split.
      
      + destruct dm as [dmn [[ ] ]]; simpl; reflexivity.
      + split; [reflexivity|].
        map_simpl_G; assumption.

    - invertSemMod HSemMod; exfalso.
      specialize (H0 (attrName dm)); destruct H0.
      specialize (H0 (or_introl eq_refl)).
      unfold InMap in H0; elim H0; reflexivity.
  Qed.

  Lemma inlineDm_prop:
    forall olds1 olds2 retK2 a2
           dm rules news1 news2 dmMap1 cmMap1 cmMap2
           (retV2: type retK2),
      Disj olds1 olds2 -> Disj news1 news2 -> Disj cmMap1 cmMap2 ->
      
      WfmActionSem' a2 ->
      SemAction olds2 a2 news2 cmMap2 retV2 ->
      
      find (attrName dm) cmMap2 = find (attrName dm) dmMap1 -> (* labels match *)
      DomainOf dmMap1 ((attrName dm) :: nil) -> (* dm is actually called *)
      
      SemMod rules olds1 None news1 (dm :: nil) dmMap1 cmMap1 ->
      SemAction (union olds1 olds2) (inlineDm a2 dm)
                (union news1 news2)
                (union cmMap1 (complement cmMap2 ((attrName dm) :: nil)))
                retV2.
  Proof.
    intros; pose proof (SemMod_singleton H6 H5); clear H5 H6; dest.
    destruct dm as [dmn [[ ]]]; simpl in *; inv H5.
    map_simpl H4.

    generalize dependent olds2; generalize dependent news2; generalize dependent cmMap2.
    induction a2; intros.

    - invertAction H5.
      simpl; destruct (string_dec meth dmn); [subst|].

      + clear H. (* don't need IH for this case *)

        map_simpl H4.
        apply opt_some_eq in H4; subst.
        apply typed_type_eq in H4; dest.
        generalize dependent H5; subst; intros.
        inv H.

        destruct (SignatureT_dec _ _); [|elim n; reflexivity].
        simpl in *; rewrite <-Eqdep.EqdepTheory.eq_rect_eq; clear e0.

        econstructor; eauto.
        apply appendAction_prop with (retV1:= x0); auto.
        map_simpl_G.

        inv H2; inv H; destruct_existT.
        specialize (H12 x0).
        pose proof (WfmActionSem_MCall H5 H12); rewrite H.
        assumption.

      + rewrite find_add_2 in H4
          by (unfold string_eq; destruct (string_dec _ _); [elim n; assumption|reflexivity]).
        econstructor; eauto.

        * instantiate (1:= union cmMap1 (complement x2 [dmn])); instantiate (1:= x1).

          clear -n H1.
          unfold Disj in H1.
          apply Equal_eq; repeat autounfold with MapDefs; intros.
          specialize (H1 k).
          destruct H1.

          { unfold find in H; rewrite H.
            destruct (in_dec _ _ _).
            { inv i; [|inv H0].
              unfold string_eq; destruct (string_dec _ _); [elim n; assumption|reflexivity].
            }
            { unfold string_eq; destruct (string_dec _ _); reflexivity. }
          }
          { destruct (cmMap1 k).
            { unfold string_eq; destruct (string_dec _ _); [|reflexivity].
              subst; map_simpl H; discriminate.
            }
            { destruct (in_dec _ _ _).
              { inv i; [|inv H0].
                unfold string_eq; destruct (string_dec _ _); [elim n; assumption|reflexivity].
              }
              { unfold string_eq; destruct (string_dec _ _); reflexivity. }
            }
          }

        * apply H; auto.
          { inv H2; inv H6; destruct_existT.
            specialize (H14 x1).
            eapply WfmActionSem_init; eauto.
          }
          { eapply Disj_add_2; eauto. }

    - invertAction H5; inv H2; inv H6; destruct_existT.
      simpl. econstructor; eauto.
      eapply H; eauto.
      eexists; apply H13.

    - invertAction H5; inv H2; inv H8; destruct_existT.
      simpl; econstructor; eauto.
      + apply Disj_find_union; eauto.
      + eapply H; eauto.
        eexists; apply H14.

    - invertAction H3; inv H2; inv H5; destruct_existT.
      simpl; econstructor; eauto.

      + instantiate (1:= union news1 x1).
        apply Equal_eq; repeat autounfold with MapDefs; intros.
        specialize (H0 k0); destruct H0.
        * unfold find in H0; rewrite H0.
          unfold string_eq; destruct (string_dec _ _); reflexivity.
        * destruct (news1 k0).
          { unfold string_eq; destruct (string_dec _ _); [|reflexivity].
            subst; map_simpl H0; inv H0.
          }
          { unfold string_eq; destruct (string_dec _ _); reflexivity. }
      + apply IHa2; auto.
        * eexists; apply H13.
        * eapply Disj_add_2; eauto.

    - invertAction H5; inv H2; inv H6; destruct_existT.
      remember (evalExpr e) as cv; destruct cv; dest; subst.

      + simpl; eapply SemIfElseTrue.

        * auto.
        * eapply IHa2_1.
          { eexists; exact H15. }
          { instantiate (1:= x2); eapply Disj_union_1; eauto. }
          { admit. (* double-call problem *) }
          { instantiate (1:= x1); eapply Disj_union_1; eauto. }
          { assumption. }
          { exact H2. }
        * eapply H.
          { eapply WfmActionSem_init; eauto. }
          { instantiate (1:= x4); eapply Disj_union_2; eauto. }
          { admit. (* double-call problem *) }
          { instantiate (1:= x3); eapply Disj_union_2; eauto. }
          { assumption. }
          { exact H5. }
        * admit. (* double-state problem *)
        * admit. (* double-call problem *)

      + simpl; eapply SemIfElseFalse.

        * auto.
        * eapply IHa2_2.
          { eexists; exact H16. }
          { instantiate (1:= x2); eapply Disj_union_1; eauto. }
          { admit. (* double-call problem *) }
          { instantiate (1:= x1); eapply Disj_union_1; eauto. }
          { assumption. }
          { exact H2. }
        * eapply H.
          { eapply WfmActionSem_init; eauto. }
          { instantiate (1:= x4); eapply Disj_union_2; eauto. }
          { admit. (* double-call problem *) }
          { instantiate (1:= x3); eapply Disj_union_2; eauto. }
          { assumption. }
          { exact H5. }
        * admit. (* double-state problem *)
        * admit. (* double-call problem *)

    - invertAction H3; inv H2; inv H6; destruct_existT.
      simpl; econstructor; eauto.
      eapply IHa2; eauto; eexists; exact H12.

    - invertAction H3; simpl; map_simpl_G.
      map_simpl H4; inv H4.

  Qed.
  
  Lemma inlineDms_prop:
    forall dms olds1 olds2 retK2 a2 rules news1 news2 dmMap1 cmMap1 cmMap2
           (retV2: type retK2),
      SemAction olds2 a2 news2 cmMap2 retV2 ->
      dmMap1 = restrict cmMap2 (map (@attrName _) dms) ->
      SemMod rules olds1 None news1 dms dmMap1 cmMap1 ->
      SemAction (union olds1 olds2) (inlineDms a2 dms)
                (union news1 news2) (union cmMap1 (complement cmMap2 (map (@attrName _) dms)))
                retV2.
  Proof.
    admit.
  Qed.

  (* TODO: extend *)

End Preliminaries.

Section Facts.
  Variables (regs1 regs2: list RegInitT)
            (r1 r2: list (Attribute (Action type (Bit 0))))
            (dms1 dms2: list (DefMethT type)).

  Variable countdown: nat. (* TODO: weird *)

  Definition m1 := Mod regs1 r1 dms1.
  Definition m2 := Mod regs2 r2 dms2.

  Definition cm := ConcatMod m1 m2.
  Definition im := @inlineMod type countdown m1 m2.

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
          pose proof (inlineToRules_In countdown _ _ (dms1 ++ dms2) Hin).
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
    
    