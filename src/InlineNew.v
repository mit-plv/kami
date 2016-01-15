Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FMap.
Require Import Syntax Wf Equiv.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section PhoasUT.
  Definition typeUT (k: Kind): Type := unit.
  Definition fullTypeUT := fullType typeUT.
  Definition getUT (k: FullKind): fullTypeUT k :=
    match k with
      | SyntaxKind _ => tt
      | NativeKind t c => c
    end.

  Fixpoint getCalls {retT} (a: ActionT typeUT retT) (cs: list DefMethT)
  : list DefMethT :=
    match a with
      | MCall name _ _ cont =>
        match getAttribute name cs with
          | Some dm => dm :: (getCalls (cont tt) cs)
          | None => getCalls (cont tt) cs
        end
      | Let_ _ ar cont => getCalls (cont (getUT _)) cs
      | ReadReg reg k cont => getCalls (cont (getUT _)) cs
      | WriteReg reg _ e cont => getCalls cont cs
      | IfElse ce _ ta fa cont =>
        (getCalls ta cs) ++ (getCalls fa cs) ++ (getCalls (cont tt) cs)
      | Assert_ ae cont => getCalls cont cs
      | Return e => nil
    end.

  Lemma getCalls_nil: forall {retT} (a: ActionT typeUT retT), getCalls a nil = nil.
  Proof.
    induction a; intros; simpl; intuition.
    rewrite IHa1, IHa2, (H tt); reflexivity.
  Qed.

  Lemma getCalls_sub: forall {retT} (a: ActionT typeUT retT) cs ccs,
                        getCalls a cs = ccs -> SubList ccs cs.
  Proof.
    induction a; intros; simpl; intuition; try (eapply H; eauto; fail).
    - simpl in H0.
      remember (getAttribute meth cs); destruct o.
      + pose proof (getAttribute_Some_body _ _ Heqo); subst.
        unfold SubList; intros.
        inv H0; [assumption|].
        eapply H; eauto.
      + eapply H; eauto.
    - simpl in H0; subst.
      unfold SubList; intros.
      apply in_app_or in H0; destruct H0; [|apply in_app_or in H0; destruct H0].
      + eapply IHa1; eauto.
      + eapply IHa2; eauto.
      + eapply H; eauto.
    - simpl in H; subst.
      unfold SubList; intros; inv H.
  Qed.

  Lemma getCalls_sub_name: forall {retT} (a: ActionT typeUT retT) cs ccs,
                             getCalls a cs = ccs -> SubList (namesOf ccs) (namesOf cs).
  Proof.
    induction a; intros; simpl; intuition; try (eapply H; eauto; fail).
    - simpl in H0.
      remember (getAttribute meth cs); destruct o.
      + pose proof (getAttribute_Some_body _ _ Heqo); subst.
        unfold SubList; intros.
        inv H0; [apply in_map; auto|].
        eapply H; eauto.
      + eapply H; eauto.
    - simpl in H0; subst.
      unfold SubList; intros.
      unfold namesOf in H0; rewrite map_app in H0.
      apply in_app_or in H0; destruct H0.
      + eapply IHa1; eauto.
      + rewrite map_app in H0; apply in_app_or in H0; destruct H0.
        * eapply IHa2; eauto.
        * eapply H; eauto.
    - simpl in H; subst.
      unfold SubList; intros; inv H.
  Qed.

  Section Exts.
    Definition getRuleCalls (r: Attribute (Action Void)) (cs: list DefMethT)
    : list DefMethT :=
      getCalls (attrType r typeUT) cs.

    Fixpoint getMethCalls (dms: list DefMethT) (cs: list DefMethT)
    : list DefMethT :=
      match dms with
        | nil => nil
        | dm :: dms' =>
          (getCalls (objVal (attrType dm) typeUT tt) cs)
            ++ (getMethCalls dms' cs)
      end.
  End Exts.

  Section Tree.
    Fixpoint isLeaf {retT} (a: ActionT typeUT retT) (cs: list string) :=
      match a with
        | MCall name _ _ cont =>
          if in_dec string_dec name cs then false else isLeaf (cont tt) cs
        | Let_ _ ar cont => isLeaf (cont (getUT _)) cs
        | ReadReg reg k cont => isLeaf (cont (getUT _)) cs
        | WriteReg reg _ e cont => isLeaf cont cs
        | IfElse ce _ ta fa cont => (isLeaf ta cs) && (isLeaf fa cs) && (isLeaf (cont tt) cs)
        | Assert_ ae cont => isLeaf cont cs
        | Return e => true
      end.

    Definition noCallDm (dm: DefMethT) (tgt: DefMethT) :=
      isLeaf (objVal (attrType dm) typeUT tt) [attrName tgt].

    Fixpoint noCallDms (dms: list DefMethT) (tgt: DefMethT) :=
      match dms with
        | nil => true
        | dm :: dms' =>
          if noCallDm dm tgt
          then noCallDms dms' tgt
          else false
      end.

    Fixpoint noCallRules (rules: list (Attribute (Action Void)))
             (tgt: DefMethT) :=
      match rules with
        | nil => true
        | r :: rules' =>
          if isLeaf (attrType r typeUT) [attrName tgt]
          then noCallRules rules' tgt
          else false
      end.

    Fixpoint noCall (m: Modules) (tgt: DefMethT) :=
      match m with
        | Mod _ rules dms =>
          (noCallRules rules tgt) && (noCallDms dms tgt)
        | ConcatMod m1 m2 => (noCall m1 tgt) && (noCall m2 tgt)
      end.

    Fixpoint noCalls' (m: Modules) (dms: list DefMethT) :=
      match dms with
        | nil => true
        | dm :: dms' =>
          (noCall m dm) && (noCalls' m dms')
      end.

    Definition noCalls (m: Modules) :=
      noCalls' m (getDmsBodies m).

  End Tree.

End PhoasUT.

Section Base.
  Variable type: Kind -> Type.

  Definition inlineArg {argT retT} (a: Expr type (SyntaxKind argT))
             (m: type argT -> ActionT type retT): ActionT type retT :=
    Let_ a m.

  Fixpoint getMethod (n: string) (dms: list DefMethT) :=
    match dms with
      | nil => None
      | {| attrName := mn; attrType := mb |} :: dms' =>
        if string_dec n mn then Some mb else getMethod n dms'
    end.
  
  Definition getBody (n: string) (dm: DefMethT) (sig: SignatureT):
    option (sigT (fun x: DefMethT => objType (attrType x) = sig)) :=
    if string_dec n (attrName dm) then
      match SignatureT_dec (objType (attrType dm)) sig with
        | left e => Some (existT _ dm e)
        | right _ => None
      end
    else None.

  Fixpoint inlineDm {retT} (a: ActionT type retT) (dm: DefMethT): ActionT type retT :=
    match a with
      | MCall name sig ar cont =>
        match getBody name dm sig with
          | Some (existT dm e) =>
            appendAction (inlineArg ar ((eq_rect _ _ (objVal (attrType dm)) _ e)
                                          type))
                         (fun ak => inlineDm (cont ak) dm)
          | None => MCall name sig ar (fun ak => inlineDm (cont ak) dm)
        end
      | Let_ _ ar cont => Let_ ar (fun a => inlineDm (cont a) dm)
      | ReadReg reg k cont => ReadReg reg k (fun a => inlineDm (cont a) dm)
      | WriteReg reg _ e cont => WriteReg reg e (inlineDm cont dm)
      | IfElse ce _ ta fa cont => IfElse ce (inlineDm ta dm) (inlineDm fa dm)
                                         (fun a => inlineDm (cont a) dm)
      | Assert_ ae cont => Assert_ ae (inlineDm cont dm)
      | Return e => Return e
    end.

End Base.

Section Exts.
  Definition inlineDmToRule (r: Attribute (Action Void)) (leaf: DefMethT)
  : Attribute (Action Void) :=
    {| attrName := attrName r;
       attrType := fun type => inlineDm (attrType r type) leaf |}.

  Definition inlineDmToRules (rules: list (Attribute (Action Void))) (leaf: DefMethT) :=
    map (fun r => inlineDmToRule r leaf) rules.

  Definition inlineDmToDm (dm leaf: DefMethT): DefMethT.
    refine {| attrName := attrName dm;
              attrType := {| objType := objType (attrType dm);
                             objVal := _ |} |}.
    unfold MethodT; intros.
    exact (inlineDm (objVal (attrType dm) ty X) leaf).
  Defined.

  Definition inlineDmToDms (dms: list DefMethT) (leaf: DefMethT) :=
    map (fun d => inlineDmToDm d leaf) dms.

  Fixpoint inlineDmToMod (m: Modules) (leaf: string) :=
    match getAttribute leaf (getDmsBodies m) with
      | Some dm =>
        if noCallDm dm dm then
          match m with
            | Mod regs rules dms =>
              Mod regs (inlineDmToRules rules dm) (inlineDmToDms dms dm)
            | ConcatMod m1 m2 =>
              ConcatMod (inlineDmToMod m1 leaf) (inlineDmToMod m2 leaf)
          end
        else m
      | None => m
    end.

  Lemma inlineDmToDms_getDmsMod:
    forall dms dm,
      namesOf dms = namesOf (inlineDmToDms dms dm).
  Proof.
    induction dms; intros; simpl; [reflexivity|].
    f_equal; apply IHdms.
  Qed.

  Fixpoint inlineDms' (m: Modules) (dms: list string) :=
    match dms with
      | nil => m
      | dm :: dms' => inlineDmToMod (inlineDms' m dms') dm
      (* | dm :: dms' => inlineDms' (inlineDmToMod m dm) dms' *)
    end.

  Definition inlineDms (m: Modules) := inlineDms' m (getDmsMod m).

  Definition inline (m: Modules) :=
    let im := inlineDms m in
    Mod (getRegInits im) (getRules im)
        (filter (fun dm => if in_dec string_dec (attrName dm) (getCmsMod m)
                           then false else true)
                (getDmsBodies im)).

End Exts.

Require Import SemanticsNew.

Section HideExts.
  Definition hideMeth {A} (l: LabelTP A) (dm: string): LabelTP A :=
    match M.find dm (dms l), M.find dm (cms l) with
      | Some v1, Some v2 =>
        match signIsEq v1 v2 with
          | left _ => {| ruleMeth := ruleMeth l;
                         dms := M.remove dm (dms l);
                         cms := M.remove dm (cms l) |}
          | _ => l
        end
      | _, _ => l
    end.

  Fixpoint hideMeths {A} (l: LabelTP A) (dms: list string): LabelTP A :=
    match dms with
      | nil => l
      | dm :: dms' => hideMeth (hideMeths l dms') dm
      (* | dm :: dms' => hideMeths (hideMeth l dm) dms' *)
    end.

  Definition wellHiddenMeth {A} (l: LabelTP A) (dm: string) :=
    M.find dm (dms l) = None /\ M.find dm (cms l) = None.

  Lemma hideMeth_preserves_hide:
    forall {A} (l: LabelTP A) dm,
      hide (hideMeth l dm) = hide l.
  Proof.
    intros; destruct l as [rm dms cms].
    admit.
  Qed.

  Lemma wellHidden_wellHiddenMeth:
    forall {A} m (l: LabelTP A) dm,
      In dm (getDmsMod m) ->
      wellHidden (hide l) m ->
      wellHiddenMeth (hideMeth l dm) dm.
  Proof.
    admit.
  Qed.

  Lemma wellHiddenMeth_find:
    forall {A} (l: LabelTP A) dm,
      wellHiddenMeth (hideMeth l dm) dm <->
      M.find dm (dms l) = M.find dm (cms l).
  Proof.
    admit. (* easy *)
  Qed.

  (* Lemma hideMeth_mergeLabel: *)
  (*   forall {A} (l1 l2: LabelTP A) dm, *)
  (*     hideMeth (mergeLabel l1 l2) dm = *)
  (*     mergeLabel (hideMeth l1 dm) (hideMeth l2 dm). *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)

  (* Lemma hideMeth_CanCombine: *)
  (*   forall u1 u2 l1 l2 dm, *)
  (*     CanCombine (u1, l1) (u2, l2) -> *)
  (*     CanCombine (u1, hideMeth l1 dm) (u2, hideMeth l2 dm). *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)

End HideExts.

Section Facts.

  Lemma noCalls_UnitSteps_hide:
    forall l m or nr,
      UnitSteps m or nr l ->
      noCalls m = true ->
      hide l = l.
  Proof.
    admit. (* Semantics proof *)
  Qed.

  Lemma hide_idempotent:
    forall {A} (l: LabelTP A), hide l = hide (hide l).
  Proof.
    admit. (* Semantics proof *)
  Qed.

  (* Lemma inlineDmToMod_correct_UnitStep: *)
  (*   forall m or nr l (dm: DefMethT), *)
  (*     UnitStep m or nr l -> *)
  (*     M.find (elt:=Typed Semantics.SignT) dm (dms l) = *)
  (*     M.find (elt:=Typed Semantics.SignT) dm (cms l) -> *)
  (*     UnitStep (inlineDmToMod m dm) or nr (hideMeth l dm). *)
  (* Proof. *)
  (*   admit. *)
  (* Qed. *)

  Lemma inlineDmToMod_correct_UnitSteps_sub:
    forall m or u1 u2 rm1 rm2 dm1 dm2 cm1 cm2 (dm: DefMethT) t l1 l2,
      l1 = {| ruleMeth := rm1; dms := dm1; cms := cm1 |} ->
      l2 = {| ruleMeth := rm2; dms := dm2; cms := cm2 |} ->
      UnitSteps m or u1 l1 -> UnitSteps m or u2 l2 ->
      MF.Disj u1 u2 -> NotBothRule rm1 rm2 -> MF.Disj dm1 dm2 -> MF.Disj cm1 cm2 ->
      Some t = M.find dm dm1 -> Some t = M.find dm cm2 ->
      UnitSteps (inlineDmToMod m dm) or (MF.union u1 u2)
                {| ruleMeth := match rm1 with
                                 | Some r => Some r
                                 | None => rm2
                               end;
                   dms := M.remove (elt:=Typed Semantics.SignT) dm (MF.union dm1 dm2);
                   cms := M.remove (elt:=Typed Semantics.SignT) dm (MF.union cm1 cm2) |}.
  Proof.
    admit.
  Qed.

  Lemma inlineDmToMod_correct_UnitSteps:
    forall m or nr l (dm: DefMethT),
      In dm (getDmsBodies m) -> noCallDm dm dm = true ->
      UnitSteps m or nr l ->
      M.find dm (dms l) = M.find dm (cms l) ->
      UnitSteps (inlineDmToMod m dm) or nr (hideMeth l dm).
  Proof.
    induction 3; intros.

    - exfalso. admit.

    - destruct l1 as [rm1 dm1 cm1], l2 as [rm2 dm2 cm2]; simpl in *.
      remember (M.find dm (MF.union dm1 dm2)) as odmv.
      destruct odmv.

      + unfold hideMeth; simpl.
        rewrite <-Heqodmv, <-H1; simpl.
        destruct (signIsEq t t); [clear e|elim n; auto].
        (* ??? *)
        unfold CanCombine in c; dest; simpl in *.
        rewrite MF.find_union in Heqodmv; rewrite MF.find_union in H1.
        remember (M.find dm dm1) as odmv1; destruct odmv1.

        * inv Heqodmv.
          remember (M.find dm cm1) as ocmv1; destruct ocmv1.
          { inv H1; specialize (IHX1 eq_refl).
            admit. (* one-side inlined *)
          }
          { eapply inlineDmToMod_correct_UnitSteps_sub; eauto. }

        * remember (M.find dm cm1) as ocmv1; destruct ocmv1.
          { clear IHX1 IHX2; inv H1.
            replace (MF.union u1 u2) with (MF.union u2 u1)
              by (apply MF.union_comm; apply MF.Disj_comm; auto).
            replace (match rm1 with | Some r => Some r | None => rm2 end) with
            (match rm2 with | Some r => Some r | None => rm1 end)
              by (destruct rm1, rm2; intuition idtac; destruct H3; discriminate).
            replace (MF.union dm1 dm2) with (MF.union dm2 dm1)
              by (apply MF.union_comm; apply MF.Disj_comm; auto).
            replace (MF.union cm1 cm2) with (MF.union cm2 cm1)
              by (apply MF.union_comm; apply MF.Disj_comm; auto).
            eapply inlineDmToMod_correct_UnitSteps_sub; eauto; try (apply MF.Disj_comm; auto).
            destruct H3; unfold NotBothRule; intuition auto.
          }
          { specialize (IHX1 eq_refl).
            admit. (* one-side inlined *)
          }

      + unfold hideMeth in *; simpl in *; rewrite <-Heqodmv.
        rewrite MF.find_union in Heqodmv.
        destruct (M.find dm dm1); [discriminate|].
        destruct (M.find dm dm2); [discriminate|].
        rewrite MF.find_union in H1.
        destruct (M.find dm cm1); [discriminate|].
        destruct (M.find dm cm2); [discriminate|].
        specialize (IHX1 eq_refl); specialize (IHX2 eq_refl).

        match goal with
            [ |- UnitSteps _ _ _ ?l] =>
            replace l with (mergeLabel {| ruleMeth:= rm1; dms:= dm1; cms:= cm1 |}
                                       {| ruleMeth:= rm2; dms:= dm2; cms:= cm2 |})
              by reflexivity
        end.
        apply UnitStepsUnion; auto.
  Qed.

  Lemma inlineDmToMod_wellHidden:
    forall {A} (l: LabelTP A) m a,
      wellHidden l m ->
      wellHidden l (inlineDmToMod m a).
  Proof.
    admit. (* Inlining proof *)
  Qed.

  Lemma inlineDms'_correct_UnitSteps:
    forall cdms m or nr l,
      UnitSteps m or nr l ->
      (* noCalls (inlineDms' m cdms) = true -> *)
      wellHidden (hide l) m ->
      UnitSteps (inlineDms' m cdms) or nr (hideMeths l cdms).
  Proof.
    induction cdms; [auto|].
    intros; simpl.
    admit. (* TODO: hideMeths also needs "m" to check
            * if inline' really does inlining or not
            *)
    
    (* induction cdms; [auto|]. *)
    (* intros; simpl in *. *)
    (* apply SubList_cons_inv in Hcdms; dest. *)

    (* specialize (@IHcdms m or nr l H1 X H). *)
    (* apply inlineDmToMod_correct_UnitSteps; auto. *)

    (* assert (hide (hideMeth l a) = hide l). *)
    (* { eapply hideMeth_preserves_hide; eauto. } *)
    (* rewrite H3 in *; clear H3. *)

    (* apply IHcdms; auto. *)
    (* - apply inlineDmToMod_correct_UnitSteps; auto. *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + apply wellHiddenMeth_find. *)
    (*     eapply wellHidden_wellHiddenMeth; eauto. *)
    (*     admit. *)
    (* - apply inlineDmToMod_wellHidden; auto. *)
  Qed.

  Lemma hideMeths_UnitSteps_hide:
    forall m or nr l,
      UnitSteps m or nr l ->
      hideMeths l (getDmsMod m) = hide l.
  Proof.
    admit.
  Qed.

  Lemma inlineDms_correct_UnitSteps:
    forall m or nr l,
      UnitSteps m or nr l ->
      noCalls (inlineDms m) = true ->
      wellHidden (hide l) m ->
      UnitSteps (inlineDms m) or nr (hide l).
  Proof.
    intros.
    erewrite <-hideMeths_UnitSteps_hide; eauto.
    apply inlineDms'_correct_UnitSteps; auto.
  Qed.

  Lemma inlineDms_wellHidden:
    forall {A} (l: LabelTP A) m,
      wellHidden l m ->
      wellHidden l (inlineDms m).
  Proof.
    intros; unfold inlineDms.
    remember (getDmsMod m) as dms; clear Heqdms.
    generalize dependent m; induction dms; intros; [assumption|].
    apply inlineDmToMod_wellHidden; auto.
  Qed.

  Lemma inlineDms_correct:
    forall m or nr l,
      Step m or nr l ->
      noCalls (inlineDms m) = true ->
      Step (inlineDms m) or nr l.
  Proof.
    induction 1; intros.
    subst; pose proof (inlineDms_correct_UnitSteps u H w).

    apply MkStep with (l:= hide l); auto.
    - apply hide_idempotent.
    - apply inlineDms_wellHidden; auto.
  Qed.

  Lemma merge_preserves_step:
    forall m or nr l,
      Step m or nr l ->
      Step (Mod (getRegInits m) (getRules m) (getDmsBodies m)) or nr l.
  Proof.
    admit.
  Qed.

  Theorem inline_correct:
    forall m or nr l,
      Step m or nr l ->
      noCalls (inlineDms m) = true -> (* TODO: necessary? *)
      Step (inline m) or nr l.
  Proof.
    intros; pose proof (inlineDms_correct X H).
    pose proof (merge_preserves_step X0).
    unfold inline.
    admit. (* By "Step m or nr l", Domain(cms l) -*- (getCmsMod m) *)
  Qed.

End Facts.

