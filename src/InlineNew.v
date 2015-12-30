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

    Fixpoint noCallDms (dms: list DefMethT) (tgt: DefMethT) :=
      match dms with
        | nil => true
        | dm :: dms' =>
          if isLeaf (objVal (attrType dm) typeUT tt) [attrName tgt]
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

  Fixpoint inlineDmToMod (m: Modules) (leaf: DefMethT) :=
    match m with
      | Mod regs rules dms =>
        Mod regs (inlineDmToRules rules leaf) (inlineDmToDms dms leaf)
      | ConcatMod m1 m2 =>
        ConcatMod (inlineDmToMod m1 leaf) (inlineDmToMod m2 leaf)
    end.

  Fixpoint inline' (m: Modules) (dms: list DefMethT) :=
    match dms with
      | nil => m
      | dm :: dms' => inline' (inlineDmToMod m dm) dms'
    end.

  Definition inline (m: Modules) := inline' m (getDmsBodies m).

End Exts.

Require Import SemanticsNew.

Section HideExts.
  Definition hideMeth {A} (l: LabelTP A) (dm: DefMethT): LabelTP A :=
    {| ruleMeth := ruleMeth l;
       dms := M.remove (attrName dm) (dms l);
       cms := M.remove (attrName dm) (cms l)
    |}.

  Lemma hideMeth_preserves_hide:
    forall {A} m (l: LabelTP A) dm,
      In dm (getDmsBodies m) ->
      wellHidden (hide l) m ->
      hide (hideMeth l dm) = hide l.
  Proof.
    admit.
  Qed.

End HideExts.

Section Facts.

  Lemma noCalls_UnitSteps_hide:
    forall m or nr l,
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

  Lemma hide_mergeLabel:
    forall u1 u2 l1 l2,
      CanCombine (u1, l1) (u2, l2) ->
      hide (mergeLabel l1 l2) = mergeLabel (hide l1) (hide l2).
  Proof.
    admit. (* Semantics proof *)
  Qed.

  Lemma hide_CanCombine:
    forall u1 u2 l1 l2,
      CanCombine (u1, l1) (u2, l2) ->
      CanCombine (u1, hide l1) (u2, hide l2).
  Proof.
    admit. (* Semantics proof *)
  Qed.

  Lemma wellHidden_mergeLabel:
    forall {A} (l1 l2: LabelTP A) m,
      wellHidden (mergeLabel l1 l2) m ->
      wellHidden l1 m /\ wellHidden l2 m.
  Proof.
    admit. (* Semantics proof *)
  Qed.

  Lemma inlineDmToMod_correct_UnitSteps:
    forall m or nr l dm,
      UnitSteps m or nr l ->
      UnitSteps (inlineDmToMod m dm) or nr (hideMeth l dm).
  Proof.
    admit.
  Qed.

  Lemma inlineDmToMod_wellHidden:
    forall {A} (l: LabelTP A) m a,
      wellHidden l m ->
      wellHidden l (inlineDmToMod m a).
  Proof.
    admit.
  Qed.

  Lemma inline'_correct_UnitSteps:
    forall dms m or nr l,
      UnitSteps m or nr l ->
      noCalls (inline' m dms) = true ->
      wellHidden (hide l) m ->
      UnitSteps (inline' m dms) or nr (hide l).
  Proof.
    induction dms; intros; simpl in *.
    - rewrite (noCalls_UnitSteps_hide X H); auto.
    - specialize (@IHdms (inlineDmToMod m a) or nr (hideMeth l a)).

      assert (hide (hideMeth l a) = hide l).
      { eapply hideMeth_preserves_hide; eauto using H0.
        admit. (* TODO: bring information from a higher lemma *)
      }
      rewrite H1 in *; clear H1.

      apply IHdms; auto.
      + apply inlineDmToMod_correct_UnitSteps; auto.
      + apply inlineDmToMod_wellHidden; auto.
  Qed.

  Lemma inline_correct_UnitSteps:
    forall m or nr l,
      UnitSteps m or nr l ->
      noCalls (inline m) = true ->
      wellHidden (hide l) m ->
      UnitSteps (inline m) or nr (hide l).
  Proof.
    intros; apply inline'_correct_UnitSteps; auto.
  Qed.

  Lemma inline_wellHidden:
    forall {A} (l: LabelTP A) m,
      wellHidden l m ->
      wellHidden l (inline m).
  Proof.
    intros; unfold inline.
    remember (getDmsBodies m) as dms; clear Heqdms.
    generalize dependent m; induction dms; intros; [assumption|].
    simpl; apply IHdms.
    apply inlineDmToMod_wellHidden; auto.
  Qed.

  Theorem inline_correct:
    forall m or nr l,
      Step m or nr l ->
      noCalls (inline m) = true ->
      Step (inline m) or nr l.
  Proof.
    induction 1; intros.
    subst; pose proof (inline_correct_UnitSteps u H w).

    apply MkStep with (l:= hide l); auto.
    - apply hide_idempotent.
    - apply inline_wellHidden; auto.
  Qed.

End Facts.
