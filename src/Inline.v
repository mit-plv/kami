Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct Lib.StringBound Lib.ilist Lib.Word Lib.FMap.
Require Import Syntax Wf.

Set Implicit Arguments.

Section PhoasUT.
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
          (getCalls (projT2 (attrType dm) typeUT tt) cs)
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
      isLeaf (projT2 (attrType dm) typeUT tt) [attrName tgt].

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
      noCalls' m (getDefsBodies m).

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
    option (sigT (fun x: DefMethT => projT1 (attrType x) = sig)) :=
    if string_dec n (attrName dm) then
      match SignatureT_dec (projT1 (attrType dm)) sig with
        | left e => Some (existT _ dm e)
        | right _ => None
      end
    else None.

  Fixpoint inlineDm {retT} (a: ActionT type retT) (dm: DefMethT): ActionT type retT :=
    match a with
      | MCall name sig ar cont =>
        match getBody name dm sig with
          | Some (existT dm e) =>
            appendAction (inlineArg ar ((eq_rect _ _ (projT2 (attrType dm)) _ e)
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

  Lemma inlineDmToRules_app:
    forall r1 r2 leaf,
      inlineDmToRules (r1 ++ r2) leaf = inlineDmToRules r1 leaf ++ inlineDmToRules r2 leaf.
  Proof. intros; apply map_app. Qed.

  Definition inlineDmToDm (dm leaf: DefMethT): DefMethT.
    refine {| attrName := attrName dm;
              attrType := existT _ (projT1 (attrType dm))
                                 _ |}.
    unfold MethodT; intros.
    exact (inlineDm (projT2 (attrType dm) ty X) leaf).
  Defined.

  Definition inlineDmToDms (dms: list DefMethT) (leaf: DefMethT) :=
    map (fun d => inlineDmToDm d leaf) dms.

  Lemma inlineDmToDms_names:
    forall dms leaf, namesOf (inlineDmToDms dms leaf) = namesOf dms.
  Proof.
    induction dms; intros; auto.
    simpl; f_equal; auto.
  Qed.

  Lemma inlineDmToDms_app:
    forall d1 d2 leaf,
      inlineDmToDms (d1 ++ d2) leaf = inlineDmToDms d1 leaf ++ inlineDmToDms d2 leaf.
  Proof. intros; apply map_app. Qed.

  Definition inlineDmToMod (m: Modules) (leaf: string) :=
    if wfModules m then
      match getAttribute leaf (getDefsBodies m) with
        | Some dm =>
          if noCallDm dm dm then
            (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
                 (inlineDmToDms (getDefsBodies m) dm), true)
          else (m, false)
        | None => (m, false)
      end
    else (m, false).
  
  Fixpoint inlineDms' (m: Modules) (dms: list string) :=
    match dms with
      | nil => (m, true)
      | dm :: dms' =>
        let (im, ib) := inlineDmToMod m dm in
        if ib then
          inlineDms' im dms'
        else
          (im, false)
    end.

  Definition inlineDms (m: Modules) := inlineDms' m (namesOf (getDefsBodies m)).

  Definition inline (m: Modules) := inlineDms m.

  Definition inlineF (m: Modules) :=
    let (im, ib) := inline m in
    (Mod (getRegInits im) (getRules im)
         (filterDms (getDefsBodies im) (Syntax.getCalls m)), ib).
  
End Exts.

