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

    Fixpoint getLeafFromDms' (tree tgt: list DefMethT): option DefMethT :=
      match tree with
        | nil => None
        | t :: tree' =>
          if isLeaf (objVal (attrType t) typeUT tt) (namesOf tgt)
          then Some t
          else getLeafFromDms' tree' tgt
      end.

    Definition getLeafFromDms (dms: list DefMethT) := getLeafFromDms' dms dms.

    Fixpoint getLeaf (m: Modules) :=
      match m with
        | Mod _ _ dms => getLeafFromDms dms
        | ConcatMod m1 m2 =>
          match getLeaf m1 with
            | Some lf => Some lf
            | _ => getLeaf m2
          end
      end.

    Fixpoint noCallsDms' (tree tgt: list DefMethT) :=
      match tree with
        | nil => true
        | t :: tree' =>
          if isLeaf (objVal (attrType t) typeUT tt) (namesOf tgt)
          then noCallsDms' tree' tgt
          else false
      end.

    Definition noCallsDms (dms: list DefMethT) := noCallsDms' dms dms.

    Fixpoint noCallsRules (rules: list (Attribute (Action Void))) (dms: list DefMethT) :=
      match rules with
        | nil => true
        | r :: rules' =>
          if isLeaf (attrType r typeUT) (namesOf dms)
          then noCallsRules rules' dms
          else false
      end.

    Fixpoint noCalls (m: Modules) :=
      match m with
        | Mod _ rules dms => (noCallsRules rules dms) && (noCallsDms dms)
        | ConcatMod m1 m2 => (noCalls m1) && (noCalls m2)
      end.

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

  Definition inlineOnce (m: Modules): Modules :=
    match getLeaf m with
      | Some lf => inlineDmToMod m lf
      | _ => m
    end.

  Fixpoint inline (m: Modules) (n: nat) :=
    match n with
      | O => m
      | S n' => inlineOnce (inline m n')
    end.

End Exts.

Require Import SemanticsNew.

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

  Lemma inline_correct_UnitStep:
    forall m or nr l n,
      UnitStep m or nr l ->
      noCalls (inline m n) = true ->
      wellHidden (hide l) m ->
      UnitStep (inline m n) or nr (hide l).
  Proof.
    induction 1; intros; simpl in *.

    - rewrite MF.subtractKV_empty_1 in *.
      admit. (* inline (Mod regInits ... ...) n = Mod regInit ... ...
              * Thus can apply EmptyStep
              *)

    - rewrite MF.subtractKV_empty_1, MF.subtractKV_empty_2 in *.
      admit.

    - admit.
    - admit.
    - admit.
  Qed.
  
  Lemma inline_correct_UnitSteps:
    forall m or nr l n,
      UnitSteps m or nr l ->
      noCalls (inline m n) = true ->
      wellHidden (hide l) m ->
      UnitSteps (inline m n) or nr (hide l).
  Proof.
    induction 1; intros.
    - apply UnitSteps1.
      apply inline_correct_UnitStep; auto.
    - erewrite hide_mergeLabel in *; eauto.
      pose proof (wellHidden_mergeLabel _ _ _ H0); dest.
      apply UnitStepsUnion; auto.
      apply hide_CanCombine; auto.
  Qed.

  Lemma inline_wellHidden:
    forall {A} (l: LabelTP A) m n,
      wellHidden l m ->
      wellHidden l (inline m n).
  Proof.
    induction n; intros; simpl in *; auto.
    admit.
  Qed.

  Theorem inline_correct:
    forall m or nr l n,
      Step m or nr l ->
      noCalls (inline m n) = true ->
      Step (inline m n) or nr l.
  Proof.
    induction 1; intros.
    subst; pose proof (inline_correct_UnitSteps n u H w).

    apply MkStep with (l:= hide l); auto.
    - apply hide_idempotent.
    - apply inline_wellHidden; auto.
  Qed.

End Facts.
