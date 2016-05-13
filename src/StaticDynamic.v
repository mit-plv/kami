Require Import Syntax Semantics List Lib.Struct String Equiv FMap Program.Equality.

Set Implicit Arguments.

Fixpoint getRegWritesA k (a: ActionT (typeUT) k) :=
  match a with
  | MCall _ _ _ c => getRegWritesA (c tt)
  | Let_ fk e c => getRegWritesA
                     (c match fk as fk' return fullType typeUT fk' with
                        | SyntaxKind _ => tt
                        | NativeKind _ c' => c'
                        end)
  | ReadReg _ fk c => getRegWritesA
                        (c match fk as fk' return fullType typeUT fk' with
                           | SyntaxKind _ => tt
                           | NativeKind _ c' => c'
                           end)
  | WriteReg r _ _ c => r :: getRegWritesA c
  | IfElse _ _ aT aF c =>
    (getRegWritesA aT) ++ (getRegWritesA aF)
                       ++ (getRegWritesA (c tt))
  | Assert_ _ c => getRegWritesA c
  | Return _ => nil
    end.

Definition getRegWritesRule (r: Attribute (Action (Bit 0)))
  : list string :=
  (getRegWritesA (attrType r typeUT)).

Fixpoint getRegWritesMeth (m: DefMethT): list string :=
  (getRegWritesA ((projT2 (attrType m)) typeUT tt)).

Section EquivMod.
  Lemma regWritesSubsetA k ct (a1: ActionT type k) (a2: ActionT typeUT k):
    ActionEquiv ct a1 a2 ->
    forall o u cs r,
      SemAction o a1 u cs r ->
      forall x, M.In x u -> In x (getRegWritesA a2).
  Proof.
    intro ae.
    induction ae; fold type in *; fold typeUT in *; subst; intros.
    - dependent destruction H1.
      apply (H0 _ _ _ _ _ _ H1 x H2).
    - dependent destruction H1.
      specialize (H0 (evalExpr e1)).
      apply (H0 _ _ _ _ _ H1 x H2).
    - dependent destruction H1.
      apply (H0 _ _ _ _ _ _ H1 x H2).
    - dependent destruction H.
      specialize (@IHae _ _ _ _ H x).
      apply M.F.P.F.add_in_iff in H0.
      simpl in *.
      destruct H0; subst; intuition.
    - dependent destruction H1.
      apply M.union_In in H2.
      simpl in *.
      specialize (IHae1 _ _ _ _ H1_ x).
      specialize (H0 _ tt _ _ _ _ H1_0 x).
      destruct H2.
      + apply in_or_app.
        intuition.
      + apply in_or_app; right; apply in_or_app.
        intuition.
      + specialize (IHae2 _ _ _ _ H1_ x).
        specialize (H0 _ tt _ _ _ _ H1_0 x).
        simpl in *.
        apply M.union_In in H2.
        destruct H2;
          apply in_or_app; right; apply in_or_app;
            intuition.
    - dependent destruction H.
      apply (IHae _ _ _ _ H x H0).
    - dependent destruction H.
      apply M.F.P.F.empty_in_iff in H0; intuition.
  Qed.

  Lemma callsSubsetA k ct (a1: ActionT type k) (a2: ActionT typeUT k):
    ActionEquiv ct a1 a2 ->
    forall o u cs r,
      SemAction o a1 u cs r ->
      forall x, M.In x cs -> In x (getCallsA a2).
  Proof.
    intro ae.
    induction ae; fold type in *; fold typeUT in *; subst; intros.
    - dependent destruction H1.
      apply M.F.P.F.add_in_iff in H2.
      specialize (@H0 _ tt _ _ _ _ H1 x).
      simpl in *.
      destruct H2; subst; intuition.
    - dependent destruction H1.
      specialize (H0 (evalExpr e1)).
      apply (H0 _ _ _ _ _ H1 x H2).
    - dependent destruction H1.
      apply (H0 _ _ _ _ _ _ H1 x H2).
    - dependent destruction H.
      apply (@IHae _ _ _ _ H x H0).
    - dependent destruction H1.
      apply M.union_In in H2.
      simpl in *.
      specialize (IHae1 _ _ _ _ H1_ x).
      specialize (H0 _ tt _ _ _ _ H1_0 x).
      destruct H2.
      + apply in_or_app.
        intuition.
      + apply in_or_app; right; apply in_or_app.
        intuition.
      + specialize (IHae2 _ _ _ _ H1_ x).
        specialize (H0 _ tt _ _ _ _ H1_0 x).
        simpl in *.
        apply M.union_In in H2.
        destruct H2;
          apply in_or_app; right; apply in_or_app;
            intuition.
    - dependent destruction H.
      apply (IHae _ _ _ _ H x H0).
    - dependent destruction H.
      apply M.F.P.F.empty_in_iff in H0; intuition.
  Qed.

  Variable m: Modules.
  Variable modEquiv: ModEquiv type typeUT m.

  (* Lemma ruleEquiv rs: *)
  (*   RulesEquiv type typeUT rs -> *)
  (*   forall rName a, In (rName :: a)%struct rs -> *)
  (*                   ActionEquiv nil (a type) (a typeUT). *)
  (* Proof. *)
  (*   induction rs; intros; simpl in *. *)
  (*   - intuition. *)
  (*   - dependent destruction H0. *)
  (*     + subst. *)
  (*       dependent destruction H; *)
  (*         intuition. *)
  (*     + dependent destruction H. *)
  (*       apply (IHrs H0 _ _ H1). *)
  (* Qed. *)
        
  (* Lemma methEquiv ms: *)
  (*   MethsEquiv type typeUT ms -> *)
  (*   forall mName a, *)
  (*     In (mName :: a)%struct ms -> *)
  (*     (forall argV1 argV2 G, ActionEquiv G (projT2 a type argV1) (projT2 a typeUT argV2)). *)
  (* Proof. *)
  (*   induction ms; intros; simpl in *. *)
  (*   - intuition. *)
  (*   - dependent destruction H0. *)
  (*     + subst. *)
  (*       dependent destruction H; *)
  (*         intuition. *)
  (*     + dependent destruction H. *)
  (*       apply (IHms H0 _ _ H1). *)
  (* Qed. *)

  (* Lemma ruleEquivM rName a: *)
  (*   In (rName :: a)%struct (getRules m) -> *)
  (*   ActionEquiv nil (a type) (a typeUT). *)
  (* Proof. *)
  (*   destruct modEquiv. *)
  (*   apply (ruleEquiv H). *)
  (* Qed. *)

  (* Lemma methEquivM rName a: *)
  (*   In (rName :: a)%struct (getDefsBodies m) -> *)
  (*   forall argV1 argV2 G, ActionEquiv G (projT2 a type argV1) (projT2 a typeUT argV2). *)
  (* Proof. *)
  (*   destruct modEquiv. *)
  (*   apply (methEquiv H0). *)
  (* Qed. *)
  
  Lemma regWritesSubsetR:
    forall o u rName cs,
      Substep m o u (Rle (Some rName)) cs ->
      forall x, M.In x u -> exists a, In (rName :: a)%struct (getRules m) /\
                                      In x (getRegWritesA (a typeUT)).
  Proof.
    destruct modEquiv.
    clear modEquiv H0.
    intros.
    dependent destruction H0.
    exists a.
    constructor.
    intuition.
    pose proof (RulesEquiv_in _ _ nil H HInRules).
    apply (regWritesSubsetA H0 HAction); intuition.
  Qed.

  Lemma callsSubsetR:
    forall o u rName cs,
      Substep m o u (Rle (Some rName)) cs ->
      forall x, M.In x cs -> exists a, In (rName :: a)%struct (getRules m) /\
                                       In x (getCallsA (a typeUT)).
  Proof.
    destruct modEquiv.
    clear modEquiv H0.
    intros.
    dependent destruction H0.
    exists a.
    constructor.
    intuition.
    pose proof (RulesEquiv_in _ _ nil H HInRules).
    apply (callsSubsetA H0 HAction); intuition.
  Qed.

  Lemma regWritesSubsetM:
    forall o u mName argRet cs,
      Substep m o u (Meth (Some (mName :: argRet)%struct)) cs ->
      forall x, M.In x u -> exists a, In (mName :: a)%struct (getDefsBodies m) /\
                                      In x (getRegWritesA (projT2 a typeUT tt)).
  Proof.
    destruct modEquiv.
    clear modEquiv H.
    intros.
    dependent destruction H.
    destruct f.
    exists attrType.
    constructor.
    intuition.
    pose proof (MethsEquiv_in _ H0 HIn argV tt nil).
    apply (regWritesSubsetA H HAction); intuition.
  Qed.

  Lemma callsSubsetM:
    forall o u mName argRet cs,
      Substep m o u (Meth (Some (mName :: argRet)%struct)) cs ->
      forall x, M.In x cs -> exists a, In (mName :: a)%struct (getDefsBodies m) /\
                                      In x (getCallsA (projT2 a typeUT tt)).
  Proof.
    destruct modEquiv.
    clear modEquiv H.
    intros.
    dependent destruction H.
    destruct f.
    exists attrType.
    constructor.
    intuition.
    pose proof (MethsEquiv_in _ H0 HIn argV tt nil).
    apply (callsSubsetA H HAction); intuition.
  Qed.
End EquivMod.
