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
    - dependent destruction H0.
      specialize (@IHae _ _ _ _ H0 x).
      apply M.F.P.F.add_in_iff in H1.
      simpl in *.
      destruct H1; subst; intuition.
    - dependent destruction H2.
      apply M.union_In in H3.
      simpl in *.
      specialize (IHae1 _ _ _ _ H2_ x).
      specialize (H1 _ tt _ _ _ _ H2_0 x).
      destruct H3.
      + apply in_or_app.
        intuition.
      + apply in_or_app; right; apply in_or_app.
        intuition.
      + specialize (IHae2 _ _ _ _ H2_ x).
        specialize (H1 _ tt _ _ _ _ H2_0 x).
        simpl in *.
        apply M.union_In in H3.
        destruct H3;
          apply in_or_app; right; apply in_or_app;
            intuition.
    - dependent destruction H0.
      apply (IHae _ _ _ _ H0 x H1).
    - dependent destruction H0.
      apply M.F.P.F.empty_in_iff in H1; intuition.
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
    - dependent destruction H0.
      apply (@IHae _ _ _ _ H0 x H1).
    - dependent destruction H2.
      apply M.union_In in H3.
      simpl in *.
      specialize (IHae1 _ _ _ _ H2_ x).
      specialize (H1 _ tt _ _ _ _ H2_0 x).
      destruct H3.
      + apply in_or_app.
        intuition.
      + apply in_or_app; right; apply in_or_app.
        intuition.
      + specialize (IHae2 _ _ _ _ H2_ x).
        specialize (H1 _ tt _ _ _ _ H2_0 x).
        simpl in *.
        apply M.union_In in H3.
        destruct H3;
          apply in_or_app; right; apply in_or_app;
            intuition.
    - dependent destruction H0.
      apply (IHae _ _ _ _ H0 x H1).
    - dependent destruction H0.
      apply M.F.P.F.empty_in_iff in H1; intuition.
  Qed.
End EquivMod.
