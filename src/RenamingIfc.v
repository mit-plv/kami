Require Import Renaming String Program.Equality FunctionalExtensionality Semantics.

Section Inverse.
  Variable p: string -> string.
  Variable p1To1: forall x y, p x = p y -> x = y.
  Variable pOnto: forall x, exists y, p y = x.
  Variable pInv: string -> string.
  Variable pInvProp: forall s, pInv (p s) = s.

  Lemma renameActionInv k t a: renameAction pInv (renameAction (t := t) (k := k) p a) = a.
  Proof.
    dependent induction a; simpl in *; try rewrite pInvProp;
      f_equal; try apply functional_extensionality; assumption.
  Qed.

  Lemma renameRulesInv rs: renameRules pInv (renameRules p rs) = rs.
  Proof.
    induction rs; simpl in *.
    - reflexivity.
    - destruct a.
      rewrite IHrs.
      repeat f_equal.
      + rewrite pInvProp; reflexivity.
      + extensionality ty.
        apply renameActionInv.
  Qed.

  Lemma renameMethsInv meths: renameMeths pInv (renameMeths p meths) = meths.
  Proof.
    induction meths; simpl in *.
    - reflexivity.
    - destruct a.
      rewrite IHmeths.
      repeat f_equal.
      + rewrite pInvProp; reflexivity.
      + destruct attrType.
        repeat f_equal.
        simpl in *.
        extensionality ty.
        extensionality v.
        apply renameActionInv.
  Qed.

  Lemma renameModulesInv m: renameModules pInv (renameModules p m) = m.
  Proof.
    induction m; simpl in *.
    - rewrite renameRulesInv, renameMethsInv.
      f_equal.
      induction regs; simpl in *.
      + reflexivity.
      + rewrite IHregs.
        f_equal.
        destruct a; unfold renameAttr; simpl.
        repeat f_equal.
        apply pInvProp.
    - f_equal; assumption.
  Qed.

  Theorem traceEqvRename m: traceRefines (renameMap p (A := _)) m (renameModules p m) /\
                       traceRefines (renameMap pInv (A := _)) (renameModules p m) m.
  Proof.
    constructor.
    - apply traceRefinesRename.
    - rewrite <- renameModulesInv.
      apply traceRefinesRename.
  Qed.
End Inverse.