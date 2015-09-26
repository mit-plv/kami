Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FnMap Syntax Semantics.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

Notation "m [ k |--> v ]" := (add k v m) (at level 0).
Notation "m [ k |-> v ]" := (m [k |--> {| objVal := v |}]) (at level 0).
Notation "v === m .[ k ]" := (find k m = Some {| objVal := v |}) (at level 70).

Notation "m ~{ k |-> v }" := ((fun a => if weq a k then v else m a) : type (Vector (Bit _) _)) (at level 0).

Fixpoint SymSemAction k (a : Action type k) (rs rs' : RegsT) (cs : CallsT) (kf : RegsT -> CallsT -> type k -> Prop) : Prop :=
  match a with
  | MCall meth s marg cont =>
    forall mret,
      cs meth = None
      /\ SymSemAction (cont mret) rs rs' cs[meth |-> (evalExpr marg, mret)] kf
  | Let_ _ e cont =>
    SymSemAction (cont (evalExpr e)) rs rs' cs kf
  | ReadReg r _ cont =>
    exists regV,
      regV === rs.[r]
      /\ SymSemAction (cont regV) rs rs' cs kf
  | WriteReg r _ e cont =>
    rs' r = None
    /\ SymSemAction cont rs rs'[r |-> evalExpr e] cs kf
  | IfElse p _ a a' cont =>
    if evalExpr p
    then SymSemAction a rs rs' cs (fun rs'' cs' rv =>
                                     SymSemAction (cont rv) rs rs'' cs' kf)
    else SymSemAction a' rs rs' cs (fun rs'' cs' rv =>
                                      SymSemAction (cont rv) rs rs'' cs' kf)
  | Assert_ p cont =>
    evalExpr p = true
    -> SymSemAction cont rs rs' cs kf
                                 
  | Return e => kf rs' cs (evalExpr e)
  end.

Lemma union_add : forall A k (v : A) m1 m2,
  m1 k = None
  -> union m1 m2[k |--> v] = union m1[k |--> v] m2.
Proof.
  unfold union, add, unionL; intros.
  extensionality k0.
  destruct (string_dec k k0); subst.
  rewrite string_dec_eq.
  rewrite H; auto.
  rewrite string_dec_neq by assumption.
  auto.
Qed.

Lemma union_assoc : forall A (a b c : @Map A),
  union a (union b c) = union (union a b) c.
Proof.
  unfold union, unionL; intros.
  extensionality k.
  destruct (a k); auto.
Qed.

Lemma double_find : forall T (v1 v2 : type T) m k,
  v1 === m.[k]
  -> v2 === m.[k]
  -> v1 = v2.
Proof.
  intros.
  rewrite H in H0.
  injection H0; intro.
  apply inj_pair2 in H1.
  auto.
Qed.

Lemma SymSemAction_sound' : forall k (a : Action type k) rs rs' cs' rv,
  SemAction rs a rs' cs' rv
  -> forall rs'' cs kf, SymSemAction a rs rs'' cs kf
    -> kf (union rs'' rs') (union cs cs') rv.
Proof.
  induction 1; simpl; intuition.

  specialize (H0 mret); intuition.
  eapply IHSemAction in H2.
  subst.
  rewrite union_add by assumption; auto.

  destruct H0; intuition.
  specialize (double_find _ _ HRegVal H1); intro; subst.
  apply IHSemAction; auto.

  apply IHSemAction in H2.
  subst.
  rewrite union_add in * by assumption; auto.

  rewrite HTrue in *.
  apply IHSemAction1 in H1.
  apply IHSemAction2 in H1.
  subst.
  repeat rewrite union_assoc; auto.

  rewrite HFalse in *.
  apply IHSemAction1 in H1.
  apply IHSemAction2 in H1.
  subst.
  repeat rewrite union_assoc; auto.

  apply IHSemAction; auto.

  repeat rewrite union_empty_2; congruence.
Qed.

Theorem SymSemAction_sound : forall k (a : Action type k) rs rs' cs rv,
  SemAction rs a rs' cs rv
  -> forall kf, SymSemAction a rs empty empty kf
    -> kf rs' cs rv.
Proof.
  intros.
  apply (SymSemAction_sound' H) in H0.
  repeat rewrite union_empty_1 in H0.
  auto.
Qed.

(* Considering method calls only.  We later build a version that considers trying a rule first, too. *)
Fixpoint SymSemMod_methods (dms : list (DefMethT type)) (rs rs' : RegsT) (dmeth cmeth : CallsT)
         (kf : RegsT -> CallsT -> CallsT -> Prop) : Prop :=
  match dms with
  | nil => kf rs' dmeth cmeth
  | meth :: dms' =>
    SymSemMod_methods dms' rs rs' dmeth cmeth kf
    /\ find (attrName meth) dmeth = None
    /\ forall argV, SymSemAction (objVal (attrType meth) argV) rs rs' cmeth
                                 (fun rs'' cmeth' retV =>
                                    SymSemMod_methods dms' rs rs'' dmeth[attrName meth |-> (argV, retV)] cmeth' kf)
  end.

(* Here's the version that also considers trying a rule first. *)
Fixpoint SymSemMod (dms : list (DefMethT type)) (rules : list (Attribute (Action type (Bit 0)))) (rs rs' : RegsT) (dmeth cmeth : CallsT)
         (kf : option string -> RegsT -> CallsT -> CallsT -> Prop) : Prop :=
  match rules with
  | nil => kf None rs' dmeth cmeth
           /\ SymSemMod_methods dms rs rs' dmeth cmeth (kf None)
  | rule :: rules' =>
    SymSemMod dms rules' rs rs' dmeth cmeth kf
    /\ SymSemAction (attrType rule) rs rs' cmeth
                    (fun rs'' cmeth' _ =>
                       SymSemMod_methods dms rs rs'' dmeth cmeth' (kf (Some (attrName rule))))
  end.

Fixpoint SymLtsStep (ms : Modules type) (rs : RegsT)
         (kf : option string -> RegsT -> CallsT -> CallsT -> Prop) : Prop :=
  match ms with
  | Mod regInits rules meths =>
    SymSemMod meths rules rs empty empty empty kf
  | ConcatMod m1 m2 =>
    (forall x, In x (map (@attrName _) (getRegInits m1))
               -> In x (map (@attrName _) (getRegInits m2))
               -> False)
    /\ SymLtsStep m1 (restrict rs (map (@attrName _) (getRegInits m1)))
    (fun rm rs1 dmeth1 cmeth1 =>
       SymLtsStep m2 (restrict rs (map (@attrName _) (getRegInits m2)))
                  (fun rm' rs2 dmeth2 cmeth2 =>
                     match match rm, rm' with Some _, Some _ => None | Some _, _ => Some rm | _, _ => Some rm' end with
                     | None => True
                     | Some rm'' =>
                       kf rm'' (disjUnion rs1 rs2 (map (@attrName _) (getRegInits m1)))
                          (disjUnion (complement dmeth1 (getCmsMod m2))
                                     (complement dmeth2 (getCmsMod m1))
                                     (listSub (getDmsMod m1) (getCmsMod m2)))
                          (disjUnion (complement cmeth1 (getDmsMod m2))
                                     (complement cmeth2 (getDmsMod m1))
                                     (listSub (getCmsMod m1) (getDmsMod m2)))
                     end))
  end.

Theorem SymSemMod_methods_sound : forall rules rs rm rs' meths dmeth cmeth,
  SemMod rules rs rm rs' meths dmeth cmeth
  -> forall rs'' dmeth' cmeth' kf, SymSemMod_methods meths rs rs'' dmeth' cmeth' kf
    -> rm = None
    -> kf (union rs'' rs') (union dmeth' dmeth) (union cmeth' cmeth).
Proof.
  induction 1; simpl; intuition subst; try discriminate.

  repeat rewrite union_empty_2; auto.

  eapply SymSemAction_sound' in HAction.
  2: eauto.
  simpl in *.
  apply IHSemMod in HAction; auto.
  repeat rewrite union_assoc.
  rewrite union_add by assumption.
  assumption.

  apply IHSemMod in H2; auto.
Qed.

Lemma SysSemMod_base : forall dms rules rs rs' dmeth cmeth kf,
  SymSemMod dms rules rs rs' dmeth cmeth kf
  -> kf None rs' dmeth cmeth.
Proof.
  induction rules; simpl; intuition.
  apply IHrules in H0; auto.
Qed.

Lemma SysSemMod_ind : forall dms rule rules rs rs' dmeth cmeth kf,
  SymSemMod dms rules rs rs' dmeth cmeth kf
  -> In rule rules
  -> SymSemAction (attrType rule) rs rs' cmeth
                  (fun rs'' cmeth' _ => SymSemMod_methods dms rs rs'' dmeth cmeth' (kf (Some (attrName rule)))).
Proof.
  induction rules; simpl; intuition (subst; auto).
Qed.

Theorem SymSemMod_sound : forall rules rs rm rs' meths dmeth cmeth,
  SemMod rules rs rm rs' meths dmeth cmeth
  -> forall rs'' dmeth' cmeth' kf, SymSemMod meths rules rs rs'' dmeth' cmeth' kf
    -> kf rm (union rs'' rs') (union dmeth' dmeth) (union cmeth' cmeth).
Proof.
  induction 1; simpl; intuition subst.

  repeat rewrite union_empty_2.
  eapply SysSemMod_base; eauto.

  eapply SysSemMod_ind in H0; eauto.
  simpl in *.
  eapply SymSemAction_sound' in H0; eauto.
  eapply SymSemMod_methods_sound in H0; eauto.
  repeat rewrite union_assoc.
  assumption.

  admit.

  admit.
Qed.

Lemma restrict_disjUnion_1 : forall A (m1 m2 : @Map A) ls,
  InDomain m1 ls
  -> restrict (disjUnion m1 m2 ls) ls = m1.
Proof.
  unfold InDomain, InMap, restrict, disjUnion, find; intros.
  extensionality k.
  specialize (H k).
  destruct (in_dec string_dec k ls); auto.
  destruct (m1 k); intuition congruence.
Qed.

Lemma restrict_disjUnion_2 : forall A (m1 m2 : @Map A) ls1 ls2,
  InDomain m2 ls2
  -> (forall x, In x ls1 -> find x m2 = None)
  -> (forall x, In x ls1 -> In x ls2 -> False)
  -> restrict (disjUnion m1 m2 ls1) ls2 = m2.
Proof.
  unfold InDomain, InMap, restrict, disjUnion, find; intros.
  extensionality k.
  specialize (H k); specialize (H0 k).
  destruct (in_dec string_dec k ls2), (in_dec string_dec k ls1); intuition auto.
  exfalso; eauto.
  destruct (m2 k); intuition congruence.
Qed.

Theorem SymLtsStep_sound : forall ms rm rs rs' dmeth cmeth,
  LtsStep ms rm rs rs' dmeth cmeth
  -> forall kf, SymLtsStep ms rs kf
    -> kf rm rs' dmeth cmeth.
Proof.
  induction 1; simpl; intros.

  eapply SymSemMod_sound in H; eauto.
  repeat rewrite union_empty_1 in H; assumption.

  hnf in HMerge; simpl in *; intuition subst.
  rewrite restrict_disjUnion_1 in H5 by assumption.
  apply IHLtsStep1 in H5.
  rewrite restrict_disjUnion_2 in H5; auto.
  2: intros; specialize (HOldRegs2 x); unfold InMap in HOldRegs2; destruct (find x olds2); auto;
  exfalso; eapply H4; eauto; intuition congruence.
  apply IHLtsStep2 in H5.
  hnf in H3; simpl in H3; subst.
  hnf in H7; simpl in H7; subst.
  hnf in H2; intuition subst.
  destruct rm2; auto.
  destruct rm1; auto.
Qed.
