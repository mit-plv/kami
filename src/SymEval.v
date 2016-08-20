Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FMap
        Syntax Semantics.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

Definition getDefault k :=
  match k as k0 return match k0 with
                         | SyntaxKind k' => type k'
                         | NativeKind t c => t
                       end with
    | SyntaxKind k' => getDefaultConstNative k'
    | NativeKind t c => c
  end.

Notation "m [ k |--> v ]" := (M.add k v m) (at level 0).
Notation "m [ k |-> v ]" := (m [k |--> existT _ _ v]) (at level 0).
Notation "v === m .[ k ]" := (M.find k m = Some (existT _ _ v)) (at level 70).
Notation "_=== m .[ k ]" := (M.find k m = None) (at level 70).

Notation "m ~{ k |-> v }" := ((fun a => if weq a k then v else m a) : type (Vector (Bit _) _))
                               (at level 0).

Definition or_wrap := or.

Definition and_wrap := and.

Fixpoint semExpr k (p: Expr type k): (k = SyntaxKind Bool) -> Prop.
  refine match p in Expr _ k' return k' = SyntaxKind Bool -> Prop with            
           | Var k' x => fun ise => (eq_rect k' (fullType type) x (SyntaxKind Bool) ise) = true
           | Const k' v => fun ise =>
                             (eq_rect (SyntaxKind k') (fullType type) (evalConstT v)
                                      (SyntaxKind Bool) ise) = true
           | UniBool Neg x => fun ise => semExpr _ x ise -> False
           | BinBool And x y => fun ise => semExpr _ x ise /\ semExpr _ y ise
           | BinBool Or x y => fun ise => or_wrap (semExpr _ x ise) (semExpr _ y ise)
           | UniBit _ _ _ _ => fun ise => _
           | BinBit _ _ _ _ _ _ => fun ise => _
           | BinBitBool n1 n2 op e1 e2 =>
             fun e => match op with
                        | Lt _ => wlt (match op in BinBitBoolOp n1' n2' return
                                             Expr type (SyntaxKind (Bit n1')) -> word n1' with
                                         | Lt _ => fun e => evalExpr e
                                       end e1)
                                      (match op in BinBitBoolOp n1' n2' return
                                             Expr type (SyntaxKind (Bit n2')) -> word n1' with
                                         | Lt _ => fun e => evalExpr e
                                       end e2)
                      end
           | ITE k' e1 e2 e3 => fun ise => (eq_rect k' (fullType type)
                                                    (evalExpr (ITE e1 e2 e3))
                                                    (SyntaxKind Bool) ise) = true
           | Eq k' e1 e2 => fun ise => evalExpr e1 = evalExpr e2
           | ReadIndex _ k' i f => fun ise => (eq_rect (SyntaxKind k')
                                                       (fullType type)
                                                       ((evalExpr f) (evalExpr i))
                                                       (SyntaxKind Bool) ise) = true
           | ReadField heading fld val =>
             fun ise => evalExpr (ReadField fld val) = match eq_sym ise in _ = y return _ y with
                                                         | eq_refl => true
                                                       end
             
             (*
             fun ise =>
               (eq_rect (SyntaxKind (GetAttrType fld)) (fullType type)
                        (mapAttrEq2 type fld
                                    ((evalExpr val) (getNewIdx2 type fld)))
                        (SyntaxKind Bool) ise) = true
              *)
              
           | BuildVector _ _ _ => fun ise => _
           | BuildStruct _ _ => fun ise => _
           | UpdateVector _ _ _ _ _ => fun ise => _
         end; clear semExpr;
  try abstract (inversion ise).
Defined.

Fixpoint SymSemAction k (a : ActionT type k) (rs rs' : RegsT) (cs : MethsT) (kf : RegsT -> MethsT -> type k -> Prop) {struct a} : Prop :=
  match a with
  | MCall meth s marg cont =>
    match M.find meth cs with
      | None => forall mret, SymSemAction (cont mret) rs rs'
                                          cs[meth |-> (evalExpr marg, mret)] kf
      | Some _ => False
    end
  | Let_ _ e cont =>
    SymSemAction (cont (evalExpr e)) rs rs' cs kf
  | ReadReg r k cont =>
    forall regV,
      regV === rs.[r] ->
      SymSemAction (cont regV) rs rs' cs kf
  | WriteReg r _ e cont =>
    match M.find r rs' with
      | None => SymSemAction cont rs rs'[r |-> evalExpr e] cs kf
      | Some _ => False
    end
  | IfElse p _ a a' cont =>
    (*
    IF_then_else
      (semExpr p eq_refl)
      (SymSemAction a rs rs' cs (fun rs'' cs' rv => SymSemAction (cont rv) rs rs'' cs' kf))
      (SymSemAction a' rs rs' cs (fun rs'' cs' rv => SymSemAction (cont rv) rs rs'' cs' kf))
     *)
    and_wrap
      (semExpr p eq_refl ->
       SymSemAction a rs rs' cs (fun rs'' cs' rv => SymSemAction (cont rv) rs rs'' cs' kf))
    ((semExpr p eq_refl -> False) ->
     SymSemAction a' rs rs' cs (fun rs'' cs' rv => SymSemAction (cont rv) rs rs'' cs' kf))
    (*
    if evalExpr p
    then SymSemAction a rs rs' cs (fun rs'' cs' rv =>
                                     SymSemAction (cont rv) rs rs'' cs' kf)
    else SymSemAction a' rs rs' cs (fun rs'' cs' rv =>
                                      SymSemAction (cont rv) rs rs'' cs' kf)
     *)
  | Assert_ p cont =>
    semExpr p eq_refl
    -> SymSemAction cont rs rs' cs kf
                                 
  | Return e => kf rs' cs (evalExpr e)
  end.

Lemma union_add : forall A k (v : A) m1 m2,
  M.find k m1 = None
  -> M.union m1 m2[k |--> v] = M.union m1[k |--> v] m2.
Proof.
  intros A k v m1.
  M.mind m1; meq.
Qed.

Lemma double_find : forall T (v1 v2 : fullType type T) m k,
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

(*
Hint Immediate Disj_union1 Disj_union2 Disj_add.
 *)

Section InductionBool.
  Variable P: forall k, k = SyntaxKind Bool -> Expr type k -> Prop.

  Variable HVar: forall v, P eq_refl (Var type (SyntaxKind Bool) v).
  Variable HConst: forall c, P eq_refl (Const type c).
  Variable HUniBool: forall op e, P eq_refl e -> P eq_refl (UniBool op e).
  Variable HBinBool: forall op e1 e2, P eq_refl e1 ->
                                      P eq_refl e2 -> P eq_refl (BinBool op e1 e2).
  Variable HBinBitBool: forall n1 n2 op e1 e2, P eq_refl (@BinBitBool type n1 n2 op e1 e2).
  Variable HITE: forall p e1 e2, P eq_refl e1 -> P eq_refl e2 ->
                                 P eq_refl (@ITE type (SyntaxKind Bool) p e1 e2).
  Variable HEq: forall k e1 e2, P eq_refl (@Eq type k e1 e2).
  Variable HReadIndex: forall i idx vec, P eq_refl (@ReadIndex type i _ idx vec).
  Variable HReadField: forall attrs attr e (tEq: SyntaxKind (GetAttrType attr) =
                                                 SyntaxKind Bool),
                         P tEq (@ReadField type attrs attr e).

  Lemma boolInduction: forall k (tEq: k = SyntaxKind Bool) (e: Expr type k),
                         P tEq e.
  Proof.
    induction e;
    progress (try (inversion tEq; subst;
                   replace tEq with (eq_refl (SyntaxKind Bool))
                     by (apply eq_sym; apply UIP_refl); auto);
              try subst; auto).
  Qed.
End InductionBool.

Lemma semExpr_sound: forall k (tEq: k = SyntaxKind Bool) (e: Expr type k),
                       (evalExpr e = match eq_sym tEq in _ = y return _ y with
                                       | eq_refl => true
                                     end <-> semExpr e tEq).
Proof.
  intros k tEq e.
  apply boolInduction with (k := k) (tEq := tEq) (e := e); intros; simpl in *;
  unfold or_wrap, and_wrap in *; intuition auto;
  repeat match goal with
           | H: negb _ = true |- _ => apply negb_true_iff in H
           | H: negb _ = false |- _ => apply negb_false_iff in H
           | H: andb _ _ = true |- _ => apply andb_true_iff in H
           | H: andb _ _ = false |- _ => apply andb_false_iff in H
           | H: orb _ _ = true |- _ => apply orb_true_iff in H
           | H: orb _ _ = false |- _ => apply orb_false_iff in H
           | H: ?q = true, H': ?r = false |- _ => rewrite H in H'; discriminate
           | |- negb _ = true => apply negb_true_iff
           | |- negb _ = false => apply negb_false_iff
           | |- andb _ _ = true => apply andb_true_iff
           | |- andb _ _ = false => apply andb_false_iff
           | |- orb _ _ = true => apply orb_true_iff
           | |- orb _ _ = false => apply orb_false_iff
           | |- context [match ?p with
                           | _ => _
                         end] => destruct p
           | H: context [match ?p with
                           | _ => _
                         end] |- _ => destruct p
           | _ => simpl in *; intros; try discriminate
         end; intuition auto.
  - rewrite H in H3; discriminate.
  - destruct (evalExpr e0);
    [specialize (H (H0 eq_refl)) |]; intuition auto.
Qed.


Lemma SymSemAction_sound' : forall k (a : ActionT type k) rs rs' cs' rv,
  SemAction rs a rs' cs' rv
  -> forall rs'' cs kf, SymSemAction a rs rs'' cs kf
    -> kf (M.union rs'' rs') (M.union cs cs') rv.
Proof.
  induction 1; simpl; unfold and_wrap; intuition auto.

  - subst.
    rewrite union_add by (destruct (M.find meth cs); intuition auto).
    case_eq (M.find meth cs); intros.
    rewrite H1 in H0; exfalso; assumption.
    rewrite H1 in H0.
    apply IHSemAction; auto.

  - apply IHSemAction; auto.

  - subst.
    case_eq (M.find r rs''); intros; subst; rewrite H1 in H0;
    [intuition auto | ].
    apply IHSemAction in H0; eauto.
    rewrite union_add; auto.

  - assert (sth: semExpr p eq_refl) by
        (apply semExpr_sound; simpl; auto).
    specialize (H2 sth); subst.
    apply IHSemAction1 in H2; eauto.
    apply IHSemAction2 in H2; eauto.
    repeat rewrite M.union_assoc; auto.
    
  - assert (sth: semExpr p eq_refl -> False) by
        (intros sth;
         apply semExpr_sound in sth;
         rewrite HFalse in sth; discriminate).
    specialize (H3 sth); subst.
    apply IHSemAction1 in H3; eauto.
    apply IHSemAction2 in H3; eauto.
    repeat rewrite M.union_assoc; auto.

  - assert (sth: semExpr p eq_refl) by
        (apply semExpr_sound; simpl; auto).
    specialize (H0 sth); subst.
    apply IHSemAction; auto.

  - repeat rewrite M.union_empty_R; congruence.
Qed.

Theorem SymSemAction_sound : forall k (a : ActionT type k) rs rs' cs rv,
  SemAction rs a rs' cs rv
  -> forall kf, SymSemAction a rs (M.empty _) (M.empty _) kf
    -> kf rs' cs rv.
Proof.
  intros.
  apply (SymSemAction_sound' H) in H0; auto.
Qed.

(*
(* Considering method calls only. 
   We later build a version that considers trying a rule first, too. *)
Fixpoint SymSemMod_methods (dms : list DefMethT) (rs rs' : RegsT) (dmeth cmeth : MethsT)
         (kf : RegsT -> MethsT -> MethsT -> Prop) : Prop :=
  match dms with
  | nil => kf rs' dmeth cmeth
  | meth :: dms' =>
    SymSemMod_methods dms' rs rs' dmeth cmeth kf
    /\ M.find (attrName meth) dmeth = None
    /\ forall argV, SymSemAction
                      (projT2 (attrType meth) _ argV) rs rs' rs' cmeth
                      (fun rs'' cmeth' retV =>
                         SymSemMod_methods dms' rs rs''
                                           dmeth[attrName meth |-> (argV, retV)] cmeth' kf)
  end.

(* Here's the version that also considers trying a rule first. *)
Fixpoint SymSemMod (dms : list (DefMethT type)) (rules : list (Attribute (Action type (Bit 0)))) (rs rs' : RegsT) (dmeth cmeth : CallsT)
         (kf : option string -> RegsT -> CallsT -> CallsT -> Prop) : Prop :=
  match rules with
  | nil => kf None rs' dmeth cmeth
           /\ SymSemMod_methods dms rs rs' dmeth cmeth (kf None)
  | rule :: rules' =>
    SymSemMod dms rules' rs rs' dmeth cmeth kf
    /\ SymSemAction (attrType rule) rs rs' rs' cmeth
                    (fun rs'' cmeth' _ =>
                       SymSemMod_methods dms rs rs'' dmeth cmeth' (kf (Some (attrName rule))))
  end.

Fixpoint SymMatchCalls (ls : list string) (cmeth dmeth : CallsT) (P : Prop) : Prop :=
  match ls with
  | nil => P
  | x :: ls' =>
    let rest := SymMatchCalls ls' cmeth dmeth P in
    match find x cmeth, find x dmeth with
    | Some _, None => True
    | Some call1, Some call2 => call1 = call2 -> rest
    | _, _ => rest
    end
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
                       SymMatchCalls (getDmsMod m2) cmeth1 dmeth2
                                     (SymMatchCalls (getDmsMod m1) cmeth2 dmeth1
                                                    (kf rm'' (disjUnion rs1 rs2 (map (@attrName _)
                                                                                     (getRegInits m1)))
                                                        (disjUnion (complement dmeth1 (getCmsMod m2))
                                                                   (complement dmeth2 (getCmsMod m1))
                                                                   (listSub (getDmsMod m1) (getCmsMod m2)))
                                                        (disjUnion (complement cmeth1 (getDmsMod m2))
                                                                   (complement cmeth2 (getDmsMod m1))
                                                                   (listSub (getCmsMod m1) (getDmsMod m2)))))
                     end))
  end.

Theorem Disj_uniony : forall A (a b c : @Map A),
  Disj a b
  -> Disj (union a b) c
  -> Disj b (union c a).
Proof.
  unfold Disj, union, unionL, find; intros.
  specialize (H k).
  specialize (H0 k).
  intuition auto.
  rewrite H1 in *; tauto.
  rewrite H; tauto.
Qed.

Hint Immediate Disj_uniony.

Theorem SymSemMod_methods_sound : forall rules rs rm rs' meths dmeth cmeth,
  SemMod rules rs rm rs' meths dmeth cmeth
  -> forall rs'' dmeth' cmeth' kf, SymSemMod_methods meths rs rs'' dmeth' cmeth' kf
    -> rm = None
    -> Disj rs' rs''
    -> kf (union rs'' rs') (union dmeth' dmeth) (union cmeth' cmeth).
Proof.
  induction 1; simpl; intuition subst; try discriminate.

  repeat rewrite union_empty_2; auto.

  eapply SymSemAction_sound' in HAction; eauto.
  simpl in *.
  apply IHSemMod in HAction; eauto.
  repeat rewrite union_assoc.
  rewrite union_add by assumption.
  assumption.

  eapply IHSemMod in H2; eauto.
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
  -> SymSemAction (attrType rule) rs rs' rs' cmeth
                  (fun rs'' cmeth' _ => SymSemMod_methods dms rs rs'' dmeth cmeth' (kf (Some (attrName rule)))).
Proof.
  induction rules; simpl; intuition (subst; auto).
Qed.

Theorem SymSemMod_sound : forall rules rs rm rs' meths dmeth cmeth,
  SemMod rules rs rm rs' meths dmeth cmeth
  -> forall rs'' dmeth' cmeth' kf, SymSemMod meths rules rs rs'' dmeth' cmeth' kf
    -> Disj rs' rs''
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

Lemma SymMatchCalls_sound : forall cmeth dmeth P ls,
  SymMatchCalls ls cmeth dmeth P
  -> (forall x, In x ls -> InMap x cmeth -> find x dmeth = find x cmeth)
  -> P.
Proof.
  induction ls; simpl; intuition.
  generalize (H0 a); intuition.
  unfold InMap in *.
  destruct (find a cmeth).
  rewrite H1 in * by discriminate.
  auto.
  destruct (find a cmeth); auto.
Qed.

(* This proof has been invalidated by a change to the semantics. *)

Theorem SymLtsStep_sound : forall ms rm rs rs' dmeth cmeth,
  LtsStep ms rm rs rs' dmeth cmeth
  -> forall kf, SymLtsStep ms rs kf
    -> kf rm rs' dmeth cmeth.
Admitted.
(*Proof.
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
  hnf in H1; simpl in H1; intuition.
  hnf in H2; intuition subst.
  destruct rm2; auto;
  (eapply SymMatchCalls_sound; [ eapply SymMatchCalls_sound | .. ]; eauto).
  destruct rm1; auto;
  (eapply SymMatchCalls_sound; [ eapply SymMatchCalls_sound | .. ]; eauto).
Qed.*)

*)