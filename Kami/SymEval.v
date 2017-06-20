Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.ilist Lib.FMap
        Kami.Syntax Kami.Semantics.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.
Set Asymmetric Patterns.

(*
Notation "m ~{ k |-> v }" := ((fun a => if weq a k%string then v else m a) : type (Vector (Bit _) _))
                               (at level 0).
*)

Open Scope fmap.

Definition getDefault k :=
  match k as k0 return match k0 with
                         | SyntaxKind k' => type k'
                         | NativeKind t c => t
                       end with
    | SyntaxKind k' => getDefaultConstNative k'
    | NativeKind t c => c
  end.

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
                                       | Slt _ => fun e => evalExpr e
                                       end e1)
                                      (match op in BinBitBoolOp n1' n2' return
                                             Expr type (SyntaxKind (Bit n2')) -> word n1' with
                                       | Lt _ => fun e => evalExpr e
                                       | Slt _ => fun e => evalExpr e
                                       end e2)
                        | Slt _ => wslt (match op in BinBitBoolOp n1' n2' return
                                               Expr type (SyntaxKind (Bit n1')) -> word n1' with
                                         | Lt _ => fun e => evalExpr e
                                         | Slt _ => fun e => evalExpr e
                                         end e1)
                                        (match op in BinBitBoolOp n1' n2' return
                                               Expr type (SyntaxKind (Bit n2')) -> word n1' with
                                         | Lt _ => fun e => evalExpr e
                                         | Slt _ => fun e => evalExpr e
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
           | ReadField _ _ fld val =>
             fun ise => evalExpr (ReadField fld val) = match eq_sym ise in _ = y return _ y with
                                                         | eq_refl => true
                                                       end
           | BuildVector _ _ _ => fun ise => _
           | BuildStruct _ _ _ => fun ise => _
           | UpdateVector _ _ _ _ _ => fun ise => _
         end; clear semExpr;
  try abstract (inversion ise).
Defined.

Fixpoint SymSemAction k (a : ActionT type k) (rs rs' : RegsT) (cs : MethsT) (kf : RegsT -> MethsT -> type k -> Prop) {struct a} : Prop :=
  match a with
  | MCall meth s marg cont =>
    match M.find meth cs with
      | None => forall mret, SymSemAction (cont mret) rs rs'
                                          cs#[meth |-> (evalExpr marg, mret)] kf
      | Some _ => False
    end
  | Let_ _ e cont =>
    SymSemAction (cont (evalExpr e)) rs rs' cs kf
  | ReadNondet k cont =>
    forall valueV,
      SymSemAction (cont valueV) rs rs' cs kf
  | ReadReg r k cont =>
    forall regV,
      regV === rs.[r] ->
      SymSemAction (cont regV) rs rs' cs kf
  | WriteReg r _ e cont =>
    match M.find r rs' with
      | None => SymSemAction cont rs rs'#[r |-> evalExpr e] cs kf
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
  | Assert_ p cont =>
    semExpr p eq_refl
    -> SymSemAction cont rs rs' cs kf
                                 
  | Return e => kf rs' cs (evalExpr e)
  end.

Lemma union_add : forall A k (v : A) m1 m2,
  M.find k m1 = None
  -> M.union m1 m2#[k |--> v] = M.union m1#[k |--> v] m2.
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
  Variable HReadField: forall n attrs fld e (tEq: SyntaxKind (Vector.nth (Vector.map (@attrType _) attrs) fld) =
                                                  SyntaxKind Bool),
                         P tEq (@ReadField type n attrs fld e).

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

Close Scope fmap.
