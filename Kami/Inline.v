Require Import Bool List String.
Require Import Lib.CommonTactics Lib.Struct.
Require Import Lib.ilist Lib.Word Lib.FMap Lib.StringEq.
Require Import Kami.Syntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Base.
  Variable type: Kind -> Type.

  Definition inlineArg {argT retT} (a: Expr type (SyntaxKind argT))
             (m: type argT -> ActionT type retT): ActionT type retT :=
    Let_ a m.
  
  Definition getBody (n: string) (dm: DefMethT) (sig: SignatureT):
    option (sigT (fun x: DefMethT => projT1 (attrType x) = sig)) :=
    if string_eq n (attrName dm) then
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
      | ReadNondet k cont => ReadNondet k (fun a => inlineDm (cont a) dm)
      | ReadReg reg k cont => ReadReg reg k (fun a => inlineDm (cont a) dm)
      | WriteReg reg _ e cont => WriteReg reg e (inlineDm cont dm)
      | IfElse ce _ ta fa cont => IfElse ce (inlineDm ta dm) (inlineDm fa dm)
                                         (fun a => inlineDm (cont a) dm)
      | Assert_ ae cont => Assert_ ae (inlineDm cont dm)
      | Displ ls cont => Displ ls (inlineDm cont dm)
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
    match getAttribute leaf (getDefsBodies m) with
      | Some dm =>
        (Mod (getRegInits m) (inlineDmToRules (getRules m) dm)
             (inlineDmToDms (getDefsBodies m) dm), noCallDm dm dm)
      | None => (m, false)
    end.

  Fixpoint inlineDms' (m: Modules) (dms: list string) :=
    match dms with
      | nil => (Mod (getRegInits m) (getRules m) (getDefsBodies m), true)
      | dm :: dms' =>
        let (im, ib) := inlineDmToMod m dm in
        let (im', ib') := inlineDms' im dms' in
        (im', ib && ib')
    end.

  Definition inlineDms (m: Modules) := inlineDms' m (namesOf (getDefsBodies m)).

  Definition inline (m: Modules) := inlineDms m.

  Definition inlineF (m: Modules) :=
    let (im, ib) := inline m in
    (Mod (getRegInits im) (getRules im)
         (filterDms (getDefsBodies im) (getCalls m)), noInternalCalls im && ib).
End Exts.

