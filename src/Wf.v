Require Import Bool List String Structures.Equalities.
Require Import Lib.Struct Lib.Word Lib.CommonTactics Lib.StringBound Lib.ilist Lib.FnMap.
Require Import Syntax.
Require Import FunctionalExtensionality Program.Equality Eqdep Eqdep_dec.

Set Implicit Arguments.

(* Well-formedness w.r.t. structural hazards:
 * 1) No double-writes and 2) No double-calls for all actions in Modules
 *)
Section Wf1.
  Variable type: Kind -> Type.

  Fixpoint appendAction {retT1 retT2} (a1: ActionT type retT1)
           (a2: type retT1 -> ActionT type retT2): ActionT type retT2 :=
    match a1 with
      | MCall name sig ar cont => MCall name sig ar (fun a => appendAction (cont a) a2)
      | Let_ _ ar cont => Let_ ar (fun a => appendAction (cont a) a2)
      | ReadReg reg k cont => ReadReg reg k (fun a => appendAction (cont a) a2)
      | WriteReg reg _ e cont => WriteReg reg e (appendAction cont a2)
      | IfElse ce _ ta fa cont => IfElse ce ta fa (fun a => appendAction (cont a) a2)
      | Assert_ ae cont => Assert_ ae (appendAction cont a2)
      | Return e => Let_ e a2
    end.

  Lemma appendAction_assoc:
    forall {retT1 retT2 retT3}
           (a1: ActionT type retT1) (a2: type retT1 -> ActionT type retT2)
           (a3: type retT2 -> ActionT type retT3),
      appendAction a1 (fun t => appendAction (a2 t) a3) = appendAction (appendAction a1 a2) a3.
  Proof.
    induction a1; simpl; intuition idtac; f_equal; try extensionality x; eauto.
  Qed.

  Inductive WfAction: list string -> list string -> forall {retT}, ActionT type retT -> Prop :=
  | WfMCall:
      forall regs calls name sig ar {retT} cont (Hnin: ~ In name calls),
        (forall t, WfAction regs (name :: calls) (cont t)) ->
        WfAction regs calls (MCall (lretT:= retT) name sig ar cont)
  | WfLet:
      forall regs calls {argT retT} ar cont,
        (forall t, WfAction regs calls (cont t)) ->
        WfAction regs calls (Let_ (lretT':= argT) (lretT:= retT) ar cont)
  | WfReadReg:
      forall regs calls {retT} reg k cont,
        (forall t, WfAction regs calls (cont t)) ->
        WfAction regs calls (ReadReg (lretT:= retT) reg k cont)
  | WfWriteReg:
      forall regs calls {writeT retT} reg e cont (Hnin: ~ In reg regs),
        WfAction regs calls cont ->
        WfAction (reg :: regs) calls (WriteReg (k:= writeT) (lretT:= retT) reg e cont)
  | WfIfElse:
      forall regs calls {retT1 retT2} ce ta fa cont,
        WfAction regs calls (appendAction (retT1:= retT1) (retT2:= retT2) ta cont) ->
        WfAction regs calls (appendAction (retT1:= retT1) (retT2:= retT2) fa cont) ->
        WfAction regs calls (IfElse ce ta fa cont)
  | WfAssert:
      forall regs calls {retT} e cont,
        WfAction regs calls cont ->
        WfAction regs calls (Assert_ (lretT:= retT) e cont)
  | WfReturn:
      forall regs calls {retT} (e: Expr type (SyntaxKind retT)), WfAction regs calls (Return e).

  Inductive WfRules: list (Attribute (Action Void)) -> Prop :=
  | WfRulesNil: WfRules nil
  | WfRulesCons:
      forall rule rules,
        WfRules rules ->
        WfAction nil nil ((attrType rule) type) ->
        WfRules (rule :: rules).

  Inductive WfDms: list DefMethT -> Prop :=
  | WfDmsNil: WfDms nil
  | WfDmsCons:
      forall (dm: DefMethT) dms,
        WfDms dms ->
        (forall argV, WfAction nil nil (objVal (attrType dm) type argV)) ->
        WfDms (dm :: dms).

  Inductive WfModules: Modules -> Prop :=
  | WfMod:
      forall regs rules dms,
        WfRules rules -> WfDms dms -> WfModules (Mod regs rules dms)
  | WfConcatMod:
      forall m1 m2,
        WfModules m1 -> WfModules m2 -> WfModules (ConcatMod m1 m2).

End Wf1.


