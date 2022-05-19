Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringAsList Lib.StringEq.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.

Import ListNotations.

Set Implicit Arguments.

Section NativeFifo.
  Variable fifoName: string.
  
  Variable dType: Kind.
  Variable default: ConstT dType.

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition listEltT ty := list (ty dType).
  Definition listEltK ty := @NativeKind (listEltT ty) nil.
  Definition listElt ty := (^"elt" :: (@NativeConst (listEltT ty) nil nil))%struct.

  Definition listIsEmpty {ty} (l: fullType ty (listEltK ty)) :=
    match l with
    | nil => ConstBool true
    | _ => ConstBool false
    end.
  Definition listEnq {ty} (a: ty dType) (l: fullType ty (listEltK ty)) :=
    l ++ [a].
  Definition listDeq {ty} (l: fullType ty (listEltK ty)) :=
    match l with
    | nil => nil
    | h :: t => t
    end.
  Definition listFirstElt {ty} (l: fullType ty (listEltK ty)): Expr ty (SyntaxKind dType) :=
    match l with
    | nil => ($$default)%kami_expr
    | h :: t => (#h)%kami_expr
    end.

  (* defined methods *)
  Definition nativeEnq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (ReadN eltT : listEltK ty <- ^"elt";
     Write ^"elt" <- (Var _ (listEltK ty) (listEnq d eltT));
     Retv)%kami_action.

  Definition nativeDeq {ty} : ActionT ty dType :=
    (ReadN eltT : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty eltT);
     Write ^"elt" <- (Var _ (listEltK ty) (listDeq eltT));
     Ret (listFirstElt eltT))%kami_action.

  Definition nativeFirstElt {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
     Ret (listFirstElt elt))%kami_action.

  Definition nativeFifo := MODULE {
    RegisterN ^"elt" : listEltK type <- (NativeConst nil nil)

    with Method ^"enq"(d : dType) : Void := (nativeEnq d)
    with Method ^"deq"() : dType := nativeDeq
    with Method ^"firstElt"() : dType := nativeFirstElt
  }.

  Definition nativeSimpleFifo := MODULE {
    RegisterN ^"elt" : listEltK type <- (NativeConst nil nil)

    with Method ^"enq"(d : dType) : Void := (nativeEnq d)
    with Method ^"deq"() : dType := nativeDeq
  }.

End NativeFifo.

#[global] Hint Unfold nativeFifo nativeSimpleFifo : ModuleDefs.
#[global] Hint Unfold listEltT listEltK listElt
     (* listIsEmpty listEnq listDeq listFirstElt *)
     nativeEnq nativeDeq nativeFirstElt: MethDefs.

Section Facts.
  Variable fifoName: string.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Hypothesis (Hgood: index 0 indexSymbol fifoName = None).

  Lemma nativeFifo_ModEquiv:
    ModPhoasWf (nativeFifo fifoName default).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve nativeFifo_ModEquiv.

  Lemma nativeSimpleFifo_ModEquiv:
    ModPhoasWf (nativeSimpleFifo fifoName default).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve nativeSimpleFifo_ModEquiv.

  Lemma nativeFifo_ValidRegs:
    ModRegsWf (nativeFifo fifoName default).
  Proof.
    kvr.
  Qed.
  #[local] Hint Resolve nativeFifo_ValidRegs.

  Lemma nativeSimpleFifo_ValidRegs:
    ModRegsWf (nativeSimpleFifo fifoName default).
  Proof.
    kvr.
  Qed.
  #[local] Hint Resolve nativeSimpleFifo_ValidRegs.

End Facts.

#[global] Hint Resolve nativeFifo_ModEquiv nativeSimpleFifo_ModEquiv.
#[global] Hint Resolve nativeFifo_ValidRegs nativeSimpleFifo_ValidRegs.

