Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Notations Lts.Semantics Lts.Equiv Lts.Tactics.

Set Implicit Arguments.

Section NativeFifo.
  Variable fifoName: string.
  
  Variable dType: Kind.
  Variable default: ConstT dType.

  Notation "^ s" := (fifoName -- s) (at level 0).

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
    (ReadN elt : listEltK ty <- ^"elt";
     Write ^"elt" <- (Var _ (listEltK ty) (listEnq d elt));
     Retv)%kami_action.

  Definition nativeDeq {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
     Write ^"elt" <- (Var _ (listEltK ty) (listDeq elt));
     Ret (listFirstElt elt))%kami_action.

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

  (** SinAction version *)
  Hypothesis HfifoName: index 0 indexSymbol fifoName = None.
  Lemma ngn:
    forall s, index 0 indexSymbol s = None -> index 0 indexSymbol (^s) = None.
  Proof.
    pose proof HfifoName.
    admit.
  Qed.

  Definition nativeEnqS {ty} : forall (d: ty dType), SinActionT ty Void := fun d =>
    (ReadN elt : listEltK ty <- { ^"elt" | ngn "elt" eq_refl };
     Write { ^"elt" | ngn "elt" eq_refl } <- (Var _ (listEltK ty) (listEnq d elt));
     Retv)%kami_sin.

  Definition nativeDeqS {ty} : SinActionT ty dType :=
    (ReadN elt : listEltK ty <- { ^"elt" | ngn "elt" eq_refl };
     Assert !$$(listIsEmpty elt);
     Write { ^"elt" | ngn "elt" eq_refl } <- (Var _ (listEltK ty) (listDeq elt));
     Ret (listFirstElt elt))%kami_sin.

  Definition nativeFirstEltS {ty} : SinActionT ty dType :=
    (ReadN elt : listEltK ty <- { ^"elt" | ngn "elt" eq_refl };
     Assert !$$(listIsEmpty elt);
     Ret (listFirstElt elt))%kami_sin.
  
  Definition nativeFifoS := META {
    RegisterN { ^"elt" | ngn "elt" eq_refl } : listEltK type <- (NativeConst nil nil)

    with Method { ^"enq" | ngn "enq" eq_refl } (d : dType) : Void := (nativeEnqS d)
    with Method { ^"deq" | ngn "deq" eq_refl } () : dType := nativeDeqS
    with Method { ^"firstElt" | ngn "firstElt" eq_refl } () : dType := nativeFirstEltS
  }.

  Definition nativeSimpleFifoS := META {
    RegisterN { ^"elt" | ngn "elt" eq_refl } : listEltK type <- (NativeConst nil nil)

    with Method { ^"enq" | ngn "enq" eq_refl } (d : dType) : Void := (nativeEnqS d)
    with Method { ^"deq" | ngn "deq" eq_refl } () : dType := nativeDeqS
  }.
  
End NativeFifo.

Hint Unfold nativeFifo nativeSimpleFifo : ModuleDefs.
Hint Unfold listEltT listEltK listElt
     listIsEmpty listEnq listDeq listFirstElt
     nativeEnq nativeDeq nativeFirstElt: MethDefs.

Hint Unfold nativeFifoS nativeSimpleFifoS : ModuleDefs.
Hint Unfold nativeEnqS nativeDeqS nativeFirstEltS: MethDefs.

Section Facts.
  Variable fifoName: string.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Hypothesis HfifoName: index 0 indexSymbol fifoName = None.

  Lemma nativeFifo_nativeFifoS:
    nativeFifo fifoName default =
    ParametricSyntax.makeModule (nativeFifoS fifoName default HfifoName).
  Proof. reflexivity. Qed.

  Lemma nativeSimpleFifo_nativeSimpleFifoS:
    nativeSimpleFifo fifoName default =
    ParametricSyntax.makeModule (nativeSimpleFifoS fifoName default HfifoName).
  Proof. reflexivity. Qed.

  Lemma nativeFifo_ModEquiv:
    forall m,
      m = nativeFifo fifoName default ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.

  Lemma nativeSimpleFifo_ModEquiv:
    forall m,
      m = nativeSimpleFifo fifoName default ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Resolve nativeFifo_ModEquiv nativeSimpleFifo_ModEquiv.

