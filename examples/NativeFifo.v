Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringExtension Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Notations Lts.Semantics.
Require Import Lts.Equiv Lts.ParametricEquiv Lts.Wf Lts.ParametricWf Lts.Tactics.

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
    unfold withPrefix; intros.
    apply index_not_in; apply index_not_in in H; apply index_not_in in HfifoName.
    intro Hx; elim H; clear H.
    apply S_in_app_or in Hx; destruct Hx; auto.
    apply S_in_app_or in H; destruct H.
    - inv H; inv H0.
    - elim HfifoName; auto.
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
  
  Definition nativeFifoS := SIN {
    RegisterN { ^"elt" | ngn "elt" eq_refl } : listEltK type <- (NativeConst nil nil)

    with Method { ^"enq" | ngn "enq" eq_refl } (d : dType) : Void := (nativeEnqS d)
    with Method { ^"deq" | ngn "deq" eq_refl } () : dType := nativeDeqS
    with Method { ^"firstElt" | ngn "firstElt" eq_refl } () : dType := nativeFirstEltS
  }.

  Definition nativeSimpleFifoS := SIN {
    RegisterN { ^"elt" | ngn "elt" eq_refl } : listEltK type <- (NativeConst nil nil)

    with Method { ^"enq" | ngn "enq" eq_refl } (d : dType) : Void := (nativeEnqS d)
    with Method { ^"deq" | ngn "deq" eq_refl } () : dType := nativeDeqS
  }.

  Definition nativeFifoM := META {
    RegisterN { ^"elt" | ngn "elt" eq_refl } : listEltK type <- (NativeConst nil nil)

    with Method { ^"enq" | ngn "enq" eq_refl } (d : dType) : Void := (nativeEnqS d)
    with Method { ^"deq" | ngn "deq" eq_refl } () : dType := nativeDeqS
    with Method { ^"firstElt" | ngn "firstElt" eq_refl } () : dType := nativeFirstEltS
  }.

  Definition nativeSimpleFifoM := META {
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

  Lemma nativeFifo_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (nativeFifo fifoName default).
  Proof.
    kequiv.
  Qed.

  Lemma nativeSimpleFifo_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (nativeSimpleFifo fifoName default).
  Proof.
    kequiv.
  Qed.

  Lemma nativeFifo_ValidRegs:
    forall ty, ValidRegsModules ty (nativeFifo fifoName default).
  Proof.
    kvr.
  Qed.

  Lemma nativeSimpleFifo_ValidRegs:
    forall ty, ValidRegsModules ty (nativeSimpleFifo fifoName default).
  Proof.
    kvr.
  Qed.

  Variable n: nat.
  Hypothesis (Hgood: index 0 indexSymbol fifoName = None).

  Lemma nativeFifoS_ModEquiv:
    forall ty1 ty2,
      MetaModEquiv ty1 ty2 (getMetaFromSinNat n (nativeFifoS fifoName default Hgood)).
  Proof.
    kequiv.
  Qed.

  Lemma nativeFifoM_ModEquiv:
    forall ty1 ty2, MetaModEquiv ty1 ty2 (nativeFifoM fifoName default Hgood).
  Proof.
    kequiv.
  Qed.

  Lemma nativeSimpleFifoS_ModEquiv:
    forall ty1 ty2,
      MetaModEquiv ty1 ty2 (getMetaFromSinNat n (nativeSimpleFifoS fifoName default Hgood)).
  Proof.
    kequiv.
  Qed.

  Lemma nativeSimpleFifoM_ModEquiv:
    forall ty1 ty2, MetaModEquiv ty1 ty2 (nativeSimpleFifoM fifoName default Hgood).
  Proof.
    kequiv.
  Qed.

  Lemma nativeFifoS_ValidRegs:
    forall ty,
      ValidRegsMetaModule ty (getMetaFromSinNat n (nativeFifoS fifoName default Hgood)).
  Proof.
    kvr.
  Qed.

  Lemma nativeFifoM_ValidRegs:
    forall ty, ValidRegsMetaModule ty (nativeFifoM fifoName default Hgood).
  Proof.
    kvr.
  Qed.

  Lemma nativeSimpleFifoS_ValidRegs:
    forall ty,
      ValidRegsMetaModule ty (getMetaFromSinNat n (nativeSimpleFifoS fifoName default Hgood)).
  Proof.
    kvr.
  Qed.

  Lemma nativeSimpleFifoM_ValidRegs:
    forall ty, ValidRegsMetaModule ty (nativeSimpleFifoM fifoName default Hgood).
  Proof.
    kvr.
  Qed.

End Facts.

Hint Resolve nativeFifo_ModEquiv nativeSimpleFifo_ModEquiv
     nativeFifoS_ModEquiv nativeFifoM_ModEquiv
     nativeSimpleFifoS_ModEquiv nativeSimpleFifoM_ModEquiv.

Hint Resolve nativeFifo_ValidRegs nativeSimpleFifo_ValidRegs
     nativeFifoS_ValidRegs nativeFifoM_ValidRegs
     nativeSimpleFifoS_ValidRegs nativeSimpleFifoM_ValidRegs.

