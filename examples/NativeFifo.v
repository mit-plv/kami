Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringAsList Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Notations Lts.Semantics.
Require Import Lts.ParametricEquiv Lts.Wf Lts.ParametricWf Lts.Tactics.

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

Hint Unfold nativeFifoS nativeSimpleFifoS nativeFifoM nativeSimpleFifoM : ModuleDefs.
Hint Unfold nativeEnqS nativeDeqS nativeFirstEltS: MethDefs.

Require Import Lib.StringEq.

Section Facts.
  Variable fifoName: string.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Hypothesis (Hgood: index 0 indexSymbol fifoName = None).

  Lemma nativeFifo_nativeFifoM:
    nativeFifo fifoName default = modFromMeta (nativeFifoM fifoName default Hgood).
  Proof. reflexivity. Qed.

  Lemma nativeFifo_nativeFifoS:
    nativeFifo fifoName default = getModFromSin (nativeFifoS fifoName default Hgood).
  Proof. reflexivity. Qed.

  Lemma nativeSimpleFifo_nativeSimpleFifoM:
    nativeSimpleFifo fifoName default =
    modFromMeta (nativeSimpleFifoM fifoName default Hgood).
  Proof. reflexivity. Qed.

  Lemma nativeSimpleFifo_nativeSimpleFifoS:
    nativeSimpleFifo fifoName default =
    getModFromSin (nativeSimpleFifoS fifoName default Hgood).
  Proof. reflexivity. Qed.

  Lemma nativeFifo_ModEquiv:
    ModPhoasWf (nativeFifo fifoName default).
  Proof.
    kequiv.
  Qed.
  Hint Resolve nativeFifo_ModEquiv.

  Lemma nativeSimpleFifo_ModEquiv:
    ModPhoasWf (nativeSimpleFifo fifoName default).
  Proof.
    kequiv.
  Qed.
  Hint Resolve nativeSimpleFifo_ModEquiv.

  Lemma nativeFifo_ValidRegs:
    ModRegsWf (nativeFifo fifoName default).
  Proof.
    kvr.
  Qed.
  Hint Resolve nativeFifo_ValidRegs.

  Lemma nativeSimpleFifo_ValidRegs:
    ModRegsWf (nativeSimpleFifo fifoName default).
  Proof.
    kvr.
  Qed.
  Hint Resolve nativeSimpleFifo_ValidRegs.

  Variable n: nat.

  Lemma nativeFifoS_ModEquiv:
    MetaModPhoasWf (getMetaFromSinNat n (nativeFifoS fifoName default Hgood)).
  Proof.
    kequiv.
  Qed.

  Lemma nativeFifoSS_ModEquiv:
    ModPhoasWf (getModFromSin (nativeFifoS fifoName default Hgood)).
  Proof.
    rewrite <-nativeFifo_nativeFifoS; kequiv.
  Qed.

  Lemma nativeFifoM_ModEquiv:
    MetaModPhoasWf (nativeFifoM fifoName default Hgood).
  Proof.
    kequiv.
  Qed.

  Lemma nativeSimpleFifoS_ModEquiv:
    MetaModPhoasWf (getMetaFromSinNat n (nativeSimpleFifoS fifoName default Hgood)).
  Proof.
    kequiv.
  Qed.

  Lemma nativeSimpleFifoSS_ModEquiv:
    ModPhoasWf (getModFromSin (nativeSimpleFifoS fifoName default Hgood)).
  Proof.
    rewrite <-nativeSimpleFifo_nativeSimpleFifoS; kequiv.
  Qed.

  Lemma nativeSimpleFifoM_ModEquiv:
    MetaModPhoasWf (nativeSimpleFifoM fifoName default Hgood).
  Proof.
    kequiv.
  Qed.

  Lemma nativeFifoS_ValidRegs:
    MetaModRegsWf (getMetaFromSinNat n (nativeFifoS fifoName default Hgood)).
  Proof.
    kvr.
  Qed.

  Lemma nativeFifoSS_ValidRegs:
    ModRegsWf (getModFromSin (nativeFifoS fifoName default Hgood)).
  Proof.
    rewrite <-nativeFifo_nativeFifoS; kvr.
  Qed.

  Lemma nativeFifoM_ValidRegs:
    MetaModRegsWf (nativeFifoM fifoName default Hgood).
  Proof.
    kvr.
  Qed.

  Lemma nativeSimpleFifoS_ValidRegs:
    MetaModRegsWf (getMetaFromSinNat n (nativeSimpleFifoS fifoName default Hgood)).
  Proof.
    kvr.
  Qed.

  Lemma nativeSimpleFifoSS_ValidRegs:
    ModRegsWf (getModFromSin (nativeSimpleFifoS fifoName default Hgood)).
  Proof.
    rewrite <-nativeSimpleFifo_nativeSimpleFifoS; kvr.
  Qed.

  Lemma nativeSimpleFifoM_ValidRegs:
    MetaModRegsWf (nativeSimpleFifoM fifoName default Hgood).
  Proof.
    kvr.
  Qed.

End Facts.

Hint Resolve nativeFifo_ModEquiv nativeSimpleFifo_ModEquiv
     nativeFifoS_ModEquiv nativeFifoSS_ModEquiv nativeFifoM_ModEquiv
     nativeSimpleFifoS_ModEquiv nativeSimpleFifoSS_ModEquiv nativeSimpleFifoM_ModEquiv.

Hint Resolve nativeFifo_ValidRegs nativeSimpleFifo_ValidRegs
     nativeFifoS_ValidRegs nativeFifoSS_ValidRegs nativeFifoM_ValidRegs
     nativeSimpleFifoS_ValidRegs nativeSimpleFifoSS_ValidRegs nativeSimpleFifoM_ValidRegs.

