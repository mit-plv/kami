Require Import Arith.Peano_dec Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv.
Require Import Ex.Fifo.

Set Implicit Arguments.

Section NativeFifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Notation "^ s" := (fifoName .. s) (at level 0).

  Definition listEltT ty := list (ty dType).
  Definition listEltK ty := @NativeKind (listEltT ty) nil.
  Definition listElt ty := (^"elt" :: (@NativeConst (listEltT ty) nil nil))%struct.

  Definition listIsFull {ty} (l: fullType ty (listEltK ty)) :=
    if eq_nat_dec (length l) sz then ConstBool true else ConstBool false.
  Definition listIsEmpty {ty} (l: fullType ty (listEltK ty)) :=
    if eq_nat_dec (length l) 0 then ConstBool true else ConstBool false.
  Definition listEnq {ty} (a: ty dType) (l: fullType ty (listEltK ty)) :=
    a :: l.
  Definition listDeq {ty} (l: fullType ty (listEltK ty)) :=
    match l with
    | nil => nil
    | h :: t => t
    end.
  Definition listFirstElt {ty} (l: fullType ty (listEltK ty)): Expr ty (SyntaxKind dType) :=
    match l with
    | nil => ($$default)%kami
    | h :: t => (#h)%kami
    end.

  (* defined methods *)
  Definition nativeEnq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsFull elt);
     Write ^"elt" <- (Var _ (listEltK ty) (listEnq d elt));
     Retv)%kami.

  Definition nativeDeq {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
     Write ^"elt" <- (Var _ (listEltK ty) (listDeq elt));
     Ret (listFirstElt elt))%kami.

  Definition nativeFirstElt {ty} : ActionT ty dType :=
    (ReadN elt : listEltK ty <- ^"elt";
     Assert !$$(listIsEmpty elt);
     Ret (listFirstElt elt))%kami.

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

Hint Unfold nativeFifo nativeSimpleFifo : ModuleDefs.
Hint Unfold listEltT listEltK listElt
     listIsFull listIsEmpty listEnq listDeq listFirstElt
     nativeEnq nativeDeq nativeFirstElt: MethDefs.

Require Import Refinement Decomposition Tactics Lib.FMap.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.
  Variable default: ConstT dType.

  Definition fifo := fifo fifoName sz dType.
  Definition nfifo := @nativeFifo fifoName sz dType default.

  Notation "^ s" := (fifoName .. s) (at level 0).

  Fixpoint fifo_nfifo_elt_not_full
           (eltv : word sz -> type dType)
           (enqPv : word sz)
           (edSub : nat): list (type dType) :=
    match edSub with
    | O => nil
    | S ed =>
      (eltv (enqPv ^- (natToWord sz edSub)))
        :: (fifo_nfifo_elt_not_full eltv enqPv ed)
    end.

  Definition fifo_nfifo_regMap (r: RegsT): RegsT.
  Proof.
    kgetv ^"elt"%string eltv r (Vector dType sz) (M.empty (sigT (fullType type))).
    kgetv ^"full"%string fullv r Bool (M.empty (sigT (fullType type))).
    kgetv ^"enqP"%string enqPv r (Bit sz) (M.empty (sigT (fullType type))).
    kgetv ^"deqP"%string deqPv r (Bit sz) (M.empty (sigT (fullType type))).

    refine (M.add ^"elt" (existT _ (listEltK dType type) _) (M.empty _)).
    destruct (weq enqPv deqPv).
    - refine (if fullv then _ else _).
      + exact ((eltv deqPv) :: (fifo_nfifo_elt_not_full eltv enqPv (wordToNat (wones sz)))).
      + exact nil.
    - exact (fifo_nfifo_elt_not_full eltv enqPv (wordToNat (enqPv ^- deqPv))).
  Defined.
  Hint Unfold fifo_nfifo_regMap: MethDefs.
  
  Definition fifo_nfifo_ruleMap (_: RegsT) (r: string): option string := Some r.
  Hint Unfold fifo_nfifo_ruleMap: MethDefs.

  Definition fifo_nfifo_labelMap (_: string) (s: sigT SignT): option (sigT SignT) := Some s.

  Definition fifo_nfifo_substepRuleMap:
    forall (oImp : RegsT) (uImp : UpdatesT)
           (rule : string) (csImp : MethsT),
      reachable oImp fifo ->
      Substep fifo oImp uImp (Rle (Some rule))
              csImp ->
      {uSpec : UpdatesT |
       Substep nfifo (fifo_nfifo_regMap oImp) uSpec
               (Rle (fifo_nfifo_ruleMap oImp rule))
               (liftToMap1 fifo_nfifo_labelMap csImp) /\
       (forall o : RegsT,
           M.union uSpec (fifo_nfifo_regMap o) =
           fifo_nfifo_regMap (M.union uImp o))}.
  Proof.
    admit.
  Qed.
  
  Definition fifo_nfifo_substepMethMap:
    forall (oImp : RegsT) (uImp : UpdatesT)
           (meth : Struct.Attribute (sigT SignT))
           (csImp : MethsT),
      reachable oImp fifo ->
      Substep fifo oImp uImp (Meth (Some meth))
              csImp ->
      {uSpec : UpdatesT |
       Substep nfifo (fifo_nfifo_regMap oImp) uSpec
               (Meth (liftP fifo_nfifo_labelMap meth))
               (liftToMap1 fifo_nfifo_labelMap csImp) /\
       (forall o : RegsT,
           M.union uSpec (fifo_nfifo_regMap o) =
           fifo_nfifo_regMap (M.union uImp o))}.
  Proof.
    admit.
  Qed.

  Lemma fifo_refines_nativefifo: fifo <<== nfifo.
  Proof.
    apply decomposition with
    (theta:= fifo_nfifo_regMap)
      (ruleMap:= fifo_nfifo_ruleMap)
      (substepRuleMap:= fifo_nfifo_substepRuleMap)
      (substepMethMap:= fifo_nfifo_substepMethMap).

    - kdecompose_regmap_init.
      kinv_finish.
    - auto.
    - auto.
    - admit.
    - kequiv.
  Qed.

End Facts.

