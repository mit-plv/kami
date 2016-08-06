Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Indexer Lib.StringAsList Lib.StringBound.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Notations Lts.Semantics.
Require Import Lts.Equiv Lts.Wf Lts.ParametricEquiv Lts.ParametricWf Lts.Tactics.
Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.
  
Section Fifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Local Notation "^ s" := (fifoName -- s) (at level 0).

  Definition enq {ty} : forall (d: ty dType), ActionT ty Void := fun d =>
    (Read isFull <- ^"full";
     Assert !#isFull;
     Read elt <- ^"elt";
     Read enqP <- ^"enqP";
     Read deqP <- ^"deqP";
     Write ^"elt" <- #elt@[#enqP <- #d];
     Write ^"empty" <- $$false;
     LET next_enqP <- (#enqP + $1) :: Bit sz;
     Write ^"full" <- (#deqP == #next_enqP);
     Write ^"enqP" <- #next_enqP;
     Retv)%kami_action.

  Definition deq {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
     Assert !#isEmpty;
     Read elt <- ^"elt";
     Read enqP <- ^"enqP";
     Read deqP <- ^"deqP";
     Write ^"full" <- $$false;
     LET next_deqP <- (#deqP + $1) :: Bit sz;
     Write ^"empty" <- (#enqP == #next_deqP);
     Write ^"deqP" <- #next_deqP;
     Ret #elt@[#deqP])%kami_action.

  Definition firstElt {ty} : ActionT ty dType :=
    (Read isEmpty <- ^"empty";
     Assert !#isEmpty;
     Read elt : Vector dType sz <- ^"elt";
     Read deqP <- ^"deqP";
     Ret #elt@[#deqP])%kami_action.
  
  Definition fifo := MODULE {
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
    with Method ^"firstElt"() : dType := firstElt
  }.

  Definition simpleFifo := MODULE {
    Register ^"elt" : Vector dType sz <- Default
    with Register ^"enqP" : Bit sz <- Default
    with Register ^"deqP" : Bit sz <- Default
    with Register ^"empty" : Bool <- true
    with Register ^"full" : Bool <- Default

    with Method ^"enq"(d : dType) : Void := (enq d)
    with Method ^"deq"() : dType := deq
  }.

  (** SinAction version *)
  Hypothesis HfifoName: index 0 indexSymbol fifoName = None.
  Lemma fgn:
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

  Definition enqS {ty} : forall (d: ty dType), SinActionT ty Void := fun d =>
    (Read isFull <- { ^"full" | fgn "full" eq_refl };
     Assert !#isFull;
     Read elt <- { ^"elt" | fgn "elt" eq_refl };
     Read enqP <- { ^"enqP" | fgn "enqP" eq_refl };
     Read deqP <- { ^"deqP" | fgn "deqP" eq_refl };
     Write { ^"elt" | fgn "elt" eq_refl } <- #elt@[#enqP <- #d];
     Write { ^"empty" | fgn "empty" eq_refl } <- $$false;
     LET next_enqP <- (#enqP + $1) :: Bit sz;
     Write { ^"full" | fgn "full" eq_refl } <- (#deqP == #next_enqP);
     Write { ^"enqP" | fgn "enqP" eq_refl } <- #next_enqP;
     Retv)%kami_sin.

  Definition deqS {ty} : SinActionT ty dType :=
    (Read isEmpty <- { ^"empty" | fgn "empty" eq_refl };
     Assert !#isEmpty;
     Read elt <- { ^"elt" | fgn "elt" eq_refl };
     Read enqP <- { ^"enqP" | fgn "enqP" eq_refl };
     Read deqP <- { ^"deqP" | fgn "deqP" eq_refl };
     Write { ^"full" | fgn "full" eq_refl } <- $$false;
     LET next_deqP <- (#deqP + $1) :: Bit sz;
     Write { ^"empty" | fgn "empty" eq_refl } <- (#enqP == #next_deqP);
     Write { ^"deqP" | fgn "deqP" eq_refl } <- #next_deqP;
     Ret #elt@[#deqP])%kami_sin.

  Definition firstEltS {ty} : SinActionT ty dType :=
    (Read isEmpty <- { ^"empty" | fgn "empty" eq_refl };
     Assert !#isEmpty;
     Read elt : Vector dType sz <- { ^"elt" | fgn "elt" eq_refl };
     Read deqP <- { ^"deqP" | fgn "deqP" eq_refl };
     Ret #elt@[#deqP])%kami_sin.
  
  Definition fifoS := SIN {
    Register { ^"elt" | fgn "elt" eq_refl } : Vector dType sz <- Default
    with Register { ^"enqP" | fgn "enqP" eq_refl } : Bit sz <- Default
    with Register { ^"deqP" | fgn "deqP" eq_refl } : Bit sz <- Default
    with Register { ^"empty" | fgn "empty" eq_refl } : Bool <- true
    with Register { ^"full" | fgn "full" eq_refl } : Bool <- Default

    with Method { ^"enq" | fgn "enq" eq_refl }(d : dType) : Void := (enqS d)
    with Method { ^"deq" | fgn "deq" eq_refl }() : dType := deqS
    with Method { ^"firstElt" | fgn "firstElt" eq_refl }() : dType := firstEltS
  }.

  Definition fifoM := META {
    Register { ^"elt" | fgn "elt" eq_refl } : Vector dType sz <- Default
    with Register { ^"enqP" | fgn "enqP" eq_refl } : Bit sz <- Default
    with Register { ^"deqP" | fgn "deqP" eq_refl } : Bit sz <- Default
    with Register { ^"empty" | fgn "empty" eq_refl } : Bool <- true
    with Register { ^"full" | fgn "full" eq_refl } : Bool <- Default

    with Method { ^"enq" | fgn "enq" eq_refl }(d : dType) : Void := (enqS d)
    with Method { ^"deq" | fgn "deq" eq_refl }() : dType := deqS
    with Method { ^"firstElt" | fgn "firstElt" eq_refl }() : dType := firstEltS
  }.

  Definition simpleFifoS := SIN {
    Register { ^"elt" | fgn "elt" eq_refl } : Vector dType sz <- Default
    with Register { ^"enqP" | fgn "enqP" eq_refl } : Bit sz <- Default
    with Register { ^"deqP" | fgn "deqP" eq_refl } : Bit sz <- Default
    with Register { ^"empty" | fgn "empty" eq_refl } : Bool <- true
    with Register { ^"full" | fgn "full" eq_refl } : Bool <- Default

    with Method { ^"enq" | fgn "enq" eq_refl }(d : dType) : Void := (enqS d)
    with Method { ^"deq" | fgn "deq" eq_refl }() : dType := deqS
  }.

  Definition simpleFifoM := META {
    Register { ^"elt" | fgn "elt" eq_refl } : Vector dType sz <- Default
    with Register { ^"enqP" | fgn "enqP" eq_refl } : Bit sz <- Default
    with Register { ^"deqP" | fgn "deqP" eq_refl } : Bit sz <- Default
    with Register { ^"empty" | fgn "empty" eq_refl } : Bool <- true
    with Register { ^"full" | fgn "full" eq_refl } : Bool <- Default

    with Method { ^"enq" | fgn "enq" eq_refl }(d : dType) : Void := (enqS d)
    with Method { ^"deq" | fgn "deq" eq_refl }() : dType := deqS
  }.

End Fifo.

Hint Unfold fifo simpleFifo : ModuleDefs.
Hint Unfold enq deq firstElt : MethDefs.

Hint Unfold fifoS simpleFifoS : ModuleDefs.
Hint Unfold enqS deqS firstEltS : MethDefs.

Section Facts.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Hypothesis HfifoName: index 0 indexSymbol fifoName = None.

  Lemma fifo_fifoM:
    fifo fifoName sz dType = modFromMeta (fifoM fifoName sz dType HfifoName).
  Proof. reflexivity. Qed.

  Lemma fifo_fifoS:
    fifo fifoName sz dType = getModFromSin (fifoS fifoName sz dType HfifoName).
  Proof. reflexivity. Qed.

  Lemma simpleFifo_simpleFifoM:
    simpleFifo fifoName sz dType = modFromMeta (simpleFifoM fifoName sz dType HfifoName).
  Proof. reflexivity. Qed.

  Lemma simpleFifo_simpleFifoS:
    simpleFifo fifoName sz dType = getModFromSin (simpleFifoS fifoName sz dType HfifoName).
  Proof. reflexivity. Qed.

  Lemma fifo_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (fifo fifoName sz dType).
  Proof. kequiv. Qed.
  Hint Resolve fifo_ModEquiv.

  Lemma simpleFifo_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (simpleFifo fifoName sz dType).
  Proof. kequiv. Qed.
  Hint Resolve simpleFifo_ModEquiv.

  Lemma fifo_ValidRegs:
    forall ty, ValidRegsModules ty (fifo fifoName sz dType).
  Proof. kvr. Qed.
  Hint Resolve fifo_ValidRegs.

  Lemma simpleFifo_ValidRegs:
    forall ty, ValidRegsModules ty (simpleFifo fifoName sz dType).
  Proof. kvr. Qed.
  Hint Resolve simpleFifo_ValidRegs.

  Variable n: nat.

  Lemma fifoSS_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (getModFromSin (fifoS fifoName sz dType HfifoName)).
  Proof. rewrite <-fifo_fifoS; kequiv. Qed.

  Lemma fifoS_ModEquiv:
    forall ty1 ty2, MetaModEquiv ty1 ty2 (getMetaFromSinNat n (fifoS fifoName sz dType HfifoName)).
  Proof. kequiv. Qed.

  Lemma fifoM_ModEquiv:
    forall ty1 ty2, MetaModEquiv ty1 ty2 (fifoM fifoName sz dType HfifoName).
  Proof. kequiv. Qed.

  Lemma simpleFifoSS_ModEquiv:
    forall ty1 ty2,
      ModEquiv ty1 ty2 (getModFromSin (simpleFifoS fifoName sz dType HfifoName)).
  Proof. rewrite <-simpleFifo_simpleFifoS; kequiv. Qed.

  Lemma simpleFifoS_ModEquiv:
    forall ty1 ty2,
      MetaModEquiv ty1 ty2 (getMetaFromSinNat n (simpleFifoS fifoName sz dType HfifoName)).
  Proof. kequiv. Qed.

  Lemma simpleFifoM_ModEquiv:
    forall ty1 ty2, MetaModEquiv ty1 ty2 (simpleFifoM fifoName sz dType HfifoName).
  Proof. kequiv. Qed.

  Lemma fifoSS_ValidRegs:
    forall ty, ValidRegsModules ty (getModFromSin (fifoS fifoName sz dType HfifoName)).
  Proof. rewrite <-fifo_fifoS; kvr. Qed.
  
  Lemma fifoS_ValidRegs:
    forall ty, ValidRegsMetaModule ty (getMetaFromSinNat n (fifoS fifoName sz dType HfifoName)).
  Proof. kvr. Qed.

  Lemma fifoM_ValidRegs:
    forall ty, ValidRegsMetaModule ty (fifoM fifoName sz dType HfifoName).
  Proof. kvr. Qed.

  Lemma simpleFifoSS_ValidRegs:
    forall ty,
      ValidRegsModules ty (getModFromSin (simpleFifoS fifoName sz dType HfifoName)).
  Proof. rewrite <-simpleFifo_simpleFifoS; kvr. Qed.

  Lemma simpleFifoS_ValidRegs:
    forall ty,
      ValidRegsMetaModule ty (getMetaFromSinNat n (simpleFifoS fifoName sz dType HfifoName)).
  Proof. kvr. Qed.

  Lemma simpleFifoM_ValidRegs:
    forall ty, ValidRegsMetaModule ty (simpleFifoM fifoName sz dType HfifoName).
  Proof. kvr. Qed.

End Facts.

Hint Resolve fifo_ModEquiv simpleFifo_ModEquiv
     fifoS_ModEquiv fifoSS_ModEquiv fifoM_ModEquiv
     simpleFifoS_ModEquiv simpleFifoSS_ModEquiv simpleFifoM_ModEquiv.
     
Hint Resolve fifo_ValidRegs simpleFifo_ValidRegs
     fifoS_ValidRegs fifoSS_ValidRegs fifoM_ValidRegs
     simpleFifoS_ValidRegs simpleFifoSS_ValidRegs simpleFifoM_ValidRegs.

