Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics.

Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.

Section Fifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Notation "^ s" := (fifoName -n- s) (at level 0).

  Definition eltReg := Register ^"elt" : Vector dType sz <- Default.
  Definition enqPReg := Register ^"enqP" : Bit sz <- Default.
  Definition deqPReg := Register ^"deqP" : Bit sz <- Default.
  Definition emptyReg := Register ^"empty" : Bool <- true.
  Definition fullReg := Register ^"full" : Bool <- Default.

  Definition fifoRegs := [eltReg; enqPReg; deqPReg; emptyReg; fullReg].

  Definition max_index : ConstT (Bit sz) := ^~ $1.

  Definition notFullSig := MethodSig ^"notFull"() : Bool.
  Definition notEmptySig := MethodSig ^"notEmpty"() : Bool.
  Definition enqSig := MethodSig ^"enq"(dType) : Void.
  Definition deqSig := MethodSig ^"deq"() : dType.
  Definition firstEltSig := MethodSig ^"notFull"() : dType.

  Definition notFullBody := Method() : Bool :=
    Read isFull <- fullReg;
    Ret !#isFull.

  Definition notEmptyBody := Method() : Bool :=
    Read isEmpty <- emptyReg;
    Ret !#isEmpty.

  Definition enqBody := Method(d : dType) : Void :=
    Read isFull <- fullReg;
    Assert !#isFull;
    Read elt <- eltReg;
    Read enqP <- enqPReg;
    Read deqP <- deqPReg;
    Write eltReg <- #elt@[#enqP <- #d];
    Write emptyReg <- $$false;
    Let next_enqP <- IF #enqP == $$max_index then $0 else #enqP + $1;
    Write fullReg <- (#deqP == #next_enqP);
    Write enqPReg <- #next_enqP;
    Retv.

  Definition deqBody := Method() : dType :=
    Read isEmpty <- emptyReg;
    Assert !#isEmpty;
    Read elt <- eltReg;
    Read enqP <- enqPReg;
    Read deqP <- deqPReg;
    Write fullReg <- $$false;
    Let next_deqP : Bit sz <- IF #deqP == $$max_index then $0 else #enqP + $1;
    Write emptyReg <- (#enqP == #next_deqP);
    Write deqPReg <- #next_deqP;
    Ret #elt@[#deqP].

  Definition firstEltBody := Method() : dType :=
    Read isEmpty <- emptyReg;
    Assert !#isEmpty;
    Read elt : Vector dType sz <- eltReg;
    Read deqP <- deqPReg;
    Ret #elt@[#deqP].

  Definition fifoRules : list (Attribute (Action type (Bit 0)))
    := nil.

  Definition fifoDefMeths : list (DefMethT type) :=
    (Build_Attribute (attrName notFullSig)
                     (Build_Typed _ (attrType notFullSig) notFullBody))
      :: (Build_Attribute (attrName notEmptySig)
                          (Build_Typed _ (attrType notEmptySig) notEmptyBody))
      :: (Build_Attribute (attrName enqSig)
                          (Build_Typed _ (attrType enqSig) enqBody))
      :: (Build_Attribute (attrName deqSig)
                          (Build_Typed _ (attrType deqSig) deqBody))
      :: (Build_Attribute (attrName firstEltSig)
                          (Build_Typed _ (attrType firstEltSig) firstEltBody))
      :: nil.

  Definition simpleFifoDefMeths : list (DefMethT type) :=
    (Build_Attribute (attrName enqSig)
                     (Build_Typed _ (attrType enqSig) enqBody))
      :: (Build_Attribute (attrName deqSig)
                          (Build_Typed _ (attrType deqSig) deqBody))
      :: nil.
                              
  Definition fifo := Mod fifoRegs fifoRules fifoDefMeths.
  Definition simpleFifo := Mod fifoRegs fifoRules simpleFifoDefMeths.

  Section Spec.
    Lemma regsInDomain_simpleFifo: RegsInDomain simpleFifo.
    Proof.
      unfold RegsInDomain; intros; inv H.
      destruct rm; [inv Hltsmod; inv HInRule|].
      invertSemModRep; invertActionRep; inDomain_tac.
    Qed.

  End Spec.

End Fifo.

Hint Unfold eltReg enqPReg deqPReg emptyReg fullReg.
Hint Unfold fifoRules notFullBody notEmptyBody enqBody deqBody firstEltBody.
Hint Unfold fifo simpleFifo : ModuleDefs.
