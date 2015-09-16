Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics.

Require Import FunctionalExtensionality Eqdep Eqdep_dec.

Set Implicit Arguments.

Section Fifo.
  Variable fifoName: string.
  Variable sz: nat.
  Variable dType: Kind.

  Definition eltReg : RegInitT := Reg#(Vector dType sz) (fifoName -n- "elt") <- mkRegU;.
  Definition enqPReg : RegInitT := Reg#(Bit sz) (fifoName -n- "enqP") <- mkRegU;.
  Definition deqPReg : RegInitT := Reg#(Bit sz) (fifoName -n- "deqP") <- mkRegU;.
  Definition emptyReg : RegInitT := Reg#(Bool) (fifoName -n- "empty") <- mkReg(ConstBool true);.
  Definition fullReg : RegInitT := Reg#(Bool) (fifoName -n- "full") <- mkRegU;.

  Definition fifoRegs : list RegInitT :=
    eltReg::enqPReg::deqPReg::emptyReg::fullReg::nil.

  Definition max_index := ConstBit (wnegN (natToWord sz 1)).

  Definition notFullSig : Attribute SignatureT :=
    Method Value#(Bool) (fifoName -n- "notFull") #(Bit 0) ;.
  Definition notEmptySig : Attribute SignatureT :=
    Method Value#(Bool) (fifoName -n- "notEmpty") #(Bit 0) ;.
  Definition enqSig : Attribute SignatureT :=
    Method Value#(Bit 0) (fifoName -n- "enq") #(dType) ;.
  Definition deqSig : Attribute SignatureT :=
    Method Value#(dType) (fifoName -n- "deq") #(Bit 0) ;.
  Definition firstEltSig : Attribute SignatureT :=
    Method Value#(dType) (fifoName -n- "notFull") #(Bit 0) ;.

  Definition notFullBody
  : type (arg (attrType notFullSig)) ->
    Action type (ret (attrType notFullSig)) :=
    fun _ =>
      vread isFull <- (attrName fullReg) #;
      vret (Not (V isFull)) #;.

  Definition notEmptyBody
  : type (arg (attrType notEmptySig)) ->
    Action type (ret (attrType notEmptySig)) :=
    fun _ =>
      vread isEmpty <- (attrName emptyReg) #;
      vret (Not (V isEmpty)) #;.

  Definition retVoid : Action type (Bit 0) :=
    vret (Cd (Bit 0)) #;.

  Definition enqBody
  : type (arg (attrType enqSig)) ->
    Action type (ret (attrType enqSig)) :=
    fun d =>
      vread isFull <- (attrName fullReg) #;
      vassert (Not (V isFull)) #;
      vread elt <- (attrName eltReg) #;
      vread enqP <- (attrName enqPReg) #;
      vread deqP <- (attrName deqPReg) #;
      (attrName eltReg) <= ((V elt) @[(V enqP) <- (V d)]) #;
      (attrName emptyReg) <= (C (ConstBool false)) #;
      vlet next_enqP <- (ITE (V enqP == (C max_index))
                             (C (ConstBit (wzero sz)))
                             (BinBit (Add _)
                                     (V enqP)
                                     (C (ConstBit (natToWord sz 1))))) #;
      (attrName fullReg) <= (V deqP == V next_enqP) #;
      (attrName enqPReg) <= (V next_enqP) #;
      retVoid.

  Definition deqBody
  : type (arg (attrType deqSig)) ->
    Action type (ret (attrType deqSig)) :=
    fun _ =>
      vread isEmpty <- (attrName emptyReg) #;
      vassert (Not (V isEmpty)) #;
      vread elt <- (attrName eltReg) #;
      vread enqP <- (attrName enqPReg) #;
      vread deqP <- (attrName deqPReg) #;
      (attrName fullReg) <= (C (ConstBool false)) #;
      vlet next_deqP <- (ITE (V deqP == C max_index)
                             (C (ConstBit (wzero sz)))
                             (BinBit (Add _)
                                     (V enqP)
                                     (C (ConstBit (natToWord sz 1))))) #;
      (attrName emptyReg) <= (V enqP == V next_deqP) #;
      (attrName deqPReg) <= (V next_deqP) #;
      vret (V elt)@[V deqP] #;.

  Definition firstEltBody
  : type (arg (attrType firstEltSig)) ->
    Action type (ret (attrType firstEltSig)) :=
    fun _ =>
      vread isEmpty <- (attrName emptyReg) #;
      vassert (Not (V isEmpty)) #;
      vread elt :@: (objType (attrType eltReg)) <- (attrName eltReg) #;
      vread deqP <- (attrName deqPReg) #;
      vassert (Not (V isEmpty)) #;
      vret (V elt)@[V deqP] #;.

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

Hint Unfold fifoRules notFullBody notEmptyBody enqBody deqBody firstEltBody.
Hint Unfold fifo simpleFifo : ModuleDefs.

