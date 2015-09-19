Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement.

(* The SC module is defined as follows: SC = n * Pinst + Minst,
 * where Pinst denotes an instantaneous processor core
 * and Minst denotes an instantaneous memory.
 *)

(* Abstract ISA *)
Section DecExec.
  Variables opIdx addrSize valSize rfIdx: nat.

  Definition StateK := Vector (Bit valSize) rfIdx.
  Definition StateT := type StateK.

  Definition DecInstA := (Build_Attribute "opcode" (Bit opIdx))
                           :: (Build_Attribute "reg" (Bit rfIdx))
                           :: (Build_Attribute "addr" (Bit addrSize))
                           :: (Build_Attribute "value" (Bit valSize))
                           :: nil.
  Definition DecInstK := Struct DecInstA.
  Definition DecInstT := type DecInstK.

  Definition DecT := StateT -> type (Bit addrSize) -> DecInstT.
  Definition ExecT := StateT -> type (Bit addrSize) -> DecInstT ->
                      (type (Bit addrSize) * StateT)%type.

End DecExec.

(* The module definition for Minst with n ports *)
Section MemInst.
  Variable n : nat.
  Variable addrSize : nat.
  Variable dType : Kind.

  (* Registers *)
  Definition memReg : RegInitT := Reg#(Vector dType addrSize) "mem" <- mkRegU;.
  Definition memRegs : list RegInitT := memReg :: nil.

  (* Method signatures *)
  Definition memLd : ConstT (Bit 2) := ConstBit (WO~0~0).
  Definition memSt : ConstT (Bit 2) := ConstBit (WO~0~1).

  Definition atomA : list (Attribute Kind) :=
    {| attrName := "type"; attrType := Bit 2 |}
      :: {| attrName := "addr"; attrType := Bit addrSize |}
      :: {| attrName := "value"; attrType := dType |}
      :: nil.
  Definition atomK : Kind := Struct atomA.

  Definition buildAtom t a v: Expr type atomK :=
    ST (icons (Build_Attribute "type" _) t
              (icons (Build_Attribute "addr" _) a
                     (icons (Build_Attribute "value" _) v
                            (inil _)))).

  Definition memExecSig (i: nat): Attribute SignatureT :=
    Method Value#(atomK) ("exec"__ i) #(atomK);.
  Definition memExec (i: nat)
  : type (arg (attrType (memExecSig i))) ->
    Action type (ret (attrType (memExecSig i))) :=
    fun a =>
      vif (V a @> "type" #[] == C memLd)
      vthen (
        vread memv <- (attrName memReg) #;
        vlet ldval <- (V memv) @[V a @> "addr" #[]] #;
        vret (buildAtom (V a @> "type" #[]) (V a @> "addr" #[]) (V ldval)) #;
      )
      velse (
        vread memv <- (attrName memReg) #;
        (attrName memReg) <= ((V memv) @[ (V a @> "addr" #[]) <- (V a @> "value" #[]) ]) #;
        vret (V a) #;
      ) #;
      (fun na => vret (V na) #;).

  Definition memRules: list (Attribute (Action type (Bit 0))) := nil.

  Fixpoint memDefMeths (i: nat) : list (DefMethT type) :=
    match i with
      | O => (Build_Attribute (attrName (memExecSig O))
                              (Build_Typed _ (attrType (memExecSig O)) (memExec O))) :: nil
      | S i' => (Build_Attribute (attrName (memExecSig i))
                                 (Build_Typed _ (attrType (memExecSig i)) (memExec i)))
                                 :: (memDefMeths i')
    end.

  Definition memInst := Mod memRegs memRules (memDefMeths n).

End MemInst.

Hint Unfold memReg memExecSig.
Hint Unfold memInst: ModuleDefs.

(* The module definition for Pinst *)
Section ProcInst.
  Variable i : nat.
  Variables opIdx addrSize valSize rfIdx : nat.
  
  (* Registers *)
  Definition pcReg : RegInitT := Reg#(Bit addrSize) ("pc"__ i) <- mkRegU;.
  Definition rfReg : RegInitT := Reg#(Vector (Bit valSize) rfIdx) ("rf"__ i) <- mkRegU;.

  Definition procRegs : list RegInitT :=
    pcReg :: rfReg :: nil.
    
  (* External abstract ISA: dec and exec *)
  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Definition getNextPc ppc st := fst (exec st ppc (dec st ppc)).
  Definition getNextState ppc st := snd (exec st ppc (dec st ppc)).

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  (* Module interface *)
  Definition procDms : list (DefMethT type) := nil.

  Definition memAtomK := atomK addrSize (Bit valSize).

  Definition execCm : Attribute SignatureT :=
    Method Value#(memAtomK) ("exec"__ i) #(memAtomK);.
  Definition haltCm : Attribute SignatureT :=
    Method Value#(Bit 0) ("HALT"__ i) #(Bit 0);.

  (* Rules *)
  Definition nextPc ppc st: Action type (Bit 0) :=
    (attrName pcReg) <= (V (getNextPc ppc st)) #;
    vret (Cd (Bit 0)) #;.

  Definition buildAtomP t a v: Expr type (atomK addrSize (Bit valSize)) :=
    ST (icons (Build_Attribute "type" _) t
              (icons (Build_Attribute "addr" _) a
                     (icons (Build_Attribute "value" _) v
                            (inil _)))).
     
  Definition procExecLd : Action type (Bit 0) :=
    vread ppc <- (attrName pcReg) #;
    vread st <- (attrName rfReg) #;
    vassert ( V (dec st ppc) @> "opcode" #[] == C opLd ) #;
    vcall ldRep <- (attrName execCm) :@: (attrType execCm)
    #(buildAtomP (C memLd) (V (dec st ppc) @> "addr" #[]) (Cd _)) #;
    (attrName rfReg) <= (V st) @[ (V (dec st ppc)) @> "reg" #[] <- (V ldRep @> "value" #[]) ] #;
    (nextPc ppc st).

  Definition procExecSt :=
    vread ppc <- (attrName pcReg) #;
    vread st <- (attrName rfReg) #;
    vassert ( V (dec st ppc) @> "opcode" #[] == C opSt ) #;
    vcall (attrName execCm) :@: (attrType execCm)
    #(buildAtomP (C memSt) (V (dec st ppc) @> "addr" #[])
                 (V (dec st ppc) @> "value" #[])) #;
    (nextPc ppc st).

  Definition procExecHt :=
    vread ppc <- (attrName pcReg) #;
    vread st <- (attrName rfReg) #;
    vassert ( V (dec st ppc) @> "opcode" #[] == C opHt ) #;
    vcall (attrName haltCm) :@: (attrType haltCm) #(Cd _) #;
    vret (Cd (Bit 0)) #;.

  Definition procExecNm :=
    vread ppc <- (attrName pcReg) #;
    vread st <- (attrName rfReg) #;
    vassert (Not ((V (dec st ppc) @> "opcode" #[] == C opLd) OR
                  (V (dec st ppc) @> "opcode" #[] == C opSt) OR
                  (V (dec st ppc) @> "opcode" #[] == C opHt))) #;
    (attrName rfReg) <= V (getNextState ppc st) #;
    (nextPc ppc st).

  Definition procVoidRule : Action type (Bit 0) :=
    vret (Cd _) #;.

  Definition procRules : list (Attribute (Action type (Bit 0))) :=
    (Build_Attribute ("execLd"__ i) procExecLd)
      ::(Build_Attribute ("execSt"__ i) procExecSt)
      ::(Build_Attribute ("execHt"__ i) procExecHt)
      ::(Build_Attribute ("execNm"__ i) procExecNm)
      ::(Build_Attribute ("voidRule"__ i) procVoidRule)
      ::nil.

  Definition procDefMeths : list (DefMethT type) := nil.

  Definition procInst := Mod procRegs procRules procDefMeths.

End ProcInst.

Hint Unfold pcReg rfReg.
Hint Unfold execCm haltCm getNextPc getNextState nextPc procRules
     procExecLd procExecSt procExecHt procExecNm.
Hint Unfold procInst : ModuleDefs.

Section SC.
  Variables opIdx addrSize valSize rfIdx : nat.

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Variables opLd opSt opHt: ConstT (Bit opIdx).

  Variable n: nat.

  Definition pinsti (i: nat) :=
    procInst i opIdx addrSize valSize rfIdx dec exec opLd opSt opHt.

  Fixpoint pinsts (i: nat): Modules type :=
    match i with
      | O => pinsti O
      | S i' => ConcatMod (pinsti i) (pinsts i')
    end.
  
  Definition minst := memInst n addrSize (Bit valSize).

  Definition sc := ConcatMod (pinsts n) minst.

End SC.

Hint Unfold pinsti pinsts minst sc : ModuleDefs.

Section Facts.
  Variables opIdx addrSize valSize rfIdx : nat.
  Variables opLd opSt opHt: ConstT (Bit opIdx).
  Variable i: nat.

  Variable dec: DecT opIdx addrSize valSize rfIdx.
  Variable exec: ExecT opIdx addrSize valSize rfIdx.

  Lemma regsInDomain_pinsti:
    RegsInDomain (pinsti opIdx _ _ _ dec exec opLd opSt opHt i).
  Proof.
    unfold RegsInDomain; intros; inv H.
    destruct rm; [|inv Hltsmod; inDomain_tac].
    inv Hltsmod; inv HSemMod.
    in_tac_H.
    - inv H; invertActionRep; inDomain_tac.
    - inv H0; invertActionRep; inDomain_tac.
    - inv H; invertActionRep; inDomain_tac.
    - inv H0; invertActionRep; inDomain_tac.
    - inv H; invertActionRep; inDomain_tac.
  Qed.

End Facts.

