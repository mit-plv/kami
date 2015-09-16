Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.

Set Implicit Arguments.

(* A decoupled processor Pdec, where data memory is detached
 * so load/store requests may not be responded in a cycle.
 * This processor does NOT use a ROB, which implies that it just stalls
 * until getting a memory operation response.
 *)
Section ProcDec.
  Variable i: nat.
  Variable inName outName: string.
  Variables addrSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition getNextPc ppc st inst := fst (exec st ppc inst).
  Definition getNextState ppc st := snd (exec st ppc (dec st ppc)).

  Definition opLd : ConstT (Bit 2) := ConstBit (WO~0~0).
  Definition opSt : ConstT (Bit 2) := ConstBit (WO~0~1).
  Definition opHt : ConstT (Bit 2) := ConstBit (WO~1~0).

  (* Registers *)
  Definition pcReg : RegInitT := Reg#(Bit addrSize) ("pc"__ i) <- mkRegU;.
  Definition rfReg : RegInitT := Reg#(Vector (Bit valSize) rfIdx) ("rf"__ i) <- mkRegU;.
  Definition stallReg : RegInitT := Reg#(Bool) ("stall"__ i) <- mkReg(ConstBool false);.

  Definition procRegs : list RegInitT := pcReg::rfReg::stallReg::nil.

  (* Called method signatures *)
  Definition memReqSig : Attribute SignatureT :=
    Method Value#(Bit 0) (inName -n- "enq") #(memAtomK addrSize valSize);.
  Definition memRepSig : Attribute SignatureT :=
    Method Value#(memAtomK addrSize valSize) (outName -n- "deq") #(Bit 0);.
  Definition haltSig : Attribute SignatureT :=
    Method Value#(Bit 0) ("HALT"__ i) #(Bit 0);.

  (* Module interface *)
  Definition procDms : list (DefMethT type) := nil.
  
  Definition build_ldExprT addr
  : Expr type (memAtomK addrSize valSize) :=
    ST (icons (Build_Attribute "type" _) (C memLd)
              (icons (Build_Attribute "addr" _) addr
                     (icons (Build_Attribute "value" _) (Cd _)
                            (inil _)))).

  Definition build_stExprT addr val
  : Expr type (memAtomK addrSize valSize) :=
    ST (icons (Build_Attribute "type" _) (C opSt)
              (icons (Build_Attribute "addr" _) addr
                     (icons (Build_Attribute "value" _) val
                            (inil _)))).

  Definition retVoid : Action type (Bit 0) :=
    vret (Cd (Bit 0)) #;.

  Definition continuePcSt cont: Action type (Bit 0) :=
    vread ppc :@: (objType (attrType pcReg)) <- (attrName pcReg) #;
    vread st :@: (objType (attrType rfReg)) <- (attrName rfReg) #;
    (cont ppc st).

  Definition nextPc ppc st: Action type (Bit 0) :=
    (attrName pcReg) <= (V (getNextPc ppc st (dec st ppc))) #;
    retVoid.

  Definition reqLd :=
    vread stall :@: (objType (attrType stallReg)) <- (attrName stallReg) #;
    vassert (V stall == C (ConstBool false)) #;
    (continuePcSt
       (fun ppc st =>
          vassert ((V (dec st ppc)) @> "opcode" #[] == C opLd) #;
          vcall (attrName memReqSig) :@: (attrType memReqSig)
          #(build_ldExprT ((V (dec st ppc)) @> "addr" #[])) #;
          (attrName stallReg) <= (C (ConstBool true)) #;
          retVoid)).

  Definition reqSt :=
    vread stall :@: (objType (attrType stallReg)) <- (attrName stallReg) #;
    vassert (V stall == C (ConstBool false)) #;
    (continuePcSt
       (fun ppc st =>
          vassert ((V (dec st ppc)) @> "opcode" #[] == C opSt) #;
          vcall (attrName memReqSig) :@: (attrType memReqSig)
          #(build_stExprT ((V (dec st ppc)) @> "addr" #[])
                          ((V (dec st ppc)) @> "value" #[])) #;
          (attrName stallReg) <= (C (ConstBool true)) #;
          retVoid)).

  Definition repLd: Action type (Bit 0) :=
    vcall val <- (attrName memRepSig) :@: (attrType memRepSig)
          #(Cd (Bit 0)) #;
    (continuePcSt
       (fun ppc st =>
          vassert ((V val) @> "type" #[] == C opLd) #;
          (attrName rfReg) <= ((V st) @[(V (dec st ppc)) @> "reg" #[] <-
                                        (V val) @> "value" #[]]) #;
          (attrName stallReg) <= (C (ConstBool false)) #;
          (nextPc ppc st))).

  Definition repSt: Action type (Bit 0) :=
    vcall val <- (attrName memRepSig) :@: (attrType memRepSig)
          #(Cd (Bit 0)) #;
    (continuePcSt
       (fun ppc st =>
          vassert ((V val) @> "type" #[] == C opSt) #;
          (attrName stallReg) <= (C (ConstBool false)) #;
          (nextPc ppc st))).
  
  Definition execHt :=
    vread stall :@: (objType (attrType stallReg)) <- (attrName stallReg) #;
    vassert (V stall == C (ConstBool false)) #;
    (continuePcSt
       (fun ppc st =>
          vassert ((V (dec st ppc)) @> "opcode" #[] == C opHt) #;
          vcall (attrName haltSig) :@: (attrType haltSig) #(Cd (Bit 0)) #;
          vret (Cd _) #;)).

  Definition execNm :=
    vread stall :@: (objType (attrType stallReg)) <- (attrName stallReg) #;
    vassert (V stall == C (ConstBool false)) #;
    (continuePcSt
       (fun ppc st =>
          vassert (Not ((V (dec st ppc) @> "opcode" #[] == C opLd) OR
                        (V (dec st ppc) @> "opcode" #[] == C opSt) OR
                        (V (dec st ppc) @> "opcode" #[] == C opHt))) #;
          (attrName rfReg) <= V (getNextState ppc st) #;
          (nextPc ppc st))).
  
  Definition procRules : list (Attribute (Action type (Bit 0))) :=
    (Build_Attribute ("reqLd"__ i) reqLd)
      ::(Build_Attribute ("reqSt"__ i) reqSt)
      ::(Build_Attribute ("repLd"__ i) repLd)
      ::(Build_Attribute ("repSt"__ i) repSt)
      ::(Build_Attribute ("execHt"__ i) execHt)
      ::(Build_Attribute ("execNm"__ i) execNm)
      ::nil.
  
  Definition procDefMeths : list (DefMethT type) := nil.

  Definition procDec := Mod procRegs procRules procDefMeths.

End ProcDec.

Hint Unfold procRules getNextPc continuePcSt nextPc reqLd reqSt repLd repSt execHt execNm
     memReqSig memRepSig haltSig.
Hint Unfold procDec : ModuleDefs.

Section ProcDecM.
  Variables addrSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition pdeci (i: nat) := procDec i ("Ins"__ i) ("Outs"__ i) dec exec.

  Definition pdecfi (i: nat) := ConcatMod (pdeci i) (iomi addrSize (Bit valSize) i).

  Fixpoint pdecfs (i: nat) :=
    match i with
      | O => pdecfi O
      | S i' => ConcatMod (pdecfi i) (pdecfs i')
    end.

  Definition procDecM (n: nat) := ConcatMod (pdecfs n) (minst addrSize (Bit valSize) n).

  Section Facts.

    Lemma regsInDomain_pdeci i: RegsInDomain (pdeci i).
    Proof.
      unfold RegsInDomain; intros.
      destRule H; try (inv HSemMod); invertActionRep; inDomain_tac.
      inv Hltsmod; reflexivity.
    Qed.

    Lemma regsInDomain_pdecfi i: RegsInDomain (pdecfi i).
    Proof.
      apply concatMod_RegsInDomain;
      [apply regsInDomain_pdeci|apply regsInDomain_iomi].
    Qed.

  End Facts.

End ProcDecM.

Hint Unfold pdeci pdecfi pdecfs procDecM : ModuleDefs.
