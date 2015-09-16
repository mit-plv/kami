Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement.

Set Implicit Arguments.

Parameter i: nat.

Section ModuleA.

  Definition regA : RegInitT := Reg#(Bool) "a" <- mkRegU;.
  Definition regsA : list RegInitT := regA::nil.

  Definition ruleA: Action type (Bit 0) :=
    vcall vb <- ("fb"__ i) :@: {| arg := Bit 0; ret := Bool |} #(Cd _) #;
    ("a" <= (V vb) #;
    vret (Cd _) #;).
  
  Definition rulesA : list (Attribute (Action type (Bit 0)))
    := (Build_Attribute "ra" ruleA)::nil.

  Definition defMethsA : list (DefMethT type) := nil.
                              
  Definition ma := Mod regsA rulesA defMethsA.

End ModuleA.

Section ModuleB.

  Definition regB : RegInitT := Reg#(Bool) "b" <- mkReg(ConstBool true);.
  Definition regsB : list RegInitT := regB::nil.

  Definition methBSig : Attribute SignatureT :=
    Method Value#(Bool) ("fb"__ i) #(Bit 0);.

  Definition methB
  : type (arg (attrType methBSig)) -> Action type (ret (attrType methBSig)) :=
    fun _ =>
      "b" <= (C (ConstBool true)) #;
      vread rb <- "b" #;
      vret (V rb) #;.
  
  Definition rulesB : list (Attribute (Action type (Bit 0))) := nil.

  Definition defMethsB : list (DefMethT type) :=
    (Build_Attribute (attrName methBSig)
                     (Build_Typed _ (attrType methBSig) methB))
      ::nil.
                              
  Definition mb := Mod regsB rulesB defMethsB.

End ModuleB.

Section Tests.

  Definition mab := ConcatMod ma mb.

  Lemma mab_prop:
    exists nr,
      LtsStep mab (Some "ra"%string) (initRegs (getRegInits mab)) nr empty empty.
  Proof.
    intros; unfold mab.
    repeat eexists.
    constr_concatMod.
    - econstructor; eauto.
      econstructor; eauto.
      + econstructor; eauto.
        econstructor; eauto.
      + apply Disj_empty_2.
      + apply Disj_empty_2.
    - econstructor; eauto.
      econstructor; eauto.
      + econstructor; eauto.
        econstructor; eauto.
      + apply Disj_empty_2.
      + apply Disj_empty_2.
    - repeat split.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
      + eauto.
  Qed.

End Tests.

