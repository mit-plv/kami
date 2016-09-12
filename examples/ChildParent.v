Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.Indexer.
Require Import Kami.Syntax Kami.ParametricSyntax Kami.Wf Kami.ParametricWf Kami.Notations.
Require Import Kami.Semantics Kami.ParametricEquiv Kami.Tactics.
Require Import Ex.MemTypes.

Set Implicit Arguments.

Section ChildParent.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Definition AddrBits := IdxBits.
  Definition Addr := Bit AddrBits.
  Definition Idx := Bit IdxBits.
  Definition Data := Bit (LgDataBytes * 8).
  Definition Offset := Bit LgNumDatas.
  Definition Line := Vector Data LgNumDatas.

  Definition RqToP := Ex.MemTypes.RqToP Addr Id.
  Definition RqFromC := Ex.MemTypes.RqFromC LgNumChildren Addr Id.
  Definition RsToP := Ex.MemTypes.RsToP LgDataBytes LgNumDatas Addr.
  Definition RsFromC := Ex.MemTypes.RsFromC LgDataBytes LgNumDatas LgNumChildren Addr.
  Definition FromP := Ex.MemTypes.FromP LgDataBytes LgNumDatas Addr Id.
  Definition ToC := Ex.MemTypes.ToC LgDataBytes LgNumDatas LgNumChildren Addr Id.

  Definition rqToPPop := MethodSig "rqToParent"--"deq" (Void): RqToP.
  Definition rqFromCEnq := MethodSig "rqFromChild"--"enq" (RqFromC): Void.
  Definition rsToPPop := MethodSig "rsToParent"--"deq" (Void): RsToP.
  Definition rsFromCEnq := MethodSig "rsFromChild"--"enq" (RsFromC): Void.

  Definition toCPop := MethodSig "toChild"--"deq" (Void): ToC.
  Definition fromPEnq := MethodSig "fromParent"--"enq" (FromP): Void.

  Local Notation "'n'" := (wordToNat (wones LgNumChildren)).
  Definition childParent :=
    META {
      Repeat Rule till n with LgNumChildren by "rqFromCToP" :=
        ILET i;  
        Calli rq <- rqToPPop();
        Call rqFromCEnq(STRUCT{"child" ::= #i; "rq" ::= #rq});
        Retv
              
      with Repeat Rule till n with LgNumChildren by "rsFromCToP" :=
        ILET i;  
        Calli rs <- rsToPPop();
        Call rsFromCEnq(STRUCT{"child" ::= #i; "rs" ::= #rs});
        Retv

      with Repeat Rule till n with LgNumChildren by "fromPToC" :=
        ILET i;
        Call msg <- toCPop();
        Assert # i == #msg@."child";
        Calli fromPEnq(#msg@."msg");
        Retv
    }.
  
End ChildParent.

Hint Unfold AddrBits Addr Idx Data Offset Line : MethDefs.
Hint Unfold RqToP RqFromC RsToP RsFromC FromP ToC : MethDefs.
Hint Unfold rqToPPop rqFromCEnq rsToPPop rsFromCEnq toCPop fromPEnq : MethDefs.

Hint Unfold childParent : ModuleDefs.

Section Facts.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Lemma childParent_ModEquiv:
    MetaModPhoasWf (childParent IdxBits LgNumDatas LgDataBytes LgNumChildren Id).
  Proof.
    kequiv.
  Qed.

  Lemma childParent_ValidRegs:
    MetaModRegsWf (childParent IdxBits LgNumDatas LgDataBytes LgNumChildren Id).
  Proof.
    kvr.
  Qed.

End Facts.

Hint Resolve childParent_ModEquiv childParent_ValidRegs.

