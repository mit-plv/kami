Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.Indexer.
Require Import Lts.Syntax Lts.Wf Lts.Notations.
Require Import Lts.Semantics Lts.Equiv Lts.Tactics.
Require Import Ex.MemTypes.

Set Implicit Arguments.

Section ChildParent.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Definition AddrBits := IdxBits + (LgNumDatas + LgDataBytes).
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

  Definition rqToPPop := MethodSig "rqToP"--"deq" (Void): RqToP.
  Definition rqFromCEnq := MethodSig "rqFromC"--"enq" (RqFromC): Void.
  Definition rsToPPop := MethodSig "rsToP"--"deq" (Void): RsToP.
  Definition rsFromCEnq := MethodSig "rsFromC"--"enq" (RsFromC): Void.

  Definition toCPop := MethodSig "toC"--"deq" (Void): ToC.
  Definition fromPEnq := MethodSig "fromP"--"deq" (FromP): Void.

  Definition n := wordToNat (wones LgNumChildren).
  Definition childParent : Modules :=
    MODULEMETA {
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
Hint Unfold rqToPPop rqFromCEnq rsToPPop rsFromCEnq toCPop fromPEnq n : MethDefs.

Hint Unfold childParent : ModuleDefs.

Section Facts.
  Variables IdxBits LgNumDatas LgDataBytes LgNumChildren: nat.
  Variable Id: Kind.

  Lemma childParent_ModEquiv:
    forall m,
      m = childParent IdxBits LgNumDatas LgDataBytes LgNumChildren Id ->
      (forall ty1 ty2, ModEquiv ty1 ty2 m).
  Proof.
    kequiv.
    unfold childParent; simpl.
    apply RulesEquiv_app; [|apply RulesEquiv_app].
    - induction (n LgNumChildren).
      + kequiv.
      + constructor; [|auto].
        kequiv.
    - induction (n LgNumChildren).
      + kequiv.
      + constructor; [|auto].
        kequiv.
    - induction (n LgNumChildren).
      + kequiv.
      + constructor; [|auto].
        kequiv.
  Qed.

End Facts.

Hint Resolve childParent_ModEquiv.

