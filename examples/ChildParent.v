Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.Indexer.
Require Import Lts.Syntax Lts.MetaSyntax Lts.Notations.
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

  Definition rqToPPop i := MethodSig "rqToP".."deq"__ i (Void): RqToP.
  Definition rqFromCEnq := MethodSig "rqFromC".."enq" (RqFromC): Void.
  Definition rsToPPop i := MethodSig "rsToP".."deq"__ i (Void): RsToP.
  Definition rsFromCEnq := MethodSig "rsFromC".."enq" (RsFromC): Void.

  Definition toCPop := MethodSig "toC".."deq" (Void): ToC.
  Definition fromPEnq i := MethodSig "fromP".."deq"__ i (FromP): Void.

  Definition n := wordToNat (wones LgNumChildren).
  Definition childParent :=
    MODULE {
      Repeat Rule as i till n by "rqFromCToP" :=
        Call rq <- (rqToPPop i)();
        Call rqFromCEnq(STRUCT{"child" ::= $ i; "rq" ::= #rq});
        Retv
              
      with Repeat Rule as i till n by "rsFromCToP" :=
        Call rs <- (rsToPPop i)();
        Call rsFromCEnq(STRUCT{"child" ::= $ i; "rs" ::= #rs});
        Retv

      with Repeat Rule as i till n by "fromPToC" :=
        Call msg <- toCPop();
        Assert $ i == #msg@."child";
        Call (fromPEnq i)(#msg@."msg");
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

