Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq Lib.Indexer.

Require Import Lts.Syntax Lts.Semantics Lts.SemOp Lts.Equiv Lts.Wf.
Require Import Lts.Inline Lts.InlineFacts_1 Lts.InlineFacts_2.
Require Import Lts.Refinement Lts.Decomposition.
Require Import Lts.Tactics.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition fbCm := MethodSig "fb"() : Bool.

Definition ma := MODULE {
  Register "a" : Bool <- Default

  with Rule "ra" :=
    Call vb <- fbCm();
    Write "a" <- #vb;
    Retv
}.

Definition mb := MODULE {
  Register "b" : Bool <- true

  with Method "fb"() : Bool :=
    Write "b" <- $$true;
    Read rb <- "b";
    Ret #rb
}.

Definition mc := MODULE {
  Register "a" : Bool <- Default
  with Register "b" : Bool <- true

  with Rule "ra" :=                           
    Write "b" <- $$true;
    Read rb : Bool <- "b";
    Write "a" <- #rb;
    Retv
}.

Hint Unfold ma mb mc: ModuleDefs.
Hint Unfold fbCm: MethDefs.

Section Facts.

  Definition theta : RegsT -> RegsT := id.
  Definition ruleMap : RegsT -> string -> option string :=
    fun _ r => Some r.

  Lemma mab_ModEquiv: ModEquiv type typeUT (ConcatMod ma mb).
  Proof. kequiv. Qed.
  Hint Resolve mab_ModEquiv.

  Lemma mab_mc: (ConcatMod ma mb) <<== mc.
  Proof.
    kinline_left mabi.
    kdecompose_nodefs theta ruleMap.
    kss_invert; kinv_magic.
    admit.
  Qed.
  
End Facts.

