Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FnMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement.

Set Implicit Arguments.

Parameter i: nat.

Definition fbCm := MethodSig ("fb"__ i)() : Bool.

Definition ma := MODULE {
  Register "a" : Bool <- Default

  with Rule "ra" :=
    Call vb <- fbCm();
    Write "a" <- #vb;
    Retv
}.

Definition mb := MODULE {
  Register "b" : Bool <- true

  with Method ("fb"__ i)() : Bool :=
    Write "b" <- $$true;
    Read rb <- "b";
    Ret #rb
}.

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
