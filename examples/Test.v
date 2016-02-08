Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.

Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Wf.
Require Import Lts.Inline Lts.InlineFacts_1 Lts.InlineFacts_2.
Require Import Lts.Decomposition.

Set Implicit Arguments.

Parameter i: nat.

Definition fbCm := MethodSig "fb"() : Bool.

(* Test below after implementing alpha-renaming *)
(* Definition fbCm := MethodSig ("fb"__ i)() : Bool. *)

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

Section Tests.

  Definition p : MethsT -> MethsT := id.
  
  Lemma mab_mc: traceRefines p (ConcatMod ma mb) mc.
  Proof.
    unfold traceRefines; intros.
    inv H; induction HMultistepBeh.

    - exists (initRegs (getRegInits mc)), nil.
      split; [|constructor].
      repeat constructor.

    - apply inline_correct in HStep.

      + simpl in HStep.
        unfold inlineDmToRule, inlineDmToDm in HStep.
        simpl in HStep.
        unfold getBody in HStep.
        simpl in HStep.
        destruct (SignatureT_dec _ _); [|elim n0; reflexivity].
        simpl in HStep.
        rewrite <-Eqdep.Eq_rect_eq.eq_rect_eq in HStep.
        unfold appendAction in HStep.

        admit.

      + repeat constructor.
      + repeat constructor.
        simpl; auto.
      + reflexivity.

  Qed.

End Tests.
