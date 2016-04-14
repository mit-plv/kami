Require Import Bool String List.
Require Import Lib.Struct Lib.StringEq Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Wf Lts.Refinement.
Require Import Lts.Inline Lts.InlineFacts_2.
Require Import Lts.Decomposition Lts.DecompositionZero.

Set Implicit Arguments.

Ltac kinline_compute :=
  repeat autounfold with ModuleDefs;
  repeat autounfold with MethDefs;
  cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule'
               wfModules wfRules wfDms wfAction wfActionC maxPathLength
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               appendName append
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb];
  repeat
    match goal with
    | [ |- context[SignatureT_dec ?s ?s] ] =>
      rewrite (signature_eq s); unfold eq_rect
    end.

Ltac kinline_compute_in H :=
  repeat autounfold with ModuleDefs in H;
  repeat autounfold with MethDefs in H;
  cbv [inlineF inline inlineDms inlineDms'
               inlineDmToMod inlineDmToRules inlineDmToRule
               inlineDmToDms inlineDmToDm inlineDm
               filterDms filter
               noInternalCalls noCalls
               noCallsRules noCallsDms noCallDm isLeaf
               getBody inlineArg
               appendAction getAttribute
               makeModule makeModule'
               wfModules wfRules wfDms wfAction wfActionC maxPathLength
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               appendName append
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb] in H;
  repeat
    match type of H with
    | context[SignatureT_dec ?s ?s] =>
      rewrite (signature_eq s) in H; unfold eq_rect in H
    end.

Ltac kinline_left im :=
  match goal with
  | [ |- traceRefines _ ?lm _ ] =>
    apply traceRefines_inlining_left; auto;
    let Heq := fresh "Heq" in
    remember (inlineF lm) as im eqn:Heq;
    kinline_compute_in Heq;
    split; [|subst; reflexivity]
  end.

Ltac kdecompose t r Hrm Hmm :=
  eapply decomposition with (theta:= t)
                              (ruleMap:= r)
                              (substepRuleMap:= Hrm)
                              (substepMethMap:= Hmm); auto; intros.

Ltac kdecompose_nodefs t r :=
  apply decompositionZero with (theta:= t) (ruleMap:= r).

Ltac kgetv k v m t f :=
  destruct (M.find k m) as [[[kind|] v]|]; [|exact f|exact f];
  destruct (decKind kind t); [subst|exact f].

(* TODO: "v" is not working *)
Ltac kexistv k v m t :=
  refine (exists v: fullType type (SyntaxKind t),
             M.find k m = Some (existT _ _ v) /\ _).

