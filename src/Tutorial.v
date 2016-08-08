Require Import Bool String List.

Require Import Lib.FMap Lib.Word.

Require Import Lts.Syntax Lts.Semantics Lts.Wf Lts.Notations.
Require Import Lts.RefinementFacts Lts.Decomposition.
Require Import Lts.Inline Lts.InlineFacts.
Require Import Lts.Tactics.

Set Implicit Arguments.

(** Welcome to the Kami tutorial! This tutorial gives a demo of implementing and verifying a very simple producer-consumer components. *)

(** Kami has its own syntax, which is very similar to Bluespec. Syntax is built with "Notation" in Coq, so module definitions are automatically type-checked internally by the Gallina type-checker. *)

(** Let's design a producer module first. A module consists of registers, rules, and methods. A rule or a method is defined as a sequence of actions. Semantically, rules are executed by a global rule scheduler. Methods are executed by method calls, which can be called by other modules once they are composed. *)

(** Producer has a data register and a rule to send the data to Consumer. *)
Definition producer :=
  MODULE {
    Register "data" : Bit 32 <- Default

    with Rule "produce" :=
      Read data <- "data";
      Call (MethodSig "send" (Bit 32): Void) (#data);
      Write "data" <- #data + $1;
      Retv
  }.

(** For proof automation, it is recommended to register module definitions to "ModuleDefs". *)
Hint Unfold producer : ModuleDefs.

(** Consumer only has one method, which takes the data sent by Producer and call an external function with the data. *)
Definition consumer :=
  MODULE {
    Method "send" (data: Bit 32): Void :=
      Call (MethodSig "extCall" (Bit 32): Void) (#data);
      Retv
  }.
Hint Unfold consumer : ModuleDefs.

(** Now we compose Producer and Consumer to make the complete implementation. *)
Definition producerConsumerImpl := (producer ++ consumer)%kami.
Hint Unfold producerConsumerImpl : ModuleDefs.

(** What is a specification of the Producer-Consumer module? We define specification also as a module in Kami. Specification is usually defined as a single module. In this case, we define the specification simply by calling the external call with the current data and update it as what Producer does. *)
Definition producerConsumerSpec :=
  MODULE {
    Register "data" : Bit 32 <- Default

    with Rule "produce_consume" :=
      Read data <- "data";
      Call (MethodSig "extCall" (Bit 32): Void) (#data);
      Write "data" <- #data + $1;
      Retv
  }.

(** Inlining and Decomposition are mostly used to prove refinement relation between impl and spec. Inlining collapses all internal method calls in impl, which enables us only to consider external calls. Decomposition allows us to relate each fine-grained state transition (by a rule or a method) in impl to one in spec. *)

(** In order to use the decomposition theorem, we have to define two maps, one for rules and the other for internal states. See "src/Notations.v" for detailed notations for mapping. *)
Definition producer_consumer_ruleMap (_: RegsT): string -> option string :=
  "produce" |-> "produce_consume"; ||.
Definition producer_consumer_regMap (r: RegsT): RegsT.
  kgetv "data"%string datav r (Bit 32) (M.empty (sigT (fullType type))).
  exact (M.add "data"%string (existT _ _ datav) (M.empty _)).
Defined.
Hint Unfold producer_consumer_regMap: MethDefs. (* for kdecompose_regMap_init *)

(** The Kami syntax is built by PHOAS, so sometimes we need to prove a PHOAS equivalence for any two variable mappings. Adding the equivalence lemma to the Coq hint database will allow related features to use it automatically. *)
Lemma impl_ModEquiv:
  forall ty1 ty2, ModEquiv ty1 ty2 producerConsumerImpl.
Proof. kequiv. Qed.
Hint Resolve impl_ModEquiv.  

(** Now we are ready to prove the refinement! *)
Theorem producer_consumer_refinement:
  producerConsumerImpl <<== producerConsumerSpec.
Proof.
  kinline_left implInlined. (* Inlining *)
  kdecompose_nodefs producer_consumer_regMap producer_consumer_ruleMap. (* Decomposition *)

  kinvert. (* Inversion for each state transition cases. *)
  kinv_magic_light. (* We have only one case for this example, which is easy. *)
Qed.

(** We can also build refinement proofs by the one-line tactic with a proof configuration. *)
Definition producer_consumer_refinement_config :=
  {| inlining := true;
     decomposition := DTFunctional producer_consumer_regMap producer_consumer_ruleMap;
     invariants := IVNil
  |}.

(** Here is the shortest proof of the refinement. *)
Theorem producer_consumer_refinement_again:
  producerConsumerImpl <<== producerConsumerSpec.
Proof.
  kami_ok producer_consumer_refinement_config idtac.
Qed.

