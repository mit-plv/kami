Require Import Bool String List Eqdep.
Require Import Lib.CommonTactics Lib.Word Lib.ilist Lib.StringBound Lib.Struct.
Require Import Lib.Indexer Lib.StringEq Lib.FMap.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Notations Lts.Semantics Lts.SemFacts.
Require Import Lts.Wf Lts.ParametricWf Lts.Equiv Lts.ParametricEquiv Lts.Refinement.
Require Import Lts.Inline Lts.InlineFacts_2 Lts.Specialize Lts.Duplicate.
Require Import Lts.Decomposition Lts.DecompositionZero Lts.ModuleBound Lts.ParametricEquiv.

Set Implicit Arguments.

(**
- Kami Tactics
  + krefl : prove (a <<== a)
  + ktrans : for given "b", convert (a <<== c) into two subgoals (a <<== b) and (b <<== c)
  + kmodular : convert (a + b <<== c + d) to (a <<== c) /\ (b <<== d) (interacting case)
  + kmodularn : convert (a + b <<== c + d) to (a <<== c) /\ (b <<== d) (non-interacting case)
  + kmodular_sim_l : convert (a + c) <<== (b + c) to (a <<== b)
  + kmodular_sim_r : convert (c + a) <<== (c + b) to (a <<== b)
  + kmodularn : convert (a + b <<== c + d) to (a <<== c) /\ (b <<== d) (non-interacting case)
  + kequiv : prove any PHOAS equivalences defined in src/Equiv.v
  + kvr : prove well-formedness conditions for valid register uses
  + kdisj_regs : prove DisjList conditions of regs
  + kdisj_dms : prove DisjList conditions of dms
  + kdisj_cms : prove DisjList conditions of cms
  + kdef_call_sub : prove DefCallSub conditions
  + kinline_compute : compute terms with _inlineF_
  + kinline_compute_in _term_ : compute terms with _inlineF_ in _term_
  + kinline_left : convert (a <<== b) to (inlineF a <<== b), where (inlineF a) is computed
  + kdecompose : apply the decomposition theorem
  + kdecompose_nodefs : apply the decompositionZero theorem,
    for modules with no defined methods.
  + kduplicated : convert (duplicate a <<== duplicate b) to (a <<== b)
  + kgetv/kexistv : used to construct register or label mappings

  + kinvert : invert Kami semantic definitions (Substep, Step, etc.)
  + kinv_magic : try to solve invariant proofs
    * kinv_simpl : simplify invariants
    * kinv_red : reduce invariants
    * kinv_contra : try to prove exfalso with invariants
    * kinv_finish : try to prove invariants.
  + kinv_magic_with _tactic_ : also try to apply _tactic_ alternately

- Kami Hints
  + Hint Extern 1 (Specializable _) => vm_compute; reflexivity.
  + Hint Extern 1 (SubList (getExtMeths _) (getExtMeths _)) => vm_compute; tauto.
  + Hint Extern 1 (_ = _: Modules) => apply eq_refl.
 *)

Ltac kstring_simpl :=
  cbv [withPrefix prefixSymbol append] in *.

Ltac krefl :=
  try rewrite idElementwiseId; apply traceRefines_refl.

Ltac ktrans m :=
  try rewrite idElementwiseId; apply traceRefines_trans with (p:= id) (q:= id) (mb:= m).

Ltac ketrans :=
  let m := fresh "m" in evar (m: Modules); ktrans m; unfold m; clear m.

Ltac kmodular :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_interacting with (vp:= (@idElementwise _)); auto.

Tactic Notation "simple" "kmodular" :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_interacting with (vp:= (@idElementwise _)).

Ltac kmodularn :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting; auto.

Tactic Notation "simple" "kmodularn" :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting.

Ltac kmodular_sim_l :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure_modular_1.

Ltac kmodular_sim_r :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure_modular_2.

Ltac unfold_head m :=
  match m with
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ _ =>
    unfold hdef
  | ?hdef _ _ _ =>
    unfold hdef
  | ?hdef _ _ =>
    unfold hdef
  | ?hdef _ =>
    unfold hdef
  | ?hdef =>
    unfold hdef
  end.

Ltac unfold_head_ret m :=
  match m with
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef _ =>
    let m' := eval cbv [hdef] in m in m'
  | ?hdef =>
    let m' := eval cbv [hdef] in m in m'
  end.

Ltac kequiv_red :=
  eauto;
  match goal with
  | [ |- ModEquiv _ _ _ ] => apply duplicate_ModEquiv
  | [ |- ModEquiv _ _ _ ] => apply ModEquiv_modular
  | [ |- ModEquiv _ _ _ ] => apply metaModEquiv_modEquiv
  | [ |- MetaModEquiv _ _ _ ] => apply metaModEquiv_modular
  | [ |- ModEquiv _ _ ?m ] => unfold_head m
  | [ |- MetaModEquiv _ _ ?m ] => unfold_head m
  end.
 
Ltac kequiv_unit :=
  match goal with
  (* for normal modules *)
  | [ |- ModEquiv _ _ _ ] => constructor; intros
  | [ |- RuleEquiv _ _ _ ] => unfold RuleEquiv; intros
  | [ |- MethEquiv _ _ _ ] => unfold MethEquiv; intros
  | [ |- RulesEquiv _ _ _ ] => apply MetaRulesEquiv_RulesEquiv
  | [ |- RulesEquiv _ _ _ ] => constructor; intros
  | [ |- MethsEquiv _ _ _ ] => apply MetaMethsEquiv_MethsEquiv
  | [ |- MethsEquiv _ _ _ ] => constructor; intros
  | [ |- ActionEquiv _ _ ] => constructor; intros
  (* for meta modules *)
  | [ |- MetaModEquiv _ _ _ ] => constructor; intros
  | [ |- MetaRulesEquiv _ _ _ ] => constructor; intros
  | [ |- MetaRuleEquiv _ _ _ ] => constructor; intros
  | [ |- MetaMethsEquiv _ _ _ ] => constructor; intros
  | [ |- MetaMethEquiv _ _ _ ] => constructor; intros
  | [ |- SinActionEquiv _ _ _ _ ] => constructor; intros
  | [ |- GenActionEquiv _ _ _ _ _ ] => constructor; intros
  | [ |- In _ _] => simpl; tauto
  end.

Ltac kequiv :=
  intros;
  (* repeat autounfold with MethDefs; *)
  repeat kequiv_red;
  repeat kequiv_unit.

Ltac kvr_red :=
  eauto;
  match goal with
  | [ |- ValidRegsModules _ (ConcatMod _ _) ] => split
  | [ |- ValidRegsModules _ (Mod (getRegInits ?m) (getRules ?m) (getDefsBodies ?m)) ] =>
    apply validRegsModules_flatten
  | [ |- ValidRegsModules _ (duplicate _ _) ] => apply duplicate_validRegsModules
  | [ |- ValidRegsModules _ (modFromMeta _) ] => apply validRegsMetaModule_validRegsModules
  | [ |- ValidRegsMetaModule _ (_ +++ _) ] => apply validRegsMetaModule_modular
  | [ |- ValidRegsModules _ ?m ] => unfold_head m
  | [ |- ValidRegsMetaModule _ ?mm ] => unfold_head mm
  end.

Ltac kvr_unit :=
  match goal with
  (* for normal modules *)
  | [ |- ValidRegsModules _ _ ] => constructor; intros
  | [ |- ValidRegsRules _ _ _ ] => constructor; intros
  | [ |- ValidRegsDms _ _ _ ] => constructor; intros
  | [ |- ValidRegsAction _ _ ] => constructor; intros
  (* for meta modules *)
  | [ |- ValidRegsMetaModule _ _ ] => constructor; intros
  | [ |- ValidRegsMetaRules _ _ _ ] => constructor; intros
  | [ |- ValidRegsMetaRule _ _ _ ] => constructor; intros
  | [ |- ValidRegsMetaMeths _ _ _ ] => constructor; intros
  | [ |- ValidRegsMetaMeth _ _ _ ] => constructor; intros
  | [ |- ValidRegsSinAction _ _ ] => constructor; intros
  | [ |- ValidRegsGenAction _ _ ] => constructor; intros
  | [ |- In _ _] => simpl; tauto
  end.

Ltac kvr :=
  intros;
  (* repeat autounfold with MethDefs; *)
  repeat kvr_red;
  repeat kvr_unit.

Ltac get_minimal_regs_bound m :=
  lazymatch m with
  | duplicate ?sm _ => constr:(getRegsBound sm)
  | modFromMeta ?mm => constr:(getRegsBoundM mm)
  | ConcatMod ?m1 ?m2 =>
    let mb1 := get_minimal_regs_bound m1 in
    let mb2 := get_minimal_regs_bound m2 in
    constr:(mb1 ++ mb2)
  | _ =>
    let m' := unfold_head_ret m in
    get_minimal_regs_bound m'
  | _ => constr:(getRegsBound m)
  end.

Ltac get_minimal_dms_bound m :=
  lazymatch m with
  | duplicate ?sm _ => constr:(getDmsBound sm)
  | modFromMeta ?mm => constr:(getDmsBoundM mm)
  | ConcatMod ?m1 ?m2 =>
    let mb1 := get_minimal_dms_bound m1 in
    let mb2 := get_minimal_dms_bound m2 in
    constr:(mb1 ++ mb2)
  | _ =>
    let m' := unfold_head_ret m in
    get_minimal_dms_bound m'
  | _ => constr:(getDmsBound m)
end.

Ltac get_minimal_cms_bound m :=
  lazymatch m with
  | duplicate ?sm _ => constr:(getCmsBound sm)
  | modFromMeta ?mm => constr:(getCmsBoundM mm)
  | ConcatMod ?m1 ?m2 =>
    let mb1 := get_minimal_cms_bound m1 in
    let mb2 := get_minimal_cms_bound m2 in
    constr:(mb1 ++ mb2)
  | _ =>
    let m' := unfold_head_ret m in
    get_minimal_cms_bound m'
  | _ => constr:(getCmsBound m)
  end.

Ltac red_to_regs_bound :=
  match goal with
  | [ |- DisjList (namesOf (getRegInits ?m1))
                  (namesOf (getRegInits ?m2)) ] =>
    let mb1' := get_minimal_regs_bound m1 in
    let mb2' := get_minimal_regs_bound m2 in
    apply regsBound_disj_regs with (mb1 := mb1') (mb2 := mb2')
  | [ |- DisjList (map _ (getRegInits ?m1))
                  (map _ (getRegInits ?m2)) ] =>
    let mb1' := get_minimal_regs_bound m1 in
    let mb2' := get_minimal_regs_bound m2 in
    apply regsBound_disj_regs with (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_dms_bound :=
  match goal with
  | [ |- DisjList (getDefs ?m1) (getDefs ?m2) ] =>
    let mb1' := get_minimal_dms_bound m1 in
    let mb2' := get_minimal_dms_bound m2 in
    apply dmsBound_disj_dms with (mb1 := mb1') (mb2 := mb2')
  | [ |- DisjList (namesOf (getDefsBodies ?m1)) (namesOf (getDefsBodies ?m2)) ] =>
    let mb1' := get_minimal_dms_bound m1 in
    let mb2' := get_minimal_dms_bound m2 in
    apply dmsBound_disj_dms with (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_cms_bound :=
  match goal with
  | [ |- DisjList (getCalls ?m1) (getCalls ?m2) ] =>
    let mb1' := get_minimal_cms_bound m1 in
    let mb2' := get_minimal_cms_bound m2 in
    apply cmsBound_disj_calls with (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_dc_bound :=
  match goal with
  | [ |- DisjList (getDefs ?m1) (getCalls ?m2) ] =>
    let mb1' := get_minimal_dms_bound m1 in
    let mb2' := get_minimal_cms_bound m2 in
    apply bound_disj_dms_calls with (mb1 := mb1') (mb2 := mb2')
  end.

Ltac red_to_cd_bound :=
  match goal with
  | [ |- DisjList (getCalls ?m1) (getDefs ?m2) ] =>
    let mb1' := get_minimal_cms_bound m1 in
    let mb2' := get_minimal_dms_bound m2 in
    apply bound_disj_calls_dms with (mb1 := mb1') (mb2 := mb2')
  end.

Ltac regs_bound_tac :=
  repeat (
      apply getRegsBoundM_bounded
      || apply getRegsBound_modular
      || apply concatMod_regsBound_1
      || (apply getRegsBound_duplicate; auto)
      || apply getRegsBound_bounded).

Ltac dms_bound_tac :=
  repeat (
      apply getDmsBoundM_bounded
      || apply getDmsBound_modular
      || apply concatMod_dmsBound_1
      || (apply getDmsBound_duplicate; auto)
      || apply getDmsBound_bounded).

Ltac cms_bound_tac :=
  repeat (
      apply getCmsBoundM_bounded
      || apply getCmsBound_modular
      || apply concatMod_cmsBound_1
      || (apply getCmsBound_duplicate; auto)
      || apply getCmsBound_bounded).

Ltac kdisj_regs :=
  red_to_regs_bound; (* always reduces to three subgoals *)
  [apply disjPrefixes_DisjPrefixes; reflexivity
  |regs_bound_tac
  |regs_bound_tac].

Ltac kdisj_dms :=
  red_to_dms_bound; (* always reduces to three subgoals *)
  [apply disjPrefixes_DisjPrefixes; reflexivity
  |dms_bound_tac
  |dms_bound_tac].

Ltac kdisj_cms :=
  red_to_cms_bound; (* always reduces to three subgoals *)
  [apply disjPrefixes_DisjPrefixes; reflexivity
  |cms_bound_tac
  |cms_bound_tac].

Ltac kdisj_dms_cms :=
  red_to_dc_bound;
  [apply disjPrefixes_DisjPrefixes; reflexivity
  |dms_bound_tac
  |cms_bound_tac].

Ltac kdisj_cms_dms :=
  red_to_cd_bound;
  [apply disjPrefixes_DisjPrefixes; reflexivity
  |cms_bound_tac
  |dms_bound_tac].

Ltac kinteracting := repeat split.

Ltac knoninteracting :=
  split; [kdisj_dms_cms|kdisj_cms_dms].

Ltac kdef_call_sub :=
  repeat
    match goal with
    | [ |- DefCallSub _ _ ] => apply DefCallSub_refl
    | [ |- DefCallSub _ _ ] => apply duplicate_defCallSub; auto
    | [ |- DefCallSub _ _ ] => vm_compute; split; intros; intuition idtac
    end.

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
               makeModule makeModule' max plus
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb];
  kstring_simpl;
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
               makeModule makeModule' max plus
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               eqb existsb andb orb negb] in H;
  kstring_simpl;
  repeat
    match type of H with
    | context[SignatureT_dec ?s ?s] =>
      rewrite (signature_eq s) in H; unfold eq_rect in H
    end.

Ltac kinline_left im :=
  match goal with
  | [ |- traceRefines _ ?lm _ ] =>
    apply traceRefines_inlining_left; eauto;
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

Ltac kregmap_red :=
  repeat autounfold with MethDefs in *;
  repeat
    (kstring_simpl;
     try match goal with
         | [H: M.find ?k ?m = _ |- context[M.find ?k ?m] ] => rewrite H
         | [H1: M.find ?k ?m = _, H2: context[M.find ?k ?m] |- _] => rewrite H1 in H2
         | [ |- context[decKind ?k ?k] ] =>
           rewrite kind_eq; unfold eq_rect_r, eq_rect, eq_sym
         | [H: context[decKind ?k ?k] |- _] =>
           rewrite kind_eq in H; unfold eq_rect_r, eq_rect, eq_sym in H
         end;
     dest; try subst;
     try findReify);
  repeat
    match goal with
    | [H: M.find _ _ = _ |- _] => clear H
    end.

Ltac kdecompose_regmap_init :=
  unfold initRegs, getRegInits; simpl;
  kregmap_red; try reflexivity.

Ltac kdecompose_regrel_init :=
  unfold initRegs, getRegInits; simpl;
  kregmap_red; eexists; split; reflexivity.

Ltac kdecompose_nodefs t r :=
  apply decompositionZero with (theta:= t) (ruleMap:= r); intros; subst;
  try reflexivity; (* "getDefsBodies _ = nil" conditions *)
  try kdecompose_regmap_init.

Ltac kdecomposeR_nodefs t r :=
  apply decompositionZeroR with (thetaR:= t) (ruleMap:= r); intros; subst;
  try reflexivity; (* "getDefsBodies _ = nil" conditions *)
  try kdecompose_regrel_init.

Ltac kinv_add inv :=
  match goal with
  | [H: reachable _ _ |- _] =>
    let Hr := fresh "Hr" in
    pose proof H as Hr; apply inv in Hr
  end.

Ltac kinv_add_end :=
  match goal with
  | [H: reachable _ _ |- _] => clear H
  end.

Ltac kinvert :=
  repeat
    match goal with
    | [H1: ?t, H2: ?t -> _ |- _] => specialize (H2 H1)
    | [H: Substep _ _ _ _ _ |- _] => inv H; CommonTactics.dest_in
    | [H: Step _ _ _ _ |- _] =>
      apply stepZero in H; [|reflexivity]; destruct H
    end.

Ltac kinv_contra :=
  try (exfalso;
       repeat autounfold with MethDefs in *;
       repeat autounfold with InvDefs in *; dest; subst;
       repeat
         (match goal with
          | [H: false = true |- _] => inversion H
          | [H: true = false |- _] => inversion H
          | [H: negb _ = true |- _] => apply negb_true_iff in H; subst
          | [H: negb _ = false |- _] => apply negb_false_iff in H; subst
          end; dest; try subst);
       fail).

Lemma Some_inv: forall A (s t: A), Some s = Some t -> s = t.
Proof.
  intros; inv H; reflexivity.
Qed.

Ltac kinv_simpl :=
  kstring_simpl;
  repeat
    (try match goal with
         | [H: ?t = ?t |- _] => clear H
         | [H: negb _ = true |- _] => apply negb_true_iff in H; subst
         | [H: negb _ = false |- _] => apply negb_false_iff in H; subst
         | [ |- context [weq ?w ?w] ] =>
           let n := fresh "n" in destruct (weq w w) as [|n]; [|elim n; reflexivity]
         | [H: context [weq ?w ?w] |- _] =>
           let n := fresh "n" in destruct (weq w w) as [|n]; [|elim n; reflexivity]
         | [H: (if ?c then true else false) = true |- _] => destruct c; [|inv H]
         | [H: (if ?c then true else false) = false |- _] => destruct c; [inv H|]
         | [H: (if ?c then false else true) = true |- _] => destruct c; [inv H|]
         | [H: (if ?c then false else true) = false |- _] => destruct c; [|inv H]
         | [H1: M.find ?k ?m = _, H2: M.find ?k ?m = _ |- _] => rewrite H1 in H2
         | [H: Some _ = Some _ |- _] => apply Some_inv in H; destruct_existT
         end; dest; try subst).

Ltac kinv_red :=
  repeat autounfold with InvDefs in *;
  dest; try subst; kinv_simpl.

Ltac kinv_finish :=
  unfold IndexBound_head, IndexBound_tail, mapAttr, addFirstBoundedIndex, bindex in *;
  repeat autounfold with MethDefs;
  simpl in *;
  repeat
    (try match goal with
         | [H: _ = _ |- _] => rewrite H in *; clear H
         | [H: _ = _ |- _] => rewrite <-H in *; clear H
         end;
     simpl in *; kinv_simpl; auto).

Ltac kinv_action_dest := kinv_red; invertActionRep.
Ltac kinv_custom tac := kinv_red; try tac; kinv_red; kinv_contra.
Ltac kinv_regmap_red := kinv_red; kregmap_red.
Ltac kinv_constr :=
  repeat
    (kinv_red;
     repeat match goal with
            | [ |- exists _, _ /\ _ ] => eexists; split
            | [ |- Substep _ _ _ _ _ ] => econstructor
            | [ |- In _ _ ] => simpl; tauto
            | [ |- SemAction _ _ _ _ _ ] => econstructor
            | [ |- _ = _ ] => reflexivity
            end
    ).
Ltac kinv_eq :=
  repeat
    (first [reflexivity
           |meqReify
           |boundedMapTac
    ]).

Ltac kinv_magic_with tac :=
  kinv_action_dest;
  kinv_custom tac;
  kinv_regmap_red;
  kinv_constr;
  kinv_eq;
  kinv_finish.

Ltac kinv_magic := kinv_magic_with idtac.

Ltac kinv_magic_light_with tac :=
  kinv_action_dest;
  kinv_custom tac;
  kinv_regmap_red;
  kinv_constr;
  kinv_eq.

Ltac kinv_magic_light := kinv_magic_light_with idtac.

Ltac kduplicated := apply duplicate_traceRefines; auto.

Ltac kgetv k v m t f :=
  destruct (M.find k m) as [[[kind|] v]|]; [|exact f|exact f];
  destruct (decKind kind t); [subst|exact f].

(* TODO: "v" is not working *)
Ltac kexistv k v m t :=
  refine (exists v: fullType type (SyntaxKind t),
             M.find k m = Some (existT _ _ v) /\ _).
Ltac kexistnv k v m t :=
  refine (exists v: fullType type t,
             M.find k m = Some (existT _ _ v) /\ _).

Hint Extern 1 (Specializable _) => vm_compute; reflexivity.
Hint Extern 1 (SubList (getExtMeths _) (getExtMeths _)) => vm_compute; tauto.
Hint Extern 1 (_ = _: Modules) => apply eq_refl.

(** Final Kami proof configuration *)

Inductive DecompositionType :=
| DTFunctional:
    forall (theta: RegsT -> RegsT)
           (ruleMap: RegsT -> string -> option string),
      DecompositionType
| DTRelational:
    forall (thetaR: RegsT -> RegsT -> Prop)
           (ruleMap: RegsT -> string -> option string),
      DecompositionType.

Inductive Invariants :=
| IVNil: Invariants
| IVCons: forall InvT, InvT -> Invariants -> Invariants.

Ltac kinv_add_rep' invs :=
  lazymatch invs with
  | IVNil => idtac
  | IVCons ?inv ?invs' => kinv_add inv; kinv_add_rep' invs'
  end.
Ltac kinv_add_rep invs :=
  kinv_add_rep' invs; kinv_add_end.

Record ProofConfig := { inlining : bool;
                        decomposition : DecompositionType;
                        invariants : Invariants
                      }.

Ltac kami_ok cfg inv_util :=
  match eval hnf in (inlining cfg) with
  | true =>
    let im := fresh "im" in
    kinline_left im
  | false => idtac
  end;
  match eval hnf in (decomposition cfg) with
  | DTFunctional ?sm ?rm => kdecompose_nodefs sm rm
  | DTRelational ?sr ?rm => kdecomposeR_nodefs sr rm
  end;
  let invs := (eval hnf in (invariants cfg)) in
  kinv_add_rep invs;
  kinvert; kinv_magic_with inv_util.

(** Notations for rule maps *)
Notation "from '|->' to ; cont" :=
  (fun s => if string_dec s from
            then Some to%string
            else (cont s)) (at level 12, right associativity).
Notation "||" := (fun _ => None) (at level 12).

(** Invariant-related definitions *)
Definition or3 (b1 b2 b3: Prop) := b1 \/ b2 \/ b3.
Tactic Notation "or3_fst" := left.
Tactic Notation "or3_snd" := right; left.
Tactic Notation "or3_thd" := right; right.
Ltac dest_or3 :=
  match goal with
  | [H: or3 _ _ _ |- _] => destruct H as [|[|]]
  end.
Ltac kinv_or3 :=
  repeat
    match goal with
    | [H: or3 _ _ _ |- _] => dest_or3; kinv_contra
    end.

