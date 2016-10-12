Require Import Bool String List Eqdep.
Require Import Lib.CommonTactics Lib.Reflection Lib.Word Lib.ilist Lib.Struct.
Require Import Lib.Indexer Lib.StringEq Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf Kami.RefinementFacts Kami.Notations.
Require Import Kami.Inline Kami.InlineFacts Kami.Specialize Kami.Duplicate Kami.Substitute.
Require Import Kami.Decomposition Kami.ModuleBound.
Require Import Kami.ParametricSyntax Kami.ParametricEquiv Kami.ParametricWf.

Set Implicit Arguments.
Set Asymmetric Patterns.

(**
- Kami Tactics
  + krefl : prove (a <<== a)
  + ktrans : for given "b", convert (a <<== c) into two subgoals (a <<== b) and (b <<== c)
    * ktrans_l : convert (a <<=[p] c) into two subgoals (a <<=[p] b) and (b <<== c)
    * ktrans_r : convert (a <<=[p] c) into two subgoals (a <<== b) and (b <<=[p] c)
  + ketrans : generate an evar for "b" convert into two subgoals (a <<== ?) and (? <<== c)
    * ketrans_l : convert (a <<=[p] c) into two subgoals (a <<=[p] ?) and (? <<== c)
    * ketrans_r : convert (a <<=[p] c) into two subgoals (a <<== ?) and (? <<=[p] c)
  + krewrite assoc left : convert (a + (b + c) <<== m) to ((a + b) + c <<== m)
  + krewrite <- assoc left : convert ((a + b) + c <<== m) to (a + (b + c) <<== m)
  + krewrite assoc right : convert (m <<== a + (b + c)) to (m <<== (a + b) + c)
  + krewrite <- assoc right : convert (m <<== (a + b) + c) to (m <<== a + (b + c))
  + kequiv : prove any PHOAS equivalences
  + kvr : prove any ValidRegsModules well-formedness conditions
  + kdisj_regs : prove DisjList conditions of regs
  + kdisj_dms : prove DisjList conditions of dms
  + kdisj_cms : prove DisjList conditions of cms
  + kdisj_dms_cms : prove DisjList conditions of dms and cms
  + kdisj_cms_dms : prove DisjList conditions of cms and dms
  + knodup_regs : prove (NoDup regs), where _regs_ are names of registers
  + kinteracting : prove the Interacting predicate
  + knoninteracting : prove the NonInteracting predicate
  + kdef_call_sub : prove the DefCallSub predicate
  + kmodular : convert (a + b <<== c + d) to (a <<== c) /\ (b <<== d) (interacting case)
    * kmodular with constr(p) : when the refinement is by "<=[p]"
  + kmodularn : convert (a + b <<== c + d) to (a <<== c) /\ (b <<== d) (non-interacting case)
    * kmodularn with constr(p) : when the refinement is by "<=[p]"
  + kmodularnp : convert (a + b <<=[compLabelMaps p q] c + d) to (a <<=[p] c) /\ (b <<=[q] d)
  + kmodular_sim_l : convert (a + c) <<== (b + c) to (a <<== b)
  + kmodular_sim_r : convert (c + a) <<== (c + b) to (a <<== b)
  + ksimilar : prove (a <<== b) when a and b have the same set of regs, rules, and methods
  + ksubst : prove (context[a] <<== context[b])
  + kinline_compute : compute terms with _inlineF_
  + kinline_compute_in _term_ : compute terms with _inlineF_ in _term_
  + kinline_left : convert (a <<== b) to (inlineF a <<== b), where (inlineF a) is computed
  + kdecompose_nodefs : apply the decompositionZero theorem, for modules with no defined methods.
  + kdecomposeR_nodefs : apply the decompositionZeroR theorem, for modules with no defined methods.
  + kinv_magic : try to solve invariant proofs (slow)
    * kinv_magic_with _tactic_ : also try to apply _tactic_ alternately
  + kinv_magic_light : a lightweight version of "kinv_magic"
    * kinv_magic_light_with _tactic_ : also try to apply _tactic_ alternately
  + kduplicated : convert (duplicate a <<== duplicate b) to (a <<== b)
  + kgetv/kexistv/kexistnv : used to construct register or label mappings

- Kami Hints
  + Hint Extern 1 (Specializable _) => vm_compute; reflexivity.
  + Hint Extern 1 (SubList (getExtMeths _) (getExtMeths _)) => vm_compute; tauto.
 *)

Ltac kstring_simpl :=
  repeat autounfold with NameDefs in *;
  cbv [withPrefix prefixSymbol append] in *.

Ltac krefl :=
  try rewrite idElementwiseId; apply traceRefines_refl.

Ltac ktrans m :=
  try rewrite idElementwiseId; apply traceRefines_trans with (p:= id) (q:= id) (mb:= m).

Ltac ktrans_l m :=
  try rewrite idElementwiseId; apply traceRefines_trans_elem_left_p with (m2:= m).

Ltac ktrans_r m :=
  try rewrite idElementwiseId; apply traceRefines_trans_elem_right_p with (m2:= m).

Ltac ketrans :=
  let m := fresh "m" in
  evar (m: Modules); ktrans m; unfold m; clear m;
  try (unfold RegInitT, MethsT; rewrite <-idElementwiseId).

Ltac ketrans_l :=
  let m := fresh "m" in
  evar (m: Modules); ktrans_l m; unfold m; clear m;
  try (unfold RegInitT, MethsT; rewrite <-idElementwiseId).

Ltac ketrans_r :=
  let m := fresh "m" in
  evar (m: Modules); ktrans_r m; unfold m; clear m;
  try (unfold RegInitT, MethsT; rewrite <-idElementwiseId).

Tactic Notation "krewrite" "assoc" "left" :=
  ketrans; [rewrite SemFacts.idElementwiseId; apply traceRefines_assoc_2|].

Tactic Notation "krewrite" "<-" "assoc" "left" :=
  ketrans; [rewrite SemFacts.idElementwiseId; apply traceRefines_assoc_1|].

Tactic Notation "krewrite" "assoc" "right" :=
  ketrans; [|rewrite SemFacts.idElementwiseId; apply traceRefines_assoc_1].

Tactic Notation "krewrite" "<-" "assoc" "right" :=
  ketrans; [|rewrite SemFacts.idElementwiseId; apply traceRefines_assoc_2|].

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
  | [ |- ValidRegsMetaRule _ _ _ ] => econstructor; intros
  | [ |- ValidRegsMetaMeths _ _ _ ] => constructor; intros
  | [ |- ValidRegsMetaMeth _ _ _ ] => econstructor; intros
  | [ |- ValidRegsSinAction _ _ ] => econstructor; intros
  | [ |- ValidRegsGenAction _ _ _ _ ] => econstructor; intros
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

Ltac knodup_regs :=
  repeat (* Separating NoDup proofs by small modules *)
    match goal with
    | [ |- NoDup (namesOf (_ ++ _)) ] => unfold RegInitT; rewrite namesOf_app
    | [ |- NoDup (_ ++ _) ] => apply NoDup_DisjList; [| |kdisj_regs]
    | [ |- NoDup (namesOf (getRegInits (duplicate _ _))) ] => apply duplicate_regs_NoDup; auto
    | [ |- NoDup (namesOf (getRegInits ?m)) ] => unfold_head m
    | [ |- NoDup (namesOf (getRegInits _)) ] =>
      progress (unfold getRegInits; fold getRegInits)
    end;
  repeat
    match goal with
    | _ => apply noDup_metaRegs
    | _ => noDup_tac
    end.

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

Ltac kmodular :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_interacting with (vp:= (@idElementwise _));
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs|kdisj_regs|kvr|kvr
   |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
   | | |kinteracting| |].

Tactic Notation "kmodular" "with" constr(p) :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_interacting with (vp:= p);
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs|kdisj_regs|kvr|kvr
   |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
   | | | | |].

Ltac kmodularn :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting;
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs|kdisj_regs|kvr|kvr
   |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
   |knoninteracting|knoninteracting| |].

Tactic Notation "kmodularn" "with" constr(p) :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting with (vp:= p);
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs|kdisj_regs|kvr|kvr
   |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
   |knoninteracting|knoninteracting| |].

Ltac kmodularnp :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting_p;
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs|kdisj_regs|kvr|kvr
   |kdisj_dms|kdisj_cms|kdisj_dms|kdisj_cms
   | |knoninteracting|knoninteracting| |].

Ltac kmodular_sim_l :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure_modular_1;
  [knodup_regs|knodup_regs|knodup_regs
   |kdisj_regs|kdisj_regs| | |].

Ltac kmodular_sim_r :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure_modular_2;
  [knodup_regs|knodup_regs|knodup_regs
   |kdisj_regs|kdisj_regs| | |].

Ltac ksimilar :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure;
  [knodup_regs|knodup_regs| | |].

Ltac ksubst fm tm om :=
  apply substitute_flattened_refines_interacting
  with (regs := getRegInits fm)
         (rules := getRules fm)
         (dms := getDefsBodies fm)
         (sregs := getRegInits tm)
         (srules := getRules tm)
         (sdms := getDefsBodies tm)
         (regs' := getRegInits om)
         (rules' := getRules om)
         (dms' := getDefsBodies om);
  repeat rewrite getDefs_flattened;
  repeat rewrite getCalls_flattened;
  [kequiv|kequiv|kequiv|
   knodup_regs|knodup_regs|knodup_regs|
   kdisj_regs|kdisj_regs|
   kdisj_dms|kdisj_dms|kdisj_cms|kdisj_cms| | |
   kvr|kvr|kvr| | | |].
      
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

Ltac kregmap_red :=
  repeat autounfold with MethDefs in *;
  repeat autounfold with MapDefs in *;
  kstring_simpl; dest;
  repeat match goal with
         | [H: M.find _ _ = None |- _] => clear H
         end;
  repeat
    (try match goal with
         | [H: M.find ?k ?m = _ |- context[M.find ?k ?m] ] => rewrite H
         | [H1: M.find ?k ?m = _, H2: context[M.find ?k ?m] |- _] => rewrite H1 in H2
         | [ |- context[decKind _ _] ] =>
           rewrite kind_eq; unfold eq_rect_r, eq_rect, eq_sym
         | [H: context[decKind _ _] |- _] =>
           rewrite kind_eq in H; unfold eq_rect_r, eq_rect, eq_sym in H
         end; try subst; try findReify).

Ltac kregmap_clear :=
  repeat
    match goal with
    | [H: M.find _ _ = _ |- _] => clear H
    end.

Ltac kdecompose_regmap_init :=
  unfold initRegs, rawInitRegs, getRegInits; simpl;
  kregmap_red; kregmap_clear; try reflexivity.

Ltac kdecompose_regrel_init :=
  unfold initRegs, rawInitRegs, getRegInits; simpl;
  kregmap_red; kregmap_clear; eexists; split; reflexivity.

Ltac kdecompose_nodefs t r :=
  apply decompositionZero with (theta:= t) (ruleMap:= r); intros; subst;
  [try reflexivity; try kdecompose_regmap_init
  |reflexivity (* "getDefsBodies _ = nil" conditions *)
  |reflexivity (* "getDefsBodies _ = nil" conditions *)
  |].
 
Ltac kdecomposeR_nodefs t r :=
  apply decompositionZeroR with (thetaR:= t) (ruleMap:= r); intros; subst;
  try reflexivity; (* "getDefsBodies _ = nil" conditions *)
  [try kdecompose_regrel_init|]. (* should have only two subgoals at this time *)

Ltac kinv_add inv :=
  match goal with
  | [H: reachable _ _ |- _] =>
    let Hr := fresh "Hr" in
    pose proof H as Hr; apply inv in Hr; auto
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
      apply step_zero in H; [|reflexivity]; destruct H
    end.

Ltac kinv_contra :=
  try (exfalso;
       simpl in *;
       repeat autounfold with MethDefs in *;
       repeat autounfold with InvDefs in *; dest; subst;
       repeat
         (match goal with
          | [H: false = true |- _] => inversion H
          | [H: true = false |- _] => inversion H
          | [H1: ?t = true, H2: ?t = false |- _] => rewrite H1 in H2
          | [H1: true = ?t, H2: false = ?t |- _] => rewrite <-H1 in H2
          | [H: negb _ = true |- _] => apply negb_true_iff in H; subst
          | [H: negb _ = false |- _] => apply negb_false_iff in H; subst
          end; dest; try subst);
       fail).

Lemma Some_inv: forall A (s t: A), Some s = Some t -> s = t.
Proof.
  intros; inv H; reflexivity.
Qed.

Lemma negb_eq_false: forall b, b = negb b -> False.
Proof. destruct b; intros; inv H. Qed.

Lemma eqb_unfolded_refl:
  forall b: bool, (if b then if b then true else false
                   else if b then false else true) = true.
Proof. destruct b; reflexivity. Qed.

Ltac kinv_simpl :=
  kstring_simpl;
  repeat
    (try match goal with
         (* about bool *)
         | [H: ?t = ?t |- _] => clear H
         | [H: ?t = ?t -> False |- _] => elim H; reflexivity
         | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl)
         | [H: ?t <> ?t |- _] => elim H; reflexivity
         | [H: ?t <> ?t -> _ |- _] => clear H
         | [H: negb _ = true |- _] => apply negb_true_iff in H; subst
         | [H: negb _ = false |- _] => apply negb_false_iff in H; subst
         | [H: false = true |- _] => inversion H
         | [H: true = false |- _] => inversion H
         | [H: false = true -> _ |- _] => clear H
         | [H: true = false -> _ |- _] => clear H
         | [H: ?t = negb ?t |- _] => exfalso; eapply negb_eq_false; eauto
         | [H: negb ?t = ?t |- _] => exfalso; apply eq_sym in H; eapply negb_eq_false; eauto
         | [H: false = negb false |- _] => inversion H
         | [H: negb false = false |- _] => inversion H
         | [H: true = negb true |- _] => inversion H
         | [H: negb true = true |- _] => inversion H
         | [H1: ?t = true, H2: ?t = false |- _] => rewrite H1 in H2
         | [H1: true = ?t, H2: false = ?t |- _] => rewrite <-H1 in H2
         | [H: (if ?c then true else false) = true |- _] => destruct c; [|inv H]
         | [H: (if ?c then true else false) = false |- _] => destruct c; [inv H|]
         | [H: (if ?c then false else true) = true |- _] => destruct c; [inv H|]
         | [H: (if ?c then false else true) = false |- _] => destruct c; [|inv H]
         | [H: context[_ || true] |- _] => rewrite orb_true_r in H
         | [H: context[true || _] |- _] => rewrite orb_true_l in H
         | [H: _ || _ = false |- _] => apply orb_false_iff in H
         | [H: false = _ || _ |- _] => apply orb_false_elim in H
         | [H: _ && _ = true |- _] => apply andb_true_iff in H
         | [H: true = _ && _ |- _] => apply andb_true_eq in H
         | [H: true <> false -> _ |- _ ] => specialize (H diff_true_false)
         | [H: (true = false -> False) -> _ |- _ ] => specialize (H diff_true_false)
         | [H: false <> true |- _ ] => specialize (H diff_false_true)
         | [H: (false = true -> False) -> _ |- _ ] => specialize (H diff_false_true)
         | [H: ?t <> true |- _] => apply not_true_is_false in H
         | [H: ?t = true -> False |- _] => apply not_true_is_false in H
         | [H: ?t <> false |- _] => apply not_false_is_true in H
         | [H: ?t = false -> False |- _] => apply not_false_is_true in H
         | [H: context[if ?b then if ?b then true else false
                       else if ?b then false else true] |- _] =>
           rewrite eqb_unfolded_refl in *
         | [ |- context[if ?b then if ?b then true else false
                        else if ?b then false else true] ] =>
           rewrite eqb_unfolded_refl in *

         (* others *)
         | [ |- context [weq ?w ?w] ] =>
           let n := fresh "n" in destruct (weq w w) as [|n]; [|elim n; reflexivity]
         | [H: context [weq ?w ?w] |- _] =>
           let n := fresh "n" in destruct (weq w w) as [|n]; [|elim n; reflexivity]
         | [H1: M.find ?k ?m = _, H2: M.find ?k ?m = _ |- _] => rewrite H1 in H2
         | [H: Some _ = Some _ |- _] => apply Some_inv in H; destruct_existT
         end; dest; try subst).

Ltac kinv_red :=
  intros; repeat autounfold with InvDefs in *;
  dest; try subst; kinv_simpl.

Ltac is_not_const_bool t :=
  match t with
  | true => fail 1
  | false => fail 1
  | _ => idtac
  end.

Ltac is_not_const_word t :=
  match t with
  | WO => fail 1
  | WS _ => fail 1
  | _ => idtac
  end.

Ltac kinv_finish :=
  repeat autounfold with MethDefs in *; simpl in *; kinv_simpl;
  repeat (
      (* heavy rewrites *)
      repeat
        (match goal with
         | [H: ?t = _ |- _] => is_not_const_bool t; is_not_const_word t; rewrite H in *
         end);
      repeat
        (match goal with
         | [H: _ = ?t |- _] => is_not_const_bool t; is_not_const_word t; rewrite <- H in *
         end);
      try assumption; try reflexivity; try discriminate;
      (* rewrites end *)
      repeat
        (kinv_simpl;
         try assumption; try discriminate;
         try match goal with
             | [H: _ <> _ |- _] => elim H; reflexivity
             | [ |- context [if weq ?w1 ?w2 then _ else _] ] => destruct (weq w1 w2)
             end;
         simpl in *; auto)
    ).

Ltac kinv_finish_with tac :=
  repeat autounfold with MethDefs in *; simpl in *; kinv_simpl;
  repeat (
      (* heavy rewrites *)
      repeat
        (match goal with
         | [H: ?t = _ |- _] => is_not_const_bool t; is_not_const_word t; rewrite H in *
         end);
      repeat
        (match goal with
         | [H: _ = ?t |- _] => is_not_const_bool t; is_not_const_word t; rewrite <- H in *
         end);
      try assumption; try reflexivity; try discriminate;
      (* rewrites end *)
      repeat
        (repeat
           (kinv_simpl;
            try assumption; try discriminate;
            try match goal with
                | [H: _ <> _ |- _] => elim H; reflexivity
                | [ |- context [if weq ?w1 ?w2 then _ else _] ] => destruct (weq w1 w2)
                end;
            simpl in *; auto);
         try tac)
    ).

Ltac invertActionRep ::=
     repeat
     match goal with
     | [H: (_ :: _)%struct = (_ :: _)%struct |- _] => inv H
     | [H: SemAction _ _ _ _ _ |- _] => invertAction H
     | [H: if ?c
           then
             SemAction _ _ _ _ _ /\ _ /\ _ /\ _
           else
             SemAction _ _ _ _ _ /\ _ /\ _ /\ _ |- _] =>
       repeat autounfold with MethDefs; simpl in *;
       match goal with
       | [H: if ?c
             then
               SemAction _ _ _ _ _ /\ _ /\ _ /\ _
             else
               SemAction _ _ _ _ _ /\ _ /\ _ /\ _ |- _] =>
         let ic := fresh "ic" in
         (remember c as ic; destruct ic; dest; subst)
       end
     end.

Ltac boundedMapTac := idtac.

Ltac kinv_action_dest := kinv_red; invertActionRep.
Ltac kinv_custom tac := kinv_red; try tac; kinv_red.
Ltac kinv_dest_custom tac := kinv_action_dest; kinv_custom tac.
Ltac kinv_regmap_red := kinv_red; kregmap_red; kregmap_clear.
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

Lemma existT_eq: forall A (x: A) P (v1 v2: P x), v1 = v2 -> existT _ x v1 = existT _ x v2.
Proof. intros; subst; auto. Qed.

Lemma pair_eq: forall A (a1 a2: A) B (b1 b2: B), a1 = a2 -> b1 = b2 -> (a1, b1) = (a2, b2).
Proof. intros; subst; auto. Qed.

Ltac kinv_eq :=
  repeat
    (first [reflexivity
           |meqReify
           |boundedMapTac
           |apply existT_eq
           |apply pair_eq
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

Ltac kduplicated :=
  apply duplicate_traceRefines;
  [auto|auto (* Specializable *)
   |kequiv|kequiv
   |kvr|kvr
   |auto (* SubList (getExtMeth _) (getExtMeth _) *)
   |].

Ltac kgetv k v m t f :=
  destruct (M.find k m) as [[[kind|] v]|]; [|exact f|exact f];
  destruct (decKind kind t); [subst|exact f].

Ltac kexistv k vn m t :=
  let v := fresh "v" in
  refine (exists v: fullType type (SyntaxKind t),
             M.find k m = Some (existT _ _ v) /\ _);
  rename v into vn.
Ltac kexistnv k vn m t :=
  let v := fresh "v" in
  refine (exists v: fullType type t,
             M.find k m = Some (existT _ _ v) /\ _);
  rename v into vn.

Hint Extern 1 (Specializable _) => vm_compute; reflexivity.
Hint Extern 1 (SubList (getExtMeths _) (getExtMeths _)) => vm_compute; tauto.

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

(** Notations for register maps *)
Notation "'mlet' vn : t <- r '|>' kn ; cont" :=
  (match M.find kn%string r with
   | Some (existT k v) =>
     match k with
     | SyntaxKind kind =>
       fun vname =>
         match decKind kind t with
         | left Heq => 
           eq_rect_r (fun kind => fullType type (SyntaxKind kind) -> RegsT)
                     (fun vn : fullType type (SyntaxKind t) => cont) Heq vname
         | right _ => M.empty _
         end
     | _ => fun _ => M.empty _
     end v
   | _ => M.empty _
   end) (at level 0, vn at level 0) : mapping_scope.
Delimit Scope mapping_scope with mapping.

(** Invariant-related definitions *)
Definition or3 (b1 b2 b3: Prop) := b1 \/ b2 \/ b3.
Tactic Notation "or3_fst" := left.
Tactic Notation "or3_snd" := right; left.
Tactic Notation "or3_thd" := right; right.

Ltac kinv_or3 :=
  repeat
    (match goal with
     | [H: _ \/ _ |- _] => destruct H
     | [H: or3 _ _ _ |- _] => destruct H as [|[|]]
     end; dest).

