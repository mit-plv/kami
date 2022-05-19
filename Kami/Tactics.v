Require Import Bool String List Eqdep.
Require Import Lib.CommonTactics Lib.Reflection Lib.Word Lib.ilist Lib.Struct.
Require Import Lib.Indexer Lib.StringEq Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.StepDet Kami.Wf.
Require Import Kami.RefinementFacts Kami.Notations.
Require Import Kami.Inline Kami.InlineFacts Kami.Specialize Kami.Duplicate Kami.Substitute.
Require Import Kami.Decomposition Kami.ModuleBound Kami.ModuleBoundEx.

Require Import FunctionalExtensionality Program.Equality.

Set Implicit Arguments.
Set Asymmetric Patterns.

(**
- Kami Tactics
  + krefl: prove (a <<== a)
  + ktrans: for given "b", convert (a <<== c) into two subgoals (a <<== b) and (b <<== c)
    * ktrans_l: convert (a <<=[p] c) into two subgoals (a <<=[p] b) and (b <<== c)
    * ktrans_r: convert (a <<=[p] c) into two subgoals (a <<== b) and (b <<=[p] c)
  + ketrans: generate an evar for "b" convert into two subgoals (a <<== ?) and (? <<== c)
    * ketrans_l: convert (a <<=[p] c) into two subgoals (a <<=[p] ?) and (? <<== c)
    * ketrans_r: convert (a <<=[p] c) into two subgoals (a <<== ?) and (? <<=[p] c)
  + krewrite assoc left: convert (a + (b + c) <<== m) to ((a + b) + c <<== m)
  + krewrite <- assoc left: convert ((a + b) + c <<== m) to (a + (b + c) <<== m)
  + krewrite assoc right: convert (m <<== a + (b + c)) to (m <<== (a + b) + c)
  + krewrite <- assoc right: convert (m <<== (a + b) + c) to (m <<== a + (b + c))
  + kequiv: prove any PHOAS equivalences
  + kvr: prove any ValidRegsModules well-formedness conditions
  + kinteracting: prove any [Interacting] predicates
  + knoninteracting: prove any [NonInteracting] predicates
  + kdef_call_sub: prove any [DefCallSub] predicates
  + kmodular: convert (a + b <<== c + d) to (a <<== c) /\ (b <<== d) (interacting case)
    * kmodular with constr(p): when the refinement is by "<=[p]"
  + kmodularn: convert (a + b <<== c + d) to (a <<== c) /\ (b <<== d) (non-interacting case)
    * kmodularn with constr(p): when the refinement is by "<=[p]"
  + kmodularnp: convert (a + b <<=[compLabelMaps p q] c + d) to (a <<=[p] c) /\ (b <<=[q] d)
  + kmodular_sim_l: convert (a + c) <<== (b + c) to (a <<== b)
  + kmodular_sim_r: convert (c + a) <<== (c + b) to (a <<== b)
  + ksimilar: prove (a <<== b) when a and b have the same set of regs, rules, and methods
  + ksubst: prove (context[a] <<== context[b])
  + kinline_compute: compute [inlineF] terms
  + kinline_compute_in: compute [inlineF] terms in a hypothesis
  + kinline_left: convert (a <<== b) to (inlineF a <<== b), where (inlineF a) is computed
  + kinline_refine: define and prove (a <<== inlineF a), where (inlineF a) is computed
  + kdecompose_nodefs: apply the decompositionZero theorem, for modules with no defined methods.
  + kdecomposeR_nodefs: apply the decompositionZeroR theorem, for modules with no defined methods.
  + kinv_magic: try to solve invariant proofs (slow)
    * kinv_magic_with _tactic_: also try to apply _tactic_ alternately
  + kinv_magic_light: a lightweight version of "kinv_magic"
    * kinv_magic_light_with _tactic_: also try to apply _tactic_ alternately
  + kduplicated: convert (duplicate a <<== duplicate b) to (a <<== b)
  + krewrite dup_dist left: convert (dup (m1 + m2) n <<== m) to (dup m1 n + dup m2 n <<== m)
  + krewrite <- dup_dist left: convert (dup m1 n + dup m2 n <<== m) to (dup (m1 + m2) n <<== m)
  + krewrite dup_dist right: convert (m <<== dup (m1 + m2) n) to (m <<== dup m1 n + dup m2 n)
  + krewrite <- dup_dist right: convert (m <<== dup m1 n + dup m2 n) to (m <<== dup (m1 + m2) n)
  + kgetv/kexistv/kexistnv: used to construct register or label mappings
  + kami_ok: the highest level tactic to prove [traceRefines];
             it tries to perform inlining, decomposition, and simulation by applying high-level
             tactics described above.

- Kami Hints
  + #[global] Hint Extern 1 (Specializable _) => vm_compute; reflexivity.
  + #[global] Hint Extern 1 (SubList (getExtMeths _) (getExtMeths _)) => vm_compute; tauto.
 *)

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
  | [ |- ModEquiv _ _ _ ] => apply duplicate_ModEquiv; intros
  | [ |- ModEquiv _ _ _ ] => apply ModEquiv_modular
  | [ |- ModEquiv _ _ ?m ] => unfold_head m
  end.
 
Ltac kequiv_unit :=
  match goal with
  | [ |- ModEquiv _ _ _ ] => constructor; intros
  | [ |- RuleEquiv _ _ _ ] => unfold RuleEquiv; intros
  | [ |- MethEquiv _ _ _ ] => unfold MethEquiv; intros
  | [ |- RulesEquiv _ _ _ ] => constructor; intros
  | [ |- MethsEquiv _ _ _ ] => constructor; intros
  | [ |- ActionEquiv _ _ ] => constructor; intros
  | [ |- In _ _] => simpl; tauto
  end.

Ltac kequiv :=
  intros;
  repeat kequiv_red;
  repeat kequiv_unit.

Ltac kvr_red :=
  eauto;
  match goal with
  | [ |- ValidRegsModules _ (ConcatMod _ _) ] => split
  | [ |- ValidRegsModules _ (Mod (getRegInits ?m) (getRules ?m) (getDefsBodies ?m)) ] =>
    apply validRegsModules_flatten
  | [ |- ValidRegsModules _ (duplicate _ _) ] => apply duplicate_validRegsModules; intros
  | [ |- ValidRegsModules _ ?m ] => unfold_head m
  end.

Ltac kvr_unit :=
  match goal with
  | [ |- ValidRegsModules _ _ ] => constructor; intros
  | [ |- ValidRegsRules _ _ _ ] => constructor; intros
  | [ |- ValidRegsDms _ _ _ ] => constructor; intros
  | [ |- ValidRegsAction _ _ ] => constructor; intros
  | [ |- In _ _] => simpl; tauto
  end.

Ltac kvr :=
  intros;
  repeat kvr_red;
  repeat kvr_unit.

Ltac get_minimal_regs_bound m :=
  lazymatch m with
  | duplicate ?sm _ => constr:(getRegsBound (sm 0))
  | ConcatMod ?m1 ?m2 =>
    let mb1 := get_minimal_regs_bound m1 in
    let mb2 := get_minimal_regs_bound m2 in
    constr:(mb1 ++ mb2)
  | makeModule _ => constr:(getRegsBound m)
  | PrimMod _ => constr:(getRegsBound m)
  | Mod _ _ _ => constr:(getRegsBound m)
  | _ =>
    let m' := unfold_head_ret m in
    get_minimal_regs_bound m'
  end.

Ltac get_minimal_dms_bound m :=
  lazymatch m with
  | duplicate ?sm _ => constr:(getDmsBound (sm 0))
  | ConcatMod ?m1 ?m2 =>
    let mb1 := get_minimal_dms_bound m1 in
    let mb2 := get_minimal_dms_bound m2 in
    constr:(mb1 ++ mb2)
  | makeModule _ => constr:(getDmsBound m)
  | PrimMod _ => constr:(getDmsBound m)
  | Mod _ _ _ => constr:(getDmsBound m)
  | _ =>
    let m' := unfold_head_ret m in
    get_minimal_dms_bound m'
  end.

Ltac get_minimal_cms_bound m :=
  lazymatch m with
  | duplicate ?sm _ => constr:(getCmsBound (sm 0))
  | ConcatMod ?m1 ?m2 =>
    let mb1 := get_minimal_cms_bound m1 in
    let mb2 := get_minimal_cms_bound m2 in
    constr:(mb1 ++ mb2)
  | makeModule _ => constr:(getCmsBound m)
  | PrimMod _ => constr:(getCmsBound m)
  | Mod _ _ _ => constr:(getCmsBound m)
  | _ =>
    let m' := unfold_head_ret m in
    get_minimal_cms_bound m'
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
      apply getRegsBound_modular
      || apply concatMod_regsBound_1
      || (apply getRegsBound_duplicate; auto)
      || apply getRegsBound_bounded).

Ltac dms_bound_tac :=
  repeat (
      apply getDmsBound_modular
      || apply concatMod_dmsBound_1
      || (apply getDmsBound_duplicate; auto)
      || apply getDmsBound_bounded).

Ltac cms_bound_tac :=
  repeat (
      apply getCmsBound_modular
      || apply concatMod_cmsBound_1
      || (apply getCmsBound_duplicate; auto)
      || apply getCmsBound_bounded).

Ltac kdisj_regs :=
  red_to_regs_bound;
  [apply disjPrefixes_DisjPrefixes; reflexivity
  |regs_bound_tac
  |regs_bound_tac].

Ltac kdisj_dms :=
  red_to_dms_bound;
  [apply disjPrefixes_DisjPrefixes; reflexivity
  |dms_bound_tac
  |dms_bound_tac].

Ltac kdisj_cms :=
  red_to_cms_bound;
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
  repeat (* to separate [NoDup] into small modules *)
    match goal with
    | [ |- NoDup (namesOf (_ ++ _)) ] => unfold RegInitT; rewrite namesOf_app
    | [ |- NoDup (_ ++ _) ] => apply NoDup_DisjList; [| |kdisj_regs]
    | [ |- NoDup (namesOf (getRegInits (duplicate _ _))) ] => apply duplicate_regs_NoDup; auto
    | [ |- NoDup (namesOf (getRegInits ?m)) ] => unfold_head m
    | [ |- NoDup (namesOf (getRegInits _)) ] =>
      progress (unfold getRegInits; fold getRegInits)
    end;
  repeat noDup_tac.

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

Ltac kmodulari i :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_interacting with (vp:= (@idElementwise _));
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs_ex i|kdisj_regs_ex i|kvr|kvr
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |kdisj_edms_cms_ex i|kdisj_ecms_dms_ex i|kinteracting| |].

Ltac kmodular := kmodulari 0.

Tactic Notation "kmodulari" "with" constr(p) constr(i) :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_interacting with (vp:= p);
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs_ex i|kdisj_regs_ex i|kvr|kvr
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |kdisj_edms_cms_ex i|kdisj_ecms_dms_ex i|kinteracting| |].

Tactic Notation "kmodular" "with" constr(p) :=
  kmodulari with p 0.

Ltac kmodularin i :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting;
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs_ex i|kdisj_regs_ex i|kvr|kvr
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |knoninteracting|knoninteracting| |].

Ltac kmodularn := kmodularin 0.

Tactic Notation "kmodularin" "with" constr(p) constr(i) :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting with (vp:= p);
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs_ex i|kdisj_regs_ex i|kvr|kvr
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |knoninteracting|knoninteracting| |].

Tactic Notation "kmodularn" "with" constr(p) :=
  kmodularin with p 0.

Ltac kmodularinp i :=
  try (unfold MethsT; rewrite <-idElementwiseId);
  apply traceRefines_modular_noninteracting_p;
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs_ex i|kdisj_regs_ex i|kvr|kvr
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   |kdisj_dms_ex i|kdisj_cms_icms_ex i|kdisj_icms_cms_ex i
   | |knoninteracting|knoninteracting| |].

Ltac kmodularnp := kmodularinp 0.

Ltac kmodulari_sim_l i :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure_modular_1;
  [knodup_regs|knodup_regs|knodup_regs
   |kdisj_regs_ex i|kdisj_regs_ex i| | |].

Ltac kmodular_sim_l := kmodulari_sim_l 0.

Ltac kmodulari_sim_r i :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure_modular_2;
  [knodup_regs|knodup_regs|knodup_regs
   |kdisj_regs_ex i|kdisj_regs_ex i| | |].

Ltac kmodular_sim_r := kmodulari_sim_r 0.

Ltac ksimilar :=
  try rewrite idElementwiseId; apply traceRefines_same_module_structure;
  [knodup_regs|knodup_regs| | |].

Ltac ksubsti i fm tm om :=
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
   kdisj_regs_ex i|kdisj_regs_ex i|
   kdisj_dms_ex i|kdisj_dms_ex i|kdisj_cms_ex i|kdisj_cms_ex i| | |
   kvr|kvr|kvr| | | |].

Ltac ksubst fm tm om := ksubsti 0 fm tm om.

Ltac kstring_simpl :=
  repeat autounfold with NameDefs in *;
  cbv [withPrefix prefixSymbol append] in *.

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
               pm_name pm_regInits pm_rules pm_methods
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               Bool.eqb existsb andb orb negb];
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
               pm_name pm_regInits pm_rules pm_methods
               getRegInits getDefs getDefsBodies getRules namesOf
               map app attrName attrType
               getCalls getCallsR getCallsM getCallsA
               ret arg fst snd projT1 projT2
               string_in string_eq ascii_eq
               Bool.eqb existsb andb orb negb] in H;
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

Ltac kinline_refine m :=
  (* 1) Bring the PHOAS equivalences proof (or prove it if not proven yet). *)
  let Hequiv := fresh "Hequiv" in
  assert (ModEquiv type typeUT m) as Hequiv by kequiv;
  (* 2) Inline the target module. *)
  let Hin := fresh "Hin" in
  pose proof (inlineF_refines
                Hequiv (Reflection.noDupStr_NoDup (namesOf (getDefsBodies m)) eq_refl))
    as Hin;
  unfold MethsT in Hin; rewrite <-SemFacts.idElementwiseId in Hin;
  (* 3) Evaluate the inlined module. *)
  let origm := fresh "origm" in
  set m as origm in Hin at 2;
  kinline_compute_in Hin;
  subst origm;
  specialize (Hin eq_refl);
  exact (existT _ _ Hin).

Ltac kinline_refine_left rm :=
  ketrans; [exact (projT2 rm)|].

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
  kregmap_red; kregmap_clear; repeat (eexists; split; try reflexivity).

Ltac kdecompose_nodefs t r :=
  apply decompositionZero with (theta:= t) (ruleMap:= r); intros; subst;
  [try reflexivity; try kdecompose_regmap_init
  |reflexivity
  |reflexivity
  |].
 
Ltac kdecomposeR_nodefs t r :=
  apply decompositionZeroR with (thetaR:= t) (ruleMap:= r); intros; subst;
  try reflexivity;
  [try kdecompose_regrel_init|].

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
         (* simplification for [bool] *)
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

         (* for the others *)
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

      (* heavy case analyses for branches *)
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

      (* heavy case analyses for branches *)
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

Ltac kinv_action_dest := kinv_red; invertActionRep.
Ltac kinv_custom tac := kinv_red; try tac; kinv_red.
Ltac kinv_dest_custom tac := kinv_action_dest; kinv_custom tac.
Ltac kinv_regmap_red := kinv_red; kregmap_red; kregmap_clear.
Ltac kinv_constr :=
  repeat
    (kinv_red;
     repeat match goal with
            | [ |- _ /\ _ ] => split
            | [ |- exists _, _ /\ _ ] => eexists; split
            | [ |- Substep _ _ _ _ _ ] => econstructor
            | [ |- In _ _ ] => simpl; tauto
            | [ |- SemAction _ _ _ _ _ ] => econstructor
            | [ |- _ = _ ] => reflexivity
            end
    ).

Ltac fin_func_tac :=
  let i := fresh "i" in
  extensionality i;
  repeat
    match goal with
    | [j: Fin.t 0 |- _] => inv j
    | [j: Fin.t _ |- _] => dependent destruction j
    end.

Ltac fin_func_eq :=
  match goal with
  | [ |- ?t = _ ] =>
    match type of t with
    | forall (_: Fin.t _), _ => fin_func_tac
    end
  end.

Lemma existT_eq: forall A (x: A) P (v1 v2: P x), v1 = v2 -> existT _ x v1 = existT _ x v2.
Proof. intros; subst; auto. Qed.

Lemma pair_eq: forall A (a1 a2: A) B (b1 b2: B), a1 = a2 -> b1 = b2 -> (a1, b1) = (a2, b2).
Proof. intros; subst; auto. Qed.

Ltac kinv_eq :=
  repeat
    (first [ reflexivity
           | meqReify
           | findReify
           | fin_func_eq
           | apply existT_eq
           | apply pair_eq
    ]).

Ltac kinv_magic_with dtac itac :=
  kinv_action_dest;
  kinv_custom dtac;
  kinv_regmap_red;
  kinv_constr;
  kinv_eq;
  kinv_finish_with itac.

Ltac kinv_magic := kinv_magic_with idtac idtac.

Ltac kinv_magic_light_with tac :=
  kinv_action_dest;
  kinv_custom tac;
  kinv_regmap_red;
  kinv_constr;
  kinv_eq.

Ltac kinv_magic_light := kinv_magic_light_with idtac.

Ltac kinvert_det_unit :=
  match goal with
  | [H: SubstepMeths _ _ _ _ |- _] => apply substepMeths_inv in H; simpl in H; dest
  | [H: Substep _ _ _ (Meth (Some _)) _ |- _] =>
    apply substep_meth_inv with (Haeq:= eq_refl) in H; [|noDup_tac];
    simpl in H
  end.

Ltac kinvert_det := repeat kinvert_det_unit.

Ltac kinv_constr_det_unit :=
  match goal with
  | [ |- exists _, _ /\ _ ] => eexists; split
  | [ |- Step _ _ _ _ ] =>
    apply stepDet_implies_step; [kequiv|repeat (constructor || reflexivity)|]
  | [ |- StepDet _ _ _ _ ] => econstructor
  | [ |- SubstepMeths _ _ _ _ ] => econstructor
  | [ |- Substep _ _ _ (Meth (Some (?fn :: _)%struct)) _ ] =>
    eapply SingleMeth with (f:= (fn :: _)%struct)
  | [ |- Substep _ _ _ _ _ ] => econstructor
  | [ |- In _ _ ] => simpl; tauto
  | [ |- SemAction _ _ _ _ _ ] => econstructor
  | [ |- _ = _ ] => reflexivity
  end.

Ltac kinv_constr_det := repeat kinv_constr_det_unit.

Ltac kinv_constr_det_false_unit :=
  match goal with
  | [ |- exists _, _ /\ _ ] => eexists; split
  | [ |- Step _ _ _ _ ] =>
    apply stepDet_implies_step; [kequiv|repeat (constructor || reflexivity)|]
  | [ |- StepDet _ _ _ _ ] => econstructor
  | [ |- SubstepMeths _ _ _ _ ] => econstructor
  | [ |- Substep _ _ _ (Meth (Some (?fn :: _)%struct)) _ ] =>
    eapply SingleMeth with (f:= (fn :: _)%struct)
  | [ |- Substep _ _ _ _ _ ] => econstructor
  | [ |- In _ _ ] => simpl; tauto
  | [ |- SemAction _ (IfElse _ _ _ _) _ _ _ ] => eapply SemIfElseFalse
  | [ |- SemAction _ _ _ _ _ ] => econstructor
  | [ |- _ = _ ] => reflexivity
  end.

Ltac kinv_constr_det_false := repeat kinv_constr_det_false_unit.

Ltac kduplicated :=
  apply duplicate_traceRefines; intros;
  [auto|auto
   |kequiv|kequiv
   |kvr|kvr
   |auto
   |].

Tactic Notation "krewrite" "dup_dist" "left" :=
  ketrans; [apply duplicate_concatMod_comm_1; auto; try kequiv; try kvr|].
Tactic Notation "krewrite" "<-" "dup_dist" "left" :=
  ketrans; [apply duplicate_concatMod_comm_2; auto; try kequiv; try kvr|].
Tactic Notation "krewrite" "dup_dist" "right" :=
  ketrans; [|apply duplicate_concatMod_comm_2; auto; try kequiv; try kvr].
Tactic Notation "krewrite" "<-" "dup_dist" "right" :=
  ketrans; [|apply duplicate_concatMod_comm_1; auto; try kequiv; try kvr].

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

#[global] Hint Extern 1 (Specializable _) => vm_compute; reflexivity.
#[global] Hint Extern 1 (SubList (getExtMeths _) (getExtMeths _)) => vm_compute; tauto.

(** Kami proof configuration for [kami_ok] *)

Inductive InliningType :=
| ITManual: InliningType
| ITProvided: forall (om: Modules), sigT (fun m: Modules => om <<== m) -> InliningType
| ITNone: InliningType.

Inductive DecompositionType :=
| DTFunctional:
    forall (theta: RegsT -> RegsT)
           (ruleMap: RegsT -> string -> option string),
      DecompositionType
| DTRelational:
    forall (thetaR: RegsT -> RegsT -> Prop),
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

Record ProofConfig := { inlining: InliningType;
                        decomposition: DecompositionType;
                        invariants: Invariants
                      }.

Ltac kami_ok cfg dtac itac :=
  match eval hnf in (inlining cfg) with
  | ITManual =>
    let im := fresh "im" in
    kinline_left im
  | ITProvided ?sigM =>
    ketrans; [exact (projT2 sigM)|]
  | ITNone => idtac
  end;
  match eval hnf in (decomposition cfg) with
  | DTFunctional ?sm ?rm => kdecompose_nodefs sm rm
  | DTRelational ?sr => kdecomposeR_nodefs sr
  end;
  let invs := (eval hnf in (invariants cfg)) in
  kinv_add_rep invs;
  kinvert; kinv_magic_with dtac itac.

(** Notations for rule maps *)
Notation "from '|->' to ; cont" :=
  (fun s => if string_dec s from
            then Some to%string
            else (cont s)) (at level 12, right associativity).
Notation "||" := (fun _ => None) (at level 12).

(** Notations for register maps *)
Declare Scope mapping_scope.
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
   end) (at level 0, vn at level 0): mapping_scope.

Notation "'mlet' vn : t <- r '|>' kn '<|' default ; cont" :=
  (match M.find kn%string r with
   | Some (existT k v) =>
     match k with
     | SyntaxKind kind =>
       fun vname =>
         match decKind kind t with
         | left Heq => 
           eq_rect_r (fun kind => fullType type (SyntaxKind kind) -> _)
                     (fun vn : fullType type (SyntaxKind t) => cont) Heq vname
         | right _ => default
         end
     | _ => fun _ => default
     end v
   | _ => default
   end) (at level 0, vn at level 0): mapping_scope.

Delimit Scope mapping_scope with mapping.

