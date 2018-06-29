Require Import Bool List String Omega.
Require Import Structures.Equalities Program.Equality Eqdep Eqdep_dec.
Require Import FunctionalExtensionality.
Require Import Lib.Word Lib.CommonTactics Lib.ilist Lib.FMap Lib.StringEq Lib.VectorFacts Lib.Struct.
Require Import Kami.Syntax Kami.Semantics Kami.Decomposition.

Section GivenModule.
  Variable m: Modules.

  Section GivenOldregs.
    Variable o: RegsT.

    Variable Prule : MethsT -> Prop.
    Variable Pmeth : MethsT -> Prop.

    Example rqMeth := "rqFromProc" : String.string.
    Example rsMeth := "rsToProc" : String.string.
    Example Qrule := fun cs => FMap.M.find (elt := {x : SignatureT & SignT x}) rqMeth cs = None \/
                            FMap.M.find (elt := {x : SignatureT & SignT x}) rsMeth cs = None.
    Example Qmeth := fun cs => FMap.M.find (elt := {x : SignatureT & SignT x}) rqMeth cs = None /\
                            FMap.M.find (elt := {x : SignatureT & SignT x}) rsMeth cs = None.

    Axiom Prule_empty : Prule ([])%fmap.
   
    Axiom Prules : forall k a, List.In {| attrName := k; attrType := a |} (getRules m) ->
                          forall u cs retVal, SemAction o (a type) u cs retVal ->
                                         Prule cs.
    Axiom Pmeths :  forall f, In f (getDefsBodies m) ->
                         forall (u : UpdatesT) (cs : MethsT) (argV : type (arg (projT1 (attrType f)))) (retV : type (ret (projT1 (attrType f)))),
                           SemAction o (projT2 (attrType f) type argV) u cs retV ->
                           Pmeth cs.

    Axiom Pmeru : forall rcs, Prule rcs ->
                         forall mcs, Pmeth mcs ->
                                Prule (M.union rcs mcs).
    
    
    Goal forall u l, Step m o u l -> Prule (calls l).
      induction 1. unfold hide.
      induction ss; simpl.
      - match goal with
          [ |- Prule ?x ] => idtac x; change x with (@M.Map.empty {z : SignatureT & SignT z})
        end; apply Prule_empty.
      - destruct a. assert (Prule cms).
        { destruct substep.
          + apply Prule_empty.
          + apply Prule_empty.
          + eapply Prules; eassumption.
          + replace (cs) with (M.union [] cs)%fmap by (apply M.union_empty_L).
            eapply Pmeru. apply Prule_empty.
            eapply Pmeths; eassumption.
        }
        simpl in IHss. inv HSubsteps. specialize (IHss H2). simpl in HWellHidden.

        (*unfold wellHidden in HWellHidden.
        RefinementFacts.DomainSubset_KeysDisj*)
        
                                        