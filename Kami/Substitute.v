Require Import List String.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.RefinementFacts Kami.Wf.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Interacting.
  Variables (regs regs' sregs oregs: list RegInitT).
  Variables (rules rules' srules orules: list (Attribute (Action Void))).
  Variables (dms dms' sdms odms: list DefMethT).

  Hypotheses (Hequiv: ModEquiv type typeUT (Mod regs rules dms))
             (Hequiv': ModEquiv type typeUT (Mod regs' rules' dms'))
             (Hequivs: ModEquiv type typeUT (Mod sregs srules sdms)).

  Hypotheses (Hnodupr: NoDup (namesOf regs))
             (Hnodupr': NoDup (namesOf regs'))
             (Hnodupor: NoDup (namesOf oregs)).

  Hypotheses (Hdisjr: DisjList (namesOf regs) (namesOf regs'))
             (Hdisjsr: DisjList (namesOf sregs) (namesOf regs'))
             (Hdisjd: DisjList (namesOf dms) (namesOf dms'))
             (Hdisjsd: DisjList (namesOf sdms) (namesOf dms'))
             (Hdisjc: DisjList (getCalls (Mod regs rules dms))
                               (getCalls (Mod regs' rules' dms')))
             (Hdisjsc: DisjList (getCalls (Mod sregs srules sdms))
                                (getCalls (Mod regs' rules' dms')))
             (Hed: DisjList (getExtDefs (Mod regs rules dms ++ Mod regs' rules' dms')%kami)
                            (getCalls (Mod sregs srules sdms ++ Mod regs' rules' dms')%kami))
             (Hec: DisjList (getExtCalls (Mod regs rules dms ++ Mod regs' rules' dms')%kami)
                            (getDefs (Mod sregs srules sdms ++ Mod regs' rules' dms')%kami)).

  Hypotheses (Hvr: ValidRegsModules type (Mod regs rules dms))
             (Hvrs: ValidRegsModules type (Mod sregs srules sdms))
             (Hvr': ValidRegsModules type (Mod regs' rules' dms')).
             
  Hypotheses (Hregs: EquivList oregs (regs ++ regs'))
             (Hrules: EquivList orules (rules ++ rules'))
             (Hdms: EquivList odms (dms ++ dms')).

  Hypothesis (Href: Mod regs rules dms <<== Mod sregs srules sdms).

  Lemma substitute_flattened_refines_interacting:
    Mod oregs orules odms <<== Mod (sregs ++ regs') (srules ++ rules') (sdms ++ dms').
  Proof.
    rewrite idElementwiseId.
    apply traceRefines_trans with
    (p:= id) (q:= id) (mb:= Mod (regs ++ regs') (rules ++ rules') (dms ++ dms')).

    - apply traceRefines_same_module_structure; simpl; auto.
      unfold RegInitT; rewrite namesOf_app.
      apply NoDup_DisjList; auto.

    - apply traceRefines_trans with
      (p:= id) (q:= id) (mb:= ConcatMod (Mod regs rules dms) (Mod regs' rules' dms'));
        [unfold MethsT; rewrite <-idElementwiseId; apply deflatten_traceRefines|].

      apply traceRefines_trans with
      (p:= id) (q:= id) (mb:= ConcatMod (Mod sregs srules sdms) (Mod regs' rules' dms'));
        [|unfold MethsT; rewrite <-idElementwiseId; apply flatten_traceRefines].

      unfold MethsT; rewrite <-idElementwiseId.
      apply traceRefines_modular_interacting with (vp:= (@idElementwise _));
        auto; try (constructor; auto; fail).
      + eapply DisjList_comm, DisjList_SubList; [apply getIntCalls_getCalls|].
        apply DisjList_comm; assumption.
      + eapply DisjList_SubList; [apply getIntCalls_getCalls|assumption].
      + eapply DisjList_comm, DisjList_SubList; [apply getIntCalls_getCalls|].
        apply DisjList_comm; assumption.
      + eapply DisjList_SubList; [apply getIntCalls_getCalls|assumption].
      + rewrite idElementwiseId; apply traceRefines_refl.
  Qed.

End Interacting.

