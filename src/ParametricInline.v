Require Import PartialInline ParametricSyntax ParametricEquiv Syntax String List Semantics.

Section GenGen.
  Variable m: MetaModule.
  Variable mEquiv: forall ty, MetaModEquiv ty typeUT m.

  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                         si = sj /\ i = j.
  Variable dm: sigT GenMethodT.
  Variable dmName: string.
  Variable ls: list A.

  Variable r: GenAction Void.
  Variable rName: string.

  Hypotheses (Hdm: In (RepMeth strA goodStrFn goodStrFn2 dm dmName ls) (metaMeths m))
             (HnoDupMeths: NoDup (map getMetaMethName (metaMeths m)))
             (HnoDupRules: NoDup (map getMetaRuleName (metaRules m))).
  Hypothesis Hrule: In (RepRule strA goodStrFn goodStrFn2 r rName ls) (metaRules m).

  Lemma InlineGenGenDmToRule_traceRefines_1:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    map (fun newr =>
                           if string_dec rName (getMetaRuleName newr)
                           then RepRule strA goodStrFn goodStrFn2
                                        (fun ty => inlineGenGenDm (r ty) dmName dm) rName ls
                           else newr) (metaRules m);
                  metaMeths := metaMeths m |}.
  Proof.
    admit.
  Qed.

  Hypothesis HnoRuleCalls: forall rule,
                             In rule (metaRules m) ->
                             getMetaRuleName rule <> rName ->
                             ~ In dmName (map (fun n => nameVal (nameRec n))
                                              (getCallsMetaRule rule)).

  Hypothesis HnoMethCalls: forall meth,
                             In meth (metaMeths m) ->
                             getMetaMethName meth <> dmName ->
                             ~ In dmName (map (fun n => nameVal (nameRec n))
                                              (getCallsMetaMeth meth)).
  
  Lemma inlineGenGenDmToRule_traceRefines_2:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    map (fun newr =>
                           if string_dec rName (getMetaRuleName newr)
                           then RepRule strA goodStrFn goodStrFn2
                                        (fun ty => inlineGenGenDm (r ty) dmName dm) rName ls
                           else newr) (metaRules m);
                  metaMeths :=
                    filter
                      (fun dm' =>
                         if string_dec dmName (getMetaMethName dm')
                         then false
                         else true) (metaMeths m) |}.
  Proof.
    admit.
  Qed.
End GenGen.

Section GenSin.
  Variable m: MetaModule.
  Variable mEquiv: forall ty, MetaModEquiv ty typeUT m.

  Variable A: Type.
  Variable strA: A -> string.
  Variable goodStrFn: forall i j, strA i = strA j -> i = j.
  Variable goodStrFn2: forall si sj i j, addIndexToStr strA i si = addIndexToStr strA j sj ->
                                         si = sj /\ i = j.
  Variable dm: sigT SinMethodT.
  Variable dmName: string.
  Variable ls: list A.

  Variable r: GenAction Void.
  Variable rName: string.

  Hypotheses (Hdm: In (OneMeth dm dmName) (metaMeths m))
             (HnoDupMeths: NoDup (map getMetaMethName (metaMeths m)))
             (HnoDupRules: NoDup (map getMetaRuleName (metaRules m))).
  Hypothesis Hrule: In (RepRule strA goodStrFn goodStrFn2 r rName ls) (metaRules m).

  Lemma InlineGenSinDmToRule_traceRefines_1:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    map (fun newr =>
                           if string_dec rName (getMetaRuleName newr)
                           then RepRule strA goodStrFn goodStrFn2
                                        (fun ty => inlineGenSinDm (r ty) dmName dm) rName ls
                           else newr) (metaRules m);
                  metaMeths := metaMeths m |}.
  Proof.
    admit.
  Qed.

  Hypothesis HnoRuleCalls: forall rule,
                             In rule (metaRules m) ->
                             getMetaRuleName rule <> rName ->
                             ~ In dmName (map (fun n => nameVal (nameRec n))
                                              (getCallsMetaRule rule)).

  Hypothesis HnoMethCalls: forall meth,
                             In meth (metaMeths m) ->
                             getMetaMethName meth <> dmName ->
                             ~ In dmName (map (fun n => nameVal (nameRec n))
                                              (getCallsMetaMeth meth)).
  
  Lemma inlineGenSinDmToRule_traceRefines_2:
    makeModule m <<==
               makeModule
               {| metaRegs := metaRegs m;
                  metaRules :=
                    map (fun newr =>
                           if string_dec rName (getMetaRuleName newr)
                           then RepRule strA goodStrFn goodStrFn2
                                        (fun ty => inlineGenSinDm (r ty) dmName dm) rName ls
                           else newr) (metaRules m);
                  metaMeths :=
                    filter
                      (fun dm' =>
                         if string_dec dmName (getMetaMethName dm')
                         then false
                         else true) (metaMeths m) |}.
  Proof.
    admit.
  Qed.
End GenSin.