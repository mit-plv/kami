
(* Partial inlining interfaces *)
Section Partial.
  Variable m: Modules.

  Variable dm: DefMethT. (* a method to be inlined *)
  Hypothesis Hdm: In dm (getDefsBodies m).
  Variable r: Attribute (Action Void). (* a rule calling dm *)
  Hypothesis Hrule: In r (getRules m).

  Lemma inlineDmToRule_traceRefines_1:
    m <<== (Mod (getRegInits m)
                (map (fun newr =>
                        if string_dec (attrName r) (attrName newr)
                        then inlineDmToRule newr dm
                        else newr) (getRules m))
                (getDefsBodies m)).
  Proof.
    apply stepRefinement with (ruleMap:= fun _ s => Some s) (theta:= id); auto.
    intros; exists u; split; auto.

    rewrite idElementwiseId.
    replace (liftPLabel _ _ _ _) with l; [|destruct l as [[[|]|] ? ?]; simpl; f_equal].
    unfold id.

    clear H.
    apply step_consistent; apply step_consistent in H0.
    inv H0; constructor.

    - admit.
    - unfold wellHidden in *; dest; split.
      + admit.
      + unfold getDefs; simpl; auto.
  Qed.

  Hypothesis (HnoRuleCalls: forall rule,
                 In rule (getRules m) ->
                 attrName rule <> attrName r ->
                 ~ In (attrName dm) (getCallsA (attrType rule typeUT))).
  Hypothesis (HnoMethCalls: forall meth,
                 In meth (getDefsBodies m) ->
                 ~ In (attrName dm) (getCallsA (projT2 (attrType meth) typeUT tt))).

  Lemma inlineDmToRule_traceRefines_2:
    m <<== (Mod (getRegInits m)
                (map (fun newr =>
                        if string_dec (attrName r) (attrName newr)
                        then inlineDmToRule newr dm
                        else newr) (getRules m))
                (filterDm (getDefsBodies m) (attrName dm))).
  Proof.
    admit.
  Qed.

End Partial.

