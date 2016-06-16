Require Import ParametricInline List ParametricSyntax String Syntax Lib.CommonTactics Tactics.

Fixpoint findDm dm pre ls :=
  match ls with
    | nil => None
    | OneMeth bd {| nameVal := dmName; goodName := pf |} :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, OneMeth bd {| nameVal := dm; goodName := match isEq with
                                                                | eq_refl => pf
                                                              end |}, xs)
        | right _ =>
          findDm dm (pre ++ OneMeth bd {| nameVal := dmName; goodName := pf |} :: nil) xs
      end
    | RepMeth A strA goodFn GenK getConstK goodFn2 bd
              {| nameVal := dmName; goodName := pf |} _ noDup :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, RepMeth strA goodFn getConstK
                             goodFn2 bd {| nameVal := dm; goodName :=
                                                            match isEq with
                                                              | eq_refl => pf
                                                            end |} noDup, xs)
        | right _ =>
          findDm dm (pre ++ RepMeth strA goodFn getConstK goodFn2
                         bd {| nameVal := dmName; goodName := pf |} noDup :: nil) xs
      end
  end.

Fixpoint findR dm pre ls :=
  match ls with
    | nil => None
    | OneRule bd {| nameVal := dmName; goodName := pf |} :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, OneRule bd {| nameVal := dm; goodName := match isEq with
                                                                | eq_refl => pf
                                                              end |}, xs)
        | right _ =>
          findR dm (pre ++ OneRule bd {| nameVal := dmName; goodName := pf |} :: nil) xs
      end
    | RepRule A strA goodFn GenK getConstK goodFn2 bd
              {| nameVal := dmName; goodName := pf |} _ noDup :: xs =>
      match string_dec dmName dm with
        | left isEq =>
          Some (pre, RepRule strA goodFn getConstK
                             goodFn2 bd {| nameVal := dm; goodName :=
                                                            match isEq with
                                                              | eq_refl => pf
                                                            end |} noDup, xs)
        | right _ =>
          findR dm (pre ++ RepRule strA goodFn getConstK goodFn2
                        bd {| nameVal := dmName; goodName := pf |} noDup :: nil) xs
      end
  end.

Ltac inlineGenDmGenRule_NoFilt m mEquiv dm r :=
  let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
    (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
        let rTriple := eval simpl in (findR r nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let m'Ref := fresh in
                    let m'Equiv := fresh in
                    pose proof (@inlineGenGenDmToRule_traceRefines_NoFilt
                                  m A strA goodFn GenK getConstK goodFn2
                                  bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                  sufR eq_refl noDupMeth noDupRule);
                      pose proof (@inlineGenGenDmToRule_ModEquiv_NoFilt
                                    m mEquiv A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule);
                      clear noDupMeth noDupRule
                end
            end.

Ltac inlineGenDmGenRule_Filt m mEquiv dm r :=
  let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
      (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
        let rTriple := eval simpl in (findR r nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let H3 := fresh in
                    let H4 := fresh in
                    let H5 := fresh in
                    assert
                      (H3:
                         forall r',
                           In r' (preR ++ sufR) ->
                           match r' with
                             | OneRule _ _ => true
                             | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                               noCallDmSigGenA (bgenB typeUT)
                                               {| isRep := true; nameRec := dmn |}
                                               (projT1 bdm)
                           end = true) by
                        (intro;
                         apply boolListReflection with
                         (f := (fun r' =>
                                  match r' with
                                    | OneRule _ _ => true
                                    | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                      noCallDmSigGenA (bgenB typeUT)
                                                      {| isRep := true; nameRec := dmn |}
                                                      (projT1 bdm)
                                  end)); apply eq_refl);
                      assert
                        (H4:
                           forall dm',
                             In dm' (metaMeths m) ->
                             match dm' with
                               | OneMeth _ _ => true
                               | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                 noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                 {| isRep := true; nameRec := dmn |}
                                                 (projT1 bdm)
                             end = true) by
                        (intro;
                         apply boolListReflection with
                         (f := (fun dm' =>
                                  match dm' with
                                    | OneMeth _ _ => true
                                    | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                      noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                      {| isRep := true; nameRec := dmn |}
                                                      (projT1 bdm)
                                  end)); apply eq_refl);
                      assert
                        (H5: exists call : NameRecIdx,
                               In call (getCallsGenA (bdr typeUT)) /\
                               nameVal (nameRec call) = nameVal dmn /\ isRep call = true) by
                          (eexists {| isRep := true;
                                      nameRec := {| nameVal := nameVal dmn;
                                                    goodName := _ |} |};
                           split; [
                             simpl; tauto | split; reflexivity]);
                      pose proof (@inlineGenGenDmToRule_traceRefines_Filt'
                                    m mEquiv A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule H3 H4 H5);
                        pose proof (@inlineGenGenDmToRule_ModEquiv_Filt'
                                      m mEquiv A strA goodFn GenK getConstK goodFn2
                                      bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                      sufR eq_refl noDupMeth noDupRule H4);
                        clear noDupMeth noDupRule H3 H4 H5
                end
            end.

Ltac inlineSinDmGenRule_NoFilt m mEquiv dm r :=
  let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
      (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
        let rTriple := eval simpl in (findR r nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let m'Ref := fresh in
                    let m'Equiv := fresh in
                    pose proof (@inlineGenSinDmToRule_traceRefines_NoFilt
                                  m A strA goodFn GenK getConstK goodFn2
                                  bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                  sufR eq_refl noDupMeth noDupRule);
                      pose proof (@inlineGenSinDmToRule_ModEquiv_NoFilt
                                    m mEquiv A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule);
                      clear noDupMeth noDupRule
                end
            end.

Theorem notNilNatList: forall n,
                         getNatListToN (Word.wordToNat (Word.wones n)) <> nil.
Proof.
  induction n; simpl in *; unfold not; intros; discriminate.
Qed.

Ltac inlineSinDmGenRule_Filt m mEquiv dm r :=
  let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
      (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
        let rTriple := eval simpl in (findR r nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                    let H3 := fresh in
                    let H4 := fresh in
                    let H5 := fresh in
                    let H6 := fresh in
                    assert
                      (H3:
                         forall r',
                           In r' (preR ++ sufR) ->
                           match r' with
                             | OneRule bgenB _ =>
                               noCallDmSigSinA (bgenB typeUT) dmn (projT1 bdm)
                             | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                               noCallDmSigGenA (bgenB typeUT)
                                               {| isRep := false; nameRec := dmn |}
                                               (projT1 bdm)
                           end = true) by
                        (intro;
                         apply boolListReflection with
                         (f := (fun r' =>
                                  match r' with
                                    | OneRule bgenB _ =>
                                      noCallDmSigSinA (bgenB typeUT) dmn (projT1 bdm)
                                    | RepRule _ _ _ _ _ _ bgenB _ _ _ =>
                                      noCallDmSigGenA (bgenB typeUT)
                                                      {| isRep := false; nameRec := dmn |}
                                                      (projT1 bdm)
                                  end)); apply eq_refl);
                      assert
                        (H4:
                           forall dm',
                             In dm' (metaMeths m) ->
                             match dm' with
                               | OneMeth bgenB _ =>
                                 noCallDmSigSinA (projT2 bgenB typeUT tt) dmn (projT1 bdm)
                               | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                 noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                 {| isRep := false; nameRec := dmn |}
                                                 (projT1 bdm)
                             end = true) by
                        (intro;
                         apply boolListReflection with
                         (f := (fun dm' =>
                                  match dm' with
                                    | OneMeth bgenB _ =>
                                      noCallDmSigSinA (projT2 bgenB typeUT tt) dmn (projT1 bdm)
                                    | RepMeth _ _ _ _ _ _ bgenB _ _ _ =>
                                      noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                      {| isRep := false; nameRec := dmn |}
                                                      (projT1 bdm)
                                  end)); apply eq_refl);
                      assert
                        (H5: exists call : NameRecIdx,
                               In call (getCallsGenA (bdr typeUT)) /\
                               nameVal (nameRec call) = nameVal dmn /\ isRep call = false) by
                          (eexists {| isRep := false;
                                      nameRec := {| nameVal := nameVal dmn;
                                                    goodName := _ |} |};
                           split; [
                             simpl; tauto | split; reflexivity]);
                      assert
                        (H6: ls <> nil) by (apply notNilNatList; auto);
                      pose proof (@inlineGenSinDmToRule_traceRefines_Filt'
                                    m mEquiv A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls H6 noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule H3 H4 H5);
                        pose proof (@inlineGenSinDmToRule_ModEquiv_Filt'
                                      m mEquiv A strA goodFn GenK getConstK goodFn2
                                      bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                      sufR eq_refl noDupMeth noDupRule H4);
                        clear noDupMeth noDupRule H3 H4 H5
                end
            end.


(*
Ltac inlineGenDmGenRule_Filt m mEquiv dm r :=
  let noDupMeth := fresh in
  let noDupRule := fresh in
  assert (noDupMeth: NoDup (map getMetaMethName (metaMeths m))) by
      (subst; simpl; clear; noDup_tac);
    assert (noDupRule: NoDup (map getMetaRuleName (metaRules m))) by
      (subst; simpl; clear; noDup_tac);
    let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
        let rTriple := eval simpl in (findR r nil (metaRules m)) in
            match dmTriple with
              | Some (?preDm, @RepMeth ?A ?strA ?goodFn ?GenK ?getConstK
                                       ?goodFn2 ?bdm ?dmn ?ls ?noDup, ?sufDm) =>
                match rTriple with
                  | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                          ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>

                    let H3 := fresh in
                    let H4 := fresh in
                    let H5 := fresh in
                    assert (H3:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : GenAction GenKB Void)
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepRule strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (preR ++ sufR) ->
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := true; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                      assert (H4:
                                forall (B : Type) (strB : B -> string)
                                       (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                       (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                       (goodStrFn2B : forall (si sj : string) (i j : B),
                                                        addIndexToStr strB i si =
                                                        addIndexToStr strB j sj ->
                                                        si = sj /\ i = j)
                                       (bgenB : sigT (GenMethodT GenKB))
                                       (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                  In
                                    (RepMeth strB goodStrFnB getConstKB
                                             goodStrFn2B bgenB rb noDupLsB)
                                    (metaMeths m) ->
                                  noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                  {| isRep := true; nameRec := dmn |}
                                                  (projT1 dm) = true) by
                          (let isIn := fresh in
                           intros ? ? ? ? ? ? ? ? ? ? isIn;
                           repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                           destruct isIn);
                      assert
                        (H5: exists call : NameRecIdx,
                               In call (getCallsGenA (r typeUT)) /\
                               nameVal (nameRec call) = nameVal dmn /\ isRep call = true) by
                          (eexists {| isRep := true;
                                      nameRec := {| nameVal := nameVal dmn;
                                                    goodName := _ |} |};
                           split; [simpl; tauto | split; reflexivity]);
                      let m'Ref := fresh in
                      let m'Equiv := fresh in
                      pose proof (@inlineGenGenDmToRule_traceRefines_Filt
                                    m A strA goodFn GenK getConstK goodFn2
                                    bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                    sufR eq_refl noDupMeth noDupRule H3 H4 H5) as m'Ref;
                        pose proof (@inlineGenGenDmToRule_ModEquiv_NoFilt
                                      m mEquiv A strA goodFn GenK getConstK goodFn2
                                      bdm dmn preDm sufDm ls noDup eq_refl bdr rn preR
                                      sufR eq_refl noDupMeth noDupRule H4) as m'Equiv;
                        clear noDupMeth noDupRule H3 H4 H5
                end
            end.
*)

(*
Ltac inlineSinDmGenRule_NoFilt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
              match rTriple with
                | Some (?preR, @RepRule ?A ?strA ?goodFn ?GenK ?getConstK
                                        ?goodFn2 ?bdr ?rn ?ls ?noDup, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDup_tac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDup_tac;
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ RepRule strA goodFn getConstK goodFn2
                                      (fun ty => inlineGenSinDm (bdr ty) dm bdm)
                                      rn noDup :: sufR;
                                     metaMeths := metaMeths m |},
                            inlineGenSinDmToRule_traceRefines_NoFilt
                              strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2,
                            inlineGenSinDmToRule_ModEquiv_NoFilt
                              mEquiv strA goodFn getConstK goodFn2
                              bdm dmn preDm sufDm noDup eq_refl bdr rn preR
                              sufR eq_refl H1 H2
                           )
              end
          end.

Ltac inlineSinDmSinRule_Filt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
              match rTriple with
                | Some (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  let H3 := fresh in
                  let H4 := fresh in
                  let H5 := fresh in
                  let H7 := fresh in
                  let H8 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDup_tac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDup_tac;
                    assert (H3:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : GenAction GenKB Void)
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepRule strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (preR ++ sufR) ->
                                noCallDmSigGenA (bgenB typeUT)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert (H4:
                              forall (B : Type) (strB : B -> string)
                                     (goodStrFnB : forall i j : B, strB i = strB j -> i = j) 
                                     (GenKB : Kind) (getConstKB : B -> ConstT GenKB)
                                     (goodStrFn2B : forall (si sj : string) (i j : B),
                                                      addIndexToStr strB i si =
                                                      addIndexToStr strB j sj ->
                                                      si = sj /\ i = j)
                                     (bgenB : sigT (GenMethodT GenKB))
                                     (rb : NameRec) (lsB : list B) (noDupLsB : NoDup lsB),
                                In
                                  (RepMeth strB goodStrFnB getConstKB
                                           goodStrFn2B bgenB rb noDupLsB)
                                  (metaMeths m) ->
                                noCallDmSigGenA (projT2 bgenB typeUT tt)
                                                {| isRep := false; nameRec := dmn |}
                                                (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? ? ? ? ? ? ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert
                      (H5: exists call : NameRec,
                             In call (getCallsGenA (r typeUT)) /\
                             nameVal call = nameVal dmn) by
                        (eexists {| nameVal := nameVal dmn;
                                    goodName := _ |};
                         split; [simpl; tauto | reflexivity]);
                    assert
                      (H7: forall rbody rb, In (OneRule rbody rb) (metaRules m) ->
                                            noCallDmSigSinA (projT2 rbody typeUT tt)
                                                            dmn (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    assert
                      (H8: forall dbody db, In (OneMeth dbody db) (metaMeths m) ->
                                            noCallDmSigSinA (projT2 dbody typeUT tt)
                                                            dmn (projT1 dm) = true) by
                        (let isIn := fresh in
                         intros ? ? isIn;
                         repeat (destruct isIn as [? | isIn]; [subst; reflexivity | ]);
                         destruct isIn);
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ OneRule
                                      (fun ty => inlineSinSinDm (bdr ty) dm bdm)
                                      rn :: sufR;
                               metaMeths := preDm ++ sufDm |},
                            inlineSinSinDmToRule_traceRefines_Filt
                              mEquiv
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H7 H3 H8 H4 H5,
                            inlineSinSinDmToRule_ModEquiv_Filt
                              mEquiv
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2 H8 H4
                           )
              end
          end.

Ltac inlineSinDmSinRule_NoFilt m mEquiv dm r :=
  let dmTriple := eval simpl in (findDm dm nil (metaMeths m)) in
      let rTriple := eval simpl in (findR r nil (metaRules m)) in
          match dmTriple with
            | Some (?preDm, @OneMeth ?bdm ?dmn, ?sufDm) =>
              match rTriple with
                | Some (?preR, @OneRule ?bdr ?rn, ?sufR) =>
                  let H1 := fresh in
                  let H2 := fresh in
                  assert (H1: NoDup (map getMetaMethName (metaMeths m))) by
                      noDup_tac;
                    assert (H2: NoDup (map getMetaRuleName (metaRules m))) by
                      noDup_tac;
                    constr:({| metaRegs := metaRegs m;
                               metaRules :=
                                 preR ++ OneRule
                                      (fun ty => inlineSinSinDm (bdr ty) dm bdm)
                                      rn :: sufR;
                               metaMeths := metaMeths m |},
                            inlineSinSinDmToRule_traceRefines_NoFilt
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2,
                            inlineSinSinDmToRule_ModEquiv_NoFilt
                              mEquiv
                              bdm dmn preDm sufDm eq_refl bdr rn preR
                              sufR eq_refl H1 H2
                           )
              end
          end.

*)