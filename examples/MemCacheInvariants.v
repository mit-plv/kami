Require Import Lib.FMap Lib.Word Lib.WordSupport Ex.MemTypes Lib.Indexer Lib.Struct Ex.Msi
        Ex.NativeFifo Kami.Notations String Ex.MemCacheInl Kami.Syntax List Kami.Semantics
        Kami.ParametricSyntax Lib.CommonTactics Kami.SemFacts Lib.FMap Lib.Concat Arith
        FunctionalExtensionality Program.Equality Kami.Tactics Lib.MapVReify Kami.SymEval
        Kami.SymEvalTac Lib.StringAsList Lib.ListSupport Lib.Misc
        Coq.Program.Basics Ex.Names Lib.FinNotations.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Notation "<| t |>" := (fullType type (SyntaxKind t)).

Local Notation "<[ t ]>" := (fullType type (@NativeKind t nil)).

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Local Notation RqFC := (RqFromC LgNumChildren (Bit (IdxBits + TagBits)) Id).
  Local Notation RsFC := (RsFromC LgDataBytes LgNumDatas LgNumChildren (Bit (IdxBits + TagBits))).
  Local Notation RqTP := (RqToP (Bit (IdxBits + TagBits)) Id).
  Local Notation RsTP := (RsToP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits))).
  Local Notation TC := (ToC LgDataBytes LgNumDatas LgNumChildren (Bit (IdxBits + TagBits)) Id).
  Local Notation FP := (FromP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits)) Id).

  Fixpoint filtRqFromC
             (c: word LgNumChildren) a
             (ls: list (type (Struct RqFC))):
    list (type (Struct RqTP)) :=
    match ls with
      | x :: xs => if weq c (x (RqFC !! child))
                   then if weq a (x (RqFC !! rq) (RqTP !! addr))
                        then x (RqFC !! rq) :: filtRqFromC c a xs
                        else filtRqFromC c a xs
                   else filtRqFromC c a xs
      | nil => nil
    end.

  Fixpoint filtRsFromC
             (c: word LgNumChildren) (a: word (IdxBits + TagBits))
             (ls: list (type (Struct RsFC))):
    list (type (Struct RsTP)) :=
    match ls with
      | x :: xs => if weq c (x (RsFC !! child))
                   then if weq a (x (RsFC !! rs) (RsTP !! addr))
                        then x (RsFC !! rs) :: filtRsFromC c a xs
                        else filtRsFromC c a xs
                   else filtRsFromC c a xs
      | nil => nil
    end.

  Fixpoint filtToC
             (c: word LgNumChildren) a
             (ls: list (type (Struct TC))):
    list (type (Struct FP)) :=
    match ls with
      | x :: xs => if weq c (x (TC !! child))
                   then if weq a (x (TC !! msg) (FP !! addr))
                        then x (TC !! msg) :: filtToC c a xs
                        else filtToC c a xs
                   else filtToC c a xs
      | nil => nil
    end.

  Fixpoint filtRqToP
             (a: word (IdxBits + TagBits))
             (ls: list (type (Struct RqTP))):
    list (type (Struct RqTP)) :=
    match ls with
      | x :: xs => if weq a (x (RqTP !! addr))
                   then x :: filtRqToP a xs
                   else filtRqToP a xs
      | nil => nil
    end.

  Fixpoint filtRsToP
             a
             (ls: list (type (Struct RsTP))):
    list (type (Struct RsTP)) :=
    match ls with
      | x :: xs => if weq a (x (RsTP !! addr))
                   then x :: filtRsToP a xs
                   else filtRsToP a xs
      | nil => nil
    end.

  Fixpoint filtFromP
             a
             (ls: list (type (Struct FP))):
    list (type (Struct FP)) :=
    match ls with
      | x :: xs => if weq a (x (FP !! addr))
                   then x :: filtFromP a xs
                   else filtFromP a xs
      | nil => nil
    end.

  Definition rqFromCToP
             (c: word LgNumChildren) a
             (l1: list (type (Struct RqFC)))
             (l2: list (type (Struct RqTP))):
    list (type (Struct RqTP)) :=
    (filtRqFromC c a l1 ++ filtRqToP a l2)%list.

  Definition rsFromCToP
             (c: word LgNumChildren) a
             (l1: list (type (Struct RsFC)))
             (l2: list (type (Struct RsTP))):
    list (type (Struct RsTP)) :=
    (filtRsFromC c a l1 ++ filtRsToP a l2)%list.

  Definition fromPToC
             (c: word LgNumChildren) a
             (l1: list (type (Struct FP)))
             (l2: list (type (Struct TC))):
    list (type (Struct FP)) :=
    (filtFromP a l1 ++ filtToC c a l2)%list.

  Definition getCs (cs: word IdxBits -> type Msi) (tag: word IdxBits -> word TagBits)
             a :=
    if weq (tag (split1 IdxBits TagBits a)) (split2 IdxBits TagBits a)
    then cs (split1 IdxBits TagBits a)
    else $ Msi.Inv.

  Fixpoint rsLessTo (ls: list (type (Struct RsTP))) :=
    match ls with
      | x :: xs =>
        match xs with
          | y :: xs' =>
            x (RsTP !! to) > y (RsTP !! to) /\ rsLessTo xs
          | nil => True
        end
      | _ => True
    end.

  Local Notation RqFPr := (RqFromProc LgDataBytes (Bit (LgNumDatas + (IdxBits + TagBits)))).
  Local Notation RsTPr := (RsToProc LgDataBytes).
  Definition isCWait a procRqValid
             (procRq: type (Struct RqFPr))
             csw :=
    procRqValid = true /\ a = split2 LgNumDatas (IdxBits + TagBits) (procRq (RqFPr !! addr)) /\
    csw = true.

  Definition isPWait a cRqValid
             (rqFromCList: list (type (Struct RqFC)))
             dirw (cword: word LgNumChildren) :=
    cRqValid = true /\
    dirw cword = true /\
    match hd_error rqFromCList with
      | Some cRq => a = cRq (RqFC !! rq) (RqTP !! addr)
      | _ => False
    end.

  Definition cache := nat.

(*
  Opaque procRqValidReg.
  Opaque procRqReplaceReg.
  Opaque procRqWaitReg.
  Opaque procRqReg.
  Opaque l1MissByState.
  Opaque l1MissByLine.
  Opaque l1Hit.
  Opaque writeback.
  Opaque upgRq.
  Opaque upgRs.
  Opaque ld.
  Opaque st.
  Opaque drop.
  Opaque pProcess.

  Opaque cRqValidReg.
  Opaque cRqDirwReg.
  Opaque cRqReg.
  Opaque missByState.
  Opaque dwnRq.
  Opaque dwnRs_wait.
  Opaque dwnRs_noWait.
  Opaque deferred.

  Opaque rqFromProc.
  Opaque rsToProc.
  Opaque rqToParent.
  Opaque rsToParent.
  Opaque rqFromChild.
  Opaque rsFromChild.
  Opaque fromParent.
  Opaque toChild.
  Opaque line.
  Opaque tag.
  Opaque cs.
  Opaque mcs.
  Opaque mline.

  Opaque elt.
  Opaque enqName.
  Opaque deqName.
  Opaque enqP.
  Opaque deqP.
  Opaque empty.
  Opaque full.
  Opaque firstEltName.

  Opaque addr.
  Opaque data.
  Opaque dataArray.
  Opaque read.
  Opaque write.

  Opaque rqFromCToPRule.
  Opaque rsFromCToPRule.
  Opaque fromPToCRule.
*)


  Open Scope fmap.

  Record nmemCache_invariants_rec (s: RegsT)
         a cword (c: cache): Prop :=
    {
      dir: <| Vector (Vector Msi LgNumChildren) (IdxBits + TagBits) |> ;
      dirFind: dir === s.[mcs -- dataArray] ;
      cRqValid: <| Bool |> ;
      cRqValidFind: cRqValid === s.[cRqValidReg] ;
      dirw: <| Vector Bool LgNumChildren |> ;
      dirwFind: dirw === s.[cRqDirwReg] ;
      rqFromCList: <[ list (type (Struct RqFC)) ]> ;
      rqFromCListFind: rqFromCList === s.[rqFromChild -- elt] ;
      rsFromCList: <[ list (type (Struct RsFC)) ]> ;
      rsFromCListFind: rsFromCList === s.[rsFromChild -- elt] ;
      toCList: <[ list (type (Struct TC)) ]>;
      toCListFind: toCList === s.[toChild -- elt] ;
      csv: <| Vector Msi IdxBits |> ;
      csFind: csv === s.[(cs -- dataArray) __ c] ;
      tagv: <| Vector (Bit TagBits) IdxBits |> ;
      tagFind: tagv === s.[(tag -- dataArray) __ c];
      procRqValid: <| Bool |> ;
      procRqValidFind: procRqValid === s.[procRqValidReg __ c] ;
      procRqReplace: <| Bool |> ;
      procRqReplaceFind: procRqReplace === s.[procRqReplaceReg __ c] ;
      procRq: <| Struct RqFPr |> ;
      procRqFind: procRq === s.[procRqReg __ c] ;
      csw: <| Bool |> ;
      cswFind: csw === s.[procRqWaitReg __ c] ;
      rqToPList: <[ list (type (Struct RqTP)) ]> ;
      rqToPListFind:  rqToPList === s.[(rqToParent -- elt) __ c] ;
      rsToPList: <[ list (type (Struct RsTP)) ]> ;
      rsToPListFind: rsToPList === s.[(rsToParent -- elt) __ c] ;
      fromPList: <[ list (type (Struct FP)) ]> ;
      fromPListFind: fromPList === s.[(fromParent -- elt) __ c] ;
      cRq: <| Struct RqFC |> ;
      cRqFind: cRq === s.[cRqReg] ;

      i5: dir a cword >= getCs csv tagv a ;
      
      i7: forall rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                     getCs csv tagv a <= rs (RsTP !! to) /\
                     dir a cword > rs (RsTP !! to) ;

      i8: forall rs, In rs (fromPToC cword a fromPList toCList) ->
                     rs (FP !! isRq) = false ->
                     getCs csv tagv a < rs (FP !! to) /\
                     dir a cword = rs (FP !! to) ;

      i9: forall rq rs,
            In rq (rqFromCToP cword a rqFromCList rqToPList) ->
            In rs (rsFromCToP cword a rsFromCList rsToPList) ->
            dir a cword <= rq (RqTP !! from) ->
            isPWait a cRqValid rqFromCList dirw cword ;

      i10: (forall beg mid last rs1 rs2,
              fromPToC cword a fromPList toCList = beg ++ rs1 :: mid ++ rs2 :: last ->
              rs1 (FP !! isRq) = false ->
              rs2 (FP !! isRq) = false ->
              False)%list ;
      
      i11: rsFromCToP cword a rsFromCList rsToPList = nil ->
           dir a cword = getCs csv tagv a ;
           
      i12: forall rs, In rs (fromPToC cword a fromPList toCList) ->
                      rs (FP !! isRq) = false ->
                      rsFromCToP cword a rsFromCList rsToPList = nil ;
    
      i13: rsLessTo (rsFromCToP cword a rsFromCList rsToPList) ;

      i14: (forall beg rs,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ [rs] ->
              rs (RsTP !! to) = getCs csv tagv a)%list ;

      i15: (forall beg mid last rq rs,
              fromPToC cword a fromPList toCList = beg ++ rq :: mid ++ rs :: last ->
              rq (FP !! isRq) = true ->
              rs (FP !! isRq) = false ->
              getCs csv tagv a = $ Msi.Inv)%list ;

      i16: isCWait a procRqValid procRq csw ->
           (getCs csv tagv a < if (procRq (RqFPr !! op)):bool
                               then $ Msi.Mod else $ Msi.Sh)
           /\
           ((exists rq, In rq (rqFromCToP cword a rqFromCList rqToPList) /\
                        rq (RqTP !! to) = (if (procRq (RqFPr !! op)):bool then $ Msi.Mod else $ Msi.Sh) /\
                        rq (RqTP !! from) >= getCs csv tagv a) \/
            (exists rs, In rs (fromPToC cword a fromPList toCList) /\
                        rs (FP !! isRq) = false /\
                        rs (FP !! to) = if (procRq (RqFPr !! op)):bool then $ Msi.Mod else $ Msi.Sh)) ;

      i16a: forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                       isCWait a procRqValid procRq csw
                       /\ (getCs csv tagv a < if (procRq (RqFPr !! op)):bool
                                            then $ Msi.Mod else $ Msi.Sh)
                       /\ rq (RqTP !! to) =
                          (if (procRq (RqFPr !! op)):bool then $ Msi.Mod else $ Msi.Sh)
                       /\ rq (RqTP !! from) >= getCs csv tagv a ;

      i16b: forall rs, In rs (fromPToC cword a fromPList toCList) ->
                       isCWait a procRqValid procRq csw
                       /\ (getCs csv tagv a < if (procRq (RqFPr !! op)):bool
                                              then $ Msi.Mod else $ Msi.Sh)
                       /\ rs (FP !! isRq) = false
                       /\ rs (FP !! to) =
                          (if (procRq (RqFPr !! op)):bool then $ Msi.Mod else $ Msi.Sh) ;
    
      i16c: forall rq rs, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                          In rs (fromPToC cword a fromPList toCList) ->
                          rs (FP !! isRq) = true ;

      i17: forall rq,
             In rq (fromPToC cword a fromPList toCList) ->
             rq (FP !! isRq) = true ->
             getCs csv tagv a = $ Msi.Inv \/
             isPWait a cRqValid rqFromCList dirw cword ;

      i18: forall rq rs,
             In rq (fromPToC cword a fromPList toCList) ->
             In rs (rsFromCToP cword a rsFromCList rsToPList) ->
             rq (FP !! isRq) = true ->
             rs (RsTP !! to) = $ Msi.Inv ;

      i19: (forall beg mid last rq rs,
              fromPToC cword a fromPList toCList = beg ++ rs :: mid ++ rq :: last ->
              rs (FP !! isRq) = false ->
              rq (FP !! isRq) = true ->
              isPWait a cRqValid rqFromCList dirw cword)%list ;

      i20: (forall beg mid last rq1 rq2,
              fromPToC cword a fromPList toCList = beg ++ rq1 :: mid ++ rq2 :: last ->
              rq1 (FP !! isRq) = true ->
              rq2 (FP !! isRq) = true ->
              getCs csv tagv a = $ Msi.Inv)%list ;

      i21: forall rs,
             In rs (rsFromCToP cword a rsFromCList rsToPList) ->
             rs (RsTP !! isVol) = false ->
             isPWait a cRqValid rqFromCList dirw cword ;

      i22: (forall beg mid last cToPRs1 cToPRs2,
              rsFromCToP cword a rsFromCList rsToPList =
              beg ++ cToPRs1 :: mid ++ cToPRs2 :: last ->
              cToPRs1 (RsTP !! isVol) = true \/
              cToPRs2 (RsTP !! isVol) = true)%list ;

      i23: forall rq rs,
             In rq (rqFromCToP cword a rqFromCList rqToPList) ->
             In rs (rsFromCToP cword a rsFromCList rsToPList) ->
             dir a cword <= rq (RqTP !! from) ->
             rs (RsTP !! isVol) = false ;

      i25: forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                      rq (RqTP !! from) < rq (RqTP !! to) ;

      i26: forall rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                      rs (RsTP !! isVol) = true ->
                      rs (RsTP !! to) = $ Msi.Inv ;

      i27: procRqValid = true -> procRqReplace = true ->
           tagv (split1 IdxBits TagBits
                        (split2 LgNumDatas (IdxBits + TagBits)
                                (procRq (RqFPr !! addr)))) =
           split2 IdxBits TagBits (split2 LgNumDatas (IdxBits + TagBits)
                                          (procRq (RqFPr !! addr))) ->
           csv (split1 IdxBits TagBits
                       (split2 LgNumDatas (IdxBits + TagBits)
                               (procRq (RqFPr !! addr)))) = $ Msi.Inv ;
      
      i28: cRqValid = true -> hd_error rqFromCList = Some cRq ;

      i29: forall rq rs, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                         In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                         rs (RqTP !! isVol) = true ->
                         rq (RqTP !! from) = $ Msi.Inv
    }.

  Lemma nmemCache_invariants_same' s a c x (pf: c <> x) k v:
    nmemCache_invariants_rec s a ($ c) c ->
    nmemCache_invariants_rec s#[k __ x |--> v] a ($ c) c.
  Proof.
    intros.
    destruct H.
    esplit;
      match goal with
        | |- ?v' === (?s) #[?k __ ?x |--> ?v] .[?k'] =>
          assert (k' <> k __ x) by (apply not_in_string_uneq; reflexivity);
            rewrite M.find_add_2; eauto
        | H: ?c <> ?x |- ?v' === (?s) #[(?k) __ (?x) |--> ?v] .[?k' __ ?c] =>
          let K := fresh in
          let sth := fresh in
          assert (k' __ c <> k __ x) by
              (intro K; apply withIndex_index_eq in K; destruct K as [? sth]; intuition auto);
            rewrite M.find_add_2; eauto
        | _ => eauto
      end.
  Qed.
  
  Lemma nmemCache_invariants_same s a c x (pf: c <> x) ls:
    nmemCache_invariants_rec s a ($ c) c ->
    nmemCache_invariants_rec (M.union (do_upd_map_key_instance x ls) s) a ($ c) c.
  Proof.
    induction ls; unfold do_upd_map_key_instance; simpl; auto; intros;
    fold (do_upd_map_key_instance x ls).
    rewrite M.union_add.
    apply nmemCache_invariants_same' with (s := M.union (do_upd_map_key_instance x ls) s); auto.
  Qed.

  Definition nmemCache_invariants (s: RegsT) :=
    forall a cword (c: cache),
      (c <= wordToNat (wones LgNumChildren))%nat ->
      cword = natToWord _ c ->
      nmemCache_invariants_rec s a cword c.



  Fixpoint getMetaRules r' ls :=
    match ls with
      | nil => None
      | OneRule _ _ :: ls => getMetaRules r' ls
      | RepRule _ strA goodStr1 _ getConstK goodStr2 a n _ noDup :: ls =>
        match string_dec r' (nameVal n) with
          | left _ => Some (RepRule strA goodStr1 getConstK goodStr2 a n noDup)
          | right _ => getMetaRules r' ls
        end
    end.

  Fixpoint getNormalRules r' ls :=
    match ls with
      | nil => None
      | OneRule a n :: ls =>
        match string_dec r' (nameVal n) with
          | left _ => Some (getActionFromSin a type)
          | right _ => getNormalRules r' ls
        end
      | RepRule _ strA _ k getConstK _ a n _ _ :: ls => getNormalRules r' ls
    end.

  Lemma invRepRule n a1 name1 pf1 a2 name2 pf2:
    RepRule string_of_nat string_of_nat_into
            (natToWordConst n) withIndex_index_eq a1
            {| nameVal := name1;
               goodName := pf1 |}
            (getNatListToN_NoDup (wordToNat (wones n))) =
    RepRule string_of_nat string_of_nat_into
            (natToWordConst n) withIndex_index_eq a2
            {| nameVal := name2;
               goodName := pf2 |}
            (getNatListToN_NoDup (wordToNat (wones n))) ->
    a1 = a2.
  Proof.
    intros.
    inv H.
    clear - H1.
    apply Eqdep.EqdepTheory.inj_pair2 in H1.
    apply H1.
  Qed.

  Local Notation "n 'is' a" :=
    (getNormalRules n
                    (metaRules (nmemCacheInl IdxBits TagBits
                                             LgNumDatas LgDataBytes Id LgNumChildren))
     = Some a) (at level 0).
  
  Local Notation "n 'metaIs' a" :=
    (getMetaRules n
                  (metaRules (nmemCacheInl IdxBits TagBits
                                           LgNumDatas LgDataBytes Id LgNumChildren))
     = Some (RepRule string_of_nat string_of_nat_into
                     (natToWordConst LgNumChildren) withIndex_index_eq a
                     {| nameVal := n;
                        goodName := eq_refl |}
                     (getNatListToN_NoDup (wordToNat (wones LgNumChildren))))) (at level 0).


  

  
  Ltac substFind :=
    match goal with
      | H: ?y === ?n .[ ?s] , H': ?v === ?n .[ ?s] |- _ =>
        rewrite H' in H;
          apply invSome in H;
          apply Eqdep.EqdepTheory.inj_pair2 in H; rewrite <- ?H in *; clear H y; intros
      | |- _ /\ _ => split; intros
      | |- _ => auto
    end.

  Ltac elimDiffC c :=
    match goal with
      | H: (?x <= wordToNat _)%nat, H': (c <= wordToNat _)%nat |-
        nmemCache_invariants_rec (M.union ?m ?n) ?a
                                 ?cword c =>
        destruct (eq_nat_dec c x);
          [subst|
           let ls := mkList_add_key_instance m in
           replace m with (do_upd_map_key_instance x ls) by
               reflexivity;
             apply nmemCache_invariants_same; auto]
      | _ => idtac
    end.
  
  Ltac destructRules c HInd :=
    unfold getActionFromGen, getGenAction, strFromName in *;
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
      subst; unfold getActionFromSin, getSinAction in *; subst;
    SymEval; subst; simpl; unfold VectorFacts.Vector_find; simpl;
    match goal with
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat, H': (c <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl);
          specialize (HInd a _ _ H' eq_refl)
      | a: word (IdxBits + TagBits), H: (_ <=
                                         _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl)          
    end;
    unfold withIndex in *;
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest;
    repeat simplBool;
    elimDiffC c.

  Ltac normalInit :=
    intros HInd HInRule HS;
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule;
    apply invSome in HInRule;
    unfold getActionFromSin, getSinAction at 1 in HInRule;
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ?; destructRules c HInd.
  
  Ltac metaInit :=
    intros HInd HInRule x xcond HS;
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule;
    apply invSome in HInRule;
    apply invRepRule in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ?; destructRules c HInd.

  Ltac invariant_simpl :=
    subst;
    try match goal with
        | [ H : nmemCache_invariants_rec _ _ _ ?c |- _ ] =>
          match goal with
          | [ _ : context[addIndexToStr _ c _] |- _ ] => clear H
          | _ => destruct H
          end
        end;
    unfold withIndex, listIsEmpty,
    listFirstElt, listEnq, listDeq in *; simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest; repeat simplBool;
    repeat match goal with
           | [ H : evalConstT match ?E with _ => _ end = _ |- _ ] =>
             destruct E; try discriminate; [ clear H ]
           end; autorewrite with invariant in *;
    dest.

  Ltac rmBadHyp :=
    repeat match goal with
             | [H: ?a === ?s .[ ?v ] |- _] =>
               clear H
             | [H: ?v = ?v |- _] => clear H
           end.








  Lemma rsLessTo_less_app ls:
    forall (v1: type (Struct RsTP)),
      rsLessTo (ls ++ [v1]) ->
      forall (v2: type (Struct RsTP)),
        v1 (RsTP !! to) > v2 (RsTP !! to) ->
        rsLessTo ((ls ++ [v1]) ++ [v2]).
  Proof.
    unfold VectorFacts.Vector_find.
    cbn.
    induction ls; [simpl; auto| intros; cbn in *].
    case_eq (ls ++ [v1])%list;
      case_eq ((ls ++ [v1]) ++ [v2])%list; intros;
      repeat match goal with
               | H: (_ ++ [_])%list = nil |- _ =>
                 apply eq_sym in H; apply app_cons_not_nil in H; exfalso; auto
             end; cbn in *; unfold VectorFacts.Vector_find in *; cbn in *.
    assert (sth: y = y0).
    { destruct ls; cbn in *.
      - inv H1;
        inv H2.
        reflexivity.
      - inv H1; inv H2.
        reflexivity.
    }

    rewrite <- sth in *; clear sth y0.
    rewrite H2 in *; cbn in *; unfold VectorFacts.Vector_find in *; cbn in *;
    inv H1.

    destruct H as [sth rsLess].
    constructor; [auto|].

    assert (rsLessTo (ls ++ [v1])).
    { rewrite H2.
      cbn.
      assumption.
    }
    apply IHls with (v2 := v2) in H.
    rewrite H2 in H.
    cbn in H.
    assumption.
    auto.
  Qed.

  Lemma rsLessTo_in_I_last ls:
      rsLessTo ls ->
      forall rs,
        In rs ls ->
        rs (RsTP !! to) = WO~0~0 ->
        exists sth, ls = (sth ++ [rs])%list.
  Proof.
    induction ls; cbn; intros; [exfalso; auto|].
    destruct H0, ls; subst; dest.
    - exists nil; reflexivity.
    - rewrite H1 in H; word_omega.
    - cbn in *; intuition auto.
    - specialize (IHls H2 rs H0 H1).
      dest.
      exists (a :: x).
      cbn.
      f_equal; auto.
  Qed.

  Lemma rsLessTo_cons_in ls:
    forall g,
      rsLessTo (g :: ls) ->
      forall rs,
        In rs ls ->
        rs (RsTP !! to) < g (RsTP !! to).
  Proof.
    induction ls; intros; cbn in *; subst; intuition auto.
    rewrite H in *; auto.
    apply IHls with (rs := rs) in H2; auto.
    word_omega.
  Qed.

  Lemma rsLessTo_cons_rsLessTo ls:
    forall g,
      rsLessTo (g :: ls) -> rsLessTo ls.
  Proof.
    intros.
    cbn in *.
    destruct ls; dest; auto.
  Qed.



  Ltac rsLessTo_thms :=
    try match goal with
          | H: rsLessTo (?ls ++ (?v :: nil))%list |- _ =>
            pose proof (@rsLessTo_less_app ls v H)
        end;
    try match goal with
          | H: rsLessTo ?ls |- _ =>
            pose proof (@rsLessTo_in_I_last ls H)
        end;
    try match goal with
          | H: rsLessTo (?g :: ?ls)%list |- _ =>
            pose proof (@rsLessTo_cons_in ls g H);
              pose proof (@rsLessTo_cons_rsLessTo ls g H)
        end.
  

  Lemma getCs_tag_match_getCs cs tag a a' upd:
    tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a ->
    getCs (fun a'' => if weq a'' (split1 IdxBits TagBits a)
                      then upd
                      else cs a'') tag a' =
    if weq a' a
    then upd
    else getCs cs tag a'.
  Proof.
    intros.
    unfold getCs.
    repeat match goal with
             | |- context[if ?p then _ else _] => destruct p; try reflexivity; try congruence
           end.
    rewrite <- (Word.combine_split IdxBits TagBits a), <- (Word.combine_split IdxBits TagBits a') in n.
    congruence.
  Qed.

  Lemma getCs_cs: forall cs tag a,
                              tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a \/
                              cs (split1 IdxBits TagBits a) = WO~0~0
                              ->
                              getCs cs tag a = cs (split1 IdxBits TagBits a).
  Proof.
    intros.
    unfold getCs; subst.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; intuition auto
           end.
  Qed.

  Lemma filtRqFromC_commute_app:
    (forall c a l1 l2, (filtRqFromC c a (l1 ++ l2)) = filtRqFromC c a l1 ++ filtRqFromC c a l2)%list.
  Proof.
    induction l1; cbn; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.
  
  Lemma filtRsFromC_commute_app:
    (forall c a l1 l2, (filtRsFromC c a (l1 ++ l2)) = filtRsFromC c a l1 ++ filtRsFromC c a l2)%list.
  Proof.
    induction l1; cbn; auto; intros.

    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.
  

  Lemma filtToC_commute_app:
    (forall c a l1 l2, (filtToC c a (l1 ++ l2)) = filtToC c a l1 ++ filtToC c a l2)%list.
  Proof.
    induction l1; cbn; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.

  Lemma filtRqToP_commute_app:
    (forall a l1 l2, (filtRqToP a (l1 ++ l2)) = filtRqToP a l1 ++ filtRqToP a l2)%list.
  Proof.
    induction l1; cbn; auto; intros.
    rewrite IHl1.
    match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.
  
  Lemma filtRsToP_commute_app:
    (forall a l1 l2, (filtRsToP a (l1 ++ l2)) = filtRsToP a l1 ++ filtRsToP a l2)%list.
  Proof.
    induction l1; cbn; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.

  Lemma filtFromP_commute_app:
    (forall a l1 l2, (filtFromP a (l1 ++ l2)) = filtFromP a l1 ++ filtFromP a l2)%list.
  Proof.
    induction l1; cbn; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.

  Lemma rewrite_rsFromCToP_revcons:
    forall c a rsFromCList rsToPList (v: type (Struct (RsToP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits))))),
      rsFromCToP c a rsFromCList (rsToPList ++ [v])%list =
      (rsFromCToP c a rsFromCList rsToPList ++ 
                  if weq a (v (RsTP !! addr))
                  then [v] else nil)%list.
  Proof.
    cbn; intros.
    unfold rsFromCToP.
    rewrite filtRsToP_commute_app.
    rewrite app_assoc.
    f_equal.
  Qed.

  Lemma rewrite_rqFromCToP_revcons:
    forall c a rqFromCList rqToPList (v: type (Struct (RqToP (Bit (IdxBits + TagBits)) Id))),
      rqFromCToP c a rqFromCList (rqToPList ++ [v])%list =
      (rqFromCToP c a rqFromCList rqToPList ++ 
                  if weq a (v (RqTP !! addr))
                  then [v] else nil)%list.
  Proof.
    cbn; intros.
    unfold rqFromCToP.
    rewrite filtRqToP_commute_app.
    rewrite app_assoc.
    f_equal.
  Qed.

  Lemma rewrite_fromPToC_cons:
    forall c a fromPList toCList (v: type (Struct (FromP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits)) Id))),
      fromPToC c a (v :: fromPList) toCList  =
      if weq a (v (FP !!addr))
      then v :: fromPToC c a fromPList toCList
      else fromPToC c a fromPList toCList.
  Proof.
    unfold fromPToC.
    cbn; intros.
    match goal with
      | |- context[if ?p then _ else _] => destruct p
    end; reflexivity.
  Qed.
  
  Ltac rmForTauto :=
    repeat match goal with
             | H: _ -> _ |- _ => clear H
           end.

  Hint Rewrite rewrite_rsFromCToP_revcons rewrite_rqFromCToP_revcons rewrite_fromPToC_cons: invariant.



  
  Ltac destruct_addr :=
    try match goal with
          | H: context[@weq (IdxBits + TagBits) ?a ?a'] |- _ =>
            let isEq := fresh in
            try (destruct (weq a a') as [isEq | ?]; rewrite ?app_nil_r in *; [rewrite isEq in *; clear isEq | assumption ])
          | |- context[@weq (IdxBits + TagBits) ?a ?a'] =>
            let isEq := fresh in
            try (destruct (weq a a') as [isEq | ?]; rewrite ?app_nil_r in *; [rewrite isEq in *; clear isEq | assumption ])
        end.

  Ltac rewrite_getCs :=
    try rewrite getCs_tag_match_getCs in * by (rmForTauto; tauto);
    destruct_addr;
    try rewrite getCs_cs in * by (rmForTauto; tauto).



  Lemma rmConj (P Q R: Prop): impl (P /\ Q -> R) (P -> Q -> R).
  Proof.
    unfold impl; tauto.
  Qed.

  Lemma rmDisj (P Q R: Prop): impl (P \/ Q -> R) ((P -> R) /\ (Q -> R)).
  Proof.
    unfold impl; tauto.
  Qed.

  Lemma dupConj (P Q R: Prop): impl (P -> (Q /\ R)) ((P -> Q) /\ (P -> R)).
  Proof.
    unfold impl; tauto.
  Qed.

  Lemma bool_true a: iff (a = true -> False) (a = false).
  Proof.
    destruct a; intuition discriminate.
  Qed.

  Lemma bool_false a: iff (a = false -> False) (a = true).
  Proof.
    destruct a; intuition discriminate.
  Qed.

  Hint Rewrite rmConj rmDisj dupConj bool_true bool_false: myLogic.

  
  

  
  Definition FinFlag := Fin.t.
  Ltac specialize_msgs :=
    repeat match goal with
             | H: (forall x: (forall i: Fin.t ?n, _ ?ls), _),
                  a: (forall i: Fin.t ?n, _ ?ls) |- _ =>
               pose proof (H a);
                 fold FinFlag in a;
                 repeat match goal with
                          | b: (forall i: Fin.t ?n, _ ?ls) |- _ =>
                            pose proof (H b);
                              fold FinFlag in b
                        end;
                 unfold FinFlag in *;
                 clear H
           end; unfold FinFlag in *.

  Ltac specialize_beg_mid_last :=
    repeat match goal with             
             | [H: (?l ++ [?v] = ?beg' ++ ?v1' :: ?mid' ++ ?v2' :: ?last')%list |- _] =>
               apply beg_mid_last_add_eq in H;
                 destruct H as [[? [? ?]] | [? [? ?]]]; subst
             | [H: forall beg mid last v1 v2,
                     (?l = beg ++ v1 :: mid ++ v2 :: last)%list -> _,
                  H': ?l = ?bg ++ ?val1 :: ?md ++ ?val2 :: ?lt |- _] =>
               specialize (@H bg md lt val1 val2 H')
             | [H: forall beg mid last v1 v2,
                     (?g :: ?l = beg ++ v1 :: mid ++ v2 :: last)%list -> _,
                  H': (?l = ?beg' ++ ?v1' :: ?mid' ++ ?v2' :: ?last')%list |- _ ] =>
               specialize (H (g :: beg') mid' last' v1' v2');
                 cbn in H;
                 specialize (H eq_refl)
             | [H: forall beg v,
                     (?g :: ?l = beg ++ (v :: nil))%list -> ?P |- _] =>
               apply list_revcons in H
           end.

  

  

  Ltac simpl_hyps :=
    repeat match goal with
             | H: exists x, _ |- _ => destruct H
             | H: ?P /\ ?Q |- _ => destruct H
             | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
             | H: ?P -> _, H': ?P |- _ =>
               match type of P with
                 | Prop => specialize (H H')
               end
             | H: ?a = ?b |- _ => rewrite H in *
           end.

  Ltac rmBadHyp2 :=
    repeat match goal with
             | H: ?v = ?v |- _ => clear H
             | H: In _ _ -> _ |- _ => clear H
             | H: forall (x: (forall i: Fin.t ?n, _ ?ls)), _ |- _ => 
               clear H
             | H: forall (x: (list (forall i: Fin.t ?n, _ ?ls))), _ |- _ => 
               clear H
           end.


  Ltac simplMapUpds tac :=
    esplit;
    unfold withIndex;
    match goal with
      | cond: (_ <= ?total)%nat |- M.find (elt := sigT ?t)
                                          (addIndexToStr _ ?c ?k) ?m = Some _ =>
        let mr := mapVR_Others t total m in
        rewrite <- (findMVR_find_var mr k eq_refl cond)
      | cond: (_ <= ?total)%nat |- M.find (elt := sigT ?t) ?k ?m = Some _ =>
        let mr := mapVR_Others t total m in
        rewrite <- (findMVR_find_string mr k eq_refl)
      | _ => idtac
    end; simpl; unfold VectorFacts.Vector_find; simpl;
    match goal with
      | |- context [eq_nat_dec ?x1 ?x2] =>
        destruct (eq_nat_dec x1 x2); (exfalso; tauto)
      | |- context [eq_nat_dec ?x1 ?x2] =>
        let isEq := fresh in
        destruct (eq_nat_dec x1 x2) as [isEq | isEq]; try (exfalso; congruence); [ clear isEq ]
      | _ => idtac
    end; (reflexivity || eassumption || tac).


  Ltac doAll :=
    autorewrite with invariant in *;
    unfold isCWait, isPWait in *;
    simpl in *;
    unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    rmBadHyp;
    try rewrite getCs_tag_match_getCs in * by assumption;
    destruct_addr;
    intros;
    rsLessTo_thms; simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    specialize_msgs;
    specialize_beg_mid_last;
    rewrite ?app_or, ?cons_or in *;
    autorewrite with myLogic in *;
    simpl_hyps;
    rmBadHyp2;
    try rewrite getCs_cs in * by tauto;
    
    try (intuition (discriminate || word_omega));
    try match goal with
          | |- context[if ?p then _ else _] =>
            let isEq := fresh in
            let nEq := fresh in
            destruct p as [isEq | nEq];
              [rewrite isEq in *|]; intuition (discriminate || word_omega)
        end;
    try (firstorder (discriminate || word_omega)).

  Ltac doMeta :=
    metaInit;
      try match goal with
            | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
          end; invariant_simpl;
      simplMapUpds doAll.

  Lemma nmemCache_invariants_hold_7 s a u cs:
    nmemCache_invariants s ->
    ld metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
  Qed.

  Lemma nmemCache_invariants_hold_8 s a u cs:
    nmemCache_invariants s ->
    st metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
  Qed.

  Lemma nmemCache_invariants_hold_10 s a u cs:
    nmemCache_invariants s ->
    pProcess metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
  Qed.

  Lemma nmemCache_invariants_hold_1 s a u cs:
    nmemCache_invariants s ->
    l1MissByState metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
  Qed.

  Lemma nmemCache_invariants_hold_2 s a u cs:
    nmemCache_invariants s ->
    l1MissByLine metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
  Qed.

  Lemma nmemCache_invariants_hold_3 s a u cs:
    nmemCache_invariants s ->
    l1Hit metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
  Qed.

  Lemma nmemCache_invariants_hold_9 s a u cs:
    nmemCache_invariants s ->
    drop metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
  Qed.

  Lemma nmemCache_invariants_hold_5 s a u cs:
    nmemCache_invariants s ->
    upgRq metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    doMeta.
    Show Ltac Profile.
  Qed.

  
  Show Ltac Profile.

  (*
  Lemma nmemCache_invariants_hold_4 s a u cs:
    nmemCache_invariants s ->
    writeback metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    Set Ltac Profiling.
    doMeta.
    Show Ltac Profile.
  Qed.


   *)

  Lemma nmemCache_invariants_hold_6 s a u cs:
    nmemCache_invariants s ->
    upgRs metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    Set Ltac Profiling.
    doMeta.
    Show Ltac Profile.
    simpl.
  Qed.

=



  
    intros HInd HInRule x xcond HS.
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule.
    apply invSome in HInRule; apply invRepRule in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ?.
    unfold getActionFromGen, getGenAction, strFromName in *;
      simpl in *; unfold VectorFacts.Vector_find in *; simpl in *;
      subst; unfold getActionFromSin, getSinAction in *; subst.
    SymEval; subst; simpl; unfold VectorFacts.Vector_find; simpl;
    match goal with
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat, H': (c <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl);
          specialize (HInd a _ _ H' eq_refl)
      | a: word (IdxBits + TagBits), H: (_ <=
                                         _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl)          
    end.
    unfold withIndex (*, withPrefix*) in *;
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest;
    repeat simplBool;
    elimDiffC c.
    try match goal with
            | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
          end; invariant_simpl.

   Set Ltac Profiling.
    simplMapUpds
      ltac:(autorewrite with invariant in *;
             unfold isCWait, isPWait in *;
             simpl in *;
             unfold Lib.VectorFacts.Vector_find in *; simpl in *;
             rmBadHyp;
            try rewrite getCs_tag_match_getCs in * by assumption;
            destruct_addr;
            intros;
            rsLessTo_thms; simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
            specialize_msgs;
            specialize_beg_mid_last;
            rewrite ?app_or, ?cons_or in *;
              autorewrite with myLogic in *;
              simpl_hyps;
            rmBadHyp2;
            try (intuition (discriminate || word_omega));
            match goal with
              | |- context[if ?p then _ else _] =>
                destruct p as [isEq | nEq];
              [rewrite isEq in *|]; intuition (discriminate || word_omega)
            end
           ).
    Show Ltac Profile.
  Qed.
    simpl.
    rewrite i27 in *.
    simpl.
    intuition (discriminate || word_omega).
    specialize_msgs.
    
    simplMapUpds idtac.
    simpl in *.

    
    metaInit.
    simpl in *.
    Set Ltac Profiling.
    metaInit;
    try match goal with
            | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
          end; invariant_simpl;
    simplMapUpds
      ltac:(autorewrite with invariant in *;
             unfold isCWait, isPWait in *;
             cbn in *;
             rmBadHyp;
            try rewrite getCs_tag_match_getCs in * by assumption;
            destruct_addr;
            intros;
            rsLessTo_thms).
    Show Ltac Profile.
    simpl.
            
            specialize_msgs;
            specialize_beg_mid_last;
            rewrite ?app_or, ?cons_or in *;
              autorewrite with myLogic in *;
              simpl_hyps;
            rmBadHyp2
           (* try (intuition (discriminate || word_omega)) *)
           ).
    Show Ltac Profile.

    Focus 24.
    
    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.

    admit.
    
    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.
  Qed.
  
    simpl.
    
    Reset Ltac Profile.
    Set Ltac Profiling.
    intuition (discriminate || word_omega).
    Show Ltac Profile.


    

    
    
    simpl.
    
    simpl.
    
    simpl.
    rewrite cons_or in H1.
    simpl.
    Focus 23.
    simpl.
      
    repeat match goal with
             | H: context[In _ (?x :: ?ls) -> ?P] |- _ =>
               setoid_rewrite (@rmDisj _ ls v) in H
           end.

    rewrite fromPToC_
    setoid_rewrite rmDisj in i8.
    simpl.
    Focus 4.
    simpl.
            specialize_msgs;
            specialize_beg_mid_last;
            mkStruct;
           ).
    Show Ltac Profile.
    Focus 3.
    rewrite ?app_nil_r in *.
    tauto.
    
    simpl.
    simpl.
    apply H4.
    tauto.
    simpl.
    simpl.
    Show Ltac Profile.
    Set Ltac Profile.
    rewrite getCs_tag_match_getCs in * by assumption.
    Show Ltac Profile.
    
    
    Lemma tst A: forall ls g (x: A), impl (g = x \/ In g ls) (In g (x :: ls)).
    Proof.
      unfold impl; simpl; intuition congruence.
    Qed.

    Hint Rewrite -> tst: murali.
    Set Ltac Profiling.
    autorewrite with murali in *.
    Show Ltac Profile.

    Lemma tst6 A: forall ls g (x: A) (B: Prop), impl (In g (x :: ls) -> B) ((g = x \/ In g ls) -> B).
    Proof.
      unfold impl; simpl; intros.
      firstorder (subst; idtac).
      intuition fail.
    Qed.

    Lemma tst7 A: forall ls g (x: A) (B: Prop), impl ((g = x \/ In g ls) -> B) (In g (x :: ls) -> B).
    Proof.
      unfold impl; simpl; intros.
      firstorder (subst; idtac).
      intuition fail.
    Qed.


    Hint Rewrite -> tst6 tst7: murali.

    Lemma tst8 A: forall ls g (x: A), impl (g = x \/ In g ls) (In g (x :: ls)).
    Proof.
      unfold impl; simpl; intros.
      firstorder (subst; idtac).
      intuition fail.
    Qed.
    
    Lemma test A: forall ls g (x: A) (X B: Prop), (X -> In g (x :: ls) -> B) -> X -> (g = x \/ In g ls) -> B.
    Proof.
      intros.
      rewrite <- tst8 in H.
      Hint Rewrite -> rmDisj: ov.
      Lemma test3: forall A B C: Prop, impl ((A \/ B) -> C) ((A -> C) /\ (B -> C)).
      Proof.
        unfold impl.
        tauto.
      Qed.
      rewrite -> test3 in H.
      
      autorewrite with ov in H.
      assert ((X -> g = x -> B) /\ In g ls -> B).
      Unset Ltac Debug.
      autorewrite with myFirstorder in H.
    autorewrite with muli in H5.
    simpl.
    
    rewrite tst5 in H5.
    simpl.
    rewrite -> tst in *.
    destruct_in;
            mkStruct;
            simpl_hyps;
            rmBadHyp2).
    Show Ltac Profile.
    Focus 2.
    destruct_in.

    Focus 4.
            rewrite_getCs;
            repeat split;
            try rewrite app_nil_l in *;
              try rewrite app_nil_r in *;
              try (assumption || word_omega)
           ).
    Show Ltac Profile.
    simpl.
    destruct_in.
    Show Ltac Profile.
    
    simpl.
    word_omega.
    simpl.

    Set Ltac Profiling.
    word_omega.

    simpl.
    simpl.
    Set Ltac Profiling.
    word_omega.
    Show Ltac Profile.
    simpl.
    word_omega.
    simpl.
    
[].

    simpl.

    rmBadHyp2.
    match type of i7 with
      | forall x: ?T, _ =>
        match type of T with
          | Prop => fail
          | _ => clear i7
        end
    end.
    Reset Ltac Profile.
    Set Ltac Profiling.
    match goal with
    end.
    Show Ltac Profile.
    simpl.

                 | forall (i: BoundedIndexFull ?), _ => pose H as murali
               end
           end.
    Show Ltac Profile.

                 | _ => fail 10
               end
           end.
    Show Ltac Profile.
    simpl.
                   match type of T with
                     | Prop => idtac
                     | _ =>
                       clear H
                   end
               end
           end.
    simpl.


    
            try rewrite getCs_tag_match_getCs in * by assumption.
    match goal with
      | |- context[if ?p then _ else _] => destruct p; [subst |]; try rewrite getCs_tag_match_cs in * by assumption; try word_omega
    end.
            
           ).









  Lemma nmemCache_invariants_hold_9 s a u cs:
    nmemCache_invariants s ->
    pProcess metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    Set Ltac Profiling.
    metaInit;
    try match goal with
            | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
          end; invariant_simpl;
    simplMapUpds
      ltac:(autorewrite with invariant in *;
            intros;
            unfold isCWait, isPWait, GetAttrType in *;
              simpl in *;
            unfold_index;
            rmBaHyp;
            specialize_msgs;
            destruct_in;
            mkStruct;
            simpl_hyps;
            rmBadHyp2;
            try rewrite getCs_tag_match_getCs in * by assumption.
    match goal with
      | |- context[if ?p then _ else _] => destruct p; [subst |]; try rewrite getCs_tag_match_cs in * by assumption; try word_omega
    end.
            
           ).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    specialize_msgs;
      destruct_in;
      mkStruct;
      simpl_hyps.
    Show Ltac Profile.
    rmBadHyp2.








  Lemma filtRsFromC_then_filtRsToP_same: forall c a l2,
                                           filtRsFromC c a l2 = filtRsToP a (filtRsFromC c a l2).
  Proof.
    induction l2; simpl; auto; intros.
    repeat match goal with
             | |- context[weq ?c ?d] => destruct (weq c d); simpl; subst; intuition auto
           end.
    f_equal; auto.
  Qed.

  Lemma rsFromCToP_left_assoc c a l1 l2 l3:
    (rsFromCToP c a (l1 ++ l2) l3 = rsFromCToP c a l1 (filtRsFromC c a l2 ++ l3))%list.
  Proof.
    induction l1; unfold rsFromCToP; simpl; auto; intros.
    - rewrite filtRsToP_commute_app; f_equal.
      rewrite <- filtRsFromC_then_filtRsToP_same.
      reflexivity.
    - repeat match goal with
               | |- context[weq ?c ?d] => destruct (weq c d); simpl; subst; intuition auto
             end.
      f_equal; auto.
  Qed.


  Lemma rqFromCToP_xfer:
    forall x a t rqFromCList rqToPList,
      rqFromCToP $ x a rqFromCList (t :: rqToPList) =
      rqFromCToP $ x a
                 (rqFromCList
                    ++
                    [mkStruct
                       (ilist.icons
                          ("child" :: Bit LgNumChildren)%struct 
                          $ (x)
                          (ilist.icons
                             ("rq"
                                :: STRUCT  {"addr" :: Bit (IdxBits + TagBits);
                                            "from" :: Bit 2; "to" :: Bit 2; 
                                            "id" :: Id})%struct t
                             (ilist.inil
                                (fun H2 : Attribute Kind => type (attrType H2)))))])
                 rqToPList.
  Proof.
    unfold rqFromCToP; intros; simpl; auto;
    (repeat match goal with
              | |- context [weq ?p ?q] => destruct (weq p q)
            end);
    mkStruct; subst;
    rewrite ?app_nil_l, ?app_nil_r; auto; try solve [intuition auto].
    - rewrite filtRqFromC_commute_app;
      simpl;
      mkStruct;
      destruct (weq $ x $ x); [ | intuition auto];
      match goal with
        | |- context [weq ?p ?q] => destruct (weq p q)
      end; [ | intuition auto];
      rewrite <- app_assoc; simpl;
      reflexivity.
    - rewrite filtRqFromC_commute_app;
      simpl;
      mkStruct;
      destruct (weq $ x $ x); [ | intuition auto];
      match goal with
        | |- context [weq ?p ?q] => destruct (weq p q)
      end; [ intuition auto| ].
      rewrite ?app_nil_l, ?app_nil_r; auto.
  Qed.

  Lemma rqFromCToP_xfer_diffAddr:
    forall c x a t rqFromCList rqToPList,
      c <> x ->
      (c <= wordToNat (wones LgNumChildren))%nat ->
      (x <= wordToNat (wones LgNumChildren))%nat ->
      rqFromCToP $ c a rqFromCList rqToPList =
      rqFromCToP $ c a
                 (rqFromCList
                    ++
                    [mkStruct
                       (ilist.icons ("child" :: Bit LgNumChildren)%struct 
                                    $ (x)
                                    (ilist.icons
                                       ("rq"
                                          :: STRUCT  {"addr" :: Bit (IdxBits + TagBits);
                                                      "from" :: Bit 2; "to" :: Bit 2; 
                                                      "id" :: Id})%struct t
                                       (ilist.inil
                                          (fun H0 : Attribute Kind =>
                                             type (attrType H0)))))])
                 rqToPList.
  Proof.
    unfold rqFromCToP; intros; simpl; auto;
    (repeat match goal with
              | |- context [weq ?p ?q] => destruct (weq p q)
            end);
    mkStruct; subst;
    rewrite ?app_nil_l, ?app_nil_r; auto; try solve [intuition auto].
    rewrite filtRqFromC_commute_app; simpl in *; mkStruct.
    destruct (weq $ c $ x).
    exfalso.
    assert (c = x).
    clear - H0 H1 e.
    assert (pow2 LgNumChildren > 0)%nat.
    clear.
    induction LgNumChildren; simpl; auto.
    omega.
    rewrite wones_pow2_minus_one in H0, H1.
    apply natToWord_inj with (sz := LgNumChildren); auto; try omega.
    intuition auto.
    rewrite ?app_nil_r; auto.
  Qed.

  Lemma rsFromCToP_xfer:
    forall x a t rsFromCList rsToPList,
      rsFromCToP $ x a rsFromCList (t :: rsToPList) =
      rsFromCToP $ x a
                 (rsFromCList
                    ++
                    [mkStruct
                       (ilist.icons
                          ("child" :: Bit LgNumChildren)%struct 
                          $ (x)
                          (ilist.icons
                             ("rs"
                                :: STRUCT
                                {"addr" :: Bit (IdxBits + TagBits);
                                 "to" :: Bit 2;
                                 "line" :: Vector (Bit (LgDataBytes*8)) LgNumDatas;
                                 "isVol" :: Bool})%struct t
                             (ilist.inil
                                (fun H2 : Attribute Kind => type (attrType H2)))))])
                 rsToPList.
  Proof.
    unfold rsFromCToP; intros; simpl; auto;
    (repeat match goal with
              | |- context [weq ?p ?q] => destruct (weq p q)
            end);
    mkStruct; subst;
    rewrite ?app_nil_l, ?app_nil_r; auto; try solve [intuition auto].
    - rewrite filtRsFromC_commute_app;
      simpl;
      mkStruct;
      destruct (weq $ x $ x); [ | intuition auto];
      match goal with
        | |- context [weq ?p ?q] => destruct (weq p q)
      end; [ | intuition auto];
      rewrite <- app_assoc; simpl;
      reflexivity.
    - rewrite filtRsFromC_commute_app;
      simpl;
      mkStruct;
      destruct (weq $ x $ x); [ | intuition auto];
      match goal with
        | |- context [weq ?p ?q] => destruct (weq p q)
      end; [ intuition auto| ].
      rewrite ?app_nil_l, ?app_nil_r; auto.
  Qed.

  Lemma rsFromCToP_xfer_diffAddr:
    forall c x a t rsFromCList rsToPList,
      c <> x ->
      (c <= wordToNat (wones LgNumChildren))%nat ->
      (x <= wordToNat (wones LgNumChildren))%nat ->
      rsFromCToP $ c a rsFromCList rsToPList =
      rsFromCToP $ c a
                 (rsFromCList
                    ++
                    [mkStruct
                       (ilist.icons ("child" :: Bit LgNumChildren)%struct 
                                    $ (x)
                                    (ilist.icons
                                       ("rs"
                                          :: STRUCT  {"addr" :: Bit (IdxBits + TagBits);
                                                      "to" :: Bit 2; 
                                                      "line" ::
                                                             Vector (Bit (LgDataBytes*8))
                                                             LgNumDatas;
                                                      "isVol" :: Bool})%struct t
                                       (ilist.inil
                                          (fun H0 : Attribute Kind =>
                                             type (attrType H0)))))])
                 rsToPList.
  Proof.
    unfold rsFromCToP; intros; simpl; auto;
    (repeat match goal with
              | |- context [weq ?p ?q] => destruct (weq p q)
            end);
    mkStruct; subst;
    rewrite ?app_nil_l, ?app_nil_r; auto; try solve [intuition auto].
    rewrite filtRsFromC_commute_app; simpl in *; mkStruct.
    destruct (weq $ c $ x).
    exfalso.
    assert (c = x).
    clear - H0 H1 e.
    assert (pow2 LgNumChildren > 0)%nat.
    clear.
    induction LgNumChildren; simpl; auto.
    omega.
    rewrite wones_pow2_minus_one in H0, H1.
    apply natToWord_inj with (sz := LgNumChildren); auto; try omega.
    intuition auto.
    rewrite ?app_nil_r; auto.
  Qed.
  
  Lemma fromPToC_xfer:    
    forall x a (t: type (ToC LgDataBytes LgNumDatas LgNumChildren _ Id))
           fromPList toCList,
      $ x = t ``"child" ->
      fromPToC $ x a fromPList (t :: toCList) =
      fromPToC $ x a
        (fromPList ++
         [t
            (addFirstBoundedIndex
               (mapAttr type ("child" :: Bit LgNumChildren)%struct)
               ``"msg" )]) toCList.
  Proof.
    unfold fromPToC; intros; simpl; auto;
    (repeat match goal with
              | |- context [weq ?p ?q] => destruct (weq p q)
            end);
    mkStruct; subst;
    rewrite ?app_nil_l, ?app_nil_r; auto; try solve [intuition auto]; try mkStruct; simpl.
    - rewrite filtFromP_commute_app; simpl; mkStruct;
      match goal with
        | |- context [weq ?p ?q] =>
          destruct (weq p q); [ | intuition auto]
      end.
      rewrite <- app_assoc; simpl; reflexivity.
    - rewrite filtFromP_commute_app; simpl; mkStruct;
      match goal with
        | |- context [weq ?p ?q] =>
          destruct (weq p q); intuition auto
      end.
      rewrite ?app_nil_r; auto.
  Qed.

  Lemma fromPToC_xfer_diffAddr:
    forall c x a (t: type (ToC LgDataBytes LgNumDatas LgNumChildren _ Id))
           fromPList toCList,
      c <> x ->
      $ x = t ``"child" ->
      (c <= wordToNat (wones LgNumChildren))%nat ->
      (x <= wordToNat (wones LgNumChildren))%nat ->
      fromPToC $ c a fromPList toCList =
      fromPToC $ c a
               fromPList
               (t :: toCList).
  Proof.
    unfold fromPToC; intros; simpl; auto;
    (repeat match goal with
              | |- context [weq ?p ?q] => destruct (weq p q)
            end);
    mkStruct; subst;
    rewrite ?app_nil_l, ?app_nil_r; auto; try solve [intuition auto].
    assert (c = x).
    simpl in *.
    clear - H0 H1 H2 e.
    rewrite <- H0 in e.
    assert (pow2 LgNumChildren > 0)%nat.
    clear.
    induction LgNumChildren; simpl; auto.
    omega.
    rewrite wones_pow2_minus_one in H1, H2.
    apply natToWord_inj with (sz := LgNumChildren); auto; try omega.
    intuition auto.
  Qed.

  Lemma rsFromCToP_sameAddr_revcons:
    forall x (a: word (IdxBits + TagBits))
           (rsFromCList:
              list
                (type (RsFromC LgDataBytes LgNumDatas LgNumChildren _)))
           (rsToPList: list (type (RsToP LgDataBytes LgNumDatas _))) v,
      a = ((mkStruct v): type (RsToP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits))))
            ``"addr" ->
      rsFromCToP x a rsFromCList (rsToPList ++ [mkStruct v]) =
      (rsFromCToP x a rsFromCList rsToPList ++ [mkStruct v])%list.
  Proof.
    unfold IndexBound_head; simpl; intros.
    unfold rsFromCToP.
    rewrite filtRsToP_commute_app.
    rewrite app_assoc.
    f_equal.
    rewrite H.
    unfold filtRsToP.
    simpl.
    match goal with
      | |- (if ?p then _ else _) = _ => destruct p; intuition auto
    end.
  Qed.

  Lemma rsFromCToP_diffAddr_revcons:
    forall x a
           (rsFromCList:
              list
                (type (RsFromC LgDataBytes LgNumDatas LgNumChildren (Bit (IdxBits + TagBits)))))
           (rsToPList: list (type (RsToP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits))))) v,
      a <> ((mkStruct v): type (RsToP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits))))
             ``"addr" ->
      rsFromCToP x a rsFromCList (rsToPList ++ [mkStruct v]) =
      rsFromCToP x a rsFromCList rsToPList.
  Proof.
    unfold IndexBound_head; simpl; intros.
    unfold rsFromCToP.
    rewrite filtRsToP_commute_app.
    rewrite app_assoc.
    rewrite <- app_nil_r with (l := (filtRsFromC x a rsFromCList ++ filtRsToP a rsToPList)%list) at 2.
    f_equal.
    unfold filtRsToP.
    simpl.
    match goal with
      | |- (if ?p then _ else _) = _ => destruct p; intuition auto
    end.
  Qed.

  Lemma cs_sameAddr_upd: forall cs tag a,
                           tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a ->
                           forall upd,
                             getCs
                               (fun a' => if weq a' (split1 IdxBits TagBits a)
                                          then upd
                                          else cs a') tag a = upd.
  Proof.
    intros.
    unfold getCs, getIdxS, getTagS; subst.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; intuition auto
           end.
  Qed.

  Lemma cs_sameAddr_no_upd: forall cs tag a,
                              tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a ->
                              getCs cs tag a = cs (split1 IdxBits TagBits a).
  Proof.
    intros.
    unfold getCs, getIdxS, getTagS; subst.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; intuition auto
           end.
  Qed.

  Lemma cs_Inv_matches_getCs: forall cs tag a,
                                cs (split1 IdxBits TagBits a) = WO~0~0 ->
                                getCs cs tag a = cs (split1 IdxBits TagBits a).
  Proof.
    unfold getCs; intros; unfold getTagS, getIdxS.
    destruct (weq (tag (split1 IdxBits TagBits a)) (split2 IdxBits TagBits a));
      intuition auto.
  Qed.

  Lemma cs_diffAddr_upd: forall cs tag a0 a upd,
                           a0 <> a ->
                           tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a ->
                           getCs
                             (fun a' => if weq a' (split1 IdxBits TagBits a)
                                        then upd
                                        else cs a') tag a0 = getCs cs tag a0.
  Proof.
    intros.
    unfold getCs, getIdxS, getTagS.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; [| auto]
           end.
    rewrite <- e0 in H0.
    rewrite e in H0.
    rewrite <- (Word.combine_split IdxBits TagBits a0) in H.
    rewrite <- (Word.combine_split IdxBits TagBits a) in H.
    rewrite H0, e0 in H.
    intuition auto.
  Qed.

  Lemma isPWait_addRq a cRqValid
        (rqFromCList: list (type (RqFromC LgNumChildren (Bit (IdxBits + TagBits)) Id)))
        dirw (cword: word LgNumChildren) rq:
    isPWait a cRqValid rqFromCList dirw cword ->
    isPWait a cRqValid (rqFromCList ++ [rq]) dirw cword.
  Proof.
    unfold isPWait; intros.
    unfold IndexBound_head, IndexBound_tail in *; simpl in *.
    intuition auto.
    case_eq (hd_error rqFromCList); intros sth; try rewrite sth in *; intuition auto.
    rewrite hd_error_revcons_same with (ls := rqFromCList) (a := sth); auto.
    rewrite H1 in H2.
    assumption.
  Qed.

  Lemma rqFromCToP_revcons a c:
    forall l1 l2
           (v: type (RqToP (Bit (IdxBits + TagBits)) Id)),
      rqFromCToP c a l1 (l2 ++ [v]) =
      (rqFromCToP c a l1 l2 ++
                  if weq a (v ``"addr") then [v] else nil)%list.
  Proof.
    unfold rqFromCToP.
    intros.
    rewrite filtRqToP_commute_app.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma fromPToC_cons a c:
    forall l1 l2 g,
      fromPToC c a (g :: l1) l2 = if weq a (g ``"addr") then
                                    g :: fromPToC c a l1 l2
                                  else fromPToC c a l1 l2.
  Proof.
    simpl.
    intros.
    unfold fromPToC.
    simpl.
    match goal with
      | |- _ = if ?p then _ else _ => destruct p; simpl; reflexivity
    end.
  Qed.



(*
  Lemma rsFromCToP_right_diffAddr_cons c a l1
        (t: type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))):
    forall l3,
      a <> t ``"addr" ->
      rsFromCToP c a l1 l3 = rsFromCToP c a l1 (t :: l3).
  Proof.
    intros.
    induction l1; simpl; unfold rsFromCToP; auto; intros.
    - f_equal; simpl.
      match goal with
        | |- context[weq ?c ?d] => destruct (weq c d); simpl; subst; intuition auto
      end.
    - simpl.
      repeat match goal with
               | |- context[weq ?c ?d] => destruct (weq c d); simpl; subst; intuition auto
             end.
  Qed.

  Lemma isCWait_dec: forall a procRqValid procRq csw, isCWait a procRqValid procRq csw \/
                                                ~ isCWait a procRqValid procRq csw.
  Proof.
    intros.
    unfold isCWait in *; simpl in *.
    destruct procRqValid, csw; try intuition discriminate.
    match goal with
      | |- context[?p = ?q] => match type of p with
                                 | word _ => destruct (weq p q); intuition auto
                               end
    end.
  Qed.

  Lemma isPWait_dec: forall a cRqValid rqFromCList dirw cword,
                       isPWait a cRqValid rqFromCList dirw cword \/
                       ~ isPWait a cRqValid rqFromCList dirw cword.
  Proof.
    intros.
    unfold isPWait in *; simpl in *.
    destruct cRqValid, dirw; try intuition discriminate.
    destruct (hd_error rqFromCList); intuition auto.
    match goal with
      | |- (_ /\ _ /\ ?p = ?q \/ _) => destruct (weq p q); intuition auto
    end.
  Qed.
  
  Hint Unfold nmemCacheInl: ModuleInl.

  Lemma rsLessTo_less_app:
    forall ls
           (v1: type (RsToP LgDataBytes LgNumDatas (Bit (IdxBits + TagBits)))),
      rsLessTo (ls ++ [v1]) ->
      forall (v2: type (RsToP _ _ _)),
        v1 {| bindex := "to";
              indexb :=
                {| boundi := eq_refl:
                               nth_error (map (@attrName _)
                                              (mapAttr type ("addr" :: Bit (IdxBits + TagBits))%struct ::
                                                       mapAttr type ("to" :: Msi)%struct ::
                                                       mapAttr type ("line" :: Line LgDataBytes LgNumDatas)%struct ::
                                                       mapAttr type ("isVol" :: Bool)%struct :: nil))
                                         1 = Some "to" |} |} >
        v2 {| bindex := "to";
              indexb :=
                {| boundi := eq_refl:
                               nth_error (map (@attrName _)
                                              (mapAttr type ("addr" :: Bit (IdxBits + TagBits))%struct ::
                                                       mapAttr type ("to" :: Msi)%struct ::
                                                       mapAttr type ("line" :: Line LgDataBytes LgNumDatas)%struct ::
                                                       mapAttr type ("isVol" :: Bool)%struct :: nil))
                                         1 = Some "to" |} |} ->
        rsLessTo ((ls ++ [v1]) ++ [v2]).
  Proof.
    simpl.
    induction ls; [simpl; auto| intros; simpl in *].
    case_eq (ls ++ [v1])%list;
      case_eq ((ls ++ [v1]) ++ [v2])%list; intros;
      repeat match goal with
               | H: (_ ++ [_])%list = nil |- _ =>
                 apply eq_sym in H; apply app_cons_not_nil in H; exfalso; auto
             end; simpl in *.
    assert (sth: g = g0).
    { destruct ls; simpl in *.
      - inv H1;
        inv H2.
        reflexivity.
      - inv H1; inv H2.
        reflexivity.
    }

    rewrite <- sth in *; clear sth g0.
    rewrite H2 in *; simpl in *.
    inv H1.

    destruct H as [sth rsLess].
    constructor; [auto|].

    assert (rsLessTo (ls ++ [v1])).
    { rewrite H2.
      simpl.
      assumption.
    }
    apply IHls with (v2 := v2) in H.
    rewrite H2 in H.
    simpl in H.
    assumption.
    auto.
  Qed.
  
  Lemma rsLessTo_in_I_last ls:
    forall rs,
      In rs ls ->
      rsLessTo ls ->
      rs {| bindex := "to";
            indexb :=
              {| boundi := eq_refl:
                             nth_error (map (@attrName _)
                                            (mapAttr type ("addr" :: Bit (IdxBits + TagBits))%struct ::
                                                     mapAttr type ("to" :: Msi)%struct ::
                                                     mapAttr type ("line" :: Line LgDataBytes LgNumDatas)%struct ::
                                                     mapAttr type ("isVol" :: Bool)%struct :: nil))
                                       1 = Some "to" |} 
         |}  = WO~0~0 ->
      exists sth, ls = (sth ++ [rs])%list.
  Proof.
    unfold IndexBound_head, IndexBound_tail; simpl.
    induction ls; simpl; intros; [exfalso; auto|].
    destruct H, ls; subst; dest.
    - exists nil; reflexivity.
    - unfold IndexBound_tail in *; simpl in *.
      rewrite H1 in H; word_omega.
    - simpl in *; intuition auto.
    - specialize (IHls rs H H2 H1).
      dest.
      exists (a :: x).
      simpl.
      f_equal; auto.
  Qed.

  Lemma rsFromCToP_sameAddr_sameChild_cons_prop a c P:
    forall rsFromCList g rsToPList,
      (forall rs, In rs (rsFromCToP ($ c) a (g :: rsFromCList) rsToPList) ->
                  P rs) ->
      a = g ``"rs" ``"addr" ->
      $ c = g ``"child" ->
      P (g ``"rs").
  Proof.
    simpl.
    unfold IndexBound_head, IndexBound_tail; simpl.
    unfold rsFromCToP.
    simpl.
    intros.
    repeat match type of X with
             | context [weq ?p ?q] => destruct (weq p q); [| intuition auto]
           end.
    match goal with
      | |- P ?a => specialize (X a)
    end.
    unfold IndexBound_head, IndexBound_tail in *; simpl in *.
    apply X; auto.
  Qed.

  Lemma rsFromCToP_sameAddr_sameChild_cons a c:
    forall rsFromCList (g: type (RsFromC LgDataBytes LgNumDatas LgNumChildren
                                         (Bit (IdxBits + TagBits))))  rsToPList,
      a = g ``"rs" ``"addr" ->
      $ c = g ``"child" ->
      rsFromCToP ($ c) a (g :: rsFromCList) rsToPList =
      g ``"rs" :: rsFromCToP ($ c) a rsFromCList rsToPList.
  Proof.
    simpl.
    unfold IndexBound_head, IndexBound_tail; simpl.
    unfold rsFromCToP.
    simpl.
    intros.
    repeat match goal with
             | |- context[if ?p then _ else _] => destruct p; [| intuition auto]
           end.
    unfold IndexBound_tail; auto.
  Qed.

  Lemma rsFromCToP_diffAddr_cons
        c a rsFromCList rsToPList (g: type (RsFromC LgDataBytes LgNumDatas
                                                    LgNumChildren (Bit (IdxBits + TagBits)))):
    a <> g ``"rs" ``"addr" ->
    rsFromCToP c a rsFromCList rsToPList = rsFromCToP c a (g :: rsFromCList) rsToPList.
  Proof.
    simpl in *; intros.
    unfold rsFromCToP; simpl.
    unfold IndexBound_head, IndexBound_tail in *; simpl in *.
    repeat match goal with
             | |- context[if ?p then _ else _] =>
               destruct p; intuition auto
           end.
  Qed.
  
  Lemma rsFromCToP_diffChild_cons
        c a rsFromCList rsToPList (g: type (RsFromC LgDataBytes LgNumDatas
                                                    LgNumChildren (Bit (IdxBits + TagBits)))):
    c <> g ``"child" ->
    rsFromCToP c a rsFromCList rsToPList = rsFromCToP c a (g :: rsFromCList) rsToPList.
  Proof.
    simpl in *; intros.
    unfold rsFromCToP; simpl.
    unfold IndexBound_head, IndexBound_tail in *; simpl in *.
    repeat match goal with
             | |- context[if ?p then _ else _] =>
               destruct p; intuition auto
           end.
  Qed.

  Lemma rsLessTo_cons_in ls:
    forall g rs,
      In rs ls ->
      rsLessTo (g :: ls) ->
      rs ``"to" < g ``"to".
  Proof.
    unfold IndexBound_head, IndexBound_tail; simpl.
    induction ls; intros; simpl in *; subst; intuition auto.
    rewrite H0 in *; auto.
    apply IHls with (rs := rs) in H2; auto.
    unfold IndexBound_head, IndexBound_tail in *; simpl in *.
    word_omega.
  Qed.

  Lemma rsLessTo_cons_rsLessTo ls:
    forall g,
      rsLessTo (g :: ls) -> rsLessTo ls.
  Proof.
    intros.
    simpl in H.
    destruct ls; dest; auto.
  Qed.

  Lemma fromPToC_xfer_diffAddr_packaged:
    forall c a (t: type (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))
           fromPList toCList,
      (exists x, c <> x
                 /\ ($ x = t ``"child"
                     /\ (x <= wordToNat (wones LgNumChildren))%nat)) ->
      (c <= wordToNat (wones LgNumChildren))%nat ->
      fromPToC $ c a fromPList toCList =
      fromPToC $ c a
               fromPList
               (t :: toCList).
  Proof.
    destruct 1; intuition idtac.
    eauto using fromPToC_xfer_diffAddr.
  Qed.
*)




  Ltac addr_eq := 
    try rewrite cs_sameAddr_upd in *;
    try rewrite rsFromCToP_sameAddr_revcons in *; auto;
    subst; try rewrite cs_sameAddr_no_upd in * by auto.
  
  Ltac addr_neq :=
    try rewrite cs_diffAddr_upd in *;
    try rewrite rsFromCToP_diffAddr_revcons in *; auto.

  Ltac destruct_addr :=
    repeat match goal with
             | H: context [@weq (IdxBits + TagBits) ?a ?b] |- _ =>
               destruct (@weq (IdxBits + TagBits) a b); [addr_eq | addr_neq]
             | |- context [@weq (IdxBits + TagBits) ?a ?b] =>
               destruct (@weq (IdxBits + TagBits) a b); [addr_eq | addr_neq]
           end.
  
  Lemma nmemCache_invariants_hold_9 s a u cs:
    nmemCache_invariants s ->
    "pProcess" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    Set Ltac Profiling.
    metaInit;
    try match goal with
            | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
          end; invariant_simpl;
    simplMapUpds
      ltac:(autorewrite with invariant in *;
            intros;
            unfold isCWait, isPWait, GetAttrType in *;
              simpl in *;
            unfold_index;
            rmBadHyp).
    Show Ltac Profile.

    Reset Ltac Profile.
    Set Ltac Profiling.
    specialize_msgs;
      destruct_in;
      mkStruct;
      simpl_hyps.
    Show Ltac Profile.
    rmBadHyp2.
    dest.
    
    rewrite getCs_tag_match_getCs in * by assumption.
    match goal with
      | |- context[if ?p then _ else _] => destruct p; [subst |]; try rewrite getCs_tag_match_cs in * by assumption; try word_omega
    end.
    destruct (weq a0 
    rewrite getCs_tag_match_cs in * by assumption.
      rewrite H, e0 in n.
      exfalso; try congruence.
      

  Lemma cs_sameAddr_upd: forall cs tag a,
                           tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a ->
                           forall upd,
                             getCs
                               (fun a' => if weq a' (split1 IdxBits TagBits a)
                                          then upd
                                          else cs a') tag a = upd.
  Proof.
    intros.
    unfold getCs, getIdxS, getTagS; subst.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; intuition auto
           end.
  Qed.

  Lemma cs_diffAddr_upd: forall cs tag a0 a upd,
                           a0 <> a ->
                           tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a ->
                           getCs
                             (fun a' => if weq a' (split1 IdxBits TagBits a)
                                        then upd
                                        else cs a') tag a0 = getCs cs tag a0.
  Proof.
    intros.
    unfold getCs, getIdxS, getTagS.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; [| auto]
           end.
    rewrite <- e0 in H0.
    rewrite e in H0.
    rewrite <- (Word.combine_split IdxBits TagBits a0) in H.
    rewrite <- (Word.combine_split IdxBits TagBits a) in H.
    rewrite H0, e0 in H.
    intuition auto.
  Qed.



    Lemma getCs_val a a' cs tag upd:
      getCs (fun w => if weq w (split1 IdxBits TagBits a')
                      then upd else cs w) tag a =
      if weq a a'
      then upd
      else getCs cs tag a.
    Proof.
      unfold getCs, getTagS, getIdxS.
      repeat match goal with
               | |- context[if ?p then _ else _] => destruct p; auto
             end.
      
    simpl.
    simpl.
      simpl_
    simpl.
            destruct_addr;
            specialize_msgs;
            destruct_in;
            mkStruct;
            simpl_hyps;
            rmBadHyp2).
    Show Ltac Profile.

    simpl.
    word_omega.
            rewrite_getCs).
    Show Ltac Profile.
    unfold spl1, spl2, cmb in *.
    word_omega.


    simpl.
    Focus 3.
    mkStruct.
    simpl.
    Focus 5.
    simpl.

(*
Take care of the following:
0. Perform rewrites of equalities
1. beg ++ mid ++ last stuff
2. repeat split
3. introducing all the theorems as hypotheses before destruct_in
4. mkStruct should happen after specialize_msgs
5. rewrite_getCs (not sure when this happens)
6. solve by word_omega or discriminate - use with firstorder, I think (because intuition wont deal with exists)
7. destruct leftovers
*)


(*
  Hint Resolve isPWait_addRq isPWait_addRq_contra hd_error_revcons_same.
  Hint Rewrite <- rqFromCToP_xfer rqFromCToP_xfer_diffAddr using congruence : invariant.
  Hint Rewrite <- rsFromCToP_xfer rsFromCToP_xfer_diffAddr using congruence : invariant.

  Hint Rewrite <- fromPToC_xfer fromPToC_xfer_diffAddr_packaged using
       (tauto || (eexists; split; [ | split; eassumption ]; congruence)) : invariant.

  Hint Rewrite rqFromCToP_revcons : invariant.
  Hint Resolve in_app_or in_or_app in_single.
  Hint Resolve f_equal app_single_r in_pre_suf in_single in_app_or app_cons_not_nil rsLessTo_less_app rsLessTo_in_I_last.

*)




            intuition (discriminate || word_omega || idtac)
           ).
    Show Ltac Profile.
    Focus 5.
    Reset Ltac Profile.
    Set Ltac Profiling.
    specialize_msgs.
    Show Ltac Profile.
    
    simpl.
            solve_simpl;
            intros).
    Show Ltac Profile.
            specialize_msgs).
    Show Ltac Profile.



  Ltac solve_simpl := try (discriminate || tauto || word_omega).



(*
  Ltac specialize_msgs' :=
    repeat
      match goal with
        | [H: (forall x:?T, _), a:?T, b: ?T, c: ?T, d: ?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); pose proof (H b); pose proof (H c); pose proof (H d); clear H
          end
        | [H: (forall x:?T, _), a:?T, b: ?T, c: ?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); pose proof (H b); pose proof (H c); clear H
          end
        | [H: (forall x:?T, _), a:?T, b: ?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); pose proof (H b); clear H
          end
        | [H: (forall x:?T, _), a:?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); clear H
          end
      end.

  Ltac apply_in_app_or_goal H :=
    intros; eapply H; eauto; apply in_or_app; eauto.

  Ltac apply_in_inv H :=
    intros; eapply H; eauto; simpl; eauto.

  Ltac specialize_in :=
    repeat
      match goal with
        | [H: In ?x _ -> _, H': In ?x _ |- _] =>
          specialize (H H')
        | [H: ?x = ?y -> _, H': ?x = ?y |- _] =>
          specialize (H H')
        | [H: ?x = ?y -> _, H': ?y = ?x |- _] =>
          specialize (H (eq_sym H'))
        | [H: In ?x (?l1 ++ ?l2)%list -> ?P |- _] =>
          assert (In x l1 -> P) by (apply_in_app_or_goal H);
            assert (In x l2 -> P) by (apply_in_app_or_goal H);
            clear H
        | [H: In ?x (?v :: ?l)%list -> ?P |- _] =>
          assert (x = v -> P) by (apply_in_inv H);
            assert (In x l -> P) by (apply_in_inv H);
            clear H
        | [H: forall beg mid last v1 v2,
                (?l = beg ++ v1 :: mid ++ v2 :: last)%list -> _,
             H': (?l ++ [?v] = ?beg' ++ ?v1' :: ?mid' ++ ?v2' :: ?last')%list |- _ ] =>
          apply beg_mid_last_add_eq in H';
            let lastNil := fresh in
            let valV := fresh in
            let valLs := fresh in
            let newLast := fresh "newLast" in
            let lastEq := fresh in
            let lsEq := fresh in
            destruct H' as [[lastNil [valV valLs]] | [newLast [lastEq lsEq]]]; subst;
            [|apply H with (beg := beg') (mid := mid') (last := newLast) in lsEq]
        | [H: forall beg mid last v1 v2,
                (?g :: ?l = beg ++ v1 :: mid ++ v2 :: last)%list -> _,
             H': (?l = ?beg' ++ ?v1' :: ?mid' ++ ?v2' :: ?last')%list |- _ ] =>
          specialize (H (g :: beg') mid' last' v1' v2');
            simpl in H;
            specialize (H eq_refl)
      end.

    Ltac solve_complex := 
    dest; repeat split; specialize_msgs; specialize_in; dest; solve_simpl.
*)






            find_simpl).

    match goal with
      | H: context [match @find ?T ?a ?b with _ => _ end] |- _ =>
        let x := fresh in
        let H' := fresh in
        case_eq (@find T a b);
          idtac end.
    intros y H'; pose proof (find_some _ _ H').
          [intros x H'; pose proof (find_some _ _ H') |
           intros H';
             ((pose proof (find_none_revcons _ _ H')) || pose proof (find_none _ _ H')) ];
          try rewrite H' in H; simpl in H
    end.
                                          progress find_simpl.
 ;
            destruct_in;
            mkStruct;
            solve_complex;
            rewrite_getCs
           ).
    Show Ltac Profile.
    simpl.

  Ltac specialize_msgs :=
    repeat
      match goal with
        | [H: (forall x:?T, _), a:?T, b: ?T, c: ?T, d: ?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); pose proof (H b); pose proof (H c); pose proof (H d); clear H
          end
        | [H: (forall x:?T, _), a:?T, b: ?T, c: ?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); pose proof (H b); pose proof (H c); clear H
          end
        | [H: (forall x:?T, _), a:?T, b: ?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); pose proof (H b); clear H
          end
        | [H: (forall x:?T, _), a:?T |- _] =>
          match T with
            | forall i: BoundedIndexFull _, attrType (GetAttr i) =>
              pose proof (H a); clear H
          end
      end.

  Ltac apply_in_app_or_goal H :=
    intros; eapply H; eauto; apply in_or_app; eauto.

  Ltac apply_in_inv H :=
    intros; eapply H; eauto; simpl; eauto.

  Ltac specialize_in :=
    repeat
      match goal with
        | [H: In ?x _ -> _, H': In ?x _ |- _] =>
          specialize (H H')
        | [H: ?x = ?y -> _, H': ?x = ?y |- _] =>
          specialize (H H')
        | [H: ?x = ?y -> _, H': ?y = ?x |- _] =>
          specialize (H (eq_sym H'))
        | [H: In ?x (?l1 ++ ?l2)%list -> ?P |- _] =>
          assert (In x l1 -> P) by (apply_in_app_or_goal H);
            assert (In x l2 -> P) by (apply_in_app_or_goal H);
            clear H
        | [H: In ?x (?v :: ?l)%list -> ?P |- _] =>
          assert (x = v -> P) by (apply_in_inv H);
            assert (In x l -> P) by (apply_in_inv H);
            clear H
        | [H: forall beg mid last v1 v2,
                (?l = beg ++ v1 :: mid ++ v2 :: last)%list -> _,
             H': (?l ++ [?v] = ?beg' ++ ?v1' :: ?mid' ++ ?v2' :: ?last')%list |- _ ] =>
          apply beg_mid_last_add_eq in H';
            let lastNil := fresh in
            let valV := fresh in
            let valLs := fresh in
            let newLast := fresh "newLast" in
            let lastEq := fresh in
            let lsEq := fresh in
            destruct H' as [[lastNil [valV valLs]] | [newLast [lastEq lsEq]]]; subst;
            [|apply H with (beg := beg') (mid := mid') (last := newLast) in lsEq]
        | [H: forall beg mid last v1 v2,
                (?g :: ?l = beg ++ v1 :: mid ++ v2 :: last)%list -> _,
             H': (?l = ?beg' ++ ?v1' :: ?mid' ++ ?v2' :: ?last')%list |- _ ] =>
          specialize (H (g :: beg') mid' last' v1' v2');
            simpl in H;
            specialize (H eq_refl)
      end.
  
  Reset Ltac Profile.
  Set Ltac Profile.
  Show Ltac Profile.

  specialize_msgs.
  speceiali
  specialize_in
  
  simpl.

    simpl.

    Focus 42.

    Show Ltac Profile.
    simpl.

    destruct_in; mkStruct.

    simpl.

    apply in_app_or in H0.
    Reset Ltac Profile.
    firstorder (mkStruct; (discriminate || word_omega || auto)).
    Show Ltac Profile.
    firstorder

    Focus 39.
    
    Show Ltac Profile.
    simpl.
            try (rewrite getCs_cs_matches in * by tauto);
            repeat match goal with
                     | |- context [if ?p then _ else _] => destruct p
                     | H: context [if ?p then _ else _] |- _ => destruct p
                   end;
            repeat split;
            intros).
    Show Ltac Profile.



            try (discriminate || tauto || word_omega)).
).
            firstorder (discriminate || word_omega || auto) with
            specialize_all;
            simpl in *;
            intuition (discriminate || word_omega || auto)).



      ltac:(autorewrite with invariant in *; eauto;
            intros; unfold isCWait, isPWait, GetAttrType in *;
                    simpl in *;
                    beg_mid_last_add;
            beg_mid_last_rm;
            destruct_addr;
            destruct_in_app;
            mkStruct;
            unfold_index;
            rmBadHyp;
            try (rewrite getCs_cs_matches in * by tauto);
            repeat match goal with
                     | |- context [if ?p then _ else _] => destruct p
                     | H: context [if ?p then _ else _] |- _ => destruct p
                   end;
            repeat split;
            intros;
            specialize_all;
            simpl in *;
            intuition (discriminate || word_omega || auto)).
(*
  Lemma nmemCache_invariants_hold_xfer_1 s a u cs:
    nmemCache_invariants s ->
    "rqFromCToP" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.
*)
(*
  Lemma nmemCache_invariants_hold_xfer_2 s a u cs:
    nmemCache_invariants s ->
    "rsFromCToP" metaIs a ->
   forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.
*)
(*
  Lemma nmemCache_invariants_hold_xfer_3 s a u cs:
    nmemCache_invariants s ->
    "fromPToC" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.

  Lemma nmemCache_invariants_hold_1 s a u cs:
    nmemCache_invariants s ->
    "l1MissByState" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.
  
  Lemma nmemCache_invariants_hold_2 s a u cs:
    nmemCache_invariants s ->
    "l1MissByLine" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.

  Lemma nmemCache_invariants_hold_3 s a u cs:
    nmemCache_invariants s ->
    "l1Hit" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.
*)
  Lemma rqFromCToP_revcons_sameAddr a c:
    forall l1 l2
           (v: type (RqToP (Bit (IdxBits + TagBits)) Id)),
      a = v ``"addr" ->
      rqFromCToP c a l1 (l2 ++ [v]) = (rqFromCToP c a l1 l2 ++ [v])%list.
  Proof.
    unfold rqFromCToP.
    intros.
    rewrite filtRqToP_commute_app.
    rewrite app_assoc.
    f_equal.
    repeat (unfold IndexBound_head, IndexBound_tail, nth_error in *; simpl in *); subst.
    match goal with
      | |- (if ?p then _ else _) = [v] => destruct p; tauto
    end.
  Qed.

  Lemma rqFromCToP_revcons_diffAddr a c:
    forall l1 l2
           (v: type (RqToP (Bit (IdxBits + TagBits)) Id)),
      a = v ``"addr" ->
      rqFromCToP c a l1 (l2 ++ [v]) = (rqFromCToP c a l1 l2 ++ [v])%list.
  Proof.
    unfold rqFromCToP.
    intros.
    rewrite filtRqToP_commute_app.
    rewrite app_assoc.
    f_equal.
    repeat (unfold IndexBound_head, IndexBound_tail, nth_error in *; simpl in *); subst.
    match goal with
      | |- (if ?p then _ else _) = [v] => destruct p; tauto
    end.
  Qed.
  
  (*
  Hint Rewrite rqFromCToP_revcons_sameAddr rqFromCToP_revcons_diffAddr
       using (tauto || congruence) : invariant.
   *)
(*  Hint Rewrite getCs_cs_matches using (tauto || congruence) : invariant. *)
  
(*
  Lemma nmemCache_invariants_hold_5 s a u cs:
    nmemCache_invariants s ->
    "upgRq" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.
*)

(*
  Lemma nmemCache_invariants_hold_6 s a u cs:
    nmemCache_invariants s ->
    "ld" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.
*)

(*
    metaInit.
    simplMapUpds ltac:(intros; exfalso;
                       unfold isCWait, getCs, getIdxS, getTagS,
                       IndexBound_head, IndexBound_tail, addFirstBoundedIndex in *;
                         simpl in *;
                         dest; try discriminate).
    - match goal with
        | H: In rq _ |- _ => destruct (i16a _ H) as [sth2 sth3]
      end.
      pose proof (i16 sth2) as [sth4 [[sth5 sth6] | [sth5 sth6]]];
        [ | dest; apply sth6 with (rq := rq); auto ].
      match goal with
        | H: context [if procRq ?p then _ else _],
             H': context [@weq ?t ?a ?b] |- _ =>
              dest;
              destruct (procRq p);
              destruct (@weq t a b); subst; try discriminate; intuition auto
      end.
    - match goal with
        | H: In rs _ |- _ => destruct (i16b _ H) as [sth2 sth3]
      end.
      pose proof (i16 sth2) as [sth4 [[sth5 sth6] | [sth5 sth6]]];
        [match goal with
           | H: In rs _ |- _ => specialize (sth6 _ H); dest; congruence
         end|].
      match goal with
        | H: context [if procRq ?p then _ else _],
             H': context [@weq ?t ?a ?b] |- _ =>
          dest;
            destruct (procRq p);
            destruct (@weq t a b); subst; try discriminate; intuition auto
      end.
  Qed.
*)

(*
  Lemma nmemCache_invariants_hold_7 s a u cs:
    nmemCache_invariants s ->
    "st" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
  Qed.
*)

(*
    metaInit.
    simplMapUpds ltac:(intros; exfalso;
                       unfold isCWait, getCs, getIdxS, getTagS,
                       IndexBound_head, IndexBound_tail, addFirstBoundedIndex in *;
                         simpl in *;
                         dest; try discriminate).
    - match goal with
        | H: In rq _ |- _ => destruct (i16a _ H) as [sth2 sth3]
      end.
      pose proof (i16 sth2) as [sth4 [[sth5 sth6] | [sth5 sth6]]];
        [ | dest; apply sth6 with (rq := rq); auto ].
      match goal with
        | H: context [if procRq ?p then _ else _],
             H': context [@weq ?t ?a ?b] |- _ =>
          dest;
            destruct (procRq p);
            destruct (@weq t a b); subst; try discriminate; intuition auto
      end; dest; try word_omega.
    - match goal with
        | H: In rs _ |- _ => destruct (i16b _ H) as [sth2 sth3]
      end.
      pose proof (i16 sth2) as [sth4 [[sth5 sth6] | [sth5 sth6]]];
        [match goal with
           | H: In rs _ |- _ => specialize (sth6 _ H); dest; congruence
         end|].
      match goal with
        | H: context [if procRq ?p then _ else _],
             H': context [@weq ?t ?a ?b] |- _ =>
              dest;
              destruct (procRq p);
              destruct (@weq t a b); subst; try discriminate; intuition auto
      end; try word_omega.
  Qed.
*)

  Lemma nmemCache_invariants_hold_9 s a u cs:
    nmemCache_invariants s ->
    "pProcess" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
    specialize (H10 eq_refl).
    specialize (H10 (conj eq_refl eq_refl)).
    Notation "a `` b" := (a ``b) (at level 0).
    simpl.
    rewrite getCs_cs_matches in i5.
    Focus 2.
    right. apply H8.

tauto.
    simpl.
  Qed.
(*
    metaInit.

    pose proof (@rsFromCToP_toI_cs_I x a0 s cs0 tag
                                     rsToPList rsFromCList csFind tagFind rsToPListFind
                                     rsFromCListFind HInd) as toI_Inv.
  
    simplMapUpds
      ltac:(unfold listEnq, listDeq, listIsEmpty,
            listFirstElt, listEltT, fromPToC, AddrBits in *;
             destruct fromPList; simpl in *; try discriminate; mkStruct;
            unfold IndexBound_head, IndexBound_tail, AddrBits, isCWait in *; simpl in *;
            match type of i8 with
              | context[weq a0 ?a] =>
                destruct (weq a0 a);
              unfold addFirstBoundedIndex in *; simpl in *;
              [try rewrite cs_sameAddr_upd in *;
                try rewrite rsFromCToP_sameAddr_revcons in *; auto;
               subst; rewrite cs_sameAddr_no_upd in * by auto
              |
              try rewrite cs_diffAddr_upd in *;
                try rewrite rsFromCToP_diffAddr_revcons in *; auto]
            end; intros
           ).
    
    - word_omega.
    - match goal with
        | H: In _ (_ ++ _) |- _ =>
          apply in_app_or in H; destruct H as [sth1 | sth2];
          [apply i7 in sth1; destruct sth1;
           split; word_omega
          |]
      end.
      simpl in sth2; apply in_single in sth2;
      rewrite sth2;
      clear sth2;
      mkStruct;
      split; word_omega.
    - match goal with
        | H: In _ _, H': msg _ = false |- _ =>
          specialize (i8 msg (or_intror H) H')
      end.
      destruct i8 as [sth1 sth2].
      split; [word_omega | exact sth2].
    - match goal with
        | |- isPWait ?a ?cRqValid ?rqFromCList ?dirw ?x =>
          pose proof (isPWait_dec a cRqValid rqFromCList dirw x) as [sth1 | sth2]
      end.
      + assumption.
      + apply i17 with (pToCRq := g) in sth2; try solve [intuition auto].
        rewrite sth2 in *; word_omega.
    - apply i10 with (msg1 := msg1) (msg2 := msg2)
                                    (beg := g :: beg) (mid := mid) (last := last);
      auto.
      simpl.
      f_equal; auto.
    - clear.
      intros sth.
      apply eq_sym in sth.
      apply app_cons_not_nil in sth.
      exact sth.
    - right; intros.
      match goal with
        | H: In ?p ?q |- _ =>
          pose proof (@or_intror (g = msg) _ H) as sth2
      end.
      apply i16b in sth2.
      dest.
      match goal with
        | H: In ?p ?q |- _ =>
          pose proof (in_pre_suf _ _ H) as sth_list
      end.
      destruct sth_list as [mid [last e]].
      apply f_equal with (f := cons g) in e.
      simpl in e.
      rewrite <- app_nil_l with (l := g :: (mid ++ msg :: last)%list) in e.
      apply i15 in e; auto.
      rewrite e in *.
      word_omega.
    - simpl.
      match goal with
        | |- rsLessTo (?l ++ [?v])%list =>
          pose proof (list_nil_revcons l) as sth; destruct sth as [sth1 | [ls [last isEq]]];
          [rewrite sth1; simpl; constructor| rewrite isEq in *; clear isEq]
      end.

      apply rsLessTo_less_app; simpl; auto.
      mkStruct.
      specialize (i14 last ls eq_refl).
      unfold IndexBound_head, IndexBound_tail in *; simpl in *.
      rewrite i14.
      auto.
    - apply app_single_r in H0.
      dest.
      subst.
      mkStruct.
      reflexivity.
    - specialize (i15 pToCRq pToCRs (g :: beg) mid last).
      match goal with
        | H: pToCRq _ = true |- _ =>
          apply i15 in H; simpl; try f_equal; auto; try rewrite H in *
      end.
      word_omega.
    - unfold IndexBound_head, IndexBound_tail in *; simpl in *.
      match type of i16 with
        | ?P -> _ =>
          match goal with
            | H: ?P |- _ =>
              apply i16 in H
          end
      end.
      dest.
      constructor.
      + word_omega.
      + match goal with
          | H: _ \/ _ |- _ => destruct H
        end.
        * match goal with
            | H: (@ex _ _) /\ _ |- _ => destruct H as [sth1 sth2]
          end.
          left; split; [| intros; apply sth2; intuition auto].
          destruct sth1 as [rq [inrq [cnd1 cnd2]]].
          exists rq; auto.
          repeat (constructor; auto); try word_omega.
        * match goal with
            | H: (@ex _ _) /\ _ |- _ => destruct H as [sth1 sth2]
          end.
          right; split; [| intros; apply sth2; intuition auto].
          destruct sth1 as [rs [inrs [cnd1 cnd2]]].
          destruct inrs; [subst; rewrite cnd1 in *; discriminate | ].
          exists rs; auto.
    - match goal with
        | H: In _ _ |- _ => apply i16a in H; dest
      end.
      repeat (constructor; auto); try word_omega.
    - match goal with
        | H: In _ _ |- _ => specialize (i16b _ (@or_intror (g = rs) _ H)); dest
      end.
      repeat (constructor; auto); try word_omega.
    - match goal with
        | H: In _ _ |- _ => specialize (i17 _ (@or_intror _ _ H))
      end.
      match goal with
        | H: pToCRq _ = true |- _ => apply i17 in H; auto; rewrite H in *
      end.
      word_omega.
    - match goal with
        | H: In pToCRq _ |- _ =>
          apply in_pre_suf in H; destruct H as [mid [last isEq]]
      end.
      apply (f_equal (cons g)) in isEq.
      simpl in isEq.
      rewrite  <- app_nil_l with (l := (g :: mid ++ pToCRq :: last)%list) in isEq.
      apply i20 in isEq; auto.
      rewrite isEq in *; word_omega.
    - apply i19 with (beg := g :: beg) (mid := mid) (last := last) (pToCRs := pToCRs)
                                       (pToCRq := pToCRq); auto; simpl; try f_equal; auto.
    - match goal with
        | H: _ = (beg ++ pToCRq1 :: mid ++ pToCRq2 :: last)%list |- _ =>
          apply (f_equal (cons g)) in H; simpl in H;
          apply i20 with (beg := g :: beg) (mid := mid) (last := last) in H; auto;
          rewrite H in *; word_omega
      end.
    - match goal with
        | |- isPWait ?a ?cv ?rq ?dw ?x =>
          destruct (isPWait_dec a cv rq dw x) as [?|sth]; [auto | ]
      end.
      apply i17 with (pToCRq := g) in sth; auto.
      rewrite sth in *; word_omega.
    - match goal with
        | H: (?ls ++ [?v] = ?beg ++ ?v1 :: ?mid ++ ?v2 :: ?last)%list |- _ =>
          apply app_cons_in in H; pose proof H as sth; apply i18 with (pToCRq := g) in H; auto
      end.
      match goal with
        | H: cToPRs1 _ = WO~0~0 |- _ =>
          apply toI_Inv in H; auto
      end.
      match goal with
        | H: g _ < cs0 _, H': cs0 _ = WO~0~0 |- _ =>
          rewrite H' in H; word_omega
      end.
    - match goal with
        | H: In _ (_ ++ _)%list |- _ =>
          apply in_app_or in H; destruct H as [sth1 | sth2]
      end.
      + apply i23 with (cToPRq := cToPRq) in sth1; auto.
      + apply in_single in sth2; subst.
        mkStruct.
        reflexivity.
    - match goal with
        | H: In _ (_ ++ _)%list |- _ =>
          apply in_app_or in H; destruct H as [sth1 | sth2]
      end.
      + apply i26 with (rs := rs) in sth1; auto.
      + apply in_single in sth2; subst.
        mkStruct.
        discriminate.
    - match goal with
        | H: procRqValid = true, H': procRqReplace = true |- _ =>
          specialize (i27 H H'); destruct i27 as [sth1 | sth2]; [intuition auto | ]
      end.
      right.
      match goal with
        | |- (if ?p then _ else _) = _ => destruct p as [sth3 | sth4]; [rewrite sth3 in *| auto]
      end.
      rewrite sth2 in *.
      word_omega.
    - match goal with
        | H: procRqValid = true, H': procRqReplace = true |- _ =>
          specialize (i27 H H'); destruct i27 as [sth1 | sth2]; [intuition auto | ]
      end.
      right.
      match goal with
        | |- (if ?p then _ else _) = _ => destruct p as [sth3 | sth4]; [rewrite sth3 in *| auto]
      end.
      rewrite sth2 in *.
      word_omega.
    - match goal with
        | H: In _ (_ ++ _)%list |- _ =>
          apply in_app_or in H; destruct H
      end.
      + apply i29 with (rs := rs); auto.
      + match goal with
          | H: In _ (_ :: nil) |- _ =>
            apply in_single in H;
              subst; mkStruct; discriminate
        end.
  Qed.
*)



  Lemma nmemCache_invariants_hold_8 s a u cs:
    nmemCache_invariants s ->
    "drop" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInvariant.
    simpl.
  Qed.
(*
    metaInit.

    simplMapUpds
      ltac:(unfold listEnq, listDeq, listIsEmpty,
            listFirstElt, listEltT, fromPToC, AddrBits in *;
             destruct fromPList; simpl in *; try discriminate; mkStruct;
            unfold IndexBound_head, IndexBound_tail, AddrBits, isCWait in *; simpl in *;
            match type of i8 with
              | context[weq a0 ?a] =>
                destruct (weq a0 a); [simpl in *|auto]
            end; intros
           ).
    - apply i8; intuition auto.
    - apply i10 with (msg1 := msg1) (msg2 := msg2) (beg := g :: beg) (mid := mid)
                                    (last := last); simpl; try f_equal; auto.
    - destruct i12 as [sth1 | sth2]; [left; assumption |
                                      right; intros; apply sth2; intuition auto].
    - apply i15 with (pToCRq := pToCRq) (pToCRs := pToCRs) (beg := g :: beg)
                                        (mid := mid) (last := last); simpl; try f_equal; auto.
    - match type of i16 with
        | ?P -> _ =>
          match goal with
            | H: ?P |- _ => apply i16 in H
          end
      end.
      dest.
      constructor; auto.
      match goal with
        | H: (_ /\ _) \/ (_ /\ _) |- _ =>
          destruct H; dest;
          [left; split;
           [eexists; eauto|
            intuition auto]
          |match goal with
             | H: _ \/ _ |- _ => destruct H; [subst; match goal with
                                                       | H1: ?A = true,
                                                             H2: ?A = false |- _ =>
                                                         rewrite H1 in H2; discriminate
                                                     end
                                             |
                                             right; split;
                                             [eexists; eauto | intuition auto]
                                             ]
           end]
      end.

    - apply i16b; intuition auto.
    - apply i17 with (pToCRq := pToCRq); intuition auto.
    - eapply i18; intuition eauto.
    - apply i19 with (pToCRs := pToCRs) (pToCRq := pToCRq) (beg := g :: beg) (mid := mid)
                                        (last := last); simpl; try f_equal; auto.
    - apply i20 with (pToCRq1 := pToCRq1) (pToCRq2 := pToCRq2)
                                          (beg := g :: beg) (mid := mid)
                                          (last := last); simpl; try f_equal; auto.
  Qed.
*)
  
  Lemma nmemCache_invariants_hold_10 s a u cs:
    nmemCache_invariants s ->
    "missByState" is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    normalInit.

    simplMapUpds ltac:(unfold listEnq, listDeq, listIsEmpty,
                       listFirstElt, listEltT, fromPToC, AddrBits in *; subst;
                       destruct rqFromCList;
                       simpl in *; try discriminate; mkStruct;
                       unfold IndexBound_head, IndexBound_tail, AddrBits, isCWait,
                       addFirstBoundedIndex in *; simpl in *; intros; auto).
    - match goal with
        | H: In _ (rqFromCToP _ _ _ _),
             H2: dir _ _ <= _,
             H': In _ (rsFromCToP _ _ _ _) |- _ =>
          specialize (i9 _ H H2 _ H'); unfold isPWait in i9; dest; discriminate
      end.
    - apply i17 with (pToCRq := pToCRq); auto.
      unfold isPWait; intros ?; dest.
      discriminate.
    - match goal with
        | H: _ = (beg ++ pToCRs :: mid ++ pToCRq :: last)%list |- _ =>
          apply i19 in H; auto
      end.
      unfold isPWait in *; dest.
      discriminate.
    - match goal with
        | H: In _ _ |- _ => apply i21 in H; auto
      end.
      unfold isPWait in *; dest; discriminate.
  Qed.

  Lemma nmemCache_invariants_hold_13 s a u cs:
    nmemCache_invariants s ->
    "dwnRs_noWait" is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    normalInit.

    - simplMapUpds
        ltac:(unfold listEnq, listDeq, listIsEmpty,
              listFirstElt, listEltT, fromPToC, AddrBits, isPWait in *; subst;
              destruct rsFromCList;
              simpl in *; try discriminate; mkStruct;
              unfold IndexBound_head, IndexBound_tail, AddrBits,
              addFirstBoundedIndex in *; simpl in *;
              match goal with
                | H: context[_ {| bindex := "rs"; indexb := ?i1 |}
                              {| bindex := "addr"; indexb := ?i2 |}] |- _ =>
                  destruct (weq a0 (g {| bindex := "rs"; indexb := i1 |}
                                      {| bindex := "addr"; indexb := i2 |})) as [e | ?];
                [ rewrite <- e in *;
                  match goal with
                    | H: context[{| bindex := "child"; indexb := ?i |}] |- _ =>
                      destruct (weq ($ c) (g {| bindex := "child"; indexb := i |}));
                        [
                          rewrite rsFromCToP_sameAddr_sameChild_cons in * by
                            (unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto);
                          unfold IndexBound_head, IndexBound_tail in *; cbv [ibound boundi] in *
                        | match goal with
                            | |- context [rsFromCToP _ _ rsFromCList rsToPList] =>
                              rewrite rsFromCToP_diffChild_cons with (g := g);
                                unfold IndexBound_head, IndexBound_tail; simpl; auto
                            | _ => auto
                          end
                        ]
                  end
                | match goal with
                    | |- context [rsFromCToP _ _ rsFromCList rsToPList] =>
                      rewrite rsFromCToP_diffAddr_cons with (g := g);
                        unfold IndexBound_head, IndexBound_tail; cbv [ibound boundi] in *; auto
                    | _ => auto
                  end
                ]
              end).
      + specialize (i7 _ (or_introl eq_refl)).
        dest; assumption.
      + intros.
        destruct i7 with (rs := rs); simpl; auto.
        constructor; [auto |].
        apply rsLessTo_cons_in with (rs := rs) in i13;
          unfold IndexBound_head, IndexBound_tail; simpl; auto.
      + intros.
        destruct i12 as [ez | diff]; [discriminate|].
        match goal with
          | H: In _ _ |- _ => apply diff in H; rewrite H in *; discriminate
        end.
      + intros.
        unfold rsFromCToP in *.
        apply rsLessTo_cons_in with (rs := rs) in i13;
          unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto.
        match goal with
          | H: In _ _ |- _ =>
            specialize (i26 _ (@or_introl _ _ eq_refl))
        end.  
        match type of i26 with
          | ?P = true -> _ =>
            case_eq (P); intros whichBool
        end.
        * specialize (i26 whichBool).
          rewrite i26 in i13.
          word_omega.
        * match goal with
            | H: In rs _ |- _ =>
              destruct (in_pre_suf _ _ H) as [mid [last sth3]]
          end.
          rewrite sth3 in i22.
          
          match goal with
            | H: a0 = g ?idx _ |- _ =>
              specialize (i22 (g idx) rs nil mid last); simpl in i22;
              specialize (i22 eq_refl);
              specialize (i7 (g idx) (@or_introl _ _ eq_refl)); destruct i7 as [sth1 sth2]
          end.
          match type of i22 with
            | _ \/ ?p =>
              assert (sth4: p) by (destruct i22; [rewrite whichBool in *; discriminate| auto])
          end.
          match goal with
            | H: In rq _, H': In rs _, H2: rs _ = true |- _ =>
              specialize (i29 _ _ H (@or_intror _ _ H') H2)
          end.
          rewrite i29 in *.
          word_omega.
      + unfold not; intros csLt isNil.
        rewrite isNil in i14.
        erewrite <- i14 with (beg := nil) in csLt;
          unfold IndexBound_head, IndexBound_tail; simpl; eauto.
        word_omega.
      + destruct i12 as [ez | diff]; [discriminate | right; auto].
      + eapply rsLessTo_cons_rsLessTo; eassumption.
      + intros;
        destruct (rsFromCToP ($ c) a0 rsFromCList rsToPList).
        * match goal with
            | H: nil = (_ ++ (_ :: nil))%list |- _ =>
              apply app_cons_not_nil in H; exfalso; assumption
          end.
        * eapply i14. match goal with
                        | H: t :: l = _ |- _ =>
                          rewrite H; rewrite app_comm_cons; reflexivity
                      end.
      + intros; eapply i18; simpl in *; eauto.
      + intros; eapply i21; simpl in *; eauto.
      + intros; eapply i22.
        match goal with
          | H: rsFromCToP _ _ _ _ = _ |- _ =>
            rewrite H; rewrite app_comm_cons; reflexivity
        end.
      + intros.
        apply rsLessTo_cons_in with (rs := cToPRs) in i13;
          unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto.
        match goal with
          | |- ?p = false => case_eq p; intros volStat; [| assumption]
        end.
        match goal with
          | H: In cToPRq _, H': In cToPRs _ |- _ =>
            specialize (i29 _ _ H (@or_intror _ _ H') volStat)
        end.
        rewrite i29 in *.
        word_omega.
      + intros; eapply i26; simpl in *; eauto.
      + intros; eapply i29; simpl in *; eauto.


    - simplMapUpds
        ltac:(unfold listEnq, listDeq, listIsEmpty,
              listFirstElt, listEltT, fromPToC, AddrBits, isPWait in *; subst;
              destruct rsFromCList;
              simpl in *; try discriminate; mkStruct;
              unfold IndexBound_head, IndexBound_tail, AddrBits,
              addFirstBoundedIndex in *; simpl in *;
              match goal with
                | H: context[_ {| bindex := "rs"; indexb := ?i1 |}
                              {| bindex := "addr"; indexb := ?i2 |}] |- _ =>
                  destruct (weq a0 (g {| bindex := "rs"; indexb := i1 |}
                                      {| bindex := "addr"; indexb := i2 |})) as [e | ?];
                [ rewrite <- e in *;
                  match goal with
                    | H: context[{| bindex := "child"; indexb := ?i |}] |- _ =>
                      destruct (weq ($ c) (g {| bindex := "child"; indexb := i |}));
                        [
                          rewrite rsFromCToP_sameAddr_sameChild_cons in * by
                            (unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto);
                          unfold IndexBound_head, IndexBound_tail in *; cbv [ibound boundi] in *
                        | match goal with
                            | |- context [rsFromCToP _ _ rsFromCList rsToPList] =>
                              rewrite rsFromCToP_diffChild_cons with (g := g);
                                unfold IndexBound_head, IndexBound_tail; simpl; auto
                            | _ => auto
                          end
                        ]
                  end
                | match goal with
                    | |- context [rsFromCToP _ _ rsFromCList rsToPList] =>
                      rewrite rsFromCToP_diffAddr_cons with (g := g);
                        unfold IndexBound_head, IndexBound_tail; cbv [ibound boundi] in *; auto
                    | _ => auto
                  end
                ]
              end).
      + specialize (i7 _ (or_introl eq_refl)).
        dest; assumption.
      + intros.
        destruct i7 with (rs := rs); simpl; auto.
        constructor; [auto |].
        apply rsLessTo_cons_in with (rs := rs) in i13;
          unfold IndexBound_head, IndexBound_tail; simpl; auto.
      + intros.
        destruct i12 as [ez | diff]; [discriminate|].
        match goal with
          | H: In _ _ |- _ => apply diff in H; rewrite H in *; discriminate
        end.
      + intros.
        unfold rsFromCToP in *.
        apply rsLessTo_cons_in with (rs := rs) in i13;
          unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto.
        match goal with
          | H: In _ _ |- _ =>
            specialize (i26 _ (@or_introl _ _ eq_refl))
        end.  
        match type of i26 with
          | ?P = true -> _ =>
            case_eq (P); intros whichBool
        end.
        * specialize (i26 whichBool).
          rewrite i26 in i13.
          word_omega.
        * match goal with
            | H: In rs _ |- _ =>
              destruct (in_pre_suf _ _ H) as [mid [last sth3]]
          end.
          rewrite sth3 in i22.
          
          match goal with
            | H: a0 = g ?idx _ |- _ =>
              specialize (i22 (g idx) rs nil mid last); simpl in i22;
              specialize (i22 eq_refl);
              specialize (i7 (g idx) (@or_introl _ _ eq_refl)); destruct i7 as [sth1 sth2]
          end.
          match type of i22 with
            | _ \/ ?p =>
              assert (sth4: p) by (destruct i22; [rewrite whichBool in *; discriminate| auto])
          end.
          match goal with
            | H: In rq _, H': In rs _, H2: rs _ = true |- _ =>
              specialize (i29 _ _ H (@or_intror _ _ H') H2)
          end.
          rewrite i29 in *.
          word_omega.
      + unfold not; intros csLt isNil.
        rewrite isNil in i14.
        erewrite <- i14 with (beg := nil) in csLt;
          unfold IndexBound_head, IndexBound_tail; simpl; eauto.
        word_omega.
      + destruct i12 as [ez | diff]; [discriminate | right; auto].
      + eapply rsLessTo_cons_rsLessTo; eassumption.
      + intros;
        destruct (rsFromCToP ($ c) a0 rsFromCList rsToPList).
        * match goal with
            | H: nil = (_ ++ (_ :: nil))%list |- _ =>
              apply app_cons_not_nil in H; exfalso; assumption
          end.
        * eapply i14. match goal with
                        | H: t :: l = _ |- _ =>
                          rewrite H; rewrite app_comm_cons; reflexivity
                      end.
      + intros; eapply i18; simpl in *; eauto.
      + intros; eapply i21; simpl in *; eauto.
      + intros; eapply i22.
        match goal with
          | H: rsFromCToP _ _ _ _ = _ |- _ =>
            rewrite H; rewrite app_comm_cons; reflexivity
        end.
      + intros.
        apply rsLessTo_cons_in with (rs := cToPRs) in i13;
          unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto.
        match goal with
          | |- ?p = false => case_eq p; intros volStat; [| assumption]
        end.
        match goal with
          | H: In cToPRq _, H': In cToPRs _ |- _ =>
            specialize (i29 _ _ H (@or_intror _ _ H') volStat)
        end.
        rewrite i29 in *.
        word_omega.
      + intros; eapply i26; simpl in *; eauto.
      + intros; eapply i29; simpl in *; eauto.
  Qed.
  

  
(*  
  
  ( *
  
  Lemma nmemCache_invariants_hold_12 s a u cs:
    nmemCache_invariants s ->
    "dwnRs" is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    normalInit.

    - simplMapUpds; (reflexivity || eassumption ||
                             unfold listEnq, listDeq, listIsEmpty,
                 listFirstElt, listEltT, fromPToC, AddrBits, isPWait in *; subst;
                 destruct rsFromCList;
                 simpl in *; try discriminate; mkStruct;
                 unfold IndexBound_head, IndexBound_tail, AddrBits,
                 addFirstBoundedIndex in *; simpl in *;
                 match goal with
                   | |- context [@weq ?t a0 ?a] =>
                     destruct (@weq t a0 a) as [e | ?];
                   [ rewrite <- e in *reflexivity || eassumption ||
                           
                   | match goal with
                       | |- context [rsFromCToP _ _ rsFromCList rsToPList] =>
                         rewrite rsFromCToP_diffAddr_first with (g := g);
                           unfold IndexBound_head, IndexBound_tail; simpl; auto
                       | _ => auto
                     end
                   ]
                   | _ => auto
                 end;
                 match goal with
                   | |- context [@weq ?t ($ c) ?a] =>
                     destruct (@weq t ($ c) a);
                   [| match goal with
                        | |- context [rsFromCToP _ _ rsFromCList rsToPList] =>
                          rewrite rsFromCToP_diffChild_first with (g := g);
                            unfold IndexBound_head, IndexBound_tail; simpl; auto
                        | _ => auto
                      end
                   ]
                   | _ => auto
                 end
                ).
      + apply rsFromCToP_sameAddr_sameChild in i7;
        unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto.
        dest; assumption.
      + intros.
        destruct i7 with (rs := rs) as [i7_a i7_b].
        * unfold rsFromCToP; simpl.
          repeat match goal with
                   | |- context[if ?p then _ else _] =>
                     destruct p
                 end; simpl; auto.
        * constructor; [auto |].
          unfold rsFromCToP in *.
          simpl in i13.
          repeat match type of i13 with
                   | context [if ?p then _ else _] =>
                     destruct p
                 end; [| intuition auto | intuition auto].
          rewrite <- app_comm_cons in i13.
          apply rsLessTo_cons_in with (rs := rs) in i13;
            unfold IndexBound_head, IndexBound_tail; simpl; auto.
      + intros.
        destruct i12 as [ez | diff].
        * unfold rsFromCToP in ez; simpl in ez.
          repeat match type of ez with
                   | context[if ?p then _ else _] =>
                     destruct p
                 end; simpl in *; try discriminate; try rewrite ez in *; simpl in *;
          intuition auto.
        * match goal with
            | H: In _ _ |- _ => apply diff in H; rewrite H in *; discriminate
          end.
      + intros.
          unfold rsFromCToP in *.
          simpl in i13.
          repeat match type of i13 with
                   | context [if ?p then _ else _] =>
                     destruct p
                 end; [| intuition auto | intuition auto].
          rewrite <- app_comm_cons in i13.
          apply rsLessTo_cons_in with (rs := rs) in i13;
            unfold IndexBound_head, IndexBound_tail in *; simpl in *; auto.
          unfold IndexBound_head, IndexBound_tail in *; simpl in *.
          repeat match type of i26 with
                   | context [if ?p then _ else _] =>
                     destruct p
                 end; [| intuition auto | intuition auto].
          simpl in *.
          match goal with
            | H: In _ _ |- _ =>
              specialize (i26 _ (@or_introl _ _ eq_refl))
          end.
          match type of i26 with
            | ?P = true -> _ =>
              case_eq (P); intros whichBool
          end.
        * specialize (i26 whichBool).
          rewrite i26 in i13.
          Nomega.nomega.
        * match goal with
            | H: In rs _ |- _ =>
              destruct (in_pre_suf _ _ H) as [mid [last sth3]]
          end.
          rewrite sth3 in i22.
          
          match goal with
            | H: a0 = g ?idx _ |- _ =>
              specialize (i22 (g idx) rs nil mid last); simpl in i22;
              specialize (i22 eq_refl);
              specialize (i7 (g idx) (@or_introl _ _ eq_refl)); destruct i7 as [sth1 sth2]
          end.
          match type of i22 with
            | _ \/ ?p =>
              assert (sth4: p) by (destruct i22; [rewrite whichBool in *; discriminate| auto])
          end.
          match goal with
            | H: In rq _, H': In rs _, H2: rs _ = true |- _ =>
              specialize (i29 _ _ H (@or_intror _ _ H') H2)
          end.
          rewrite i29 in *.
          Nomega.nomega.
      + intros; unfold isPWait.
        match goal with
          | |- context [@weq ?t ($ c) ?a] =>
            destruct (@weq t ($ c) a);
              [intuition auto
              | match goal with
                  | |- context [rsFromCToP _ _ rsFromCList rsToPList] =>
                    rewrite rsFromCToP_diffChild_first with (g := g);
                      unfold IndexBound_head, IndexBound_tail; simpl; auto
                  | _ => auto
                end
              ]
        end.
        apply i9; auto.
      + 

        
              apply i23 with (cToPRs := rs) in H; try (Nomega.nomega);
              try rewrite sth4 in H; try discriminate; auto
          end.
          unfold IndexBound_head, IndexBound_tail in i23; simpl in i23.
          repeat match type of i23 with
                   | context [if ?p then _ else _] =>
                     destruct p
                 end; [| intuition auto | intuition auto].
          simpl in i23.
          simpl in ez
        destruct i
        
          
          simpl.          repeat match goal with
                   | |- context[if ?p then _ else _] =>
                     destruct p
                 end; simpl; auto.

          right; apply in_or_app; auto.
    - match goal with
        | |- context [weq ?a ?b] =>
          destruct (weq a b) as [sth1 | ?]; [rewrite <- sth1 in
                                            |
                                            auto]
      end.
      admit.
      match goal with
        | |- context[rsFromCToP ?c ?a rsFromCList rsToPList] =>
          rewrite rsFromCToP_diffAddr_first with (g := g);
            unfold IndexBound_head, IndexBound_tail; simpl; auto
      end.
      match goal with
        | |- context[rsFromCToP ?c ?a rsFromCList rsToPList] =>
          rewrite rsFromCToP_diffChild_first with (g := g);
            unfold IndexBound_head, IndexBound_tail; simpl; auto
      end.
      
      apply i7.
      simpl.
      assumption.
      match goal with
        | |- context [weq ?p ?q] => destruct (weq p q) as [sth2 |?]; [| auto]
      end.
      intros.
      
      
  Qed.
   *)

  (*
      simpl.
      match goal with
        | H: g _ < cs0 _ |- _ =>
          rewrite sth2 in H
      end.
          rewrite H' in H; Nomega.nomega
      end.
      rewrite sth2 in *Nomega.nomega.
    - 
      match goal with
        | H: ?p = true, H': ?p = false |- _ =>
          rewrite H in H'; discriminate
      end.
    - 
        rewrite mkStruct_eq; simpl; unfold StringBound.ith_Bounded; simpl.
        reflexivity.

      match goal with
          [apply i23 in sth1; auto|]
      end.
      rewrite H0 in H7.
      Nomega.nomega.
      simpl.
                                try (rewrite H in *; Nomega.nomega)
      end.
      simpl.
      simpl.
      Nomega.nomega.
    - 
          ( *rewrite H in H'; exfalso; Nomega.nomega * ) idtac
      end.
      simpl.
    - 
      
      simpl.
    - 
      exfalso; Nomega.nomega.
    - 
      
    - 
      
      destruct (isPWait_dec 
          simpl in H;
          apply i20 in H; auto;
          try (rewrite H in *; Nomega.nomega)
      end.
      apply i20 with (beg := g :: beg) (mid := mid) (last := last) (pToCRq1 := pToCRq1)
                                       (pToCRq2 := pToCRq2); auto; simpl; try f_equal; auto.
    - 
      
      exfalso; Nomega.pre_nomega; Nomega.nomega.
    - 
      dest.c
      match goal with
        | H: In _ (_ ++ _) |- _ =>
          apply in_app_or in H; destruct H;
          [apply i18 with (pToCRq := pToCRq) (cToPRs := cToPRs); intuition auto| ]
      end.
      match goal with
        | H: In _ (?p :: nil) |- _ =>
          apply in_single in H; subst; simpl in *
      end.
      rewrite mkStruct_eq; 
        simpl; unfold StringBound.ith_Bounded; simpl.
      apply i18 with (pToCRq := pToCRq) (cToPRs := cToPRs); intuition auto.
    - 
      
    - 
          repeat (constructor; intuition auto); try Nomega.nomega.
          
    -
          simpl.
    - 
        * 
      specialize (i16 H0).
              specialize (i16 P)
          end
      end.
      specialize
     
      
      Nomega.pre_nomega; Nomega.nomega.
    - 
      simpl.

      match type of i14 with
        | last {| indexb := {| boundi := ?p |} |} = _ =>
          match type of p with
            | ?P => pose P
          end
      end.
      match goal with
        | |- _ < last {| indexb := {| boundi := ?p |} |} =>
          match type of p with
            | ?Q => pose Q
          end
      end.
      Set Printing All.
      
      simpl in i14.
      rewrite i14.
      Nomega.pre_nomega. Nomega.nomega.
    - 
      match goal with
        | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq);
            simpl; unfold StringBound.ith_Bounded; simpl
      end.
      dest.
      
             simpl.
              
        
        right; eexists; intuition eauto.
        
      match goal with
        | |- rsLessTo (?l ++ [?v])%list =>
          destruct l; [simpl; constructor | ]
      end.
      Lemma rsLessTo_
      simpl in e.
      simpl.
      
      specialize (i15 g msg).
      assert (cs0 (split2 TagBits IdxBits
                          (g {| bindex := "isRq";
                                indexb := {| ibound := 0; boundi := eq_refl |} |} = WO~0~0))).
      especialize (i15 _ _ _ _ H2 H5).
      apply i15 with (beg := nil) (mid := mid) (last := last) in H2; auto.
      dest.
      simpl.
      pose proof (
      apply 
      
      Nomega.pre_nomega; Nomega.nomega.
    - 
      clear.
      intros sth.
      apply eq_sym in sth.
      apply app_cons_not_nil in sth.
      exact sth.
    - 
        
    - 

    - match goal with
        | |- isPWait ?a ?cRqValid ?rqFromCList ?dirw ?x =>
          pose proof (isPWait_dec a cRqValid rqFromCList dirw x) as [sth1 | sth2]
      end.
      + assumption.
      + apply i17 with (pToCRq := g) in sth2; try solve [intuition auto].
        rewrite sth2 in *; Nomega.pre_nomega; Nomega.nomega.


    - match goal with
        | |- isPWait ?a ?cRqValid ?rqFromCList ?dirw ?x =>
          pose proof (isPWait_dec a cRqValid rqFromCList dirw x) as [sth1 | sth2]
      end.
      match goal with
        | H: In _ (_ ++ _) |- _ =>
          apply in_app_or in H; destruct H as [sth1 | sth2]
      end.
      
      apply i9 with (rq := rq) in sth1; auto.
      apply in_single in sth2.
      simpl in sth2; destruct sth2 as [sth3 | sth4];
      [ | exfalso; exact sth4].
      
      split; Nomega.pre_nomega; Nomega.nomega.
          [apply i9 in sth1; destruct sth1;
           split; Nomega.pre_nomega; Nomega.nomega
          | simpl in sth2; destruct sth2 as [sth3 | sth4];
            [ rewrite <- sth3;
              clear sth3;
              repeat match goal with
                       | |- context [mkStruct] =>
                         rewrite mkStruct_eq; simpl; unfold ith_Bounded; simpl
                     end; split; Nomega.pre_nomega; Nomega.nomega
            | exfalso; exact sth4]]
      end.
      apply sth2.
      assumption.
      Nomega.pre_nomega;
        Nomega.nomega.
      simpl.
      
      split; Nomega.pre_nomega; Nomega.nomega.
    - 

      destruct i8 with (msg := msg).
       match goal with
        | H: In _ _ |- _ =>
          apply i8 in H ( *;
          split; Nomega.pre_nomega; Nomega.nomega * )
      end.
          | ( *simpl in sth2; destruct sth2 as [sth3 | sth4];
            [ rewrite <- sth3;
              clear sth3;
              repeat match goal with
                       | |- context [mkStruct] =>
                         rewrite mkStruct_eq; simpl; unfold ith_Bounded; simpl
                     end; split; Nomega.pre_nomega; Nomega.nomega
            | exfalso; exact sth4]* )]
      end.
      
      Focus 2.
      Print Ltac mkStruct.
      repeat match goal with
               | |- context [mkStruct ?p ?q] =>
                 rewrite mkStruct_eq; simpl; unfold ith_Bounded; simpl
             end.
      
      simpl.
      mkStruct.

      Focus 2.
      
      apply i7.
    - match goal with
        | H: a0 = ?a |- _ =>
          rewrite sameAddr_old with (a := a) in i5; auto
      end.
    Focus 24.
    - 
    Focus 23.
    intuition auto.
    rewrite rsFromCToP_sameAddr.
    
          c
          c
          
    subst.
    rewrite <- rsFromCToP_xfer.
    simpl.
    simpl.
    unfold addFirstBoundedIndex.
    simpl.

  
      (pToCRq2 := pToCRq2) (beg := 

      eapply i20; intuition eauto.
      


      right; split.
      
      firstorder.
      match goal with
        | H: forall msg: ?T, ?A \/ ?B -> ?P |- ?P =>
          idtac ( *
                  apply H; intuition auto * )
      end.
          [left; split; [eexists; eauto| intros; match goal with
                                                   | H: _ -> ?P |- ?P =>
                                                     apply H] | right; split; [eexists; eauto|]]
      end.
      
    - unfold IndexBound_head in i15.
      simpl in i15.

      apply i10 in H3.
      eapply i10; intuition eauto.
    - 
               match goal with
                 | H: context[weq a0 ?a] |- _ =>
                   destruct (weq a0 a) as [e | n]
               end).
                 [rewrite <- e in *; intros; match goal with
                                               | H: In ?p (?q ++ ?r) |- _ =>
                                                 apply in_app_or in H; destruct H;
                                                 [auto | simpl in *; destruct H;
                                                         [rewrite <- H in *; mkStruct
                                                         |exfalso; intuition]]
                                               | _ => idtac
                                             end
                 | rewrite ?app_nil_r; auto]
                 | _ => idtac
               end).
               
               mk
                simpl in *; mkStruct; rewrite ?app_assoc;
               unfold IndexBound_head, IndexBound_tail, AddrBits, isCWait in *; simpl in *;
               match goal with
                 | |- context[weq a0 ?a] =>
                   destruct (weq a0 a) as [e | n];
                 [rewrite <- e in *; intros; match goal with
                                               | H: In ?p (?q ++ ?r) |- _ =>
                                                 apply in_app_or in H; destruct H;
                                                 [auto | simpl in *; destruct H;
                                                         [rewrite <- H in *; mkStruct
                                                         |exfalso; intuition]]
                                               | _ => idtac
                                             end
                 | rewrite ?app_nil_r; auto]
                 | _ => idtac
               end
              ).
    simpl in *; discriminate.

*)
End MemCacheInl.
