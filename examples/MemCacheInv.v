Require Import Lib.FMap Lib.Word Ex.MemTypes Lib.Indexer Lib.Struct Ex.Msi
        Ex.NativeFifo Kami.Notations String Ex.MemCacheInl Kami.Syntax List Kami.Semantics
        Kami.ParametricSyntax Lib.CommonTactics Kami.SemFacts Lib.FMap Lib.Concat Arith
        FunctionalExtensionality Program.Equality Kami.Tactics Lib.MapVReify Kami.SymEval
        Kami.SymEvalTac Lib.StringAsList Lib.ListSupport Lib.Misc
        Coq.Program.Basics Ex.Names Lib.FinNotations Lib.MyLogic.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Notation "<| t |>" := (fullType type (SyntaxKind t)).

Local Notation "<[ t ]>" := (fullType type (@NativeKind t nil)).

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas DataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Local Notation RqFC := (RqFromC LgNumChildren (Bit (IdxBits + TagBits)) Id).
  Local Notation RsFC := (RsFromC DataBytes LgNumDatas LgNumChildren (Bit (IdxBits + TagBits))).
  Local Notation RqTP := (RqToP (Bit (IdxBits + TagBits)) Id).
  Local Notation RsTP := (RsToP DataBytes LgNumDatas (Bit (IdxBits + TagBits))).
  Local Notation TC := (ToC DataBytes LgNumDatas LgNumChildren (Bit (IdxBits + TagBits)) Id).
  Local Notation FP := (FromP DataBytes LgNumDatas (Bit (IdxBits + TagBits)) Id).

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

  Local Notation RqFPr := (RqFromProc DataBytes (Bit (LgNumDatas + (IdxBits + TagBits)))).
  Local Notation RsTPr := (RsToProc DataBytes).
  Definition isCWait a procRqValid
             (procRq: type (Struct RqFPr))
             csw :=
    procRqValid = true /\ a = split2 LgNumDatas (IdxBits + TagBits) (procRq (RqFPr !! addr)) /\
    csw = true.

  Definition isPWait a cRqValid
             (rqFromCList: list (type (Struct RqFC)))
             dirw (cword: word LgNumChildren) (dir: <| Vector (Vector Msi LgNumChildren) (IdxBits + TagBits) |>) :=
    cRqValid = true /\
    dirw cword = true /\
    match hd_error rqFromCList with
      | Some cRq => a = cRq (RqFC !! rq) (RqTP !! addr) /\ cword <> cRq (RqFC !! child) /\
                    (cRq (RqFC !! rq) (RqTP !! to) >
                     if weq (dir a cword) ($ Msi.Mod)
                     then $ Msi.Inv
                     else if weq (dir a cword) ($ Msi.Ex)
                          then $ Msi.Sh
                          else if weq (dir a cword) ($ Msi.Sh)
                               then $ Msi.Ex
                               else $ Msi.Mod)
      | _ => False
    end.

  Definition cache := nat.

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
            isPWait a cRqValid rqFromCList dirw cword dir ;

      i10: (forall beg mid last rs1 rs2,
              fromPToC cword a fromPList toCList = beg ++ rs1 :: mid ++ rs2 :: last ->
              rs1 (FP !! isRq) = false ->
              rs2 (FP !! isRq) = false ->
              False)%list ;

      i11: rsFromCToP cword a rsFromCList rsToPList = nil ->
           (forall msg, In msg (fromPToC cword a fromPList toCList) -> msg (FP !! isRq) = true) ->
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
                       rs (FP !! isRq) = false ->
                       isCWait a procRqValid procRq csw
                       /\ (getCs csv tagv a < if (procRq (RqFPr !! op)):bool
                                              then $ Msi.Mod else $ Msi.Sh)
                       /\ rs (FP !! to) =
                          (if (procRq (RqFPr !! op)):bool then $ Msi.Mod else $ Msi.Sh) ;
    
      i16c: forall rq rs, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                          In rs (fromPToC cword a fromPList toCList) ->
                          rs (FP !! isRq) = true ;

      i17: forall rq,
             In rq (fromPToC cword a fromPList toCList) ->
             rq (FP !! isRq) = true ->
             getCs csv tagv a = $ Msi.Inv \/
             isPWait a cRqValid rqFromCList dirw cword dir ;

      i18: forall rq rs,
             In rq (fromPToC cword a fromPList toCList) ->
             In rs (rsFromCToP cword a rsFromCList rsToPList) ->
             rq (FP !! isRq) = true ->
             rs (RsTP !! to) = $ Msi.Inv ;

      i19: (forall beg mid last rq rs,
              fromPToC cword a fromPList toCList = beg ++ rs :: mid ++ rq :: last ->
              rs (FP !! isRq) = false ->
              rq (FP !! isRq) = true ->
              isPWait a cRqValid rqFromCList dirw cword dir)%list ;

      i20: (forall beg mid last rq1 rq2,
              fromPToC cword a fromPList toCList = beg ++ rq1 :: mid ++ rq2 :: last ->
              rq1 (FP !! isRq) = true ->
              rq2 (FP !! isRq) = true ->
              getCs csv tagv a = $ Msi.Inv)%list ;

      i21: forall rs,
             In rs (rsFromCToP cword a rsFromCList rsToPList) ->
             rs (RsTP !! isVol) = false ->
             isPWait a cRqValid rqFromCList dirw cword dir ;

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
      
      i27b: procRqValid = true -> procRqReplace = false ->
            tagv (split1 IdxBits TagBits
                         (split2 LgNumDatas (IdxBits + TagBits)
                                 (procRq (RqFPr !! addr)))) =
            split2 IdxBits TagBits (split2 LgNumDatas (IdxBits + TagBits)
                                           (procRq (RqFPr !! addr))) \/
            csv (split1 IdxBits TagBits
                        (split2 LgNumDatas (IdxBits + TagBits)
                                (procRq (RqFPr !! addr)))) = $ Msi.Inv ;
      
      i28: cRqValid = true -> hd_error rqFromCList = Some cRq ;

      i29: forall rq rs, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                         In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                         rs (RqTP !! isVol) = true ->
                         rq (RqTP !! from) = $ Msi.Inv ;

      i30: forall rq tl, rqFromCToP cword a rqFromCList rqToPList = rq :: tl -> tl = nil ;

      i31: forall beg mid1 mid2 last rs rq1 rq2,
             fromPToC cword a fromPList toCList = beg ++ rs :: mid1 ++ rq1 :: mid2 ++ rq2 :: last ->
             rs (FP !! isRq) = false ->
             rq1 (FP !! isRq) = true ->
             rq2 (FP !! isRq) = true ->
             False

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
                                             LgNumDatas DataBytes Id LgNumChildren))
     = Some a) (at level 0).
  
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

  Lemma rsLessTo_app ls:
    forall rs: type (Struct RsTP),
      rsLessTo ls ->
      (forall ls' x, ls = ls' ++ [x] -> x (RsTP!!to) > rs (RsTP!!to)) ->
      rsLessTo (ls ++ [rs]).
  Proof.
    pose proof (list_nil_revcons ls).
    destruct H; intros; simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *; dest; subst; auto.
    specialize (H1 _ _ eq_refl).
    apply rsLessTo_less_app with (v2 := rs) in H0; assumption.
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
  

  Lemma getCs_tag_match_getCs cs tag a a':
    tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a ->
    forall upd,
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
    forall c a rsFromCList rsToPList (v: type (Struct (RsToP DataBytes LgNumDatas (Bit (IdxBits + TagBits))))),
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

  Lemma rewrite_rsFromCToP_cons:
    forall c a rsFromCList rsToPList (v: type (Struct (RsFC))),
      rsFromCToP c a (v :: rsFromCList) (rsToPList)%list =
      if weq c (v (RsFC !! child))
      then if weq a (v (RsFC !! rs) (RsTP !! addr))
           then v (RsFC !! rs) :: rsFromCToP c a rsFromCList rsToPList
           else rsFromCToP c a rsFromCList rsToPList
      else rsFromCToP c a rsFromCList rsToPList.
  Proof.
    cbn; intros.
    unfold rsFromCToP.
    repeat match goal with
             | |- context[ if ?p then _ else _] => destruct p; simpl; try reflexivity
           end.
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

  Lemma rewrite_rqFromCToP_cons:
    forall c a rqFromCList rqToPList (v: type (Struct (RqFC))),
      rqFromCToP c a (v :: rqFromCList) (rqToPList)%list =
      if weq c (v (RqFC !! child))
      then if weq a (v (RqFC !! rs) (RqTP !! addr))
           then v (RqFC !! rs) :: rqFromCToP c a rqFromCList rqToPList
           else rqFromCToP c a rqFromCList rqToPList
      else rqFromCToP c a rqFromCList rqToPList.
  Proof.
    cbn; intros.
    unfold rqFromCToP.
    repeat match goal with
             | |- context[ if ?p then _ else _] => destruct p; simpl; try reflexivity
           end.
  Qed.

  Lemma rewrite_fromPToC_cons:
    forall c a fromPList toCList (v: type (Struct (FromP DataBytes LgNumDatas (Bit (IdxBits + TagBits)) Id))),
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
  
  Lemma rewrite_fromPToC_revcons:
    forall c a fromPList toCList (v: type (Struct TC)),
      fromPToC c a fromPList (toCList ++ [v])  =
      if weq c (v (TC !! child))
      then if weq a (v (TC !! msg) (FP !!addr))
           then fromPToC c a fromPList toCList ++ [v (TC !! msg)]
           else fromPToC c a fromPList toCList
      else fromPToC c a fromPList toCList.
  Proof.
    cbn; intros.
    unfold fromPToC.
    rewrite filtToC_commute_app.
    cbn.
    repeat match goal with
      | |- context[if ?p then _ else _] => destruct p; simpl; rewrite ?app_assoc, ?app_nil_r; try reflexivity
    end.
  Qed.

  Hint Rewrite rewrite_rsFromCToP_revcons rewrite_rsFromCToP_cons rewrite_rqFromCToP_revcons rewrite_rqFromCToP_cons
       rewrite_fromPToC_cons rewrite_fromPToC_revcons: invariant.

  Lemma app_or_impl A l1 l2 (x: A) (P: Prop): (In x (l1 ++ l2) -> P) -> (In x l1 -> P) /\ (In x l2 -> P).
  Proof.
    rewrite app_or in *.
    tauto.
  Qed.

  Lemma cons_or_impl A l (x v: A) (P: Prop): (In x (v :: l) -> P) -> (x = v -> P) /\ (In x l -> P).
  Proof.
    rewrite cons_or in *.
    tauto.
  Qed.
  
  Ltac simplMapUpds tac :=
    (try esplit);
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

  Ltac destruct_addr_base a a' :=
    let isEq := fresh in
    destruct (@weq (IdxBits + TagBits) a a') as [isEq | ?]; rewrite ?app_nil_r in *; [rewrite isEq in *; clear isEq | try assumption].

  Lemma eq_weq sz a: (@weq sz a a) = left _ eq_refl.
    Proof.
      rewrite rewrite_weq with (pf := eq_refl).
      reflexivity.
    Qed.

  Ltac destruct_addr :=
    match goal with
      | |- context[@weq (IdxBits + TagBits) ?a ?a] =>
        rewrite (@eq_weq (IdxBits + TagBits) a) in *
      | H: context[@weq (IdxBits + TagBits) ?a ?a] |- _ =>
        rewrite (@eq_weq (IdxBits + TagBits) a) in *
      | |- context[@weq (IdxBits + TagBits) ?a ?a'] =>
        destruct_addr_base a a'
      | H: context[@weq (IdxBits + TagBits) ?a ?a'] |- _ =>
        destruct_addr_base a a'
    end.

    Lemma neq_combine1 sz1 sz2 a p:
      p <> split2 sz1 sz2 a ->
      a = Word.combine (split1 sz1 sz2 a) p -> False.
    Proof.
      intros.
      rewrite H0 in *; clear H0.
      rewrite split2_combine in H.
      tauto.
    Qed.
    
    Lemma neq_combine2 sz1 sz2 a p q:
      split1 sz1 sz2 a <> p ->
      a = Word.combine p q -> False.
    Proof.
      intros.
      rewrite H0 in *; clear H0.
      rewrite split1_combine in H.
      tauto.
    Qed.
    
    Ltac destruct_combine1 tagv a neq' :=
      let isEq'' := fresh in
      destruct (@weq (IdxBits + TagBits) a (Word.combine (split1 IdxBits TagBits a)
                                                         (tagv (split1 IdxBits TagBits a)))) as [isEq'' | ?];
        [apply (@neq_combine1 _ _ _ _ neq') in isEq''; exfalso; apply isEq'' |
         rewrite ?app_nil_r in *
        ].
    
    Ltac destruct_combine2 tagv a a' neq :=
      let isEq'' := fresh in
      destruct (@weq (IdxBits + TagBits) a (Word.combine (split1 IdxBits TagBits a')
                                                         (tagv (split1 IdxBits TagBits a')))) as [isEq'' | ?];
        [apply (@neq_combine2 _ _ _ _ _ neq) in isEq''; exfalso; apply isEq'' |
         rewrite ?app_nil_r in *
        ].
    
    Ltac destruct_idx_tag_base tagv a a' :=
      let isEq := fresh in
      let isEq' := fresh in
      let isEq'' := fresh in
      let neq' := fresh in
      let neq := fresh in
      destruct (@weq IdxBits (split1 IdxBits TagBits a) (split1 IdxBits TagBits a')) as [isEq | neq];
        [destruct (@weq TagBits (tagv (split1 IdxBits TagBits a)) (split2 IdxBits TagBits a)) as [isEq' | neq'];
          rewrite <- ?isEq in *; clear isEq;
          rewrite ?app_nil_r in *;
          [rewrite ?isEq' in *; (* clear isEq'; *) rewrite ?Word.combine_split, ?split1_combine, ?split2_combine, ?eq_weq in * |
           rewrite ?split1_combine, ?split2_combine in *;
           try match goal with
                 | H: context[@weq (IdxBits + TagBits) a (Word.combine (split1 IdxBits TagBits a)
                                                                       (tagv (split1 IdxBits TagBits a)))] |- _ =>
                   destruct_combine1 tagv a neq'
                 | |- context[@weq (IdxBits + TagBits) a (Word.combine (split1 IdxBits TagBits a)
                                                                       (tagv (split1 IdxBits TagBits a)))] =>
                   destruct_combine1 tagv a neq'
               end
          ] |
         rewrite ?split1_combine, ?split2_combine in *;
           try match goal with
                 | H: context[@weq (IdxBits + TagBits) a (Word.combine (split1 IdxBits TagBits a')
                                                                       (tagv (split1 IdxBits TagBits a')))] |- _ =>
                   destruct_combine2 tagv a a' neq
                 | |- context[@weq (IdxBits + TagBits) a (Word.combine (split1 IdxBits TagBits a')
                                                                       (tagv (split1 IdxBits TagBits a')))] =>
                   destruct_combine2 tagv a a' neq
               end].

  Ltac destruct_idx_tag :=
    match goal with
      | |- context[if @weq IdxBits (split1 IdxBits TagBits ?a) (split1 IdxBits TagBits ?a')
                   then if @weq TagBits (?tagv (split1 IdxBits TagBits ?a)) (split2 IdxBits TagBits ?a) then _ else _
                   else _] => destruct_idx_tag_base tagv a a'
      | H: context[if @weq IdxBits (split1 IdxBits TagBits ?a) (split1 IdxBits TagBits ?a')
                   then if @weq TagBits (?tagv (split1 IdxBits TagBits ?a)) (split2 IdxBits TagBits ?a) then _ else _
                   else _] |- _ => destruct_idx_tag_base tagv a a'
    end.

  Lemma getCs_full cs tag a a' upd:
    getCs (fun a'' => if weq a'' (split1 IdxBits TagBits a)
                      then upd
                      else cs a'') tag a' =
    if weq (split1 IdxBits TagBits a') (split1 IdxBits TagBits a)
    then if weq (tag (split1 IdxBits TagBits a')) (split2 IdxBits TagBits a')
         then upd
         else getCs cs tag a'
    else getCs cs tag a'.
  Proof.
    unfold getCs.
    repeat match goal with
             | |- context[if ?p then _ else _] => destruct p; try reflexivity; try congruence
           end.
  Qed.

  Lemma getCs_tag cs tag a a':
    tag (split1 IdxBits TagBits a) = split2 IdxBits TagBits a \/
    cs (split1 IdxBits TagBits a) = WO~0~0 ->
    forall upd,
      getCs
        (fun a'' =>
           if weq a'' (split1 IdxBits TagBits a) then upd else cs a'')
        (fun a'' =>
           if weq a'' (split1 IdxBits TagBits a)
           then split2 IdxBits TagBits a
           else tag a'') a' = if weq a' a then upd else getCs cs tag a'.
  Proof.
    intros.
    unfold getCs.
    repeat match goal with
             | |- context[if ?p then _ else _] => destruct p; try reflexivity
           end.
    - rewrite <- (@Word.combine_split IdxBits TagBits a') in n.
      rewrite <- (@Word.combine_split IdxBits TagBits a) in n.
      rewrite e, e0 in *.
      tauto.
    - rewrite <- (@Word.combine_split IdxBits TagBits a') in n.
      rewrite <- (@Word.combine_split IdxBits TagBits a) in n.
      rewrite e, e0 in *.
      tauto.
    - subst; tauto.
    - tauto.
    - subst.
      rewrite eq_weq in *.
      tauto.
    - match goal with
        | H: context[if ?p then _ else _] |- _ => destruct p
      end.
      + rewrite e0 in *.
        destruct H.
        * rewrite H in *.
          tauto.
        * rewrite H; reflexivity.
      + tauto.
  Qed.

  Ltac rewrite_getCs :=
    match goal with
      | H: ?tag (split1 IdxBits TagBits ?a) = (split2 IdxBits TagBits ?a) |- _ =>
        (rewrite getCs_tag_match_getCs in * by (apply H)); destruct_addr
      | _ => rewrite getCs_tag in * by tauto; destruct_addr
      | _ => rewrite getCs_full in *; try destruct_idx_tag
    end.

  Ltac existentials :=
    repeat match goal with
             | |- (exists x, In x (?ls ++ [?a]) /\ _) \/ _ =>
               left; exists a; rewrite app_or;
               simpl; unfold Lib.VectorFacts.Vector_find; simpl;
               do 2 (intuition idtac; try (discriminate || word_omega))
             | |- _ \/ (exists x, In x (?ls ++ [?a]) /\ _) =>
               right; exists a; rewrite app_or;
               simpl; unfold Lib.VectorFacts.Vector_find; simpl;
               do 2 (intuition idtac; try (discriminate || word_omega))
           end.

  (*
  Hint Rewrite app_or cons_or revcons_or: myLogic.
   *)

  Ltac destruct_cache :=
    match goal with
      | H: context[@weq LgNumChildren ?c ?c] |- _ =>
        rewrite (@eq_weq LgNumChildren c) in *
      | |- context[@weq LgNumChildren ?c ?c] =>
        rewrite (@eq_weq LgNumChildren c) in *
      | H: context[@weq LgNumChildren ?c ?y] |- _ =>
        let isEq := fresh in
        destruct (@weq LgNumChildren c y) as [isEq | ?]; [rewrite isEq in * | try assumption]
      | |- context[@weq LgNumChildren ?c ?y] =>
        let isEq := fresh in
        destruct (@weq LgNumChildren c y) as [isEq | ?]; [rewrite isEq in * | try assumption]
    end.
  
  Ltac helpNormal :=
    autorewrite with invariant in *;
    unfold isCWait, isPWait in *;
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    rmBadHyp.
  (*
    repeat destruct_cache;
    repeat destruct_addr;
    ( assumption || intros).*)
  
  Ltac doNormal :=
    normalInit;
    invariant_simpl;
    simplMapUpds helpNormal.

  Lemma word_help: forall sz n (c: word sz),
                     (S n <= wordToNat (wones sz))%nat ->
                     c < $ (S n) ->
                     c <= $ n.
  Proof.
    intros.
    rewrite wones_pow2_minus_one in H.
    pre_word_omega.
    pose proof (pow2_zero sz).
    rewrite wordToNat_natToWord_2 in *; Omega.omega.
  Qed.

  Lemma word_help2:
    forall sz n (c: word sz),
      (S n <= wordToNat (wones sz))%nat ->
      c <= $ (S n) ->
      c = $ (S n) \/ c <= $ n.
  Proof.
    intros.
    pre_word_omega.
    assert (sth: (wordToNat c = wordToNat (@natToWord sz (S n)) \/(wordToNat c <= wordToNat (@natToWord sz n))%nat) ->
                 (c = $ (S n) \/ c <= $ n)).
    { intros.
      repeat (intuition idtac; word_omega).
    }
    apply sth; clear sth.
    pose proof (pow2_zero sz).
    rewrite wones_pow2_minus_one in H.
    assert (n <= pow2 sz)%nat by Omega.omega.
    rewrite ?wordToNat_natToWord_2 in *; try Omega.omega.
  Qed.
  
  Lemma compatPair':
    forall (rq: <| Struct RqTP |>) c c' dir,
      c' <= $ (wordToNat (wones LgNumChildren)) ->
      evalExpr (MemDir.othersCompat (LgNumChildren := LgNumChildren)
                                    (#c)%kami_expr
                                    (@ReadField _ _ _ F3 (#rq)%kami_expr)
                                    (#dir)%kami_expr) = true ->
      c' <> c ->
      rq F3 <= if weq (dir c') ($ Msi.Mod)
               then $ Msi.Inv
               else if weq (dir c') ($ Msi.Ex)
                    then $ Msi.Sh
                    else if weq (dir c') ($ Msi.Sh)
                         then $ Msi.Ex
                         else $ Msi.Mod.
  Proof.
    unfold MemDir.othersCompat, MemDir.foldInc.
    remember (wordToNat (wones LgNumChildren)).
    assert (n <= wordToNat (wones LgNumChildren))%nat by Omega.omega.
    clear Heqn.
    dependent induction n; auto; simpl; intros.
    - destruct (weq c ($ 0)); simpl in *.
      + word_omega.
      + assert (c' = $ 0) by word_omega; subst.
        repeat match goal with
                 | H: context[weq ?a ?b] |- _ => destruct (weq a b)
                 | H: context[wlt_dec ?a ?b] |- _ => destruct (wlt_dec a b)
               end; simpl in *; try discriminate; try (split; intros; word_omega); try assumption.
    - destruct (weq c ($ (S n))); simpl in *.
      + assert (sth: c' < $ (S n)) by word_omega.
        apply (@word_help _ _ _ H) in sth.
        assert (n <= wordToNat (wones LgNumChildren))%nat by Omega.omega.
        eapply IHn; eassumption.
      + apply word_help2 in H0; try assumption.
        destruct H0; subst.
        * { repeat match goal with
                     | |- context[if ?p then _ else _] => destruct p
                   end.
            - destruct (wlt_dec WO~0~0 (rq F3)); simpl in *; [discriminate | assumption].
            - destruct (wlt_dec WO~0~1 (rq F3)); simpl in *; [discriminate | assumption].
            - destruct (wlt_dec WO~1~0 (rq F3)); simpl in *; [discriminate | assumption].
            - destruct (wlt_dec WO~1~1 (rq F3)); simpl in *; [discriminate | assumption].
          }
        * eapply IHn; try eassumption;
          try Omega.omega.
          apply Bool.andb_true_iff in H1; dest; assumption.
  Qed.

  Lemma compatPair:
    forall (rq: <| Struct RqTP |>) c c' dir,
      evalExpr (MemDir.othersCompat (LgNumChildren := LgNumChildren)
                                    (#c)%kami_expr
                                    (@ReadField _ _ _ F3 (#rq)%kami_expr)
                                    (#dir)%kami_expr) = true ->
      c' <> c ->
      rq F3 <= if weq (dir c') ($ Msi.Mod)
               then $ Msi.Inv
               else if weq (dir c') ($ Msi.Ex)
                    then $ Msi.Sh
                    else if weq (dir c') ($ Msi.Sh)
                         then $ Msi.Ex
                         else $ Msi.Mod.
  Proof.
    intros;
    eapply compatPair'; try eassumption.
    rewrite wones_pow2_minus_one.
    clear; simpl in *.
    pose proof (pow2_zero LgNumChildren).
    pre_word_omega.
    rewrite wordToNat_natToWord_2; try Omega.omega.
    pose proof (wordToNat_bound c').
    Omega.omega.
  Qed.

  Lemma compatPair_sem:
    forall (rq: <| Struct RqTP |>) c dir c',
      c' <> c ->
      semExpr (MemDir.othersCompat (LgNumChildren := LgNumChildren)
                                   (#c)%kami_expr
                                   (@ReadField _ _ _ F3 (#rq)%kami_expr)
                                   (#dir)%kami_expr) eq_refl ->
      rq F3 <= if weq (dir c') ($ Msi.Mod)
               then $ Msi.Inv
               else if weq (dir c') ($ Msi.Ex)
                    then $ Msi.Sh
                    else if weq (dir c') ($ Msi.Sh)
                         then $ Msi.Ex
                         else $ Msi.Mod.
  Proof.
    intros.
    apply semExpr_sound in H0.
    simpl in *.
    eapply compatPair; eassumption.
  Qed.

  Lemma notIn_impl_nil A ls: (forall a: A, ~ In a ls) -> ls = nil.
  Proof.
    induction ls; auto; simpl; intros.
    specialize (H a).
    tauto.
  Qed.

  Lemma beg_mid_last_add_eq2 A ls:
    (forall (v: A) v1 v2 v3 beg mid1 mid2 last,
       ls ++ [v] = beg ++ v1 :: mid1 ++ v2 :: mid2 ++ v3 :: last ->
       (last = nil /\ v = v3 /\ ls = beg ++ v1 :: mid1 ++ v2 :: mid2) \/
       (exists last', last = last' ++ [v] /\ ls = beg ++ v1 :: mid1 ++ v2 :: mid2 ++ v3 :: last'))%list.
  Proof.
    intros.
    rewrite app_comm_cons with (x := mid2) (y := v3 :: last) in H.
    rewrite app_assoc in H.
    apply beg_mid_last_add_eq in H.
    destruct H; dest; subst.
    - left; tauto.
    - right.
      exists x.
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      tauto.
  Qed.
  
  Lemma nmemCache_invariants_hold_05 s a u cs:
    nmemCache_invariants s ->
    deferred is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    time doNormal; try destruct_addr; try destruct_cache; (assumption || intros; try discriminate).
    - clear - i16a i25.
      specialize (i16a (y F2) (or_introl eq_refl)).
      specialize (i25 (y F2) (or_introl eq_refl)).
      dest; word_omega.
    - clear - i5 i7 i25 H1 H5.
      specialize (i25 (y F2) (or_introl eq_refl)).
      specialize (i7 rs H1).
      dest; split; word_omega.
    - clear - i5 i8 i16a i16c i25 H1 H2.
      apply in_app_or in H1.
      destruct H1 as [prev | new].
      + specialize (i16c (y F2) rs (or_introl eq_refl) prev).
        rewrite i16c in *; discriminate.
      + apply in_single in new.
        rewrite new in *; simpl in *; clear new.
        specialize (i25 (y F2) (or_introl eq_refl)).
        specialize (i16a (y F2) (or_introl eq_refl)).
        dest; split; word_omega.
    - exfalso.
      clear - i30 H1.
      specialize (i30 (y F2) _ eq_refl).
      rewrite i30 in H1; apply H1.
    - exfalso.
      clear - n i9 H6 H0 H1 H2.
      apply (@compatPair_sem (y F2) (y F1) (dir (y F2 F1)) ($ c) n) in H6.
      specialize (i9 _ _ H0 H1 H2).
      dest; word_omega.
    - exfalso.
      clear - n i9 H1 H2 H3.
      specialize (i9 _ _ H1 H2 H3).
      dest; tauto.
    - exfalso.
      clear - n i9 H0 H1 H2.
      specialize (i9 _ _ H0 H1 H2).
      dest; tauto.
    - clear - i16c H1 H2 H3.
      apply app_cons_in in H1.
      specialize (i16c (y F2) rs1 (or_introl eq_refl) H1).
      congruence.
    - clear - H2.
      setoid_rewrite app_or in H2.
      specialize (H2 _ (or_intror (or_introl eq_refl))).
      discriminate.
    - clear - i9 H5.
      match type of i9 with
        | forall (rq: ?rqT) (rs: ?rsT), ?P -> ?Q -> ?R -> ?W =>
          assert (sth: forall (rq: rqT), P -> R -> forall (rs: rsT), Q -> False)
            by (intros; eapply i9; try eassumption; tauto); clear i9
      end.
      specialize (sth _ (or_introl eq_refl) H5).
      apply notIn_impl_nil; assumption.
    - clear - i17 H1 H2.
      apply app_cons_in in H1.
      apply i17 in H1; try assumption; dest; try tauto.
    - clear - i16a.
      specialize (i16a _ (or_introl eq_refl)); dest.
      split; [assumption|].
      right.
      match goal with
        | |- exists x, In x (?ls ++ [?v]) /\ _ =>
          exists v; rewrite app_or; simpl; try tauto
      end.
    - clear - i16a H1.
      apply i16a.
      apply (or_intror H1).
    - clear - i16a i16b H1 H2.
      rewrite app_or in H1; destruct H1.
      + apply i16b; assumption.
      + apply in_single in H; subst; simpl in *.
        specialize (i16a _ (or_introl eq_refl)); tauto.
    - exfalso.
      clear - i30 H1.
      specialize (i30 _ _ eq_refl).
      rewrite i30 in H1; simpl in H1; assumption.
    - clear - i17 H1 H2.
      rewrite app_or in H1.
      destruct H1.
      + left; apply i17 in H; tauto.
      + apply in_single in H; subst; simpl in *; discriminate.
    - clear - i17 H0 H1 H5 H6.
      specialize (i17 _ H0 H1).
      destruct i17; [left; assumption|].
      dest.
      apply (@compatPair_sem (y F2) (y F1) (dir (y F2 F1)) ($ c) H4) in H6.
      tauto.
    - clear - i17 H1 H2.
      specialize (i17 _ H1 H2).
      destruct i17; tauto.
    - clear - i17 H0 H1 H5 H6.
      specialize (i17 _ H0 H1).
      destruct i17; [left; assumption|].
      dest; subst.
      apply (@compatPair_sem (y F2) (y F1) (dir (y F2 F1)) ($ c) H4) in H6.
      tauto.
    - clear - i18 H1 H2 H3.
      rewrite app_or in H1.
      destruct H1.
      + eapply i18; eassumption.
      + apply in_single in H; subst; simpl in H3; discriminate.
    - exfalso.
      clear - i19 H1 H2 H3.
      apply beg_mid_last_add_eq in H1.
      destruct H1; dest.
      + subst; simpl in H3; discriminate.
      + specialize (i19 _ _ _ _ _ H0 H2 H3).
        tauto.
    - exfalso.
      clear - H5 H6 i19 H0 H1 H2.
      specialize (i19 _ _ _ _ _ H0 H1 H2).
      dest.
      apply (@compatPair_sem (y F2) (y F1) (dir (y F2 F1)) ($ c) H7) in H6.
      tauto.
    - exfalso.
      clear - i19 H1 H2 H3.
      specialize (i19 _ _ _ _ _ H1 H2 H3).
      tauto.
    - exfalso.
      clear - H5 H6 i19 H0 H1 H2.
      specialize (i19 _ _ _ _ _ H0 H1 H2).
      dest; subst.
      apply (@compatPair_sem (y F2) (y F1) (dir (y F2 F1)) ($ c) H7) in H6.
      tauto.
    - clear -i20 H1 H2 H3.
      apply beg_mid_last_add_eq in H1.
      destruct H1; dest.
      + subst; simpl in H3; discriminate.
      + specialize (i20 _ _ _ _ _ H0 H2 H3).
        tauto.
    - exfalso.
      clear - i9 H1 H5.
      specialize (i9 _ _ (or_introl eq_refl) H1 H5).
      tauto.
    - exfalso.
      clear - H5 H6 i21 H0 H1.
      specialize (@i21 _  H0 H1).
      dest; try subst.
      apply (@compatPair_sem (y F2) (y F1) (dir (y F2 F1)) ($ c) H4) in H6.
      tauto.
    - exfalso.
      clear - i21 H1 H2.
      specialize (@i21 _  H1 H2).
      tauto.
    - exfalso.
      clear - H5 H6 i21 H0 H1.
      specialize (@i21 _  H0 H1).
      dest; try subst.
      apply (@compatPair_sem (y F2) (y F1) (dir (y F2 F1)) ($ c) H4) in H6.
      tauto.
    - exfalso.
      clear - i30 H1.
      specialize (i30 _ _ eq_refl).
      rewrite i30 in H1.
      simpl in H1.
      assumption.
    - exfalso.
      clear - i30 H1.
      specialize (i30 _ _ eq_refl).
      rewrite i30 in H1.
      simpl in H1.
      assumption.
(*    - discriminate.
    - discriminate.
    - discriminate.
    - discriminate. *)
    - exfalso.
      clear - i30 H1.
      specialize (i30 _ _ eq_refl).
      rewrite i30 in H1.
      simpl in H1.
      assumption.
    - exfalso.
      clear - i30 H1.
      specialize (i30 _ _ eq_refl).
      rewrite i30 in H1.
      discriminate.
    - apply beg_mid_last_add_eq2 in H1.
      destruct H1; dest.
      + subst; simpl in H4; discriminate.
      + eapply i31 in H7; eassumption.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma findIncompat_means (rq: type (Struct RqTP)) (c: word LgNumChildren) dir dirw:
    evalExpr (MemDir.findIncompat (#c)%kami_expr (ReadField F3 (#rq)%kami_expr) (#dir)%kami_expr (#dirw)%kami_expr) F1 = true ->
    c <> evalExpr (MemDir.findIncompat (#c)%kami_expr (ReadField F3 (#rq)%kami_expr) (#dir)%kami_expr (#dirw)%kami_expr) F2 /\
    (rq F3 > if weq (dir (evalExpr (MemDir.findIncompat (#c)%kami_expr (ReadField F3 (#rq)%kami_expr)
                                                        (#dir)%kami_expr (#dirw)%kami_expr) F2)) ($ Msi.Mod)
             then $ Msi.Inv
             else if weq (dir (evalExpr (MemDir.findIncompat (#c)%kami_expr (ReadField F3 (#rq)%kami_expr)
                                                             (#dir)%kami_expr (#dirw%kami_expr)) F2)) ($ Msi.Ex)
                  then $ Msi.Sh
                  else if weq (dir (evalExpr (MemDir.findIncompat (#c)%kami_expr (ReadField F3 (#rq)%kami_expr)
                                                                  (#dir)%kami_expr (#dirw%kami_expr)) F2)) ($ Msi.Sh)
                       then $ Msi.Ex
                       else $ Msi.Mod) /\
    dirw (evalExpr (MemDir.findIncompat (#c)%kami_expr (ReadField F3 (#rq)%kami_expr) (#dir)%kami_expr (#dirw)%kami_expr) F2) = false.
  Proof.
    (* SKIP_PROOF_ON
    unfold MemDir.findIncompat, MemDir.foldInc.
    rewrite wones_pow2_minus_one.
    generalize c.
    clear c.
    induction (pow2 LgNumChildren - 1); simpl; unfold Lib.VectorFacts.Vector_find; simpl; auto; intros.
    - destruct (weq c ($ 0)); subst; simpl in *.
      + discriminate.
      + destruct (weq (dir ($ 0)) WO~1~1) as [isEq | ?]; [rewrite ?isEq, ?eq_weq in *|].
        * { destruct (wlt_dec WO~0~0 (rq F3)); simpl in *.
            - case_eq (dirw ($ 0)); intros; simpl in *.
              + rewrite H0 in *; simpl in *.
                discriminate.
              + rewrite H0 in *; simpl in *.
                rewrite isEq, eq_weq in *.
                tauto.
            - discriminate.
          }
        * { destruct (weq (dir ($ 0)) WO~1~0) as [isEq | ?]; [rewrite ?isEq, ?eq_weq in *|].
            - destruct (wlt_dec WO~0~1 (rq F3)); simpl in *.
              + case_eq (dirw ($ 0)); intros; simpl in *.
                * rewrite H0 in *; simpl in *.
                  discriminate.
                * rewrite H0 in *; simpl in *.
                  rewrite isEq, eq_weq in *.
                  tauto.
              + discriminate.
            - { destruct (weq (dir ($ 0)) WO~0~1) as [isEq | ?]; [rewrite ?isEq, ?eq_weq in *|].
                - destruct (wlt_dec WO~1~0 (rq F3)); simpl in *.
                  + case_eq (dirw ($ 0)); intros; simpl in *.
                    * rewrite H0 in *; simpl in *.
                      discriminate.
                    * rewrite H0 in *; simpl in *.
                      rewrite isEq, eq_weq in *.
                      destruct (weq WO~0~1 WO~1~1); tauto.
                  + discriminate.
                - destruct (wlt_dec WO~1~1 (rq F3)) as [isEq | ?]; [rewrite ?isEq, ?eq_weq in *|]; simpl in *.
                  + case_eq (dirw ($ 0)); intros; simpl in *.
                    * rewrite H0 in *; simpl in *.
                      discriminate.
                    * rewrite H0 in *; simpl in *.
                      destruct (weq (dir ($ 0)) WO~1~1), (weq (dir ($ 0)) WO~1~0), (weq (dir ($ 0)) WO~0~1); try tauto.
                  + discriminate.
              }
          }
    - destruct (weq c ($ (S n))); subst; simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      + rewrite ?Bool.andb_false_r, ?Bool.andb_false_l in *.
        specialize (IHn _ H).
        assumption.
      + destruct (weq (dir ($ (S n))) WO~1~1) as [isEq | ?]; [rewrite ?isEq, ?eq_weq in *|].
        * { destruct (wlt_dec WO~0~0 (rq F3)); simpl in *.
            - rewrite ?Bool.andb_true_r, ?Bool.andb_true_l in *.
              case_eq (dirw ($ (S n))); intros; simpl in *.
              + rewrite H0 in *; simpl in *.
                rewrite ?Bool.andb_false_r, ?Bool.andb_false_r in *.
                specialize (IHn _ H).
                assumption.
              + rewrite H0 in *; simpl in *.
                rewrite ?Bool.andb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.andb_true_r in *.
                match type of H with
                  | (if negb ?P then _ else _) F1 = true => case_eq P; intros; simpl in *
                end.
                * specialize (IHn _ H1).
                  assumption.
                * rewrite H1 in *.
                  simpl in *.
                  rewrite isEq, H0, eq_weq in *.
                  tauto.
            - rewrite ?Bool.andb_true_r, ?Bool.andb_true_l, ?Bool.andb_false_l, ?Bool.andb_false_r in *.
              simpl in *.
              specialize (IHn _ H); assumption.
          }
        * { destruct (weq (dir ($ (S n))) WO~1~0) as [isEq | ?]; [rewrite ?isEq, ?eq_weq in *|].
            - destruct (wlt_dec WO~0~1 (rq F3)); simpl in *.
              +  rewrite ?Bool.andb_true_r, ?Bool.andb_true_l in *.
                 case_eq (dirw ($ (S n))); intros; simpl in *.
                 * rewrite H0 in *; simpl in *.
                   rewrite ?Bool.andb_false_r, ?Bool.andb_false_r in *.
                   specialize (IHn _ H).
                   assumption.
                 *  { rewrite H0 in *; simpl in *.
                      rewrite ?Bool.andb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.andb_true_r in *.
                      match type of H with
                        | (if negb ?P then _ else _) F1 = true => case_eq P; intros; simpl in *
                      end.
                      - specialize (IHn _ H1).
                        assumption.
                      - rewrite H1 in *.
                        simpl in *.
                        rewrite isEq, H0, eq_weq in *.
                        tauto.
                    } 
              + rewrite ?Bool.andb_true_r, ?Bool.andb_true_l, ?Bool.andb_false_l, ?Bool.andb_false_r in *.
                simpl in *.
                specialize (IHn _ H); assumption.
            - { destruct (weq (dir ($ (S n))) WO~0~1) as [isEq | ?]; [rewrite ?isEq, ?eq_weq in *|].
                - destruct (wlt_dec WO~1~0 (rq F3)); simpl in *.
                  +  rewrite ?Bool.andb_true_r, ?Bool.andb_true_l in *.
                     case_eq (dirw ($ (S n))); intros; simpl in *.
                     * rewrite H0 in *; simpl in *.
                       rewrite ?Bool.andb_false_r, ?Bool.andb_false_r in *.
                       specialize (IHn _ H).
                       assumption.
                     *  { rewrite H0 in *; simpl in *.
                          rewrite ?Bool.andb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.andb_true_r in *.
                          match type of H with
                            | (if negb ?P then _ else _) F1 = true => case_eq P; intros; simpl in *
                          end.
                          - specialize (IHn _ H1).
                            assumption.
                          - rewrite H1 in *.
                            simpl in *.
                            rewrite isEq, H0, eq_weq in *.
                            tauto.
                        } 
                  + rewrite ?Bool.andb_true_r, ?Bool.andb_true_l, ?Bool.andb_false_l, ?Bool.andb_false_r in *.
                    simpl in *.
                    specialize (IHn _ H); assumption.
                - destruct (wlt_dec WO~1~1 (rq F3)); simpl in *.
                  +  rewrite ?Bool.andb_true_r, ?Bool.andb_true_l in *.
                     case_eq (dirw ($ (S n))); intros; simpl in *.
                     * rewrite H0 in *; simpl in *.
                       rewrite ?Bool.andb_false_r, ?Bool.andb_false_r in *.
                       specialize (IHn _ H).
                       assumption.
                     *  { rewrite H0 in *; simpl in *.
                          rewrite ?Bool.andb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.andb_true_r in *.
                          match type of H with
                            | (if negb ?P then _ else _) F1 = true => case_eq P; intros; simpl in *
                          end.
                          - specialize (IHn _ H1).
                            assumption.
                          - rewrite H1 in *.
                            simpl in *.
                            rewrite ?isEq, ?H0, ?eq_weq in *.
                            destruct (weq (dir $ (S n)) WO~1~1); try tauto.
                            destruct (weq (dir $ (S n)) WO~1~0); try tauto.
                            destruct (weq (dir $ (S n)) WO~0~1); try tauto.
                        }
                  + rewrite ?Bool.andb_true_r, ?Bool.andb_true_l, ?Bool.andb_false_l, ?Bool.andb_false_r in *.
                    simpl in *.
                    specialize (IHn _ H); assumption.
              }
          }
  Qed.

  Lemma evalE K (e: K@type): evalExpr (#(evalExpr e)%kami_expr) = evalExpr e.
  Proof.
    dependent induction e; simpl in *; auto.
  Qed.

  
  Lemma nmemCache_invariants_hold_02 s a u cs:
    nmemCache_invariants s ->
    dwnRq is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    time (doNormal;
          match goal with
            | H: evalExpr (MemDir.findIncompat (?c) (ReadField F3 (?rq)) (?dir) (?dirw)) F1 = true |- _ =>
              apply findIncompat_means in H;
            destruct H as [? [? ?]]
          end;
          repeat destruct_cache;
          try match goal with
                | H: ?y F1 = evalExpr ?c F2 |- _ =>
                  rewrite <- ?H in *
              end;
          try match goal with
                | H: ?x = ?y, H': ?x <> ?y |- _ => exfalso; apply (H' H)
              end;
          repeat destruct_addr;
          try match goal with
                | H: context[evalExpr ?c F2] |- _ =>
                  let x := fresh "x" in
                  let Heqx := fresh "Heqx" in
                  remember (evalExpr c F2) as x eqn:Heqx in *
              end;
          unfold MemDir.Child, Child, MemDir.Dir, MemDir.Dirw, RqToP, Msi in *;
            simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
            rewrite <- ?Heqx in *;
            (assumption || intros)).
    - clear - i8 H4 H5.
      rewrite app_or in H4.
      destruct H4.
      + apply i8; assumption.
      + apply in_single in H; subst; simpl in *; discriminate.
    - clear - i9 H4 H5 H6.
      specialize (i9 _ _ H4 H5 H6).      
      tauto.
    - clear - i10 H4 H5 H6.
      apply beg_mid_last_add_eq in H4.
      destruct H4; dest; subst.
      + discriminate.
      + eapply i10; eassumption.
    - clear -i11 H4 H5.
      apply (i11 H4).
      intros.
      setoid_rewrite app_or in H5.
      specialize (H5 msg (or_introl H)).
      assumption.
    - clear - i12 H4 H5.
      rewrite app_or in H4.
      destruct H4 as [ez | hard].
      + eapply i12; eassumption.
      + apply in_single in hard; subst; simpl in *; discriminate.
    - clear - i15 H4 H5 H6.
      apply beg_mid_last_add_eq in H4.
      destruct H4; dest; subst.
      + discriminate.
      + eapply i15; eassumption.
    - clear - i16 H4.
      setoid_rewrite app_or.
      setoid_rewrite app_or in i16.
      specialize (i16 H4).
      destruct i16 as [ez [hard1 | hard2]].
      + split; [assumption | left].
        assumption.
      + split; [assumption | right].
        dest.
        unfold fromPToC.
        setoid_rewrite app_or.
        exists x0; tauto.
    - clear - i16b H4 H5.
      rewrite app_or in H4.
      destruct H4 as [ez | hard].
      + eapply i16b; eassumption.
      + apply in_single in hard; subst; simpl in H5; discriminate.
    - clear - i16c H4 H5.
      rewrite app_or in H5.
      destruct H5 as [ez | hard].
      + eapply i16c; eassumption.
      + apply in_single in hard.
        subst.
        reflexivity.
    - clear - n H1.
      tauto.
    - clear - i17 H4 H5.
      specialize (i17 _ H4 H5).
      tauto.
    - clear - i21 i26 H2 H5.
      specialize (i21 _ H5).
      specialize (i26 _ H5).
      destruct (rs F4).
      + tauto.
      + specialize (i21 eq_refl); dest; rewrite H2 in *; discriminate.
    - clear - n H1.
      tauto.
    - clear - i19 H4 H5 H6.
      specialize (i19 _ _ _ _ _ H4 H5 H6).
      tauto.
    - clear - H2 i17 H4 H5 H6.
      apply app_cons_in in H4.
      specialize (i17 _ H4 H5).
      destruct i17; [assumption | dest; rewrite H2 in *; discriminate].
    - clear - i21 H4 H5.
      specialize (i21 _ H4 H5); tauto.
    - apply beg_mid_last_add_eq2 in H4.
      destruct H4; dest.
      + specialize (i19 _ _ _ _ _ H9).
        specialize (i19 H5 H6).
        dest.
        congruence.
      + eapply i31 in H7; eassumption.
        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma beg_last_in A ls: forall v: A, In v ls -> exists beg last, ls = beg ++ v :: last.
  Proof.
    induction ls; simpl; auto; try tauto; intros.
    destruct H; subst.
    - exists nil, ls.
      rewrite app_nil_l.
      reflexivity.
    - specialize (IHls _ H).
      destruct IHls as [beg [last pf]].
      exists (a :: beg), last; simpl.
      rewrite pf.
      reflexivity.
  Qed.
    
  Lemma beg_mid_last_cons A ls: forall v1 v2: A, In v2 ls ->
                                                 exists mid last,
                                                   v1 :: ls = nil ++ v1 :: mid ++ v2 :: last.
  Proof.
    intros.
    apply beg_last_in in H.
    destruct H as [beg [last pf]].
    exists beg, last.
    simpl.
    rewrite pf.
    reflexivity.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.
      
  Lemma nmemCache_invariants_hold_03 s a u cs:
    nmemCache_invariants s ->
    dwnRs_noWait is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    time (doNormal;
          repeat destruct_addr;
          repeat destruct_cache;
          (assumption || intros)).
    - clear - i7.
      specialize (i7 _ (or_introl eq_refl)).
      destruct i7; assumption.
    - clear - i7 i13 H2.
      specialize (i7 _ (or_intror H2)).
      rsLessTo_thms.
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      specialize (H0 _ H2).
      tauto.
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - clear - i13 i21 i26 i28 H2 H3 H4 H5.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      specialize (i21 _ (or_introl eq_refl) sth1).
      dest.
      specialize (i28 H6).
      rewrite i28 in *.
      dest.
      specialize (H5 (conj H6 (eq_sym H8))).
      exfalso.
      assumption.
    - clear - i14 H2.
      rewrite H2 in i14.
      specialize (i14 nil (y F2)).
      simpl in i14.
      apply (i14 eq_refl).
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - rsLessTo_thms; assumption.
    - clear - i14 H2.
      specialize (i14 (y F2 :: beg) rs).
      simpl in i14.
      specialize (i14 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i17 i28 H2 H3 H5.
      specialize (i17 _ H2 H3).
      destruct i17; [left; assumption|].
      dest.
      specialize (i28 H).
      rewrite i28 in *.
      dest.
      specialize (H5 (conj H (eq_sym H1))).
      exfalso; assumption.
    - clear - i18 H2 H3 H4.
      specialize (i18 _ _ H2 (or_intror H3) H4).
      assumption.
    - clear - i19 i28 H2 H3 H4 H5.
      specialize (i19 _ _ _ _ _ H2 H3 H4).
      dest.
      specialize (i28 H).
      rewrite i28 in *.
      dest.
      specialize (H5 (conj H (eq_sym H1))).
      exfalso; assumption.
    - clear - i21 i28 H2 H3 H5.
      exfalso.
      specialize (i21 _ (or_intror H2) H3).
      dest.
      specialize (i28 H).
      rewrite i28 in *.
      dest.
      specialize (H5 (conj H (eq_sym H1))).
      assumption.
    - clear - i22 H2.
      specialize (i22 (y F2 :: beg) mid last cToPRs1 cToPRs2).
      simpl in i22.
      specialize (i22 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i13 i21 i22 i26 i28 H2 H3 H4 H5.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      specialize (i21 _ (or_introl eq_refl) sth1).
      dest.
      specialize (i28 H6).
      rewrite i28 in *.
      dest.
      specialize (H5 (conj H6 (eq_sym H8))).
      exfalso.
      assumption.
    - clear - i26 H2 H3.
      specialize (i26 _ (or_intror H2) H3).
      assumption.
    - clear - i29 H2 H3 H4.
      specialize (i29 _ _ H2 (or_intror H3) H4).
      assumption.
    - clear - i7.
      specialize (i7 _ (or_introl eq_refl)).
      destruct i7; assumption.
    - clear - i7 i13 H2.
      specialize (i7 _ (or_intror H2)).
      rsLessTo_thms.
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      specialize (H0 _ H2).
      tauto.
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - clear - i13 i21 i26 i28 H2 H3 H4 H5.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      specialize (i21 _ (or_introl eq_refl) sth1).
      dest.
      specialize (i28 H6).
      rewrite i28 in *.
      dest.
      specialize (H4 (conj H6 (eq_sym H8))).
      exfalso.
      assumption.
    - clear - i14 H2.
      rewrite H2 in i14.
      specialize (i14 nil (y F2)).
      simpl in i14.
      apply (i14 eq_refl).
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - rsLessTo_thms; assumption.
    - clear - i14 H2.
      specialize (i14 (y F2 :: beg) rs).
      simpl in i14.
      specialize (i14 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i17 i28 H2 H3 H4.
      specialize (i17 _ H2 H3).
      destruct i17; [left; assumption|].
      dest.
      specialize (i28 H).
      rewrite i28 in *.
      dest.
      specialize (H4 (conj H (eq_sym H1))).
      exfalso; assumption.
    - clear - i18 H2 H3 H5.
      specialize (i18 _ _ H2 (or_intror H3) H5).
      assumption.
    - clear - i19 i28 H2 H3 H4 H5.
      specialize (i19 _ _ _ _ _ H2 H3 H5).
      dest.
      specialize (i28 H).
      rewrite i28 in *.
      dest.
      specialize (H4 (conj H (eq_sym H1))).
      exfalso; assumption.
    - clear - i21 i28 H2 H3 H4.
      exfalso.
      specialize (i21 _ (or_intror H2) H3).
      dest.
      specialize (i28 H).
      rewrite i28 in *.
      dest.
      specialize (H4 (conj H (eq_sym H1))).
      assumption.
    - clear - i22 H2.
      specialize (i22 (y F2 :: beg) mid last cToPRs1 cToPRs2).
      simpl in i22.
      specialize (i22 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i13 i21 i22 i26 i28 H2 H3 H4 H5.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      specialize (i21 _ (or_introl eq_refl) sth1).
      dest.
      specialize (i28 H6).
      rewrite i28 in *.
      dest.
      specialize (H4 (conj H6 (eq_sym H8))).
      exfalso.
      assumption.
    - clear - i26 H2 H3.
      specialize (i26 _ (or_intror H2) H3).
      assumption.
    - clear - i29 H2 H3 H5.
      specialize (i29 _ _ H2 (or_intror H3) H5).
      assumption.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.


  Lemma beg_mid_last_in A ls: forall beg last (a: A), ls = beg ++ a :: last -> In a ls.
  Proof.
    induction ls; simpl; auto; intros.
    - apply app_cons_not_nil in H; exfalso; assumption.
    - destruct beg; simpl in *.
      + inv H.
        tauto.
      + inv H.
        right; eapply IHls; eauto.
  Qed.

  Lemma beg_mid_last_in2 A ls: forall beg mid last (a1 a2: A), ls = beg ++ a1 :: mid ++ a2 :: last -> In a1 ls /\ In a2 ls.
  Proof.
    intros.
    pose proof (@beg_mid_last_in _ _ _ _ _ H).
    assert (sth: (beg ++ a1 :: mid) ++ a2 :: last = beg ++ a1 :: mid ++ a2 :: last) by
        (rewrite <- app_assoc; simpl; reflexivity).
    rewrite <- sth in H.
    pose proof (@beg_mid_last_in _ _ _ _ _ H).
    tauto.
  Qed.

  
  Lemma nmemCache_invariants_hold_04 s a u cs:
    nmemCache_invariants s ->
    dwnRs_wait is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    time (doNormal;
          repeat destruct_addr;
          repeat destruct_cache;
          (assumption || intros)).
    - clear - i7.
      specialize (i7 _ (or_introl eq_refl)).
      destruct i7; assumption.
    - clear - i7 i13 H2.
      specialize (i7 _ (or_intror H2)).
      rsLessTo_thms.
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      specialize (H0 _ H2).
      tauto.
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - exfalso.
      clear - i13 i22 i26 i29 H2 H3 H4.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      pose proof (@beg_mid_last_cons _ _ (y F2) rs H3) as sth2.
      dest.
      specialize (@i22 _ _ _ _ _ H5).
      destruct i22 as [isEq | isEq1]; [rewrite isEq in *; discriminate|].
      specialize (i29 _ _ H2 (or_intror H3) isEq1).
      word_omega.
    - exfalso.
      clear - i9 i28 H7 n H2 H3 H4.
      specialize (i9 _ _ H2 H3 H4).
      specialize (i28 eq_refl).
      rewrite i28 in i9.
      dest.
      congruence.
    - clear - i14 H2.
      rewrite H2 in i14.
      specialize (i14 nil (y F2)).
      simpl in i14.
      apply (i14 eq_refl).
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - rsLessTo_thms; assumption.
    - clear - i14 H2.
      specialize (i14 (y F2 :: beg) rs).
      simpl in i14.
      specialize (i14 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i7 i18 H2 H3.
      left.
      specialize (i18 _ _ H2 (or_introl eq_refl) H3).
      specialize (i7 _ (or_introl eq_refl)).
      dest.
      word_omega.
    - clear - i17 i28 n H2 H3 H7.
      specialize (i28 eq_refl).
      specialize (i17 _ H2 H3).
      rewrite i28 in *.
      rewrite <- H7 in n.
      tauto.
    - clear - i18 H2 H3 H4.
      specialize (i18 _ _ H2 (or_intror H3) H4).
      assumption.
    - exfalso.
      clear - i12 H2 H3.
      apply beg_mid_last_in in H2.
      specialize (i12 _ H2 H3).
      discriminate.
    - clear - i19 i28 H7 n H2 H3 H4.
      specialize (i19 _ _ _ _ _ H2 H3 H4).
      specialize (i28 eq_refl).
      rewrite i28 in *.
      dest.
      congruence.
    - exfalso.
      clear - i13 i22 i26 H2 H3.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H2).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      pose proof (@beg_mid_last_cons _ _ (y F2) rs H2) as sth2.
      dest.
      specialize (@i22 _ _ _ _ _ H4).
      destruct i22 as [isEq | isEq1]; [rewrite isEq in *; discriminate|].
      congruence.
    - clear - i21 i28 n H7 H2 H3.
      specialize (i28 eq_refl).
      specialize (i21 _ H2 H3).
      rewrite i28 in i21.
      rewrite <- H7 in n; tauto.
    - clear - i22 H2.
      specialize (i22 (y F2 :: beg) mid last cToPRs1 cToPRs2).
      simpl in i22.
      specialize (i22 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i13 i22 i26 i29 H2 H3 H4.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      pose proof (@beg_mid_last_cons _ _ (y F2) rs H3) as sth2.
      dest.
      specialize (@i22 _ _ _ _ _ H5).
      destruct i22 as [isEq | isEq1]; [rewrite isEq in *; discriminate|].
      specialize (i29 _ _ H2 (or_intror H3) isEq1).
      word_omega.
    - clear - i26 H2 H3.
      specialize (i26 _ (or_intror H2) H3).
      assumption.
    - clear - i29 H2 H3 H4.
      specialize (i29 _ _ H2 (or_intror H3) H4).
      assumption.


    - clear - i7.
      specialize (i7 _ (or_introl eq_refl)).
      destruct i7; assumption.
    - clear - i7 i13 H2.
      specialize (i7 _ (or_intror H2)).
      rsLessTo_thms.
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      specialize (H0 _ H2).
      tauto.
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - exfalso.
      clear - i13 i22 i26 i29 H2 H3 H4.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      pose proof (@beg_mid_last_cons _ _ (y F2) rs H3) as sth2.
      dest.
      specialize (@i22 _ _ _ _ _ H5).
      destruct i22 as [isEq | isEq1]; [rewrite isEq in *; discriminate|].
      specialize (i29 _ _ H2 (or_intror H3) isEq1).
      word_omega.
    - exfalso.
      clear - i9 i28 H6 n H2 H3 H4.
      specialize (i9 _ _ H2 H3 H4).
      specialize (i28 eq_refl).
      rewrite i28 in i9.
      dest.
      congruence.
    - clear - i14 H2.
      rewrite H2 in i14.
      specialize (i14 nil (y F2)).
      simpl in i14.
      apply (i14 eq_refl).
    - clear - i12 H2 H3.
      specialize (i12 _ H2 H3).
      discriminate.
    - rsLessTo_thms; assumption.
    - clear - i14 H2.
      specialize (i14 (y F2 :: beg) rs).
      simpl in i14.
      specialize (i14 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i7 i18 H2 H3.
      left.
      specialize (i18 _ _ H2 (or_introl eq_refl) H3).
      specialize (i7 _ (or_introl eq_refl)).
      dest.
      word_omega.
    - clear - i17 i28 n H2 H3 H6.
      specialize (i28 eq_refl).
      specialize (i17 _ H2 H3).
      rewrite i28 in *.
      rewrite <- H6 in n.
      tauto.
    - clear - i18 H2 H3 H4.
      specialize (i18 _ _ H2 (or_intror H3) H4).
      assumption.
    - exfalso.
      clear - i12 H2 H3.
      apply beg_mid_last_in in H2.
      specialize (i12 _ H2 H3).
      discriminate.
    - clear - i19 i28 H6 n H2 H3 H4.
      specialize (i19 _ _ _ _ _ H2 H3 H4).
      specialize (i28 eq_refl).
      rewrite i28 in *.
      dest.
      congruence.
    - exfalso.
      clear - i13 i22 i26 H2 H3.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H2).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      pose proof (@beg_mid_last_cons _ _ (y F2) rs H2) as sth2.
      dest.
      specialize (@i22 _ _ _ _ _ H4).
      destruct i22 as [isEq | isEq1]; [rewrite isEq in *; discriminate|].
      congruence.
    - clear - i21 i28 n H6 H2 H3.
      specialize (i28 eq_refl).
      specialize (i21 _ H2 H3).
      rewrite i28 in i21.
      rewrite <- H6 in n; tauto.
    - clear - i22 H2.
      specialize (i22 (y F2 :: beg) mid last cToPRs1 cToPRs2).
      simpl in i22.
      specialize (i22 (f_equal (cons (y F2)) H2)).
      assumption.
    - clear - i13 i22 i26 i29 H2 H3 H4.
      rsLessTo_thms.
      specialize (i26 _ (or_introl eq_refl)).
      specialize (H0 _ H3).
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
      assert (sth1: y F2 F4 = false) by 
          (destruct (y F2 F4); [specialize (i26 eq_refl); rewrite i26 in H0; word_omega|reflexivity]).
      pose proof (@beg_mid_last_cons _ _ (y F2) rs H3) as sth2.
      dest.
      specialize (@i22 _ _ _ _ _ H5).
      destruct i22 as [isEq | isEq1]; [rewrite isEq in *; discriminate|].
      specialize (i29 _ _ H2 (or_intror H3) isEq1).
      word_omega.
    - clear - i26 H2 H3.
      specialize (i26 _ (or_intror H2) H3).
      assumption.
    - clear - i29 H2 H3 H4.
      specialize (i29 _ _ H2 (or_intror H3) H4).
      assumption.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma nmemCache_invariants_hold_01 s a u cs:
    nmemCache_invariants s ->
    missByState is a ->
    SemAction s a
              u cs WO ->
    nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    time (doNormal;
          repeat destruct_cache;
          repeat destruct_addr;
          (assumption || intros)).
    - clear - i9 H1 H2 H3.
      specialize (i9 _ _ H1 H2 H3).
      tauto.
    - clear - i9 H1 H2 H3.
      specialize (i9 _ _ H1 H2 H3).
      tauto.
    - clear - i9 H0 H1 H2.
      specialize (i9 _ _ H0 H1 H2).
      dest; discriminate.
    - clear - i17 H1 H2.
      specialize (i17 _ H1 H2).
      destruct i17; dest; [left; assumption | discriminate].
    - clear - i17 H1 H2.
      specialize (i17 _ H1 H2).
      destruct i17; dest; [left; assumption | discriminate].
    - clear - i17 H0 H1.
      specialize (i17 _ H0 H1).
      destruct i17; dest; [left; assumption | discriminate].
    - clear - i19 H1 H2 H3.
      specialize (i19 _ _ _ _ _ H1 H2 H3).
      dest; discriminate.
    - clear - i19 H1 H2 H3.
      specialize (i19 _ _ _ _ _ H1 H2 H3).
      dest; discriminate.
    - clear - i19 H0 H1 H2.
      specialize (i19 _ _ _ _ _ H0 H1 H2).
      dest; discriminate.
    - clear - i21 H1 H2.
      specialize (i21 _ H1 H2).
      dest; discriminate.
    - clear - i21 H1 H2.
      specialize (i21 _ H1 H2).
      dest; discriminate.
    - clear - i21 H0 H1.
      specialize (i21 _ H0 H1).
      dest; discriminate.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.







  

  Ltac metaInit :=
    intros HInd HInRule x xcond HS;
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule;
    apply invSome in HInRule;
    apply invRepRule in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ?; destructRules c HInd.

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

  
  Lemma eq_split sz1 sz2 a b:
    Word.combine (split1 sz1 sz2 a) b = a ->
    b = split2 sz1 sz2 a.
  Proof.
    intros.
    pose proof (f_equal (split2 sz1 sz2) H).
    rewrite split2_combine in H0.
    assumption.
  Qed.
  
  
  Ltac simpl_hyps :=
    repeat match goal with
             | H: exists x, _ |- _ => destruct H
             | H: ?P /\ ?Q |- _ => destruct H
             | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
             | H: ?P -> _, H': ?P |- _ =>
               match type of P with
                 | Prop => specialize (H H')
               end
             | H: Word.combine (split1 ?sz1 ?sz2 ?a) ?b = ?a |- _ =>
               apply (@eq_split sz1 sz2 a b) in H
             | H: ?P \/ ?Q |- _ => destruct H
             | H: In _ nil |- _ => exfalso; apply (@in_nil _ _ H)
             | H: ?x ++ ?a :: ?y = nil |- _ => exfalso; apply eq_sym in H; apply (@app_cons_not_nil _ x y a H)
             | H: ?ls1 ++ (?v1 :: nil) = ?ls2 ++ (?v2 :: nil) |- _ =>
               apply app_single_r in H;
                 let eq1 := fresh in
                 let eq2 := fresh in
                 destruct H as [eq1 eq2];
                   rewrite <- ?eq1 in *;
                   rewrite <- ?eq2 in *;
                   simpl in *
             | H: In ?x (?a :: nil) |- _ =>
               apply in_single in H
             | [H: forall (beg: ?begT) (v: ?vT),
                    ?beg' ++ (?v' :: nil) = beg ++ (v :: nil) -> _ |- _] =>
               specialize (H beg' v' eq_refl)
             | H: rsLessTo ?ls |- rsLessTo (?ls ++ [?rs])%list =>
               apply (@rsLessTo_app ls rs H);
                 let beg := fresh in
                 let last := fresh in
                 let hyp := fresh in
                 intros beg last hyp;
                   simpl in beg, last, hyp; unfold Lib.VectorFacts.Vector_find in beg, last, hyp;
                   simpl in beg, last, hyp;
                   simpl; unfold Lib.VectorFacts.Vector_find; simpl;
                   rewrite hyp in *
(*             | H: In ?x (?l1 ++ ?l2) -> _ |- _ => rewrite app_or in H
             | H: In ?x (?v :: ?l) -> _ |- _ => rewrite cons_or in H
             | H: ?P \/ ?Q -> ?R |- _ => apply (@rmDisj P Q R) in H; destruct H *)
           end.
  
  Ltac rmBadHyp2 :=
    repeat match goal with
             | H: ?v = ?v |- _ => clear H
             | H: true = false -> _ |- _ => clear H
             | H: false = true -> _ |- _ => clear H
             | H: In _ _ -> _ |- _ => clear H
             | H: forall (x: (forall i: Fin.t ?n, _ ?ls)), _ |- _ => 
               clear H
             | H: forall (x: (list (forall i: Fin.t ?n, _ ?ls))), _ |- _ => 
               clear H
           end.

  Ltac rewriteEq :=
    repeat match goal with
             | H: ?a = ?b |- _ => rewrite H in *; generalize H; clear H
           end; intros; simpl in *.

  
  Hint Rewrite app_or cons_or revcons_or: myLogic.


  Ltac doAll :=
    autorewrite with invariant in *;
    unfold isCWait, isPWait in *;
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    rmBadHyp;
    try rewrite_getCs;
    try destruct_addr;
    rewrite ?split1_combine, ?split2_combine in *;
    ( assumption ||
                 ( intros;
                   rsLessTo_thms;
                   simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
                   specialize_msgs;
                   specialize_beg_mid_last;
                   autorewrite with myLogic in *;
                     rewriteEq;
                   simpl_hyps;
                   rewriteEq;
                   rmBadHyp2;
                   try rewrite getCs_cs in * by (rewrite ?split1_combine, ?split2_combine; tauto);
                   rewrite ?split1_combine, ?split2_combine in *;
                   try (intuition (discriminate || word_omega));
                   try match goal with
                         | |- context[if ?p then _ else _] =>
                           let isEq := fresh in
                           let nEq := fresh in
                           destruct p as [isEq | nEq];
                         [rewrite ?isEq in *|]; intuition (try (discriminate || word_omega))
                       end;
                   existentials;
                   try (firstorder (discriminate || word_omega)))).
  
  Ltac doMetaComplex :=
    metaInit;
      try match goal with
            | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
          end; invariant_simpl;
      simplMapUpds ltac:(try (solve [doAll])).

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


  Local Notation "n 'metaIs' a" :=
    (getMetaRules n
                  (metaRules (nmemCacheInl IdxBits TagBits
                                           LgNumDatas DataBytes Id LgNumChildren))
     = Some (RepRule string_of_nat string_of_nat_into
                     (natToWordConst LgNumChildren) withIndex_index_eq a
                     {| nameVal := n;
                        goodName := eq_refl |}
                     (getNatListToN_NoDup (wordToNat (wones LgNumChildren))))) (at level 0).

  Lemma hd_error_some_impl_In A ls: forall a: A, Some a = hd_error ls -> In a ls.
  Proof.
    intros.
    destruct ls; simpl in *.
    - discriminate.
    - inv H; tauto.
  Qed.

  Lemma hd_error_some_rewrite A ls: forall a: A, Some a = hd_error ls -> exists tl, ls = a :: tl.
  Proof.
    intros.
    destruct ls; simpl in *.
    - discriminate.
    - inv H.
      exists ls; reflexivity.
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
    (* SKIP_PROOF_ON
    doMetaComplex.
    END_SKIP_PROOF_ON *) apply cheat.
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
    (* SKIP_PROOF_ON
    doMetaComplex.
    END_SKIP_PROOF_ON *) apply cheat.
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
    (* SKIP_PROOF_ON
    doMetaComplex.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma nmemCache_invariants_hold_4 s a u cs:
    nmemCache_invariants s ->
    writeback metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    doMetaComplex.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma nmemCache_invariants_hold_7 s a u cs:
    nmemCache_invariants s ->
    ld metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    doMetaComplex.
    END_SKIP_PROOF_ON *) apply cheat.
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
    (* SKIP_PROOF_ON
    doMetaComplex.
    END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Ltac doMeta :=
    metaInit;
    try match goal with
          | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
        end;
    invariant_simpl;
    simplMapUpds helpNormal.
  
  Lemma nmemCache_invariants_hold_9 s a u cs:
    nmemCache_invariants s ->
    drop metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    time (doMeta; repeat destruct_cache; repeat destruct_addr; (assumption || intros)).
    - clear - i8 H0 H1.
      specialize (i8 _ (or_intror H0) H1).
      assumption.
    - clear - i10 H0 H1 H3.
      specialize (i10 (y :: beg) mid last rs1 rs2).
      simpl in i10.
      specialize (i10 (f_equal (cons y) H0)).
      tauto.
    - clear - i11 H0 H1 H2.
      apply i11; try assumption.
      intros.
      simpl in H.
      destruct H; subst; [assumption |].
      apply H1; assumption.
    - clear - i12 H0 H1.
      apply i12 with (rs := rs); try assumption.
      simpl.
      right; assumption.
    - clear - i15 H0 H1 H3.
      specialize (i15 (y :: beg) mid last rq rs).
      simpl in i15.
      specialize (i15 (f_equal (cons y) H0)).
      tauto.
    - clear - i16 H0 H2.
      specialize (i16 H0).
      destruct i16 as [sth1 sth2].
      split; [assumption |].
      destruct sth2 as [case_rq | case_rs].
      + left; assumption.
      + right; dest.
        exists x0.
        simpl in H3.
        destruct H3; [congruence | tauto].
    - clear - i16b H0 H1.
      specialize (i16b _ (or_intror H0) H1).
      assumption.
    - clear - i16c H0 H1.
      specialize (i16c _ _ H0 (or_intror H1)).
      assumption.
    - clear - i17 H0 H1.
      specialize (i17 _ (or_intror H0) H1).
      assumption.
    - clear - i18 H0 H1 H3.
      specialize (i18 _ _ (or_intror H0) H1 H3).
      assumption.
    - clear - i19 H0 H1 H3.
      specialize (i19 (y :: beg) mid last rq rs).
      simpl in i19.
      specialize (i19 (f_equal (cons y) H0) H1 H3).
      assumption.
    - clear - i20 H0 H1 H3.
      specialize (i20 (y :: beg) mid last rq1 rq2).
      simpl in i20.
      specialize (i20 (f_equal (cons y) H0) H1 H3).
      assumption.
    - specialize (i31 (y :: beg) mid1 mid2 last rs rq1 rq2).
      simpl in i31.
      specialize (i31 (f_equal (cons y) H0) H1 H3 H4).
      assumption.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.
      
  Lemma rsLessTo_in_app ls:
    forall rs: type (Struct RsTP),
      rsLessTo ls ->
      (forall x, In x ls -> x (RsTP!!to) > rs (RsTP!!to)) ->
      rsLessTo (ls ++ [rs]).
  Proof.
    intros.
    apply rsLessTo_app; try assumption; intros.
    subst.
    apply H0.
    rewrite app_or.
    right.
    simpl.
    tauto.
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
    (* SKIP_PROOF_ON
    time (doMeta; repeat destruct_cache; try rewrite_getCs; try rewrite getCs_cs in * by tauto;
          repeat destruct_addr; (assumption || intros)).
    - word_omega.
    - rewrite app_or in H0.
      destruct H0 as [ez | hard].
      + specialize (i7 _ ez); dest; split; word_omega.
      + apply in_single in hard.
        subst.
        simpl in *.
        dest; split; word_omega.
    - specialize (i8 _ (or_intror H0) H1).
      dest; split; word_omega.
    - specialize (i17 _ (or_introl eq_refl) H2).
      destruct i17 as [c1 | c2]; [rewrite getCs_cs in c1 by tauto; word_omega | try assumption].
    - specialize (i10 (y :: beg) mid last rs1 rs2).
      simpl in i10.
      specialize (i10 (f_equal (cons y) H0) H1 H3).
      assumption.
    - apply eq_sym in H0.
      apply app_cons_not_nil in H0.
      exfalso; assumption.
    - exfalso.
      apply beg_mid_last_cons with (v1 := y) in H0.
      dest.
      specialize (i15 _ _ _ _ _ H0 H2 H1).
      rewrite getCs_cs in i15 by tauto.
      word_omega.
    - apply rsLessTo_in_app; try assumption.
      simpl; unfold Lib.VectorFacts.Vector_find; simpl.
      intros.
      specialize (i7 _ H0); destruct i7 as [c1 c2].
      rewrite getCs_cs in c1 by tauto.
      word_omega.
    - apply app_single_r in H0; destruct H0 as [m1 m2].
      subst; simpl; reflexivity.
    - specialize (i15 (y :: beg) mid last rq rs).
      simpl in i15.
      specialize (i15 (f_equal (cons y) H0) H1 H3).
      word_omega.
    - specialize (i16 H0).
      destruct i16 as [u1 e12].
      split; [word_omega|].
      destruct e12 as [e1 | e2]; dest.
      + left; exists x0; intuition word_omega.
      + right; exists x0.
        simpl in H4.
        destruct H4; simpl in H4; subst; [congruence | ].
        intuition word_omega.
    - specialize (i16a _ H0).
      intuition word_omega.
    - specialize (i16b _ (or_intror H0) H1).
      intuition word_omega.
    - specialize (i16c _ _ H0 (or_intror H1)).
      assumption.
    - specialize (i17 _ (or_intror H0) H1).
      intuition word_omega.
    - apply beg_mid_last_cons with (v1 := y) in H0.
      destruct H0 as [mid [last pf]].
      specialize (i20 _ _ _ _ _ pf H2 H3).
      rewrite getCs_cs in i20 by tauto.
      apply app_or in H1; destruct H1 as [ez | hard]; [| apply in_single in hard; subst].
      + specialize (i18 _ _ (or_introl eq_refl) ez H2); assumption.
      + word_omega.
    - specialize (i19 (y :: beg) mid last rq rs).
      simpl in i19.
      specialize (i19 (f_equal (cons y) H0) H1 H3).
      assumption.
    - specialize (i20 (y :: beg) mid last rq1 rq2).
      simpl in i20.
      specialize (i20 (f_equal (cons y) H0) H1 H3).
      word_omega.
    - specialize (i17 _ (or_introl eq_refl) H2).
      rewrite getCs_cs in i17 by tauto.
      intuition word_omega.
    - apply beg_mid_last_add_eq in H0.
      destruct H0 as [c1 | c2]; dest.
      + apply beg_mid_last_in in H3.
        specialize (i18 _ _ (or_introl eq_refl) H3 H2).
        specialize (i7 _ H3).
        rewrite getCs_cs in i7 by tauto.
        dest; word_omega.
      + dest.
        specialize (i22 _ _ _ _ _ H1); assumption.
    - rewrite app_or in H1.
      destruct H1 as [ez | hard].
      + eapply i23; eassumption.
      + apply in_single in hard.
        subst; simpl.
        reflexivity.
    - rewrite app_or in H0.
      destruct H0 as [ez | hard].
      + eapply i26; eassumption.
      + apply in_single in hard; subst; discriminate.
    - specialize (i27 H0 H1 H3).
      match goal with
        | |- (if ?p then _ else _) = _ => destruct p
      end.
      + rewrite e in H3.
        rewrite H8 in H3.
        assert (sth: split2 LgNumDatas (IdxBits + TagBits) (procRq F1) = y F2).
        { rewrite <- (Word.combine_split IdxBits TagBits (split2 LgNumDatas (IdxBits + TagBits) (procRq F1))).
          rewrite <- (Word.combine_split IdxBits TagBits (y F2)).
          rewrite H3, <- e.
          reflexivity.
        }
        rewrite sth in i27; word_omega.
      + assumption.
    - specialize (i27 H0 H1 H3).
      match goal with
        | |- (if ?p then _ else _) = _ => destruct p
      end.
      + rewrite e in H3.
        rewrite H8 in H3.
        assert (sth: split2 LgNumDatas (IdxBits + TagBits) (procRq F1) = y F2).
        { rewrite <- (Word.combine_split IdxBits TagBits (split2 LgNumDatas (IdxBits + TagBits) (procRq F1))).
          rewrite <- (Word.combine_split IdxBits TagBits (y F2)).
          rewrite H3, <- e.
          reflexivity.
        }
        rewrite sth in i27; word_omega.
      + assumption.
    - specialize (i27b H0 H1).
      destruct i27b as [ez | hard].
      + left; assumption.
      + match goal with
          | |- context[if ?p then _ else _] => destruct p
        end.
        * rewrite e in *; word_omega.
        * right; assumption.
    - specialize (i27b H0 H1).
      destruct i27b as [ez | hard].
      + left; assumption.
      + match goal with
          | |- context[if ?p then _ else _] => destruct p
        end.
        * rewrite e in *; word_omega.
        * right; assumption.
    - apply app_or in H1.
      destruct H1 as [c1 | c2].
      + eapply i29; eassumption.
      + apply in_single in c2; subst; simpl in H3; discriminate.
    - specialize (i31 (y :: beg) mid1 mid2 last rs rq1 rq2).
      simpl in i31.
      specialize (i31 (f_equal (cons y) H0) H1 H3 H4).
      assumption.
      END_SKIP_PROOF_ON *) apply cheat.
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
    (* SKIP_PROOF_ON
    doMetaComplex.
    - doAll;
      destruct (rs F1); intuition discriminate.
    - helpNormal; repeat destruct_addr; (assumption || intros).
      clear - i16a i30 H0.
      destruct (rqFromCToP ($ x) (split2 LgNumDatas (IdxBits + TagBits) (procRq F1)) rqFromCList rqToPList).
      + simpl in H0.        
        inv H0.
        reflexivity.
      + specialize (i16a t (or_introl eq_refl)).
        dest; discriminate.
        END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Ltac diffAddr_sameIdx :=
    match goal with
      | H: ?a0 <> ?a, H': split1 IdxBits TagBits ?a = split1 IdxBits TagBits ?a0 |- _ =>
        match goal with
          | |- context[if weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0)
                       then ?P else ?Q] =>
            let s1 := fresh in
            let s2 := fresh in
            destruct (weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0)) as [s1 | s2];
              [rewrite <- (Word.combine_split IdxBits TagBits a0) in H;
                rewrite <- (Word.combine_split IdxBits TagBits a) in H;
                rewrite H', s1 in H; exfalso; specialize (H eq_refl); apply H|]
          | H: context[if weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0) then ?P else ?Q] |- _ =>
            let s1 := fresh in
            let s2 := fresh in
            assert (Q) by
                (destruct (weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0)) as [s1 | s2];
                 [rewrite <- (Word.combine_split IdxBits TagBits a0) in H;
                   rewrite <- (Word.combine_split IdxBits TagBits a) in H;
                   rewrite H', s1 in H; exfalso; specialize (H eq_refl); apply H| assumption])
        end
      | H: ?a0 <> ?a, H': split1 IdxBits TagBits ?a = split1 IdxBits TagBits ?a0,
                          H'': split2 IdxBits TagBits ?a = split2 IdxBits TagBits ?a0
        |- _ =>
        let s1 := fresh in
        let s2 := fresh in
        rewrite <- (Word.combine_split IdxBits TagBits a0) in H;
          rewrite <- (Word.combine_split IdxBits TagBits a) in H;
          rewrite H', H'' in H; exfalso; specialize (H eq_refl); apply H
      | H: ?a0 <> ?a, H': split1 IdxBits TagBits ?a0 = split1 IdxBits TagBits ?a |- _ =>
        match goal with
          | |- context[if weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0)
                       then ?P else ?Q] =>
            let s1 := fresh in
            let s2 := fresh in
            destruct (weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0)) as [s1 | s2];
              [rewrite <- (Word.combine_split IdxBits TagBits a0) in H;
                rewrite <- (Word.combine_split IdxBits TagBits a) in H;
                rewrite <- H', s1 in H; exfalso; specialize (H eq_refl); apply H|]
          | H: context[if weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0) then ?P else ?Q] |- _ =>
            let s1 := fresh in
            let s2 := fresh in
            assert (Q) by
                (destruct (weq (split2 IdxBits TagBits a) (split2 IdxBits TagBits a0)) as [s1 | s2];
                 [rewrite <- (Word.combine_split IdxBits TagBits a0) in H;
                   rewrite <- (Word.combine_split IdxBits TagBits a) in H;
                   rewrite <- H', s1 in H; exfalso; specialize (H eq_refl); apply H| assumption])
        end
      | H: ?a0 <> ?a, H': split1 IdxBits TagBits ?a0 = split1 IdxBits TagBits ?a,
                          H'': split2 IdxBits TagBits ?a = split2 IdxBits TagBits ?a0
        |- _ =>
        let s1 := fresh in
        let s2 := fresh in
        rewrite <- (Word.combine_split IdxBits TagBits a0) in H;
          rewrite <- (Word.combine_split IdxBits TagBits a) in H;
          rewrite <- H', H'' in H; exfalso; specialize (H eq_refl); apply H
    end.
                            
            
  
  Lemma tag_upd cs tag a a0:
    getCs cs (fun w => if weq w (split1 IdxBits TagBits a)
                       then split2 IdxBits TagBits a
                       else tag w) a0 =
    if weq a0 a
    then cs (split1 IdxBits TagBits a0)
    else if weq (split1 IdxBits TagBits a) (split1 IdxBits TagBits a0)
         then $ Msi.Inv
         else getCs cs tag a0.
  Proof.
    unfold getCs.
    repeat match goal with
             | |- context [if ?p then _ else _] => destruct p
             | H: context [if ?p then _ else _] |- _ => destruct p
           end; subst; try reflexivity.
    - diffAddr_sameIdx.
    - apply eq_sym in e0; tauto.
    - apply eq_sym in e0; tauto.
    - tauto.
    - tauto.
    - tauto.
    - apply eq_sym in e0; tauto.
    - tauto.
  Qed.
  
  Lemma nmemCache_invariants_hold_6 s a u cs:
    nmemCache_invariants s ->
    upgRs metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    time (doMeta;
          try rewrite_getCs; (* try rewrite getCs_cs in * by tauto; *)
          rewrite ?tag_upd in *;
            repeat destruct_addr;
          repeat diffAddr_sameIdx;
          repeat match goal with
                   | |- context[if @weq IdxBits ?a ?b then _ else _] =>
                     let isEq := fresh in
                     (destruct (@weq IdxBits a b) as [isEq | ?]; [rewrite ?isEq in *| try assumption])
                   | H: context[if @weq IdxBits ?a ?b then _ else _] |- _ =>
                     let isEq := fresh in
                     (destruct (@weq IdxBits a b) as [isEq | ?]; [rewrite ?isEq in *| try assumption])
                 end;
          rewrite ?eq_weq in *; repeat diffAddr_sameIdx; (assumption || intros)).
    - specialize (i8 _ (or_introl eq_refl) H2).
      dest; word_omega.
    - specialize (i12 _ (or_introl eq_refl) H2).
      rewrite i12 in H1.
      simpl in H1; exfalso; apply H1.
    - apply beg_mid_last_cons with (v1 := y) in H1.
      dest.
      specialize (i10 _ _ _ _ _ H1 H2 H3).
      exfalso; assumption.
    - specialize (i10 (y :: beg) mid last rs1 rs2).
      simpl in i10.
      specialize (i10 (f_equal (cons y) H1) H3 H4).
      assumption.
    - specialize (i8 _ (or_introl eq_refl) H2).
      destruct i8; assumption.
    - specialize (i12 _ (or_introl eq_refl) H2); assumption.
    - specialize (i12 _ (or_introl eq_refl) H2).
      rewrite i12 in H1.
      apply app_cons_not_nil in H1.
      exfalso; assumption.
    - apply beg_mid_last_in2 in H1.
      destruct H1 as [_ u1].
      apply beg_mid_last_cons with (v1 := y) in u1.
      destruct u1 as [? val].
      destruct val as [v1 v2].
      specialize (i10 _ _ _ _ _ v2 H2 H4).
      exfalso; assumption.
    - dest; discriminate.
    - dest; discriminate.
    - specialize (i16c _ _ H1 (or_introl eq_refl)).
      congruence.
    - specialize (i16a _ H1); dest; subst.
      rewrite H9 in *; tauto.
    - exfalso.
      apply beg_mid_last_cons with (v1 := y) in H1.
      destruct H1 as [? [v1 v2]].
      specialize (i10 _ _ _ _ _ v2 H2 H3).
      exfalso; assumption.
    - specialize (i16b _ H1); dest; subst.
      rewrite H9 in *; tauto.
    - specialize (i16c _ _ H1 (or_intror H3)); assumption.
    - apply beg_mid_last_cons with (v1 := y) in H1.
      destruct H1 as [? [v1 v2]].
      specialize (i19 _ _ _ _ _ v2 H2 H3).
      right; assumption.
    - specialize (i18 _ _ (or_intror H1) H3 H4); assumption.
    - specialize (i19 (y :: beg) mid last rq rs).
      simpl in i19.
      specialize (i19 (f_equal (cons y) H1) H3 H4).
      assumption.
    - specialize (i31 nil beg mid last y rq1 rq2).
      rewrite app_nil_l in i31.
      specialize (i31 (f_equal (cons y) H1)).
      specialize (i31 H2 H3 H4).
      exfalso; assumption.
    - discriminate.
    - discriminate.
    - specialize (i16b _ (or_introl eq_refl) H2); dest.
      left.
      apply (f_equal (split2 IdxBits TagBits) H8).
    - clear - H9; left; f_equal; assumption.
    - specialize (i31 (y :: beg) mid1 mid2 last rs rq1 rq2).
      simpl in i31.
      specialize (i31 (f_equal (cons y) H1) H3 H4 H5).
      assumption.
    - specialize (i8 _ (or_introl eq_refl) H2); dest; word_omega.
    - tauto.
    - simpl; word_omega.
    - clear - n0; tauto.
    - specialize (i12 _ (or_introl eq_refl) H2); rewrite i12 in H3; simpl in H3; exfalso; assumption.
    - clear -n; tauto.
    - specialize (i7 _ H4).
      clear - i7; dest; split; word_omega.
    - specialize (i7 _ H3).
      clear - i7; dest; split; word_omega.
    - apply beg_mid_last_cons with (v1 := y) in H3; destruct H3 as [? [? v]].
      specialize (i10 _ _ _ _ _ v H2 H4).
      exfalso; assumption.
    - apply beg_mid_last_cons with (v1 := y) in H1; destruct H1 as [? [? v]].
      specialize (i10 _ _ _ _ _ v H2 H3).
      exfalso; assumption.
    - specialize (i8 _ H4 H6); clear - i8; dest; split; word_omega.
    - specialize (i8 _ H3 H4); clear - i8; dest; split; word_omega.
    - specialize (i10 (y :: beg) mid last rs1 rs2).
      simpl in i10.
      specialize (i10 (f_equal (cons y) H1) H3 H4).
      assumption.
    - specialize (i8 _ (or_introl eq_refl) H2); dest; assumption.
    - clear -n; tauto.
    - specialize (i11 H4 H6).
      rewrite i11.
      specialize (i27b eq_refl eq_refl).
      rewrite <- H8 in *.
      unfold getCs.
      destruct (weq (tagv (split1 IdxBits TagBits a0)) (split2 IdxBits TagBits a0)).
      + rewrite <- e in H5.
        rewrite H1 in H5.
        rewrite <- H1 in i27b.
        destruct i27b as [ez | hard]; simpl in *; [ | assumption].
        rewrite <- ez in H5.
        rewrite H1 in H5.
        tauto.
      + reflexivity.
    - clear - n0; tauto.
    - specialize (i12 _ (or_intror H1) H3); assumption.
    - rewrite H3 in i12.
      specialize (i12 _ (or_introl eq_refl) H2).
      apply eq_sym in i12.
      apply app_cons_not_nil in i12.
      exfalso; assumption.
    - rewrite H1 in i12.
      specialize (i12 _ (or_introl eq_refl) H2).
      apply eq_sym in i12.
      apply app_cons_not_nil in i12.
      exfalso; assumption.
    - rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      specialize (i14 _ _ H4).
      clear - i27b i14 H1 H3 H5.
      unfold getCs in *.
      destruct (weq (tagv (split1 IdxBits TagBits a0)) (split2 IdxBits TagBits a0)).
      + rewrite <- e in H5.
        rewrite H1 in H5.
        rewrite <- H1 in i27b.
        destruct i27b as [ez | hard]; simpl in *; [ | congruence].
        rewrite <- ez in H5.
        rewrite H1 in H5.
        tauto.
      + simpl.
        simpl in *; assumption.
    - clear - n0; tauto.
    - rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      specialize (i15 (y :: beg) mid last rq rs).
      simpl in i15.
      specialize (i15 (f_equal (cons y) H3) H4 H5).
      destruct i27b as [hard|ez]; [| apply H0 in ez; exfalso; assumption].
      unfold getCs in i15.
      rewrite hard in i15.
      rewrite eq_weq in i15.
      apply H0 in i15; exfalso; assumption.
    - rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      specialize (i15 (y :: beg) mid last rq rs).
      simpl in i15.
      specialize (i15 (f_equal (cons y) H1) H3 H4).
      destruct i27b as [hard|ez]; [| apply H0 in ez; exfalso; assumption].
      unfold getCs in i15.
      rewrite hard in i15.
      rewrite eq_weq in i15.
      apply H0 in i15; exfalso; assumption.
    - reflexivity.
    - reflexivity.
    - dest; discriminate.
    - dest; discriminate.
    - dest; discriminate.
    - dest; discriminate.
    - dest; discriminate.
    - dest; discriminate.
    - specialize (i16c _ _ H3 (or_introl eq_refl)); congruence.
    - specialize (i16c _ _ H1 (or_introl eq_refl)); congruence.
    - rewrite <- H8 in *.
      specialize (i16a _ H4); dest; tauto.
    - rewrite <- H8 in *.
      specialize (i16a _ H3); dest; tauto.
    - clear - n0; tauto.
    - specialize (i16a _ H1); dest; congruence.
    - apply beg_mid_last_cons with (v1 := y) in H3.
      destruct H3 as [? [? v]].
      specialize (i10 _ _ _ _ _ v H2 H4).
      exfalso; assumption.
    - clear -n; tauto.
    - rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      destruct i27b as [hard|ez]; [| apply H0 in ez; exfalso; assumption].
      specialize (i16b _ H4 H6); dest; tauto.
    - rewrite <- H8 in *.
      specialize (i16b _ H3 H5); dest; tauto.
    - clear - n0; tauto.
    - rewrite <- H8 in *.
      specialize (i16b _ H1 H3); dest; tauto.
    - specialize (i16c _ _ H1 (or_intror H3)).
      assumption.
    - specialize (i17 _ (or_intror H3) H4).
      destruct i17 as [hard | ez]; [|right; assumption].
      rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      destruct i27b as [hard2|ez2]; [| apply H0 in ez2; exfalso; assumption].
      unfold getCs in hard; rewrite hard2 in hard; rewrite eq_weq in hard.
      apply H0 in hard; exfalso; assumption.
    - clear - n; tauto.
    - left; reflexivity.
    - clear - n0; tauto.
    - specialize (i18 _ _ (or_intror H1) H3 H4); assumption.
    - apply (i19 (y :: beg) mid last rq rs); try assumption.
      simpl; f_equal; assumption.
    - rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      destruct i27b as [hard|ez]; [| apply H0 in ez; exfalso; assumption].
      specialize (i20 (y :: beg) mid last rq1 rq2).
      simpl in i20.
      specialize (i20 (f_equal (cons y) H3) H4 H5).
      unfold getCs in i20.
      rewrite hard, eq_weq in i20.
      apply H0 in i20; exfalso; assumption.
    - rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      destruct i27b as [hard|ez]; [| apply H0 in ez; exfalso; assumption].
      specialize (i20 (y :: beg) mid last rq1 rq2).
      simpl in i20.
      specialize (i20 (f_equal (cons y) H1) H3 H4).
      unfold getCs in i20.
      rewrite hard, eq_weq in i20.
      apply H0 in i20; exfalso; assumption.
    - reflexivity.
    - reflexivity.
    - discriminate.
    - discriminate.
    - rewrite <- H8 in *.
      specialize (i27b eq_refl eq_refl).
      destruct i27b as [hard|ez]; [| apply H0 in ez; exfalso; assumption].
      left; reflexivity.
    - rewrite <- H8 in *; left; reflexivity.
    - specialize (i31 (y :: beg) mid1 mid2 last rs rq1 rq2).
      simpl in i31.
      specialize (i31 (f_equal (cons y) H1) H3 H4 H5).
      assumption.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.



  
  Lemma isPWait_addRq a cRqValid
        (rqFromCList: list (type (Struct RqFC)))
        dirw (cword: word LgNumChildren) rq dir:
    isPWait a cRqValid rqFromCList dirw cword dir ->
    isPWait a cRqValid (rqFromCList ++ [rq]) dirw cword dir.
  Proof.
    unfold isPWait; intros.
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *.
    intuition auto.
    case_eq (hd_error rqFromCList); intros sth; try rewrite sth in *; intuition auto.
    rewrite hd_error_revcons_same with (ls := rqFromCList) (a := sth); auto.
    rewrite H1 in H2.
    assumption.
  Qed.
  
  Ltac invariant_complex :=
    subst;
    match goal with
    | HInd : nmemCache_invariants _, a: word (IdxBits + TagBits), H: (_ <= _)%nat |- _ =>
      destruct (HInd a _ _ H eq_refl)
    end; unfold withIndex, withPrefix, listIsEmpty,
         listFirstElt, listEnq, listDeq in *; simpl in *;
    unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest; repeat simplBool;
    repeat match goal with
           | [ H : evalConstT match ?E with _ => _ end = _ |- _ ] =>
             destruct E; try discriminate; [ clear H ]
           end.

  Ltac invariant_notComplex c :=
    subst;
    match goal with
    | HInd : nmemCache_invariants _, a: word (IdxBits + TagBits), H: (c <= _)%nat |- _ =>
      destruct (HInd a _ _ H eq_refl)
    end; unfold withIndex, withPrefix, listIsEmpty,
         listFirstElt, listEnq, listDeq in *; simpl in *;
    unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest; repeat simplBool;
    repeat match goal with
           | [ H : evalConstT match ?E with _ => _ end = _ |- _ ] =>
             destruct E; try discriminate; [ clear H ]
           end.


  Ltac invariant_solve :=
    simplMapUpds ltac:(try assumption).

  Ltac invariant1 := invariant_complex; invariant_solve.
  Ltac invariant2 c := invariant_notComplex c; invariant_solve.

  Ltac invariant_step :=
    intros; hnf; intros; simpl in *;
    unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat match goal with
           | [ H : Some _ = Some _ |- _ ] =>
             apply invSome in H
           | [ H : RepRule _ _ _ _ _ _ _ = RepRule _ _ _ _ _ _ _ |- _ ] =>
             apply invRepRule in H
           end; subst;
    unfold getActionFromGen, getGenAction, strFromName in *; simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *; subst;
    unfold getActionFromSin, getSinAction, listIsEmpty, listFirstElt, listEnq, listDeq in *;
    SymEval.

  Ltac invariant x c := invariant_step;
                   destruct (eq_nat_dec c x); [subst; invariant1| invariant2 c].

  Hint Resolve isPWait_addRq hd_error_revcons_same.

  Lemma diffCache_absurd (x c: cache) (xle: (x <= wordToNat (wones LgNumChildren))%nat) (yle: (c <= wordToNat (wones LgNumChildren))%nat)
        (neq: c <> x) (isEq: natToWord LgNumChildren c = natToWord LgNumChildren x): False.
  Proof.
    pose proof (pow2_zero LgNumChildren).
    rewrite wones_pow2_minus_one in xle, yle.
    apply natToWord_inj with (sz := LgNumChildren) in isEq; subst.
    - tauto.
    - Omega.omega.
    - Omega.omega.
  Qed.
      
  Ltac xfer H a0 y :=
     unfold rqFromCToP, rsFromCToP, fromPToC in *;
       rewrite ?filtRqFromC_commute_app, ?filtRsFromC_commute_app, ?filtFromP_commute_app, ?filtToC_commute_app in *;
       simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
       ((intros;
         rewrite ?eq_weq in *;
           solve [intros;
                   try apply isPWait_addRq;
                   try apply hd_error_revcons_same;
                   try solve [destruct (weq a0 y);
                               [subst; rewrite <- ?app_assoc in *; simpl in *| rewrite ?app_nil_r in *]; eapply H; eauto]])
          ||
          (match goal with
             | neq: ?c <> ?x, xle: (?x <= wordToNat (wones LgNumChildren))%nat, yle: (?c <= wordToNat (wones LgNumChildren))%nat
               |- _ =>
               destruct (weq (natToWord LgNumChildren c) (natToWord LgNumChildren x)) as [isEq | ?];
             [pose proof (@diffCache_absurd x c xle yle neq isEq); exfalso; assumption |
              intros;
              try apply isPWait_addRq;
              try apply hd_error_revcons_same;
              rewrite ?app_nil_r in *; try eapply H; eauto
             ]
           end)).
  

  Lemma nmemCache_invariants_hold_xfer_1 s a u cs:
    nmemCache_invariants s ->
    rqFromCToPRule metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    invariant x c.
    - xfer i9 a0 (y F1).
    - xfer i16 a0 (y F1).
    - xfer i16a a0 (y F1).
    - xfer i16c a0 (y F1).
    - unfold rqFromCToP, rsFromCToP, fromPToC in *;
      rewrite ?filtRqFromC_commute_app, ?filtRsFromC_commute_app, ?filtFromP_commute_app, ?filtToC_commute_app in *;
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
      rewrite ?eq_weq in *;
      intros;
      destruct (weq a0 (y F1)); [subst; rewrite <- ?app_assoc in *; simpl in *| rewrite ?app_nil_r in *].
      + specialize (i17 _ H0 H2).
        destruct i17.
        * left; assumption.
        * right; apply isPWait_addRq; auto.
      + specialize (i17 _ H0 H2).
        destruct i17.
        * left; assumption.
        * right; apply isPWait_addRq; auto.
    - xfer i19 a0 (y F1).
    - xfer i21 a0 (y F1).
    - xfer i23 a0 (y F1).
    - xfer i25 a0 (y F1).
    - xfer i28 a0 (y F1).
    - xfer i29 a0 (y F1).
    - xfer i30 a0 (y F1).
    - xfer i9 a0 y.
    - xfer i16 a0 y.
    - xfer i16a a0 y.
    - xfer i16c a0 y.
    - unfold rqFromCToP, rsFromCToP, fromPToC in *;
      rewrite ?filtRqFromC_commute_app, ?filtRsFromC_commute_app, ?filtFromP_commute_app, ?filtToC_commute_app in *;
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
      intros.
      + specialize (i17 _ H2 H4).
        destruct i17.
        * left; assumption.
        * right; apply isPWait_addRq; auto.
    - xfer i19 a0 y.
    - xfer i21 a0 y.
    - xfer i23 a0 y.
    - xfer i25 a0 y.
    - xfer i28 a0 y.
    - xfer i29 a0 y.
    - xfer i30 a0 y.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma nmemCache_invariants_hold_xfer_2 s a u cs:
    nmemCache_invariants s ->
    rsFromCToPRule metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    invariant x c.
    - xfer i7 a0 (y F1).
    - xfer i9 a0 (y F1).
    - xfer i11 a0 (y F1).
    - xfer i12 a0 (y F1).
    - xfer i13 a0 (y F1).
    - xfer i14 a0 (y F1).
    - xfer i18 a0 (y F1).
    - xfer i21 a0 (y F1).
    - xfer i22 a0 (y F1).
    - xfer i23 a0 (y F1).
    - xfer i26 a0 (y F1).
    - xfer i29 a0 (y F1).
    - xfer i7 a0 y.
    - xfer i9 a0 y.
    - xfer i11 a0 y.
    - xfer i12 a0 y.
    - xfer i13 a0 y.
    - xfer i14 a0 y.
    - xfer i18 a0 y.
    - xfer i21 a0 y.
    - xfer i22 a0 y.
    - xfer i23 a0 y.
    - xfer i26 a0 y.
    - xfer i29 a0 y.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Ltac xfer2 H a0 y :=
     unfold rqFromCToP, rsFromCToP, fromPToC in *;
       rewrite ?filtRqFromC_commute_app, ?filtRsFromC_commute_app, ?filtFromP_commute_app, ?filtToC_commute_app in *;
       simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
       intros;
       match goal with
         | H: natToWord _ _ = y F1 |- _ =>
           rewrite H in *
       end;
       rewrite ?eq_weq in *;
       solve [intros;
               try apply isPWait_addRq;
               try apply hd_error_revcons_same;
               try solve [destruct (weq a0 (y F2 F2));
                           [subst; rewrite <- ?app_assoc in *; simpl in *| rewrite ?app_nil_r in *]; eapply H; eauto]].
  
  Ltac xfer3 H y :=
     unfold rqFromCToP, rsFromCToP, fromPToC in *;
       rewrite ?filtRqFromC_commute_app, ?filtRsFromC_commute_app, ?filtFromP_commute_app, ?filtToC_commute_app in *;
       simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
       match goal with
         | H: natToWord _ _ = y F1 |- _ => rewrite <- H in *
       end;
       match goal with
         | neq: ?c <> ?x, xle: (?x <= wordToNat (wones LgNumChildren))%nat, yle: (?c <= wordToNat (wones LgNumChildren))%nat
           |- _ =>
           destruct (weq (natToWord LgNumChildren c) (natToWord LgNumChildren x)) as [isEq | ?];
             [pose proof (@diffCache_absurd x c xle yle neq isEq); exfalso; assumption |
              intros;
                try apply isPWait_addRq;
                try apply hd_error_revcons_same;
                rewrite ?app_nil_r in *; try eapply H; eauto
             ]
       end.
  

  
  Lemma nmemCache_invariants_hold_xfer_3 s a u cs:
    nmemCache_invariants s ->
    fromPToCRule metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    invariant x c.
    - xfer2 i8 a0 y.
    - xfer2 i10 a0 y.
    - xfer2 i11 a0 y.
    - xfer2 i12 a0 y.
    - xfer2 i15 a0 y.
    - xfer2 i16 a0 y.
    - xfer2 i16b a0 y.
    - xfer2 i16c a0 y.
    - xfer2 i17 a0 y.
    - xfer2 i18 a0 y.
    - xfer2 i19 a0 y.
    - xfer2 i20 a0 y.
    - xfer2 i31 a0 y.
    - xfer3 i8 y.
    - xfer3 i10 y.
    - xfer3 i11 y.
    - xfer3 i12 y.
    - xfer3 i15 y.
    - xfer3 i16 y.
    - xfer3 i16b y.
    - xfer3 i16c y.
    - xfer3 i17 y.
    - xfer3 i18 y.
    - xfer3 i19 y.
    - xfer3 i20 y.
    - xfer3 i31 y.
      END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Record dirCompat_inv' a cword (c: cache) c2 (c2nat: cache) (s: RegsT): Prop :=
    {
      newdir: <| Vector (Vector Msi LgNumChildren) (IdxBits + TagBits) |> ;
      newdirFind: newdir === s.[mcs -- dataArray] ;
      isDirCompat:
        cword <> c2 ->
        newdir a cword <=
        if weq (newdir a c2) ($ Msi.Mod)
        then $ Msi.Inv
        else if weq (newdir a c2) ($ Msi.Ex)
             then $ Msi.Sh
             else if weq (newdir a c2) ($ Msi.Sh)
                  then $ Msi.Ex
                  else $ Msi.Mod
    }.

  Definition dirCompat_inv s := forall a cword c, (c <= wordToNat (wones LgNumChildren))%nat ->
                                                  (cword = $ c) ->
                                                  forall cword2 c2,
                                                    (c2 <= wordToNat (wones LgNumChildren))%nat ->
                                                    (cword2 = $ c2) ->
                                                    dirCompat_inv' a cword c cword2 c2 s.

  Ltac metaDir :=
    intros HDir HInd HInRule x xcond HS;
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule;
    apply invSome in HInRule;
    apply invRepRule in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    unfold getActionFromGen, getGenAction, strFromName in *;
      intros ? ? c ? ? ? c2 ? ?;
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
      subst; unfold getActionFromSin, getSinAction in *; subst;
    SymEval; subst; simpl; unfold VectorFacts.Vector_find; simpl;
    match goal with
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat, H': (c <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl);
          specialize (HInd a _ _ H' eq_refl)
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl)          
    end;
    match goal with
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat, H': (c <= _)%nat, H2: (c2 <= _)%nat |- _ =>
        destruct (HDir a _ _ H eq_refl _ _ H2 eq_refl);
          specialize (HInd a _ _ H' eq_refl)
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat, H2: (c2 <= _)%nat |- _ =>
        destruct (HDir a _ _ H eq_refl _ _ H2 eq_refl)
    end;
    unfold withIndex in *;
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest;
    repeat simplBool;
    elimDiffC c;
    try match goal with
          | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
        end;
    invariant_simpl;
      simplMapUpds helpNormal.
    
  Lemma dirCompat_inv_hold_1 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    l1MissByState metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_2 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    l1MissByLine metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_3 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    l1Hit metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_4 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    writeback metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_5 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    upgRq metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_6 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    upgRs metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_7 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    ld metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_8 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    st metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_9 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    drop metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_10 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    pProcess metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_xfer_1 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    rqFromCToPRule metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_xfer_2 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    rsFromCToPRule metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_xfer_3 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    fromPToCRule metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    metaDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.


  Ltac normalDir :=
    intros HDir HInd HInRule HS;
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule;
    apply invSome in HInRule;
    unfold getActionFromSin, getSinAction at 1 in HInRule;
    simpl in HInRule; unfold Lib.VectorFacts.Vector_find in HInRule; simpl in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ? ? c2 ? ?;
      simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
      subst; unfold getActionFromSin, getSinAction in *; subst;
    SymEval; subst; simpl; unfold VectorFacts.Vector_find; simpl;
    match goal with
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat, H': (c <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl);
          specialize (HInd a _ _ H' eq_refl)
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl)          
    end;
    match goal with
      | a: word (IdxBits + TagBits), H: (_ <= _)%nat, H2: (c2 <= _)%nat |- _ =>
        destruct (HDir a _ _ H eq_refl _ _ H2 eq_refl);
          destruct (HDir a _ _ H2 eq_refl _ _ H eq_refl)
    end;
    unfold withIndex in *;
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest;
    repeat simplBool;
    elimDiffC c;
    try match goal with
          | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
        end;
    invariant_simpl;
    simplMapUpds helpNormal.

  
  Lemma dirCompat_inv_hold_02 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    dwnRq is a ->
    SemAction s a
              u cs WO ->
    dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    normalDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_01 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    missByState is a ->
    SemAction s a
              u cs WO ->
    dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    normalDir.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma wordToNat_wones sz (w: word sz):
    ( wordToNat w <= wordToNat (wones sz))%nat.
  Proof.
    rewrite wones_pow2_minus_one.
    pose proof (pow2_zero sz).
    pose proof (wordToNat_bound w).
    Omega.omega.
  Qed.

  Lemma neq_sym A (a b: A): a <> b -> b <> a.
  Proof.
    intros.
    intro.
    subst.
    tauto.
  Qed.
  
  Lemma dirCompat_inv_hold_03 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    dwnRs_wait is a ->
    SemAction s a
              u cs WO ->
    dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    normalDir.
    normalDir.
    - intros.
      specialize (isDirCompat H2).
      specialize (isDirCompat0 (neq_sym H2)).
      destruct (weq a0 (y F2 F1)); [subst|].
      + destruct (weq ($ c) (y F1)) as [isEq | ?]; [rewrite isEq in * |].
        * destruct (weq ($ c2) (y F1)) as [isEq' | ?]; [rewrite isEq' in *; try tauto|].
          specialize (i1 _ (or_introl eq_refl)).
          destruct i1 as [_ useful].
          word_omega.
        * destruct (weq ($ c2) (y F1)) as [isEq'|?]; [rewrite isEq' in * | assumption].
          specialize (i7 _ (or_introl eq_refl)).
          destruct i7 as [_ useful].
          clear - isDirCompat isDirCompat0 useful.
          repeat match goal with
                   | H: context[if ?p then _ else _] |- _ => destruct p
                   | |- context[if ?p then _ else _] => destruct p
                 end; try word_omega.
      + try assumption.
    - intros.
      specialize (isDirCompat H2).
      specialize (isDirCompat0 (neq_sym H2)).
      destruct (weq a0 (y F2 F1)); [subst|].
      + destruct (weq ($ c) (y F1)) as [isEq | ?]; [rewrite isEq in * |].
        * destruct (weq ($ c2) (y F1)) as [isEq' | ?]; [rewrite isEq' in *; try tauto|].
          specialize (i1 _ (or_introl eq_refl)).
          destruct i1 as [_ useful].
          word_omega.
        * destruct (weq ($ c2) (y F1)) as [isEq'|?]; [rewrite isEq' in * | assumption].
          specialize (i7 _ (or_introl eq_refl)).
          destruct i7 as [_ useful].
          clear - isDirCompat isDirCompat0 useful.
          repeat match goal with
                   | H: context[if ?p then _ else _] |- _ => destruct p
                   | |- context[if ?p then _ else _] => destruct p
                 end; try word_omega.
      + try assumption.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_04 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    dwnRs_noWait is a ->
    SemAction s a
              u cs WO ->
    dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    normalDir.
    - intros.
      specialize (isDirCompat H2).
      specialize (isDirCompat0 (neq_sym H2)).
      destruct (weq a0 (y F2 F1)); [subst|].
      + destruct (weq ($ c) (y F1)) as [isEq | ?]; [rewrite isEq in * |].
        * destruct (weq ($ c2) (y F1)) as [isEq' | ?]; [rewrite isEq' in *; try tauto|].
          specialize (i1 _ (or_introl eq_refl)).
          destruct i1 as [_ useful].
          word_omega.
        * destruct (weq ($ c2) (y F1)) as [isEq'|?]; [rewrite isEq' in * | assumption].
          specialize (i7 _ (or_introl eq_refl)).
          destruct i7 as [_ useful].
          clear - isDirCompat isDirCompat0 useful.
          repeat match goal with
                   | H: context[if ?p then _ else _] |- _ => destruct p
                   | |- context[if ?p then _ else _] => destruct p
                 end; try word_omega.
      + try assumption.
    - intros.
      specialize (isDirCompat H2).
      specialize (isDirCompat0 (neq_sym H2)).
      destruct (weq a0 (y F2 F1)); [subst|].
      + destruct (weq ($ c) (y F1)) as [isEq | ?]; [rewrite isEq in * |].
        * destruct (weq ($ c2) (y F1)) as [isEq' | ?]; [rewrite isEq' in *; try tauto|].
          specialize (i1 _ (or_introl eq_refl)).
          destruct i1 as [_ useful].
          word_omega.
        * destruct (weq ($ c2) (y F1)) as [isEq'|?]; [rewrite isEq' in * | assumption].
          specialize (i7 _ (or_introl eq_refl)).
          destruct i7 as [_ useful].
          clear - isDirCompat isDirCompat0 useful.
          repeat match goal with
                   | H: context[if ?p then _ else _] |- _ => destruct p
                   | |- context[if ?p then _ else _] => destruct p
                 end; try word_omega.
      + try assumption.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Lemma dirCompat_inv_hold_05 s a u cs:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    deferred is a ->
    SemAction s a
              u cs WO ->
    dirCompat_inv (M.union u s).
  Proof.
    (* SKIP_PROOF_ON
    normalDir.
    - intros.
      specialize (isDirCompat H0).
      specialize (isDirCompat0 (neq_sym H0)).
      destruct (weq a0 (y F2 F1)); [subst|].
      + destruct (weq ($ c) (y F1)) as [isEq | ?]; [rewrite isEq in * |].
        * destruct (weq ($ c2) (y F1)) as [isEq' | ?]; [rewrite isEq' in *; tauto|].
          apply (@compatPair_sem (y F2) (y F1) (newdir0 (y F2 F1)) ($ c2) (neq_sym H0)) in H7.
          assumption.
        * destruct (weq ($ c2) (y F1)) as [isEq'|?]; [rewrite isEq' in * | assumption].
          apply (@compatPair_sem (y F2) (y F1) (newdir0 (y F2 F1)) ($ c) H0) in H7.
          clear - isDirCompat H7.
          repeat match goal with
                   | H: context[if ?p then _ else _] |- _ => destruct p
                   | |- context[if ?p then _ else _] => destruct p
                 end; try word_omega.
      + assumption.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

  Record cacheCompat_inv' a (cword1: word LgNumChildren) (c1: cache) cword2 (c2: cache) (s: RegsT) csv1 csv2 tagv1 tagv2: Prop :=
    {
      isCacheCompat:
        cword1 <> cword2 ->
        getCs csv1 tagv1 a <=
        if weq (getCs csv2 tagv2 a) ($ Msi.Mod)
        then $ Msi.Inv
        else if weq (getCs csv2 tagv2 a) ($ Msi.Ex)
             then $ Msi.Sh
             else if weq (getCs csv2 tagv2 a) ($ Msi.Sh)
                  then $ Msi.Ex
                  else $ Msi.Mod
    }.

  Definition cacheCompat_inv s := forall a cword1 c1, (c1 <= wordToNat (wones LgNumChildren))%nat ->
                                                      (cword1 = $ c1) ->
                                                      forall cword2 c2,
                                                        (c2 <= wordToNat (wones LgNumChildren))%nat ->
                                                        (cword2 = $ c2) ->
                                                        forall (csv1: <| Vector Msi IdxBits |>)
                                                               (csv2: <| Vector Msi IdxBits |>)
                                                               (csFind1: csv1 === s.[(cs -- dataArray) __ c1])
                                                               (csFind2: csv2 === s.[(cs -- dataArray) __ c2])
                                                               (tagv1: <| Vector (Bit TagBits) IdxBits |>)
                                                               (tagFind1: tagv1 === s.[(tag -- dataArray) __ c1])
                                                               (tagv2: <| Vector (Bit TagBits) IdxBits |>)
                                                               (tagFind2: tagv2 === s.[(tag -- dataArray) __ c2]),
                                                          cacheCompat_inv' a cword1 c1 cword2 c2 s csv1 csv2 tagv1 tagv2.

  Lemma cacheCompat_inv_holds s:
    dirCompat_inv s ->
    nmemCache_invariants s ->
    cacheCompat_inv s.
  Proof.
    (* SKIP_PROOF_ON
    intros.
    intros a cword1 c1 c1Le c1Eq cword2 c2 c2Le c2Eq.
    destruct (H a cword1 c1 c1Le c1Eq cword2 c2 c2Le c2Eq), (H0 a cword1 c1 c1Le c1Eq).
    destruct (H a cword2 c2 c2Le c2Eq cword1 c1 c1Le c1Eq), (H0 a cword2 c2 c2Le c2Eq).
    intros csv1 csv1Find csv2 csv2Find tagv1 tagv1Find tagv2 tagv2Find.
    unfold withIndex in *;
    simpl in *; unfold Lib.VectorFacts.Vector_find in *; simpl in *;
    repeat substFind; dest;
    repeat simplBool;
    elimDiffC c;
    invariant_simpl;
    simplMapUpds idtac.
    intros.
    clear - i5 i0 isDirCompat isDirCompat0 H1.
    specialize (isDirCompat H1).
    specialize (isDirCompat0 (neq_sym H1)).
    repeat match goal with
             | H: context [if ?p then _ else _] |- _ => destruct p
             | |- context [if ?p then _ else _] => destruct p
           end; try word_omega.
END_SKIP_PROOF_ON *) apply cheat.
  Qed.

End MemCacheInl.
