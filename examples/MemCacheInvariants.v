Require Import Lib.FMap Lib.Word Ex.MemTypes Lib.Indexer Lib.Struct Ex.Msi
        Ex.NativeFifo Lts.Notations String Ex.MemCacheInl Lts.Syntax List Lts.Semantics
        ParametricSyntax Lib.CommonTactics Lts.SemFacts Lib.FMap Lib.Concat
        FunctionalExtensionality Program.Equality Lts.Tactics Arith Ex.MapVReify Lts.SymEval
        Lts.SymEvalTac.

Set Implicit Arguments.

(* Local Notation "x 'is' y 'of' s" := (M.find y%string s = Some (existT _ _ x)) (at level 12). *)

Local Notation "<| t |>" := (fullType type (SyntaxKind t)).

Local Notation "<< t >>" := (fullType type (@NativeKind t nil)).

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.


  Definition getTagIdxS (x: word (TagBits + IdxBits)):
    word (TagBits + IdxBits) :=
    x.

  Definition getTagS (x: word (TagBits + IdxBits)):
    word TagBits :=
    split1 TagBits IdxBits x.

  Definition getIdxS (x: word (TagBits + IdxBits)):
    word IdxBits :=
    split2 TagBits IdxBits x.

  Definition AddrBits := TagBits + IdxBits.
  
  Definition getAddrS (tag: word TagBits) (idx: word IdxBits): word AddrBits :=
    Word.combine tag idx.


  Definition isCompat c (dir: type (Vector Msi LgNumChildren)) :=
    (dir c = $ Msi.Mod -> forall i, i <> c -> dir c = $ Msi.Inv) /\
    (forall i, i <> c -> dir i = $ Msi.Mod -> dir c = $ Msi.Inv).

  Fixpoint filtRqFromC
             (c: word LgNumChildren) (a: word AddrBits)
             (ls: list (type (RqFromC LgNumChildren (Bit AddrBits) Id))):
    list (type (RqToP (Bit AddrBits) Id)) :=
    match ls with
      | x :: xs => if weq c (x ``"child")
                   then if weq a (x ``"rq" ``"addr")
                        then x ``"rq" :: filtRqFromC c a xs
                        else filtRqFromC c a xs
                   else filtRqFromC c a xs
      | nil => nil
    end.

  Lemma filtRqFromC_commute_app:
    forall c a l1 l2, (filtRqFromC c a (l1 ++ l2)) = filtRqFromC c a l1 ++ filtRqFromC c a l2.
  Proof.
    induction l1; simpl; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.
  
  Fixpoint filtRsFromC
             (c: word LgNumChildren) (a: word AddrBits)
             (ls: list (type (RsFromC LgDataBytes LgNumDatas LgNumChildren
                                      (Bit AddrBits)))):
    list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) :=
    match ls with
      | x :: xs => if weq c (x ``"child")
                   then if weq a (x ``"rs" ``"addr")
                        then x ``"rs" :: filtRsFromC c a xs
                        else filtRsFromC c a xs
                   else filtRsFromC c a xs
      | nil => nil
    end.

  Lemma filtRsFromC_commute_app:
    forall c a l1 l2, (filtRsFromC c a (l1 ++ l2)) = filtRsFromC c a l1 ++ filtRsFromC c a l2.
  Proof.
    induction l1; simpl; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.
  
  Fixpoint filtToC
             (c: word LgNumChildren) (a: word AddrBits)
             (ls: list (type (ToC LgDataBytes LgNumDatas LgNumChildren
                                  (Bit AddrBits) Id))):
    list (type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id)) :=
    match ls with
      | x :: xs => if weq c (x ``"child")
                   then if weq a (x ``"msg" ``"addr")
                        then x ``"msg" :: filtToC c a xs
                        else filtToC c a xs
                   else filtToC c a xs
      | nil => nil
    end.

  Lemma filtToC_commute_app:
    forall c a l1 l2, (filtToC c a (l1 ++ l2)) = filtToC c a l1 ++ filtToC c a l2.
  Proof.
    induction l1; simpl; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.

  Fixpoint filtRqToP
             (a: word AddrBits)
             (ls: list (type (RqToP (Bit AddrBits) Id))):
    list (type (RqToP (Bit AddrBits) Id)) :=
    match ls with
      | x :: xs => if weq a (x ``"addr")
                   then x :: filtRqToP a xs
                   else filtRqToP a xs
      | nil => nil
    end.

  Lemma filtRqToP_commute_app:
    forall a l1 l2, (filtRqToP a (l1 ++ l2)) = filtRqToP a l1 ++ filtRqToP a l2.
  Proof.
    induction l1; simpl; auto; intros.
    rewrite IHl1.
    match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.
  
  Fixpoint filtRsToP
             (a: word AddrBits)
             (ls: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))):
    list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) :=
    match ls with
      | x :: xs => if weq a (x ``"addr")
                   then x :: filtRsToP a xs
                   else filtRsToP a xs
      | nil => nil
    end.

  Lemma filtRsToP_commute_app:
    forall a l1 l2, (filtRsToP a (l1 ++ l2)) = filtRsToP a l1 ++ filtRsToP a l2.
  Proof.
    induction l1; simpl; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.

  Fixpoint filtFromP
             (a: word AddrBits)
             (ls: list (type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id))):
    list (type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id)) :=
    match ls with
      | x :: xs => if weq a (x ``"addr")
                   then x :: filtFromP a xs
                   else filtFromP a xs
      | nil => nil
    end.

  Lemma filtFromP_commute_app:
    forall a l1 l2, (filtFromP a (l1 ++ l2)) = filtFromP a l1 ++ filtFromP a l2.
  Proof.
    induction l1; simpl; auto; intros.
    rewrite IHl1.
    repeat match goal with |- context[weq ?p ?q] => destruct (weq p q) end; auto.
  Qed.
  
  Definition rqFromCToP
             (c: word LgNumChildren) (a: word AddrBits)
             (l1: list (type (RqFromC LgNumChildren (Bit AddrBits) Id)))
             (l2: list (type (RqToP (Bit AddrBits) Id))):
    list (type (RqToP (Bit AddrBits) Id)) :=
    filtRqFromC c a l1 ++ filtRqToP a l2.

  Definition rsFromCToP
             (c: word LgNumChildren) (a: word AddrBits)
             (l1: list (type (RsFromC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits))))
             (l2: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))):
    list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) :=
    filtRsFromC c a l1 ++ filtRsToP a l2.

  Lemma filtRsToP_a: forall c a l2, filtRsFromC c a l2 = filtRsToP a (filtRsFromC c a l2).
  Proof.
    induction l2; simpl; auto; intros.
    repeat match goal with
             | |- context[weq ?c ?d] => destruct (weq c d); simpl; subst; intuition auto
           end.
    f_equal; auto.
  Qed.

  Lemma rsFromCToP_assoc c a l1 l2 l3:
    rsFromCToP c a (l1 ++ l2) l3 = rsFromCToP c a l1 (filtRsFromC c a l2 ++ l3).
  Proof.
    induction l1; unfold rsFromCToP; simpl; auto; intros.
    - rewrite filtRsToP_commute_app; f_equal.
      rewrite <- filtRsToP_a.
      reflexivity.
    - repeat match goal with
               | |- context[weq ?c ?d] => destruct (weq c d); simpl; subst; intuition auto
             end.
      f_equal; auto.
  Qed.

  Lemma rsFromCToP_notA c a l1 (t: type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))):
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

  Definition fromPToC
             (c: word LgNumChildren) (a: word AddrBits)
             (l1: list (type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id)))
             (l2: list (type (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))):
    list (type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id)) :=
    filtFromP a l1 ++ filtToC c a l2.

  Definition getCs (cs: word IdxBits -> type Msi) (tag: word IdxBits -> word TagBits)
             (a: word AddrBits) :=
    if weq (tag (getIdxS a)) (getTagS a)
    then cs (getIdxS a)
    else $ Msi.Inv.

  Definition xor a b := (a /\ ~ b) \/ (~ a /\ b).

  Fixpoint rsLessTo (ls: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))) :=
    match ls with
      | x :: y :: xs => x ``"to" > y ``"to" /\ rsLessTo xs
      | _ => True
    end.

  Definition isCWait a procv
             (procRq: type (RqFromProc LgDataBytes (Bit (TagBits + IdxBits + LgNumDatas))))
             csw :=
    procv = true /\ split1 (TagBits + IdxBits) LgNumDatas (procRq ``"addr") = a /\
    csw = true.

  Definition isPWait a cRqValid
             (rqFromCToP: list (type (RqFromC LgNumChildren (Bit (TagBits + IdxBits)) Id)))
             dirw (cword: word LgNumChildren) :=
    exists cRq rest,
      rqFromCToP = cRq :: rest /\
      cRqValid = true /\
      cRq ``"rq" ``"addr" = a /\ dirw cword = true.

  Lemma singleUnfoldConcat A B a (f: A -> list B) (ls: list A):
    concat (map f (a :: ls)) = f a ++ concat (map f ls).
  Proof.
    reflexivity.
  Qed.

  Ltac simplRsFromCToP rs inv :=
    match goal with
      | H: In rs (rsFromCToP ?x ?a ?l1 (?l2 ++ ?l3)) |- _ =>
        unfold rsFromCToP in H; rewrite filtRsToP_commute_app in H;
        rewrite app_assoc in H; fold (rsFromCToP x a l1 l2) in H; apply in_app_or in H;
        destruct H;
        [ apply inv in H; auto | simpl in H]
      | H: In rs (rsFromCToP ?x ?a (?l1 ++ ?l2) ?l3) |- _ =>
        idtac
    end.

  Hint Unfold nmemCacheInl: ModuleInl.

  Lemma In_metaRules:
    forall k a m,
      In (k :: a)%struct (getRules (modFromMeta m)) ->
      exists r, match r with
                  | OneRule bd rname => k = (nameVal rname) /\ a = getActionFromSin bd
                  | RepRule A strA goodName1 GenK getConstK goodName2 bd rname ls noDup =>
                    exists i, In i ls /\ k = addIndexToStr strA i (nameVal rname) /\
                              a = getActionFromGen strA getConstK bd i
                end /\ In r (metaRules m).
  Proof.
    intros.
    destruct m; simpl in *.
    induction metaRules; simpl in *.
    - exfalso; auto.
    - apply in_app_or in H.
      destruct H.
      + exists a0.
               split.
               * { destruct a0; simpl in *.
                   - destruct H; [| exfalso; auto]; simpl in *.
                     inversion H; auto.
                   - unfold repRule, getListFromRep in H.
                     apply in_map_iff in H.
                     dest;
                       eexists; inversion H; constructor; eauto.
                 }
               * auto.
               + apply IHmetaRules in H.
                 dest.
                 destruct x; dest; eexists; constructor; simpl in *; eauto; simpl in *; eauto.
  Qed.
  
  Ltac invMetaMod :=
    intros;
    match goal with
      | H: Substep (modFromMeta ?m) ?s ?u ?ul ?cs |- _ =>
        autounfold with ModuleInl in H;
        inv H; subst; [unfold modFromMeta in *; simpl in *;
                       rewrite M.union_empty_L; eexists; eauto|
                       unfold modFromMeta in *; simpl in *;
                       rewrite M.union_empty_L; eexists; eauto|
                       |
                       unfold modFromMeta in *; simpl in *; exfalso; auto]
    end;
    match goal with
      | H: In ?sth (getRules (modFromMeta ?m)) |- _ =>
        apply In_metaRules in H; simpl in *; dest;
        unfold getActionFromGen, getGenAction, getActionFromSin, getSinAction,
        strFromName in *; doDestruct; simpl in *
    end.

  Open Scope string.

  Record nmemCache_invariants_rec (s: RegsT)
         cword c: Prop :=
    {
      dir: <| Vector (Vector Msi LgNumChildren) (TagBits + IdxBits) |> ;
      dirFind: dir === s.["dataArray.mcs"];
      mline: <|Vector (Line LgDataBytes LgNumDatas) (TagBits + IdxBits) |> ;
      mlineFind: mline === s.["dataArray.mline"];
      cRqValid: <| Bool |> ;
      cRqValidFind: cRqValid === s.["cRqValid"];
      dirw: <| Vector Bool LgNumChildren |> ;
      dirwFind: dirw === s.["cRqDirw"];
      rqFromCList: << list (type (RqFromC LgNumChildren (Bit AddrBits) Id)) >> ;
      rqFromCListFind: rqFromCList === s.["elt.rqFromChild"];
      rsFromCList: << list (type (RsFromC LgDataBytes LgNumDatas LgNumChildren
                                          (Bit AddrBits))) >> ;
      rsFromCListFind: rsFromCList === s.["elt.rsFromChild"];
      toCList: << list (type
                          (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))
                  >> ;
      toCListFind: toCList === s.["elt.toChild"];
      cs: <| Vector Msi IdxBits |> ;
      csFind: cs === s.["dataArray.cs" __ c];
      tag: <| Vector (Bit TagBits) IdxBits |> ;
      tagFind: tag === s.["dataArray.tag" __ c];
      line: <| Vector (Line LgDataBytes LgNumDatas) IdxBits |> ;
      lineFind: line === s.["dataArray.line" __ c];
      procv: <| Bool |> ;
      procVFind: procv === s.["procRqValid" __ c];
      procRqReplace: <| Bool |> ;
      procRqReplaceFind: procRqReplace === s.["procRqReplace" __ c];
      procRq: <| RqFromProc LgDataBytes (Bit (TagBits + IdxBits + LgNumDatas)) |> ;
      procRqFind: procRq === s.["procRq" __ c];
      csw: <| Bool |> ;
      cswFind: csw === s.["procRqWait" __ c];
      rqToPList: << list (type (RqToP (Bit AddrBits) Id)) >> ;
      rqToPListFind:  rqToPList === s.["elt.rqToParent" __ c];
      rsToPList: << list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) >> ;
      rsToPListFind: rsToPList === s.["elt.rsToParent" __ c];
      fromPList: << list (type (FromP LgDataBytes LgNumDatas
                                      (Bit AddrBits) Id)) >> ;
      fromPListFind: fromPList === s.["elt.fromParent" __ c];

      i5: (forall a, dir (getTagIdxS a) cword >= getCs cs tag a);
      
      i6: (forall a, isCompat cword (dir (getTagIdxS a)));
      
      i7: (forall a rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                        getCs cs tag a <= rs ``"to" /\ dir (getTagIdxS a) cword > rs ``"to");

      i8: (forall a msg, In msg (fromPToC cword a fromPList toCList) ->
                         msg ``"isRq" = false ->
                         getCs cs tag a < msg ``"to" /\ dir (getTagIdxS a) cword = msg ``"to");

      i9: (forall a rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                        dir (getTagIdxS a) cword <= rq ``"from" ->
                        forall rs,
                          In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                          isPWait a cRqValid rqFromCList dirw cword);

      i10: (forall a msg1 msg2 beg mid last,
              fromPToC cword a fromPList toCList = beg ++ msg1 :: mid ++ msg2 :: last ->
              msg1 ``"isRq" = false ->
              msg2 ``"isRq" = false ->
              False)%list;
      
      i11: (forall a, dir (getTagIdxS a) cword > getCs cs tag a ->
                      rsFromCToP cword a rsFromCList rsToPList <> nil);
      
      i12: (forall a,
              rsFromCToP cword a rsFromCList rsToPList = nil \/
              forall msg, In msg (fromPToC cword a fromPList toCList) -> msg ``"isRq" = true);

      i13: (forall a, rsLessTo (rsFromCToP cword a rsFromCList rsToPList));

      i14: (forall a cToPRsLast beg,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ [cToPRsLast] ->
              cToPRsLast ``"to" = getCs cs tag a)%list;

      i15: (forall a pToCRq pToCRs beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRq :: mid ++ pToCRs :: last ->
              pToCRq ``"isRq" = true ->
              pToCRs ``"isRq" = false ->
              getCs cs tag a = $ Msi.Inv)%list;

      i16: (forall a,
              isCWait a procv procRq csw ->
              xor (exists rq, In rq (rqFromCToP cword a rqFromCList rqToPList)
                              /\ rq ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod
                                              else $ Msi.Sh)
                              /\ rq ``"from" >= getCs cs tag a)
                  (exists rs, In rs (fromPToC cword a fromPList toCList)
                              /\ rs ``"isRq" = false
                              /\ rs ``"to" = if (procRq ``"op"):bool then $ Msi.Mod
                                             else $ Msi.Sh));

      i16a: (forall a rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                          isCWait a procv procRq csw
                          /\ rq ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh)
                          /\ rq ``"from" >= getCs cs tag a);

      i16b: (forall a rs, In rs (fromPToC cword a fromPList toCList) ->
                          isCWait a procv procRq csw
                          /\ rs ``"isRq" = false
                          /\ rs ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh));

      i17: (forall a pToCRq,
              In pToCRq (fromPToC cword a fromPList toCList) ->
              pToCRq ``"isRq" = true ->
              isPWait a cRqValid rqFromCList dirw cword ->
              getCs cs tag a = $ Msi.Inv);

      i18: (forall a pToCRq cToPRs,
              In pToCRq (fromPToC cword a fromPList toCList) ->
              pToCRq ``"isRq" = true ->
              In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
              cToPRs ``"to" = $ Msi.Inv);

      i19: (forall a pToCRs pToCRq beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRs :: mid ++ pToCRq :: last ->
              pToCRs ``"isRq" = false ->
              pToCRq ``"isRq" = true ->
              isPWait a cRqValid rqFromCList dirw cword)%list;

      i20: (forall a pToCRq1 pToCRq2 beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRq1 :: mid ++ pToCRq2 :: last ->
              pToCRq1 ``"isRq" = true ->
              pToCRq2 ``"isRq" = true ->
              getCs cs tag a = $ Msi.Inv)%list;

      i21: (forall a rs,
              In rs (rsFromCToP cword a rsFromCList rsToPList) ->
              rs ``"isVol" = false ->
              isPWait a cRqValid rqFromCList dirw cword);

      i22: (forall a cToPRs1 cToPRs2 beg mid last,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ cToPRs1 :: mid ++ cToPRs2 :: last ->
              cToPRs1 ``"isVol" = true \/ cToPRs2 ``"isVol" = true)%list;

      i23: (forall a cToPRq,
              In cToPRq (rqFromCToP cword a rqFromCList rqToPList) ->
              dir (getTagIdxS a) cword <= cToPRq ``"from" ->
              forall cToPRs,
                In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
                cToPRs ``"isVol" = false);

      i24: (forall a, length (rsFromCToP cword a rsFromCList rsToPList) <= 2)%nat;

      i25: forall a rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                        rq ``"from" < rq ``"to";

      i26: forall a rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                        rs ``"isVol" = true ->
                        rs ``"to" = $ Msi.Inv
    }.

  Hint Unfold modFromMeta nmemCacheInl metaRegs metaRules metaMeths Concat.concat
       getListFromMetaReg getListFromMetaRule getListFromMetaMeth getCs getTagS getTagIdxS
       getIdxS getAddrS isCompat fromPToC rqFromCToP rsFromCToP isCWait isPWait
       withIndex: MethDefs.

  Definition nmemCache_invariants (s: RegsT) :=
    forall cword c,
      (c <= wordToNat (wones LgNumChildren))%nat ->
      cword = natToWord _ c ->
      nmemCache_invariants_rec s cword c.
  
  Theorem nmemCache_invariants_true s ll:
    Behavior (modFromMeta (nmemCacheInl IdxBits TagBits
                                        LgNumDatas LgDataBytes Id LgNumChildren)) s ll ->
    nmemCache_invariants s.
  Proof.
    intros beh.
    destruct beh.
    match goal with
      | H: Multistep _ ?P _ _ |- _ =>
        remember P as init
    end.
    induction HMultistepBeh; repeat subst; intros.
    - (* SKIP_PROOF_ON
      unfold nmemCacheInl, modFromMeta, metaRegs, getRegInits, initRegs;
      repeat (
          rewrite singleUnfoldConcat;
          rewrite makeMap_union;
          [| apply disjList_metaRegs; simpl; intro H;
             (repeat (destruct H; [discriminate | ]); assumption)]); simpl;
      cbv [getListFromRep];
      rewrite ?M.union_add, ?M.union_empty_R, ?M.union_empty_L.
      rewrite ?makeMap_fold_eq.
      prelimSimplRegs LgNumChildren.
      SKIP_PROOF_ON *) admit.
    - specialize (IHHMultistepBeh eq_refl).
      apply Lts.SemFacts.stepZero in HStep; [| apply eq_refl].
      dest; subst.
      destruct l.
      simpl in H, H0.
      destruct annot; subst; [| inv H0; rewrite M.union_empty_L; auto].
      clear - H0 IHHMultistepBeh.
      inv H0; [rewrite M.union_empty_L; auto|].
      apply In_metaRules in HInRules; dest; unfold nmemCacheInl in *; simpl in *; dest.
      doDestruct; unfold getActionFromGen, getGenAction, strFromName in HAction;
      simpl in *; SymEval.

(*
   - expression in asserts and if-then-else to be expanded
   - use default value for read regs (remove exists)
   - list of Prop or more structure to Prop
   - list of Prop -> implications

Theorem forall qs: list Prop, qs => Forall qs.
*)
      
      idtac.
      Reset Profile.
      Start Profiling.
      match goal with
        | H: (_ <= _)%nat |- _ =>
          destruct (IHHMultistepBeh _ _ H eq_refl);
            unfold withIndex in *;
            (repeat match goal with
                      | H:?x === ?m.[?s] |- exists v, v === ?m.[?s] /\ _ =>
                        exists x; split; [assumption | intros; auto]
                                       | |- _ /\ _ => split; auto
                               end)
      end.
            destructWeq;
            (repeat match goal with
                      | H: andb _ _ = true |- _ =>
                        apply Bool.andb_true_iff in H;
                      destruct H
                      | H: negb ?v = true |- _ => apply Bool.negb_true_iff in H; rewrite H
                      | H: negb ?v = false |- _ => apply Bool.negb_false_iff in H; rewrite H
                      | H: ?v = ?v |- _ => clear H
                    end); try discriminate
        | _ => idtac
      end.

      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      exists line.
      
      match goal with
        | H: (_ <= _)%nat |- _ =>
            (repeat match goal with
                      | H:?x === ?m.[?s] |- exists v, v === ?m.[?s] /\ _ =>
                        exists x; split; [assumption | intros; auto]
                                       | |- _ /\ _ => split; auto
                               end)
      end.
            destructWeq;

      simpl in H2.
                                               | _ => idtac
                              end.
      + SymEval.
        match goal with
          | H: (_ <= _)%nat |- _ =>
            destruct (IHHMultistepBeh _ _ H eq_refl)
        end.
                          do 4 intro.
                          esplit.
                          SymEval_simpl.
                          eapply Build_nmemCache_invariants_rec.
                          constructor.
        match goal with
          | |- ?p === ?m.[?i] =>
            match type of p with
              | ?Q => pose Q
            end
        end.
        eapply procVFind.
        Grab Existential Variables.
        eassumption.
        instantiate (1:= procv).
        apply procVFind.
        assumption.
        destruct (IHHMultistepBeh _ _ H eq_refl).
        unfold nmemCache_invariants; intros.
        destruct (IHHMultistepBeh _ _ H0 eq_refl).
        
        esplit.
        .
        repeat (try eexists; esplit; eauto).
        repeat (eexists; eauto).
        esplit; eauto.
        destruct IH.
      SymEval.

      + specialize (IHHMultistepBeh _ _ H eq_refl).

        Lemma test: forall A B (P: A -> B -> Prop),
                      forall a, exists b, P a b <-> exists b, forall a, P a b.
        destruct (IHHMultistepBeh).
        repeat (eexists; esplit; eauto).
               split.

      + (* SKIP_PROOF_ON
           allRules; intros; rule1.
         SKIP_PROOF_ON *) admit.
      + (* SKIP_PROOF_ON
           allRules; intros; rule1.
         SKIP_PROOF_ON *) admit.
      + (* SKIP_PROOF_ON
           allRules; intros; rule1.
         SKIP_PROOF_ON *) admit.
      + allRules; intros; mergeFinds; repeat rewrite mkStruct_eq in *;
        unfold StringBound.ith_Bounded in *; simpl in *.
        * admit.
        * match goal with
            | H: In rs (rsFromCToP ?x ?a ?l1 (?l2 ++ ?l3)) |- _ =>
              unfold rsFromCToP in H; rewrite filtRsToP_commute_app in H;
              rewrite app_assoc in H; fold (rsFromCToP x a l1 l2) in H; apply in_app_or in H;
              destruct H6
          end.
          admit.
          simpl in H6.
        try (unfold rsFromCToP in *; rewrite filtRsToP_commute_app in *;
             rewrite app_assoc in *; fold (rsFromCToP $(x) a rsFromCList rsToPList) in *).

        * repeat rewrite mkStruct_eq; unfold StringBound.ith_Bounded; simpl.
          unfold getCs in *.
          destructWeq.
        * repeat rewrite mkStruct_eq; unfold StringBound.ith_Bounded; simpl.
          apply 
          unfold getCs in *.
          rewrite rsFromCToP_app_commute in H6.
          simpl.
          { destructWeq; unfold negb in *; try discriminate.
            - rewrite <- e0 in n0.
              admit.
            - admit.
            - admit.
          } 
              constructor; [pre_nomega; omega | ].
              apply i5 in n0.
          
          { destructWeq.
          { destructWeq.
            rewrite <- e0 in e1.
            rewrite <- e1.

            constructor.
            - destructWeq.
              + unfold negb in *; discriminate.
              + 
                - 
              
            [destructWeq; pre_nomega; nomega | ].
            - 
            - constructor; [pre_nomega; nomega | ].
              unfold negb in *; discriminate.
            - 
          destructWeq; mergeFinds.
          mergeFinds.
          repeat match goal with
             | H: M.find ?x ?m = Some ?p1, H': M.find ?x ?m = Some ?p2 |- _ =>
               rewrite H in H'
          (*end.
          repeat match goal with *)
                   | H: Some ?p = Some ?q |- _ =>
                     apply invSome in H; destruct_existT; (try discriminate || auto)
           end. 


          unfold getCs in *.
        * mergeFinds; destructWeq.
        * mergeFinds; destructWeq.
          unfold negb in *; try discriminate.
          constructor; [pre_nomega; nomega | ].
          apply i7.
          apply in_or_app.
          apply in_app_or in H6.
          destruct H6; intuition auto.
          rewrite filtRsToP_commute_app in H6.
          apply in_app_or in H6.
          destruct H6; intuition auto.
          simpl in H6.
          repeat rewrite mkStruct_eq in H6; unfold StringBound.ith_Bounded in H6; simpl in H6.
          unfold AddrBits in *; destructWeq.
          simpl in H6.
          destruct H6; [ | exfalso; auto].
          exfalso.
          subst.
          match goal with
             | |- context[weq ?p ?q] => destruct (weq p q)
             | H: context[weq ?p ?q] |- _ => destruct (weq p q)
           end.
          destructWeq.
          
                               
        * 
          mergeFinds.
        * destructWeq; auto; mergeFinds; auto.
        * 
        pre_nomega;nomega.
          repeat match goal with
                   | H: M.find ?x ?m = Some ?p1, H': M.find ?x ?m = Some ?p2 |- _ =>
                     rewrite H in H'
                   | H: Some ?p = Some ?q |- _ =>
                     apply invSome in H; destruct_existT; (try discriminate || auto)
                 end.
        * repeat rewrite mkStruct_eq; unfold StringBound.ith_Bounded; simpl.
          unfold getCs in *; repeat match goal with
                                      | |- context[weq ?p ?q] => destruct (weq p q)
                                      | H: context[weq ?p ?q] |- _ => destruct (weq p q)
                                    end; ((pre_nomega; nomega) || auto);
          repeat match goal with
                   | H: M.find ?x ?m = Some ?p1, H': M.find ?x ?m = Some ?p2 |- _ =>
                     rewrite H in H'
                   | H: Some ?p = Some ?q |- _ =>
                     apply invSome in H; destruct_existT; (try discriminate || auto)
                 end.
       * 
          
          repeat match goal with
                   | H: M.find ?x ?m = Some ?p1, H': M.find ?x ?m = Some ?p2 |- _ =>
                     rewrite H in H'
                   | H: Some ?p = Some ?q |- _ =>
                     apply invSome in H; destruct_existT; auto
                 end.

          
          unfold getIdxS.
        *
          Theorem test: existT (fun t => t) bool true = existT (fun t => t) bool false -> False.
          Proof.
            intros H.
            apply Eqdep.EqdepTheory.inj_pair2 in H.
            discriminate.
          Qed.

          Theorem test2:
            forall (U : Type) (Q : U -> Type) (p :U) (x : Q p) (h: p = p),
              True.
          Proof.
            clear.
            intros.
            pose (eq_rect p Q x p h).
            unfold eq_rect in q; simpl in q.
            intros.
            pose U: Type).
              forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
            exact Eqdep.EqdepTheory.inj_pair2.
      Qed.

      Print Assumptions test.
        *             repeat match goal with
             | H: isCWait _ _ _ _ |- _ => unfold isCWait in H; dest; discriminate
             | H: In ?rq ?l, H': forall rq, In rq ?l -> isCWait _ _ _ _ /\ _ |- _ =>
               apply H' in H; [unfold isCWait in H; dest; subst]
             | H: M.find ?x ?m = Some ?p1, H': M.find ?x ?m = Some ?p2 |- _ =>
               rewrite H in H'
             | H: Some ?p = Some ?q |- _ => apply invSome in H; destruct_existT; discriminate
                             end.

        repeat autounfold with MethDefs in *; dest.
        discriminate.

           end.

        intros; solve [rule1].
        intros; solve [rule1].
        solve rule1.
        
        match goal with
          | |- context[eq_nat_dec ?c ?x] =>
            destruct (eq_nat_dec c x)
          | |- _ => idtac
        end; auto.

        intros; rule1.
        intros; subst.
        apply i16a in H1; dest.
        unfold isCWait in H1.
        dest.
        rule1.
        intros; subst; rule1.
End MemCacheInl.
