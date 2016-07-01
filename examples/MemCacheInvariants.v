Require Import Lib.FMap Lib.Word Ex.MemTypes Lib.Indexer Lib.Struct Ex.Msi
        Ex.NativeFifo Lts.Notations String Ex.MemCacheInl Lts.Syntax List Lts.Semantics
        ParametricSyntax Lib.CommonTactics Lts.SemFacts Lib.FMap Lib.Concat
        FunctionalExtensionality Program.Equality Lts.Tactics Arith.

Set Implicit Arguments.

Lemma mapVec_replicate_commute:
  forall A B (f: A -> B) n v, mapVec f (replicate v n) = replicate (f v) n.
Proof.
  induction n; simpl in *; auto; intros.
  rewrite IHn; reflexivity.
Qed.

Lemma evalVec_replicate:
  forall A n (v: A) i, evalVec (replicate v n) i = v.
Proof.
  induction n; simpl in *; auto; intros.
  dependent destruction i.
  destruct b;
    rewrite IHn; reflexivity.
Qed.

Require Import Nomega NArith.

Theorem roundTrip_0' : forall sz, wordToN (natToWord sz 0) = 0%N.
  induction sz; simpl; subst; intuition.
  rewrite IHsz.
  auto.
Qed.


Lemma wzero_le:
  forall n (w: word n), wzero n <= w.
Proof.
  unfold wzero, not; intros.
  pre_nomega.
  rewrite roundTrip_0' in H.
  nomega.
Qed.
  
Section makeMapUnion.
  Variable A: Type.
  Variable f1 f2: A -> Type.
  Variable f: forall x, f1 x -> f2 x.

  Theorem makeMapUnion l1 l2:
    (forall i, In i (namesOf l1) -> In i (namesOf l2) -> False) ->
    makeMap f2 f (l1 ++ l2) = M.union (makeMap f2 f l1) (makeMap f2 f l2).
  Proof.
    intros.
    apply makeMap_union.
    unfold DisjList; intros.
    specialize (H e).
    pose proof (in_dec string_dec e (namesOf l1)) as K1.
    pose proof (in_dec string_dec e (namesOf l1)) as K2.
    destruct K1, K2; intuition auto.
  Qed.
End makeMapUnion.
  
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

  Local Notation "x 'is' y 'of' s" := (M.find y%string s = Some (existT _ _ x)) (at level 12).

  Local Notation "<| t |>" := (fullType type (SyntaxKind t)).

  Local Notation "<< t >>" := (fullType type (@NativeKind t nil)).

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

  Definition fromPToC
             (c: word LgNumChildren) (a: word AddrBits)
             (l1: list (type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id)))
             (l2: list (type (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))):
    list (type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id)) :=
    filtFromP a l1 ++ filtToC c a l2.

  Definition getCs (cs: word IdxBits -> type Msi) (tag: word IdxBits -> word TagBits)
             (a: word AddrBits) :=
    if weq (cs (getIdxS a)) ($ Msi.Inv)
    then $ Msi.Inv
    else if weq (tag (getIdxS a)) (getTagS a)
         then cs (getIdxS a)
         else $ Msi.Inv.

  Definition xor a b := (a /\ ~ b) \/ (~ a /\ b).

  Local Notation "x '__' y" := (addIndexToStr string_of_nat y x).

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

  Definition nmemCache_invariants (s: RegsT) :=
    forall (a: word (TagBits + IdxBits)) cword c,
      (c <= wordToNat (wones LgNumChildren))%nat ->
      cword = natToWord _ c ->
    exists dir: <| Vector (Vector Msi LgNumChildren) (TagBits + IdxBits) |> ,
      dir is "dataArray.mcs" of s
    /\ exists mline:
                <|Vector (Line LgDataBytes LgNumDatas) (TagBits + IdxBits) |> ,
         mline is "dataArray.mline" of s
    /\ exists cRqValid: <| Bool |> ,
         cRqValid is "cRqValid" of s
    /\ exists dirw: <| Vector Bool LgNumChildren |> ,
         dirw is "cRqDirw" of s
    /\ exists rqFromCList: << list (type (RqFromC LgNumChildren (Bit AddrBits) Id)) >> ,
         rqFromCList is "elt.rqFromChild" of s
    /\ exists rsFromCList: << list (type (RsFromC LgDataBytes LgNumDatas LgNumChildren
                                                  (Bit AddrBits))) >> ,
         rsFromCList is "elt.rsFromChild" of s
    /\ exists toCList: << list (type
                                  (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))
                          >> ,
         toCList is "elt.toChild" of s
    /\ exists cs: <| Vector Msi IdxBits |> ,
         cs is ("dataArray.cs" __ c) of s
    /\ exists tag: <| Vector (Bit TagBits) IdxBits |> ,
         tag is ("dataArray.tag" __ c) of s
    /\ exists line: <| Vector (Line LgDataBytes LgNumDatas) IdxBits |> ,
         line is ("dataArray.line" __ c) of s
    /\ exists procv: <| Bool |> ,
         procv is ("procRqValid" __ c) of s
    /\ exists procRq: <| RqFromProc LgDataBytes (Bit (TagBits + IdxBits + LgNumDatas)) |> ,
         procRq is ("procRq" __ c) of s
    /\ exists csw: <| Bool |> ,
         csw is ("procRqWait" __ c) of s
    /\ exists rqToPList: << list (type (RqToP (Bit AddrBits) Id)) >> ,
         rqToPList is ("elt.rqToParent" __ c) of s
    /\ exists rsToPList: << list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) >> ,
         rsToPList is ("elt.rsToParent" __ c) of s
    /\ exists fromPList: << list (type (FromP LgDataBytes LgNumDatas
                                              (Bit AddrBits) Id)) >> ,
         fromPList is ("elt.fromParent" __ c) of s

    (* 5 *)
    /\ (dir (getTagIdxS a) cword >= getCs cs tag a)
              
    (* 6 *)
    /\ isCompat cword (dir (getTagIdxS a))
                
    (* 7 *)
    /\ (forall rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                   getCs cs tag a <= rs ``"to" /\ dir (getTagIdxS a) cword > rs ``"to")

    (* 8 *)
    /\ (forall msg, In msg (fromPToC cword a fromPList toCList) ->
                    msg ``"isRq" = false ->
                    getCs cs tag a < msg ``"to" /\ dir (getTagIdxS a) cword = msg ``"to")

    (* 9 *)
    /\ (forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                   dir (getTagIdxS a) cword <= rq ``"from" ->
                   forall rs,
                     In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                     isPWait a cRqValid rqFromCList dirw cword)

    (* 10 *)
    /\ (forall msg1 msg2 beg mid last,
          fromPToC cword a fromPList toCList = beg ++ msg1 :: mid ++ msg2 :: last ->
          msg1 ``"isRq" = false ->
          msg2 ``"isRq" = false ->
          False)
                   
    (* 11 *)
    /\ (dir (getTagIdxS a) cword > getCs cs tag a ->
        rsFromCToP cword a rsFromCList rsToPList <> nil)
         
    (* 12 *)
    /\ (rsFromCToP cword a rsFromCList rsToPList = nil \/
        forall msg, In msg (fromPToC cword a fromPList toCList) -> msg ``"isRq" = true)

    (* 13 *)
    /\ (rsLessTo (rsFromCToP cword a rsFromCList rsToPList))

    (* 14 *)
    /\ (forall cToPRsLast beg,
          rsFromCToP cword a rsFromCList rsToPList = beg ++ [cToPRsLast] ->
          cToPRsLast ``"to" = getCs cs tag a)

    (* 15 *)
    /\ (forall pToCRq pToCRs beg mid last,
          fromPToC cword a fromPList toCList = beg ++ pToCRq :: mid ++ pToCRs :: last ->
          pToCRq ``"isRq" = true ->
          pToCRs ``"isRq" = false ->
          getCs cs tag a = $ Msi.Inv)

    (* 16 *)
    /\ (isCWait a procv procRq csw ->
        xor (exists rq, In rq (rqFromCToP cword a rqFromCList rqToPList)
                        /\ rq ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh)
                        /\ rq ``"from" >= getCs cs tag a)
            (exists rs, In rs (fromPToC cword a fromPList toCList)
                        /\ rs ``"isRq" = false
                        /\ rs ``"to" = if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh))

    (* 16a *)
    /\ (forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                   isCWait a procv procRq csw
                   /\ rq ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh)
                   /\ rq ``"from" >= getCs cs tag a)

    (* 16b *)
    /\ (forall rs, In rs (fromPToC cword a fromPList toCList) ->
                   isCWait a procv procRq csw
                   /\ rs ``"isRq" = false
                   /\ rs ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh))

    (* 17 *)
    /\ (forall pToCRq,
          In pToCRq (fromPToC cword a fromPList toCList) ->
          pToCRq ``"isRq" = true ->
          isPWait a cRqValid rqFromCList dirw cword ->
          getCs cs tag a = $ Msi.Inv)

    (* 18 *)
    /\ (forall pToCRq cToPRs,
          In pToCRq (fromPToC cword a fromPList toCList) ->
          pToCRq ``"isRq" = true ->
          In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
          cToPRs ``"to" = $ Msi.Inv)

    (* 19 *)
    /\ (forall pToCRs pToCRq beg mid last,
          fromPToC cword a fromPList toCList = beg ++ pToCRs :: mid ++ pToCRq :: last ->
          pToCRs ``"isRq" = false ->
          pToCRq ``"isRq" = true ->
          isPWait a cRqValid rqFromCList dirw cword)

    (* 20 *)
    /\ (forall pToCRq1 pToCRq2 beg mid last,
          fromPToC cword a fromPList toCList = beg ++ pToCRq1 :: mid ++ pToCRq2 :: last ->
          pToCRq1 ``"isRq" = true ->
          pToCRq2 ``"isRq" = true ->
          getCs cs tag a = $ Msi.Inv)

    (* 21 *)
    /\ (forall rs,
          In rs (rsFromCToP cword a rsFromCList rsToPList) ->
          rs ``"isVol" = false ->
          isPWait a cRqValid rqFromCList dirw cword)

    (* 22 *)
    /\ (forall cToPRs1 cToPRs2 beg mid last,
          rsFromCToP cword a rsFromCList rsToPList = beg ++ cToPRs1 :: mid ++ cToPRs2 :: last ->
          cToPRs1 ``"isVol" = true \/ cToPRs2 ``"isVol" = true)

    (* 23 *)
    /\ (forall cToPRq,
          In cToPRq (rqFromCToP cword a rqFromCList rqToPList) ->
          dir (getTagIdxS a) cword <= cToPRq ``"from" ->
          forall cToPRs,
            In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
            cToPRs ``"isVol" = false)

    (* 24 *)
    /\ (length (rsFromCToP cword a rsFromCList rsToPList) <= 2)%nat.

  Hint Unfold modFromMeta nmemCacheInl metaRegs metaRules metaMeths Concat.concat
       getListFromMetaReg getListFromMetaRule getListFromMetaMeth: MethDefs.


  Lemma singleUnfoldConcat A B a (f: A -> list B) (ls: list A):
    concat (map f (a :: ls)) = f a ++ concat (map f ls).
  Proof.
    reflexivity.
  Qed.

  Section ConvMakeMap.
    Variable A: Type.
    Variable f1 f2: A -> Type.
    Variable f: forall x, f1 x -> f2 x.

    Variable g: nat -> Attribute (sigT f1).

    Fixpoint repMap n :=
      M.add (attrName (g n))
            (existT _ (projT1 (attrType (g n))) (f (projT2 (attrType (g n)))))
            match n with
              | 0 => M.empty _
              | S m => repMap m
            end.
    Lemma makeMap_fold_eq n:
      makeMap f2 f (map g (getNatListToN n)) = repMap n.
    Proof.
      induction n; simpl in *; auto.
      destruct (g 0); destruct attrType; simpl; auto.
      rewrite <- IHn.
      destruct (g (S n)); destruct attrType; reflexivity.
    Qed.
  End ConvMakeMap.

  Section MapVar.
    Require Import Lib.StringEq.
    Variable n: nat.
    Variable A: Type.
    Variable f1 f2: A -> Type.
    Variable f: forall x, f1 x -> f2 x.

    Inductive MapVR : M.t (sigT f2) -> Type :=
    | MVParam m: MapVR m
    | MVREmpty: MapVR (M.empty _)
    | MVRAdd:
        forall k (pf: index 0 indexSymbol k = None) v {m},
          MapVR m -> MapVR (M.add k v m)
    | MVRAddV:
        forall k (pf: index 0 indexSymbol k = None) i v {m},
          MapVR m -> MapVR (M.add (k __ i) v m)
    | MVRUnion:
        forall {m1 m2},
          MapVR m1 -> MapVR m2 ->
          MapVR (M.union m1 m2)
    | MVRVar s (pf: index 0 indexSymbol s = None) (v: sigT f1) m (mr: MapVR m):
        MapVR
          (M.union (repMap f2 f (fun i => (addIndexToStr string_of_nat
                                                         i s :: v)%struct) n) m).

    Fixpoint findMVR_string k (pf: index 0 indexSymbol k = None)
             {m} (mr : MapVR m): option (sigT f2) :=
      match mr with
        | MVParam m => M.find k m
        | MVREmpty => None
        | MVRAdd k' pf' v _ mr' => if string_eq k k'
                                   then Some v else findMVR_string k pf mr'
        | MVRAddV k' pf' i v _ mr' => findMVR_string k pf mr'
        | MVRUnion _ _ mr1 mr2 =>
          match findMVR_string k pf mr1 with
            | Some v => Some v
            | _ => findMVR_string k pf mr2
          end
        | MVRVar s pf' v m mr => findMVR_string k pf mr
      end.

    Fixpoint findMVR_var k (pf: index 0 indexSymbol k = None)
             i {m} (mr : MapVR m): option (sigT f2) :=
      match mr with
        | MVParam m => M.find (addIndexToStr string_of_nat i k) m
        | MVREmpty => None
        | MVRAdd k' pf' v _ mr' => findMVR_var k pf i mr'
        | MVRAddV k' pf' i' v _ mr' => if string_eq k k'
                                       then if eq_nat_dec i i'
                                            then Some v
                                            else findMVR_var k pf i mr'
                                       else findMVR_var k pf i mr'
        | MVRUnion _ _ mr1 mr2 =>
          match findMVR_var k pf i mr1 with
            | Some v => Some v
            | _ => findMVR_var k pf i mr2
          end
        | MVRVar s pf' v m mr => if string_eq k s
                                 then Some (existT _ (projT1 v) (f (projT2 v)))
                                 else findMVR_var k pf i mr
      end.

    Lemma not_find_string_rep:
      forall s (pfs: index 0 indexSymbol s = None) k (pf: index 0 indexSymbol k = None) v,
        M.Map.find (elt:=sigT f2) k
                   (repMap f2 f
                           (fun i : nat =>
                              (addIndexToStr string_of_nat i s :: v)%struct) n) = None.
    Proof.
      induction n; simpl in *; auto; intros.
      - rewrite <- (@M.find_empty _ k).
        apply M.find_add_2.
        intro H; subst;
        apply badIndex in pf; auto.
      - rewrite M.find_add_2; auto.
        intro H; subst; apply badIndex in pf; auto.
    Qed.

    Lemma not_find_string_var:
      forall k k0 (pf0: index 0 indexSymbol k0 = None) i v m,
        M.find (elt:=sigT f2) k0 (M.add (k) __ (i) v m) = M.find k0 m.
    Proof.
      induction n; simpl in *; auto; intros.
      rewrite M.find_add_2; auto.
      intro H; subst.
      apply badIndex in pf0.
      auto.
    Qed.
      

    
    Lemma findMVR_find_string:
      forall m (mr: MapVR m) k (pf: index 0 indexSymbol k = None),
        findMVR_string k pf mr = M.find k m.
    Proof.
      induction mr; simpl; auto; intros.
      - dest_str; simpl in *.
        specialize (IHmr k pf); simpl in *.
        findeq.
        specialize (IHmr k0 pf0); simpl in *.
        findeq.
      - rewrite not_find_string_var; auto.
      - specialize (IHmr1 k pf); specialize (IHmr2 k pf); findeq.
      - rewrite IHmr.
        rewrite M.find_union.
        rewrite not_find_string_rep; auto.
    Qed.

    Lemma find_var_rep:
      forall i s v,
        (i <= n)%nat ->
        M.Map.find (addIndexToStr string_of_nat i s)
                   (repMap f2 f
                           (fun i0 : nat =>
                              (addIndexToStr string_of_nat i0 s :: v)%struct) n) =
        Some (existT _ (projT1 v) (f (projT2 v))).
    Proof.
      induction n; simpl in *; auto; intros.
      - assert (i = 0) by omega; subst; apply M.find_add_1.
      - assert (dst: i = S n0 \/ (i <= n0)%nat) by omega.
        destruct dst as [ez | hard]; subst.
        + apply M.find_add_1.
        + rewrite M.find_add_2; auto.
          intro sth.
          pose proof (withIndex_index_eq s s i (S n0) sth).
          dest; omega.
    Qed.

    Lemma not_find_var_rep:
      forall i s s' v,
        s <> s' ->
        M.Map.find (elt:=sigT f2) (addIndexToStr string_of_nat i s)
                   (repMap f2 f
                           (fun i0 : nat =>
                              (addIndexToStr string_of_nat i0 s' :: v)%struct) n)
        = None.
    Proof.
      induction n; simpl; auto; intros.
      - rewrite M.find_add_2; auto.
        intro sth;
          pose proof (withIndex_index_eq s s' i 0 sth).
        dest; auto.
      - rewrite M.find_add_2; auto.
        intro sth;
          pose proof (withIndex_index_eq s s' i (S n0) sth).
        dest; auto.
    Qed.

    Lemma addStrGood si sj i j:
      si __ i = sj __ j -> si = sj /\ i = j.
    Proof.
      intros.
      unfold addIndexToStr in H.
      assert (withIndex si i = withIndex sj j) by
          (rewrite withIndex_eq; assumption).
      apply withIndex_index_eq; auto.
    Qed.
      
    Lemma findMVR_find_var:
      forall m (mr: MapVR m) k pf i,
        (i <= n)%nat ->
        findMVR_var k pf i mr =
        M.find (addIndexToStr string_of_nat i k) m.
    Proof.
      induction mr; simpl; auto; intros.
      - rewrite M.find_add_2; auto.
        let H := fresh in intro H; subst; apply badIndex in pf; auto.
      - dest_str; simpl in *.
        + destruct (eq_nat_dec i0 i); simpl in *; subst.
          * findeq.
          * rewrite M.find_add_2; auto.
            intro sth.
            apply addStrGood in sth; dest; auto.
        + rewrite M.find_add_2; auto.
          intro sth.
          apply addStrGood in sth; dest; auto.
      - rewrite M.find_union.
        rewrite (@IHmr1 _ _ i), (@IHmr2 _ _ i); auto.
      - dest_str; simpl in *.
        + rewrite M.find_union.
          rewrite find_var_rep; auto.
        + rewrite M.find_union.
          rewrite <- (IHmr k pf0 i); auto.
          rewrite (not_find_var_rep i); auto.
    Qed.
  End MapVar.

  Ltac mapVReify f2 f n m :=
    match m with
      | M.union
          (repMap _ _ (fun i => (addIndexToStr string_of_nat
                                                  i ?s :: ?v)%struct) _) ?m
        =>
        let mr := mapVReify f2 f n m in
        constr:(MVRVar s eq_refl v mr)
      | M.empty _ => constr:(MVREmpty n _ f2 f)
      | M.add (?k __ ?i) ?v ?m' =>
        let mr' := mapVReify f2 f n m' in
        constr:(MVRAddV k eq_refl i v mr')
      | M.add ?k ?v ?m' =>
        let mr' := mapVReify f2 f n m' in
        constr:(MVRAdd k eq_refl v mr')
      | M.union ?m1 ?m2 =>
        let mr1 := mapVReify f2 f n m1 in
        let mr2 := mapVReify f2 f n m2 in
        constr:(MVRUnion mr1 mr2)
      | _ => constr:(MVParam n _ f m)
    end.

  Ltac mapVR m := mapVReify (fullType type) evalConstFullT
                            (wordToNat (wones LgNumChildren)) m.

  Ltac mapVR2 t m := mapVReify t (fun k (v: t k) => v)
                               (wordToNat (wones LgNumChildren)) m.

  Ltac mapVR3 m := mapVReify SignT (fun k (v: fullType type k) => v)
                             (wordToNat (wones LgNumChildren)) m.


  Ltac findVR mr cond :=
    repeat match goal with
      | |- M.find (?k __ ?c) _ = _ =>
        rewrite <- (findMVR_find_var mr k eq_refl cond)
      | |- M.find ?k _ = _ =>
        erewrite <- (findMVR_find_string mr k eq_refl)
    end.

  Ltac doSplit := split; [| try doSplit].

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

  Lemma In_getNatListToN: forall n i, In i (getNatListToN n) -> (i <= n)%nat.
  Proof.
    induction n; simpl in *; auto; intros.
    - destruct H; omega.
    - destruct H; subst; [ | apply IHn in H]; omega.
  Qed.

  Ltac doDestruct := (repeat match goal with
                               | H: _ \/ _ |- _ =>
                                 destruct H
                               | H: False |- _ => exfalso; auto
                               | _ => subst; simpl in *; dest;
                               match goal with
                                 | H: In ?i (getNatListToN ?n) |- _ =>
                                   apply In_getNatListToN in H; subst
                               end
                             end
                     ).


  Ltac solveFinds :=
    match goal with
        | |- ?inv ?s =>
          unfold inv;
            intros;
            let mr := mapVR s in
            match goal with
              | cond: (_ <= _)%nat |- _ =>
                repeat (eexists; split; [findVR mr cond; eauto |])
            end
      end;
      simpl in *.

  Ltac customCache := repeat match goal with
                               | H: andb ?a ?b = true |- _ =>
                                 apply Bool.andb_true_iff in H; dest
                               | H: (if weq ?a ?b then _ else _) = _ |- _ =>
                                 destruct (weq a b)
                               | H: true = true |- _ => clear H
                               | H: false = false |- _ => clear H
                               | H: true = false |- _  => discriminate
                               | H: false = true |- _ => discriminate
                             end.
        
  Lemma invSome: forall t (a b: t), Some a = Some b -> a = b.
  Proof.
    intros t a b cond; subst; inv cond; reflexivity.
  Qed.

  Ltac initRed :=
    kinv_action_dest;
    kinv_custom customCache;
    kinv_red; kregmap_red.

  Ltac rewriteFind :=
    repeat match goal with
             | cond: (?c <= wordToNat ?n)%nat, H: M.find (elt := sigT ?t)
                                                         (?k __ ?c) ?m = _ |- _ =>
               let mr := mapVR2 t m in
               rewrite <- (findMVR_find_var mr k eq_refl cond) in H
             | H: M.find (elt := sigT ?t) ?k ?m = _ |- _ =>
               let mr := mapVR2 t m in
               rewrite <- (findMVR_find_string mr k eq_refl) in H
           end; simpl in *; repeat match goal with
                                     | H: ?a = ?a |- _ => clear H
                                   end.

  Ltac instantiateExists :=
  match goal with
    | xcond: (?x <= wordToNat (wones LgNumChildren))%nat,
             prevState: ?inv ?n |- ?inv ?s =>
      let a := fresh in
      let cword := fresh in
      let c := fresh in
      let cond := fresh in
      let trans := fresh in
      let curr_a_c := fresh in
      unfold inv;
        intros a cword c cond trans;
        pose proof (prevState a cword c cond trans) as curr_a_c;
        dest;
        let mr := mapVR2 (fullType type) s in
        repeat (eexists; split;
                [findVR mr cond;
                  try ( (progress eauto)
                          ||
                          (progress simpl;
                           instantiate (1:= if eq_nat_dec c x then _ else _);
                           destruct (eq_nat_dec c x); eauto))
                | ])
  end.

  Ltac splitInv :=
  repeat (match goal with
            | |- _ /\ _ => split; [auto | ]
                                | _ => auto
          end);
  
  match goal with
    | |- context [eq_nat_dec ?c ?x] =>
      destruct (eq_nat_dec c x); subst; [|auto]; intros
  end.
  
  Ltac allRules :=
    initRed;
    rewriteFind;
    instantiateExists;
    splitInv.
  
  Ltac rule1 :=
    repeat match goal with
             | H: isCWait _ _ _ _ |- _ => unfold isCWait in H; dest; discriminate
             | H: In ?rq ?l, H': forall rq, In rq ?l -> _ |- _ =>
               apply H' in H; [unfold isCWait in H; dest; subst]
             | H: M.find ?x ?m = Some ?p1, H': M.find ?x ?m = Some ?p2 |- _ =>
               rewrite H in H'
             | H: Some ?p = Some ?q |- _ => apply invSome in H; destruct_existT; discriminate
           end.
  
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
          [| apply disjList_metaRegs; simpl; intro H; (repeat (destruct H; [discriminate | ]); assumption)]); simpl;
      cbv [getListFromRep];
      rewrite ?M.union_add, ?M.union_empty_R, ?M.union_empty_L.
      rewrite ?makeMap_fold_eq.

      solveFinds.

      cbv [getTagIdxS getTagS getIdxS getAddrS AddrBits
                      isCompat filtRqFromC filtRsFromC filtToC filtRqToP filtRsToP
                      filtFromP rqFromCToP rsFromCToP fromPToC getCs].

      doSplit; intros; try (exfalso; assumption);
      repeat (rewrite ?mapVec_replicate_commute, ?evalVec_replicate in *; simpl in *; idtac); auto.
      + apply wzero_le.
      + exfalso; apply app_cons_not_nil in H1; auto.
      + nomega.
      + exfalso; apply app_cons_not_nil in H1; auto.
      + constructor; intros; unfold xor in *; simpl in *.
        * discriminate.
        * destruct H1; dest; exfalso; auto.
      + exfalso; apply app_cons_not_nil in H1; auto.
      + exfalso; apply app_cons_not_nil in H1; auto.
       END_SKIP_PROOF_ON *) admit.
    - specialize (IHHMultistepBeh eq_refl).
      apply Lts.SemFacts.stepZero in HStep; [| apply eq_refl].
      dest; subst.
      destruct l.
      simpl in H, H0.
      destruct annot; subst; [| inv H0; rewrite M.union_empty_L; auto].
      clear - H0 IHHMultistepBeh.
      inv H0; [rewrite M.union_empty_L; auto|].

      apply In_metaRules in HInRules; dest; unfold nmemCacheInl in *; simpl in *; dest.

      doDestruct; unfold getActionFromGen, getGenAction, strFromName in HAction; simpl in *.

      + admit.
      + admit.
      + admit.
      + initRed.
        rewriteFind.
        Print Ltac dest.

  match goal with
    | xcond: (?x <= wordToNat (wones LgNumChildren))%nat,
             prevState: nmemCache_invariants ?n |- nmemCache_invariants ?s =>
      let a := fresh in
      let cword := fresh in
      let c := fresh in
      let cond := fresh in
      let trans := fresh in
      let curr_a_c := fresh in
      unfold nmemCache_invariants;
        intros a cword c cond trans;
        pose proof (prevState a cword c cond trans) as curr_a_c;
        (* dest; *)
        idtac end.

  Ltac unitt :=
    match goal with
   | H:_ /\ _ |- _ => destruct H
   | H:exists _, _ |- _ => destruct H
    end.

  do 25 unitt.
  unitt.
  unitt.

        let mr := mapVR2 (fullType type) s in
        (eexists; split;
                [findVR mr cond;
                  try ( (progress eauto)
                          ||
                          (progress simpl;
                           instantiate (1:= if eq_nat_dec c x then _ else _);
                           destruct (eq_nat_dec c x); eauto))
                | ])
  end.


        Reset Profile.
        Start Profiling.
        
        instantiateExists.

        Stop Profiling.
        Show Profile.
        repeat match goal with
          | H: M.Disj _ _ |- _ => clear H
               end.
        unfold nmemCache_invariants; intros.
        instantiateExists.
        
      + initRed.
        instantiateExists.
      + initRed.
      + allRules.
        * rule1.
        * rule1.
        * rule1.
      + allRules.
        * rule1.
        * rule1.
        * rule1.
      + allRules.
        * rule1.
        * rule1.
        * rule1.
      + allRules.






      + 
        thisSubgoal.
        thisSubgoal.
        thisSubgoal.

                repeat match goal with
          | H: isCWait _ _ _ _ |- _ => unfold isCWait in H; dest; discriminate
          | H: In ?rq ?l, H': forall rq, In rq ?l -> _ |- _ =>
            apply H' in H; [unfold isCWait in H; dest; subst]
        end.

        thisSubgoal.
        apply H37 in H2; dest.
        unfold isCWait in *; dest.
        subst.
        rewrite H19 in H0.
        apply invSome in H0.
        destruct_existT; discriminate.
        apply H38 in H2; dest.
        unfold isCWait in *; dest.
        subst.
        rewrite H19 in H0.
        apply invSome in H0.
        destruct_existT; discriminate.
  Qed.
End MemCacheInl.
