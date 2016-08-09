Require Import Lib.FMap Lib.Word Ex.MemTypes Lib.Indexer Lib.Struct Ex.Msi
        Ex.NativeFifo Lts.Notations String Ex.MemCacheInl Lts.Syntax List Lts.Semantics
        ParametricSyntax Lib.CommonTactics Lts.SemFacts Lib.FMap Lib.Concat
        FunctionalExtensionality Program.Equality Lts.Tactics Arith Ex.MapVReify Lts.SymEval
        Lts.SymEvalTac Lib.StringAsList Lib.StringBound.

Set Implicit Arguments.

(* Local Notation "x 'is' y 'of' s" := (M.find y%string s = Some (existT _ _ x)) (at level 12). *)

(*
Ltac findVR mr cond :=
  repeat match goal with
           | |- M.find (addIndexToStr string_of_nat ?c ?k) _ = _ =>
             rewrite <- (findMVR_find_var mr k eq_refl cond)
           | |- M.find ?k _ = _ =>
             rewrite <- (findMVR_find_string mr k eq_refl)
         end.
*)

Local Notation "<| t |>" := (fullType type (SyntaxKind t)).

Local Notation "<< t >>" := (fullType type (@NativeKind t nil)).

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition getTagIdxS (x: word (TagBits + IdxBits)):
    word (TagBits + IdxBits) := x.

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

  Open Scope string.

  Fixpoint filtRqFromC
             (c: word LgNumChildren) (a: word AddrBits)
             (ls: list (type (RqFromC LgNumChildren (Bit AddrBits) Id))):
    list (type (RqToP (Bit AddrBits) Id)) :=
    match ls with
      | x :: xs => if weq c (x {| bindex := "child" |})
                   then if weq a (x {| bindex := "rq" |} {| bindex := "addr" |})
                        then x {| bindex := "rq" |} :: filtRqFromC c a xs
                        else filtRqFromC c a xs
                   else filtRqFromC c a xs
      | nil => nil
    end.

  Lemma filtRqFromC_commute_app:
    (forall c a l1 l2, (filtRqFromC c a (l1 ++ l2)) = filtRqFromC c a l1 ++ filtRqFromC c a l2)%list.
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
      | x :: xs => if weq c (x {| bindex := "child" |})
                   then if weq a (x {| bindex := "rs" |} {| bindex := "addr" |})
                        then x {| bindex := "rs" |} :: filtRsFromC c a xs
                        else filtRsFromC c a xs
                   else filtRsFromC c a xs
      | nil => nil
    end.

  Lemma filtRsFromC_commute_app:
    (forall c a l1 l2, (filtRsFromC c a (l1 ++ l2)) = filtRsFromC c a l1 ++ filtRsFromC c a l2)%list.
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
      | x :: xs => if weq c (x {| bindex := "child" |})
                   then if weq a (x {| bindex := "msg" |} {| bindex := "addr" |})
                        then x {| bindex := "msg" |} :: filtToC c a xs
                        else filtToC c a xs
                   else filtToC c a xs
      | nil => nil
    end.

  Lemma filtToC_commute_app:
    (forall c a l1 l2, (filtToC c a (l1 ++ l2)) = filtToC c a l1 ++ filtToC c a l2)%list.
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
      | x :: xs => if weq a (x {| bindex := "addr" |})
                   then x :: filtRqToP a xs
                   else filtRqToP a xs
      | nil => nil
    end.

  Lemma filtRqToP_commute_app:
    (forall a l1 l2, (filtRqToP a (l1 ++ l2)) = filtRqToP a l1 ++ filtRqToP a l2)%list.
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
      | x :: xs => if weq a (x {| bindex := "addr" |})
                   then x :: filtRsToP a xs
                   else filtRsToP a xs
      | nil => nil
    end.

  Lemma filtRsToP_commute_app:
    (forall a l1 l2, (filtRsToP a (l1 ++ l2)) = filtRsToP a l1 ++ filtRsToP a l2)%list.
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
      | x :: xs => if weq a (x {| bindex := "addr" |})
                   then x :: filtFromP a xs
                   else filtFromP a xs
      | nil => nil
    end.

  Lemma filtFromP_commute_app:
    (forall a l1 l2, (filtFromP a (l1 ++ l2)) = filtFromP a l1 ++ filtFromP a l2)%list.
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
    (filtRqFromC c a l1 ++ filtRqToP a l2)%list.

  Definition rsFromCToP
             (c: word LgNumChildren) (a: word AddrBits)
             (l1: list (type (RsFromC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits))))
             (l2: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))):
    list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) :=
    (filtRsFromC c a l1 ++ filtRsToP a l2)%list.

  Lemma filtRsToP_a: forall c a l2, filtRsFromC c a l2 = filtRsToP a (filtRsFromC c a l2).
  Proof.
    induction l2; simpl; auto; intros.
    repeat match goal with
             | |- context[weq ?c ?d] => destruct (weq c d); simpl; subst; intuition auto
           end.
    f_equal; auto.
  Qed.

  Lemma rsFromCToP_assoc c a l1 l2 l3:
    (rsFromCToP c a (l1 ++ l2) l3 = rsFromCToP c a l1 (filtRsFromC c a l2 ++ l3))%list.
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
      a <> t {| bindex := "addr" |} ->
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
    (filtFromP a l1 ++ filtToC c a l2)%list.

  Definition getCs (cs: word IdxBits -> type Msi) (tag: word IdxBits -> word TagBits)
             (a: word AddrBits) :=
    if weq (tag (getIdxS a)) (getTagS a)
    then cs (getIdxS a)
    else $ Msi.Inv.

  Definition xor a b := (a /\ ~ b) \/ (~ a /\ b).

  Fixpoint rsLessTo (ls: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))) :=
    match ls with
      | x :: y :: xs => x {| bindex := "to" |} > y {| bindex := "to" |} /\ rsLessTo xs
      | _ => True
    end.

  Definition isCWait a procV
             (procRq: type (RqFromProc LgDataBytes (Bit (TagBits + IdxBits + LgNumDatas))))
             csw :=
    procV = true /\ split1 (TagBits + IdxBits) LgNumDatas (procRq {| bindex := "addr" |}) = a /\
    csw = true.

  Definition isPWait a cRqValid
             (rqFromCList: list (type (RqFromC LgNumChildren (Bit (TagBits + IdxBits)) Id)))
             dirw (cword: word LgNumChildren) :=
    cRqValid = true /\
    dirw cword = true /\
    forall cRq, hd_error rqFromCList = Some cRq ->
                cRq {| bindex := "rq" |} {| bindex := "addr" |} = a.

  Lemma hd_error_same A ls: forall (a: A), hd_error ls = Some a ->
                                           forall v, hd_error (ls ++ [v]) = Some a.
  Proof.
    induction ls; auto; simpl; intros; discriminate.
  Qed.

  Lemma holdsNilList A (P: A -> Prop) (ls: list A):
    forall a, hd_error ls = Some a ->
              P a ->
              forall b v, hd_error (ls ++ [v]) = Some b ->
                          P b.
  Proof.
    intros.
    rewrite hd_error_same with (a := a) in H1; auto.
    inv H1; auto.
  Qed.
  
  Lemma singleUnfoldConcat A B a (f: A -> list B) (ls: list A):
    concat (map f (a :: ls)) = (f a ++ concat (map f ls))%list.
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

  (*
  Record nmemCache_invariants_simple_rec (s: RegsT)
         a cword c: Prop :=
    {
      cs: <| Vector Msi IdxBits |> ;
      csFind: cs === s.["dataArray.cs" __ c];
      tag: <| Vector (Bit TagBits) IdxBits |> ;
      tagFind: tag === s.["dataArray.tag" __ c];
      rsFromCList: << list (type (RsFromC LgDataBytes LgNumDatas LgNumChildren
                                          (Bit AddrBits))) >> ;
      rsFromCListFind: rsFromCList === s.["elt.rsFromChild"];
      rqFromCList: << list (type (RqFromC LgNumChildren (Bit AddrBits) Id)) >> ;
      rqFromCListFind: rqFromCList === s.["elt.rqFromChild"];
      rqToPList: << list (type (RqToP (Bit AddrBits) Id)) >> ;
      rqToPListFind:  rqToPList === s.["elt.rqToParent" __ c];
      rsToPList: << list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) >> ;
      rsToPListFind: rsToPList === s.["elt.rsToParent" __ c];
      procV: <| Bool |> ;
      procVFind: procV === s.["procRqValid" __ c];
      procRqReplace: <| Bool |> ;
      procRqReplaceFind: procRqReplace === s.["procRqReplace" __ c];
      procRq: <| RqFromProc LgDataBytes (Bit (TagBits + IdxBits + LgNumDatas)) |> ;
      procRqFind: procRq === s.["procRq" __ c]

    }.
   *)

  Record nmemCache_invariants_rec (s: RegsT)
         a cword c: Prop :=
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
      procV: <| Bool |> ;
      procVFind: procV === s.["procRqValid" __ c];
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

      i5: (dir (getTagIdxS a) cword >= getCs cs tag a);
      
      (* i6: (isCompat cword (dir (getTagIdxS a))); *)
      
      i7: (forall rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                      getCs cs tag a <= rs {| bindex := "to" |} /\
                      dir (getTagIdxS a) cword > rs {| bindex := "to" |});

      i8: (forall msg, In msg (fromPToC cword a fromPList toCList) ->
                         msg {| bindex := "isRq" |} = false ->
                         getCs cs tag a < msg {| bindex := "to" |} /\
                         dir (getTagIdxS a) cword = msg {| bindex := "to" |});

      i9: (forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                        dir (getTagIdxS a) cword <= rq {| bindex := "from" |} ->
                        forall rs,
                          In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                          isPWait a cRqValid rqFromCList dirw cword);

      i10: (forall msg1 msg2 beg mid last,
              fromPToC cword a fromPList toCList = beg ++ msg1 :: mid ++ msg2 :: last ->
              msg1 {| bindex := "isRq" |} = false ->
              msg2 {| bindex := "isRq" |} = false ->
              False)%list;
      
      i11: (dir (getTagIdxS a) cword > getCs cs tag a ->
                      rsFromCToP cword a rsFromCList rsToPList <> nil);
      
      i12: (
              rsFromCToP cword a rsFromCList rsToPList = nil \/
              forall msg, In msg (fromPToC cword a fromPList toCList) ->
                          msg {| bindex := "isRq" |} = true);

      i13: (rsLessTo (rsFromCToP cword a rsFromCList rsToPList));

      i14: (forall cToPRsLast beg,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ [cToPRsLast] ->
              cToPRsLast {| bindex := "to" |} = getCs cs tag a)%list;

      i15: (forall pToCRq pToCRs beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRq :: mid ++ pToCRs :: last ->
              pToCRq {| bindex := "isRq" |} = true ->
              pToCRs {| bindex := "isRq" |} = false ->
              getCs cs tag a = $ Msi.Inv)%list;

      i16: (
             isCWait a procV procRq csw ->
             (getCs cs tag a < if (procRq {| bindex := "op" |}):bool
                               then $ Msi.Mod else $ Msi.Sh) /\
             (((exists rq, In rq (rqFromCToP cword a rqFromCList rqToPList)
                           /\ rq {| bindex := "to" |} =
                              (if (procRq {| bindex := "op" |}):bool then $ Msi.Mod
                                              else $ Msi.Sh)
                              /\ rq {| bindex := "from" |} >= getCs cs tag a) /\
               forall msg, In msg (fromPToC cword a fromPList toCList) ->
                           msg {| bindex := "isRq"|} = true)
              \/
              ((exists rs, In rs (fromPToC cword a fromPList toCList)
                              /\ rs {| bindex := "isRq" |} = false
                              /\ rs {| bindex := "to" |} =
                                 if (procRq {| bindex := "op" |}):bool then $ Msi.Mod
                                             else $ Msi.Sh)) /\
              forall rq, ~ In rq (rqFromCToP cword a rqFromCList rqToPList)));
             (*
              xor (exists rq, In rq (rqFromCToP cword a rqFromCList rqToPList)
                              /\ rq ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod
                                              else $ Msi.Sh)
                              /\ rq ``"from" >= getCs cs tag a)
                  (exists rs, In rs (fromPToC cword a fromPList toCList)
                              /\ rs ``"isRq" = false
                              /\ rs ``"to" = if (procRq ``"op"):bool then $ Msi.Mod
                                             else $ Msi.Sh));
              *)

      i16a: (forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                        isCWait a procV procRq csw
                        /\ (getCs cs tag a < if (procRq {| bindex := "op" |} ):bool
                                             then $ Msi.Mod else $ Msi.Sh)
                        /\ rq {| bindex := "to" |} =
                           (if (procRq {| bindex := "op" |}):bool then $ Msi.Mod else $ Msi.Sh)
                          /\ rq {| bindex := "from" |} >= getCs cs tag a);

      i16b: (forall rs, In rs (fromPToC cword a fromPList toCList) ->
                          isCWait a procV procRq csw
                          /\ (getCs cs tag a < if (procRq {| bindex := "op" |}):bool
                                               then $ Msi.Mod else $ Msi.Sh)
                          /\ rs {| bindex := "isRq" |} = false
                          /\ rs {| bindex := "to" |} =
                             (if (procRq {| bindex := "op" |}):bool then $ Msi.Mod else $ Msi.Sh));

      i17: (forall pToCRq,
              In pToCRq (fromPToC cword a fromPList toCList) ->
              pToCRq {| bindex := "isRq" |} = true ->
              isPWait a cRqValid rqFromCList dirw cword ->
              getCs cs tag a = $ Msi.Inv);

      i18: (forall pToCRq cToPRs,
              In pToCRq (fromPToC cword a fromPList toCList) ->
              pToCRq {| bindex := "isRq" |} = true ->
              In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
              cToPRs {| bindex := "to" |} = $ Msi.Inv);

      i19: (forall pToCRs pToCRq beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRs :: mid ++ pToCRq :: last ->
              pToCRs {| bindex := "isRq" |} = false ->
              pToCRq {| bindex := "isRq" |} = true ->
              isPWait a cRqValid rqFromCList dirw cword)%list;

      i20: (forall pToCRq1 pToCRq2 beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRq1 :: mid ++ pToCRq2 :: last ->
              pToCRq1 {| bindex := "isRq" |} = true ->
              pToCRq2 {| bindex := "isRq" |} = true ->
              getCs cs tag a = $ Msi.Inv)%list;

      i21: (forall rs,
              In rs (rsFromCToP cword a rsFromCList rsToPList) ->
              rs {| bindex := "isVol" |} = false ->
              isPWait a cRqValid rqFromCList dirw cword);

      i22: (forall cToPRs1 cToPRs2 beg mid last,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ cToPRs1 :: mid ++ cToPRs2 :: last ->
              cToPRs1 {| bindex := "isVol" |} = true \/
              cToPRs2 {| bindex := "isVol" |} = true)%list;

      i23: (forall cToPRq,
              In cToPRq (rqFromCToP cword a rqFromCList rqToPList) ->
              dir (getTagIdxS a) cword <= cToPRq {| bindex := "from" |} ->
              forall cToPRs,
                In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
                cToPRs {| bindex := "isVol" |} = false);

      i24: (length (rsFromCToP cword a rsFromCList rsToPList) <= 2)%nat;

      i25: forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                        rq {| bindex := "from" |} < rq {| bindex := "to" |};

      i26: forall rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                        rs {| bindex := "isVol" |} = true ->
                        rs {| bindex := "to" |} = $ Msi.Inv ;

      i27: procV = true -> procRqReplace = true ->
           split1 TagBits IdxBits (split1 (TagBits + IdxBits) LgNumDatas
                                          (procRq {| bindex := "addr" |}))
           <> tag (split2 TagBits IdxBits
                          (split1 (TagBits + IdxBits) LgNumDatas
                                  (procRq {| bindex := "addr" |}))) \/
           cs (split2 TagBits IdxBits
                      (split1 (TagBits + IdxBits) LgNumDatas
                              (procRq {| bindex := "addr" |}))) = $ Msi.Inv ;

      i28: cRqValid = true -> hd_error rqFromCList <> None
    }.

  Hint Unfold modFromMeta nmemCacheInl metaRegs metaRules metaMeths Concat.concat
       getListFromMetaReg getListFromMetaRule getListFromMetaMeth getCs getTagS getTagIdxS
       getIdxS getAddrS isCompat fromPToC rqFromCToP rsFromCToP isCWait isPWait
       withIndex: MethDefs.

  Definition nmemCache_invariants (s: RegsT) :=
    forall a cword c,
      (c <= wordToNat (wones LgNumChildren))%nat ->
      cword = natToWord _ c ->
      nmemCache_invariants_rec s a cword c.

  Theorem true_False_false: forall v, (v = true -> False) -> v = false.
  Proof.
    intros.
    destruct v; intuition auto.
  Qed.

  Theorem false_False_true: forall v, (v = false -> False) -> v = true.
  Proof.
    intros.
    destruct v; intuition auto.
  Qed.

  Definition doUpds (x: nat) (ls: list (string * sigT (fullType type))): RegsT :=
    fold_right (fun nk (m: RegsT) =>
                  m[(fst nk) __ x |--> snd nk]) (M.empty _) ls.

  Lemma strings_in_uneq':
    forall a x n s, ~ S_In a s -> s <> x ++ (String a n).
  Proof.
    induction x; simpl; auto; intros; intro; subst; simpl in *; [intuition auto|].
    assert (sth: ~ S_In a (x ++ String a n)) by intuition auto.
    clear - sth.
    assert ((S_In a x \/ S_In a (String a n)) -> False) by
        (intros H; apply S_in_or_app in H; intuition auto).
    assert (sth2: S_In a (String a n) -> False) by intuition auto.
    simpl in sth2.
    intuition auto.
  Qed.
  
  Lemma strings_in_uneq:
    forall a x n s, index 0 (String a EmptyString) s = None -> s <> x ++ (String a n).
  Proof.
    intros.
    apply strings_in_uneq'.
    apply index_not_in; auto.
  Qed.

  Lemma nmemCache_invariants_same' s a c x (pf: c <> x) k v:
    nmemCache_invariants_rec s a ($ c) c ->
    nmemCache_invariants_rec s[k __ x |--> v] a ($ c) c.
  Proof.
    intros.
    destruct H.
    esplit;
      match goal with
        | |- ?v' === (?s) [?k __ ?x |--> ?v] .[?k'] =>
          assert (k' <> k __ x) by (apply strings_in_uneq; reflexivity);
            rewrite M.find_add_2; eauto
        | H: ?c <> ?x |- ?v' === (?s) [(?k) __ (?x) |--> ?v] .[?k' __ ?c] =>
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
    nmemCache_invariants_rec (M.union (doUpds x ls) s) a ($ c) c.
  Proof.
    induction ls; unfold doUpds; simpl; auto; intros;
    fold (doUpds x ls).
    rewrite M.union_add.
    apply nmemCache_invariants_same' with (s := M.union (doUpds x ls) s); auto.
  Qed.

  Ltac mkAddList madds :=
    match madds with
      | M.add (addIndexToStr _ ?x ?k) ?v ?m =>
        let ls := mkAddList m in
        constr:( (k, v) :: ls)
      | M.empty ?t => constr:(@nil (string * t))
    end.

  Lemma rqFromCToP_unchanged:
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
                                :: STRUCT  {"addr" :: Bit (TagBits + IdxBits);
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
    (repeat 
       match goal with
         | H: context[(mkStruct ?p ?q ?r)] |- _ =>
           rewrite (mkStruct_eq p q) in H;
         simpl in H;
         unfold ith_Bounded in H;
         simpl in H
         | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq p q);
         simpl; unfold ith_Bounded; simpl
       end);
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

  Lemma rqFromCToP_unchanged_diff:
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
                                          :: STRUCT  {"addr" :: Bit (TagBits + IdxBits);
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
    (repeat 
       match goal with
         | H: context[(mkStruct ?p ?q ?r)] |- _ =>
           rewrite (mkStruct_eq p q) in H;
         simpl in H;
         unfold ith_Bounded in H;
         simpl in H
         | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq p q);
         simpl; unfold ith_Bounded; simpl
       end);
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

  Lemma rsFromCToP_unchanged:
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
                                {"addr" :: Bit (TagBits + IdxBits);
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
    (repeat 
       match goal with
         | H: context[(mkStruct ?p ?q ?r)] |- _ =>
           rewrite (mkStruct_eq p q) in H;
         simpl in H;
         unfold ith_Bounded in H;
         simpl in H
         | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq p q);
         simpl; unfold ith_Bounded; simpl
       end);
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

  Lemma rsFromCToP_unchanged_diff:
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
                                          :: STRUCT  {"addr" :: Bit (TagBits + IdxBits);
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
    (repeat 
       match goal with
         | H: context[(mkStruct ?p ?q ?r)] |- _ =>
           rewrite (mkStruct_eq p q) in H;
         simpl in H;
         unfold ith_Bounded in H;
         simpl in H
         | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq p q);
         simpl; unfold ith_Bounded; simpl
       end);
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

  
  Lemma fromPToC_unchanged:    
    forall x a (t: type (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))
           fromPList toCList,
      $ x = t {| bindex := "child" |} ->
      fromPToC $ x a fromPList (t :: toCList) =
      fromPToC $ x a
        (fromPList ++
         [t
            (addFirstBoundedIndex
               (mapAttr type ("child" :: Bit LgNumChildren)%struct)
               {| bindex := "msg" |} )]) toCList.
  Proof.
    unfold fromPToC; intros; simpl; auto;
    (repeat match goal with
              | |- context [weq ?p ?q] => destruct (weq p q)
            end);
    mkStruct; subst;
    (repeat 
       match goal with
         | H: context[(mkStruct ?p ?q ?r)] |- _ =>
           rewrite (mkStruct_eq p q) in H;
         simpl in H;
         unfold ith_Bounded in H;
         simpl in H
         | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq p q);
         simpl; unfold ith_Bounded; simpl
       end);
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

  Lemma fromPToC_unchanged_diff:
    forall c x a (t: type (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))
           fromPList toCList,
      c <> x ->
      $ x = t {| bindex := "child" |} ->
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
    (repeat 
       match goal with
         | H: context[(mkStruct ?p ?q ?r)] |- _ =>
           rewrite (mkStruct_eq p q) in H;
         simpl in H;
         unfold ith_Bounded in H;
         simpl in H
         | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq p q);
         simpl; unfold ith_Bounded; simpl
       end);
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


  (*
  Lemma nmemCache_invariants_preserve s u r cs:
    nmemCache_invariants s ->
    Substep (modFromMeta (nmemCacheInl IdxBits TagBits
                                       LgNumDatas LgDataBytes Id LgNumChildren))
            s u (Rle r) cs ->
    nmemCache_invariants (M.union u s).
   *)

  Lemma weqDest1 T (v1 v2: T) (P: T -> Prop) sz (p q: word sz):
    P (if weq p q then v1 else v2) ->
    (p = q /\ P v1) \/ (p <> q /\ P v2).
  Proof.
    intros;
    destruct (weq p q); intuition auto.
  Qed.

  Lemma weqDest2 T (v1 v2: T) (P: T -> Prop) sz (p q: word sz):
    (p = q -> P v1) /\ (p <> q -> P v2) ->
    P (if weq p q then v1 else v2).
  Proof.
    intros;
    destruct (weq p q); intuition auto.
  Qed.

  Ltac weqHyp H :=
    match type of H with
      | context[if weq ?p ?q then ?v1 else ?v2] =>
        pattern (if weq p q then v1 else v2) in H;
          match goal with
            | H': ?P (if weq p q then v1 else v2) |- _ =>
              apply (weqDest1 v1 v2 P p q H')
          end
    end.

  Ltac weqGoal :=
    match goal with
      | |- context[if weq ?p ?q then ?v1 else ?v2] =>
        pattern (if weq p q then v1 else v2);
          match goal with
            | |- ?P (if weq p q then v1 else v2) =>
              apply (weqDest2 v1 v2 P)
          end
    end.

  Lemma invertSubstep m s u r cs:
    Substep m s u (Rle (Some r)) cs ->
    exists a, In (r :: a)%struct (getRules m) /\
              SemAction s (a type) u cs WO.
  Proof.
    intros Hs.
    inv Hs.
    eexists; eauto.
  Qed.

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
      (*
            intros; constructor 1 with (x := y);
            (* exists y; *)
            split; [assumption|]; intros *)
      | |- _ /\ _ => split; intros
      | |- _ => auto
    end.

  Ltac simplBool :=
    match goal with
      | H: ?v = true -> False |- _ =>
        apply true_False_false in H
      | H: ?v = false -> False |- _ =>
        apply false_False_true in H
    end.

  Ltac elimDiffC c :=
    match goal with
      | H: (?x <= wordToNat _)%nat, H': (c <= wordToNat _)%nat |-
        nmemCache_invariants_rec (M.union ?m ?n) ?a
                                 ?cword c =>
        destruct (eq_nat_dec c x);
          [subst|
           let ls := mkAddList m in
           replace m with (doUpds x ls) by
               reflexivity;
             apply nmemCache_invariants_same; auto]
      | _ => idtac
    end.
  
  Ltac destructRules c IH :=
    unfold getActionFromGen, getGenAction, strFromName in *;
    simpl in *; subst; unfold getActionFromSin, getSinAction in *; subst;
    SymEval; subst; simpl;
    match goal with
      | a: word (TagBits + IdxBits), H: (_ <= _)%nat, H': (c <= _)%nat |- _ =>
        destruct (IH a _ _ H eq_refl);
          specialize (IH a _ _ H' eq_refl)
      | a: word (TagBits + IdxBits), H: (_ <= _)%nat |- _ =>
        destruct (IH a _ _ H eq_refl)          
    end;
    unfold withIndex, withPrefix in *;
    simpl in *;
    repeat substFind; dest;
    repeat simplBool;
    elimDiffC c; mkStruct.

  Ltac metaInit :=
    intros HInd HInRule x xcond HS;
    simpl in HInRule; apply invSome in HInRule; apply invRepRule in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ?; destructRules c HInd.
  
  Lemma nmemCache_invariants_hold_1 s a u cs:
    nmemCache_invariants s ->
    "l1MissByState" metaIs a ->
    forall x,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInit.
    allRules; (reflexivity || eassumption ||
                           intros; unfold isCWait in *; dest; try discriminate).
    - apply i16a in H0; dest; discriminate.
    - apply i16b in H0; dest; discriminate.
  Qed.

  Lemma nmemCache_invariants_hold_2 s a u cs:
    nmemCache_invariants s ->
    "l1MissByLine" metaIs a ->
    forall x,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInit.
    - allRules; (reflexivity || eassumption ||
                             intros; unfold isCWait in *; dest; try discriminate).
      + apply i16a in H0; dest; discriminate.
      + apply i16b in H0; dest; discriminate.
      + intuition auto.
    - allRules; (reflexivity || eassumption ||
                             intros; unfold isCWait in *; dest; try discriminate).
      + apply i16a in H0; dest; discriminate.
      + apply i16b in H0; dest; discriminate.
      + intuition auto.
  Qed.

  Lemma nmemCache_invariants_hold_3 s a u cs:
    nmemCache_invariants s ->
    "l1Hit" metaIs a ->
    forall x,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInit.
    - allRules; (reflexivity || eassumption ||
                             intros; unfold isCWait in *; dest; try discriminate).
      + apply i16a in H0; dest; discriminate.
      + apply i16b in H0; dest; discriminate.
    - allRules; (reflexivity || eassumption ||
                             intros; unfold isCWait in *; dest; try discriminate).
      + apply i16a in H0; dest; discriminate.
      + apply i16b in H0; dest; discriminate.
  Qed.

  Lemma word_le_ge_eq sz (w1 w2: word sz): w1 <= w2 -> w1 >= w2 -> w1 = w2.
  Proof.
    intros.
    apply wordToN_inj.
    Nomega.pre_nomega.
    Nomega.nomega.
  Qed.
  
  Lemma nmemCache_invariants_hold_5 s a u cs:
    nmemCache_invariants s ->
    "upgRq" metaIs a ->
    forall x,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    metaInit.
    
    - allRules; (reflexivity || eassumption || unfold listEnq, listDeq, listIsEmpty,
                 listFirstElt, listEltT, rqFromCToP, AddrBits in *;
                  rewrite ?filtRqFromC_commute_app, ?filtRqToP_commute_app in *;
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
      + apply i9 with (rq := rq) (rs := rs); auto.
      + admit.
      + repeat (constructor; auto);
        dest; unfold addFirstBoundedIndex in *;
        simpl in *; unfold getCs, getIdxS; try rewrite H8.
        * match goal with
            | |- (if ?p then _ else _) < if ?q then _ else _ => destruct p;
                destruct q; Nomega.pre_nomega; Nomega.nomega
          end.
        * match goal with
            | |- context[mkStruct ?p] =>
              intros; constructor 1 with (x := mkStruct p) end.
          { constructor.
            - apply in_or_app; right; left;
              reflexivity.
            - mkStruct.
              constructor; [auto|].
              unfold getIdxS.
              match goal with
                | |- (if weq ?v1 ?v2 then _ else _) <= _ =>
                  destruct (weq v1 v2); Nomega.pre_nomega; Nomega.nomega
              end.
          }
        * destruct i12; [| assumption].
          assert(~ (getCs cs0 tag a0 < dir (getTagIdxS a0) $ x)) by
              match goal with
                | |- ?a <= ?b =>
                  destruct (@wlt_dec _ a b); intuition auto
              end.
          assert (dir (getTagIdxS a0) $ x = getCs cs0 tag a0)
            by (apply word_le_ge_eq; auto).
          intros msg inMsg.
          match goal with
            | |- ?a = ?b =>
              assert (sth: {a = true} + {a = false})
                by (clear; destruct a; intuition auto)
          end.
          destruct sth; [assumption | apply i8 in inMsg; auto].
          dest.
          rewrite <- H9 in H7.
          Nomega.pre_nomega; Nomega.nomega.
      + intros; dest.
        unfold IndexBound_head, IndexBound_tail, AddrBits, nth_error in *.
        rewrite H2 in n.
        intuition auto.
      + intros; apply i16a in H1; dest; discriminate.
      + admit.
      + intros; apply i16a in H1; dest; discriminate.
      + intros; apply i16b in H1; dest; discriminate.
      + apply i23 with (cToPRq := cToPRq); auto.
      + admit.
      + rewrite H8.
        match goal with
          | |- _ < if ?p then _ else _ =>
            destruct p; Nomega.pre_nomega; Nomega.nomega
        end.
    - allRules; (reflexivity || eassumption || unfold listEnq, listDeq, listIsEmpty,
                 listFirstElt, listEltT, rqFromCToP, AddrBits in *;
                  rewrite ?filtRqFromC_commute_app, ?filtRqToP_commute_app in *;
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
      + apply i9 with (rq := rq) (rs := rs); auto.
      + admit.
      + repeat (constructor; auto);
        dest; unfold addFirstBoundedIndex in *;
        simpl in *; unfold getCs.
        * match goal with
            | |- (if ?p then _ else _) < if ?q then _ else _ => destruct p;
                [auto | clear; destruct q; Nomega.pre_nomega; Nomega.nomega]
          end.
        * match goal with
            | |- context[mkStruct ?p] =>
              intros; constructor 1 with (x := mkStruct p) end.
          { constructor.
            - apply in_or_app; right; left;
              reflexivity.
            - mkStruct.
              constructor; [auto|].
              unfold getIdxS.
              match goal with
                | |- (if weq ?v1 ?v2 then _ else _) <= _ =>
                  destruct (weq v1 v2); Nomega.pre_nomega; Nomega.nomega
              end.
          }
        * destruct i12; [| assumption].
          assert(~ (getCs cs0 tag a0 < dir (getTagIdxS a0) $ x)) by
              match goal with
                | |- ?a <= ?b =>
                  destruct (@wlt_dec _ a b); intuition auto
              end.
          assert (dir (getTagIdxS a0) $ x = getCs cs0 tag a0)
            by (apply word_le_ge_eq; auto).
          intros msg inMsg.
          match goal with
            | |- ?a = ?b =>
              assert (sth: {a = true} + {a = false})
                by (clear; destruct a; intuition auto)
          end.
          destruct sth; [assumption | apply i8 in inMsg; auto].
          dest.
          rewrite <- H8 in H7.
          Nomega.pre_nomega; Nomega.nomega.
      + intros; dest.
        unfold IndexBound_head, IndexBound_tail, AddrBits, nth_error in *.
        rewrite H2 in n.
        intuition auto.
      + intros; apply i16a in H1; dest; discriminate.
      + admit.
      + intros; apply i16a in H1; dest; discriminate.
      + intros; apply i16b in H1; dest; discriminate.
      + apply i23 with (cToPRq := cToPRq); auto.
      + admit.
      + apply H11.
  Qed.

  (*
  
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
      intros ? ? c ? ?.
             
      doDestruct; unfold getActionFromGen, getGenAction, strFromName in HAction;
      simpl in *; subst; unfold getActionFromSin, getSinAction in *; subst;
      SymEval; subst; simpl;
      match goal with
        | a: word (TagBits + IdxBits), H: (_ <= _)%nat, H': (c <= _)%nat |- _ =>
          destruct (IHHMultistepBeh a _ _ H eq_refl);
            specialize (IHHMultistepBeh a _ _ H' eq_refl)
        | a: word (TagBits + IdxBits), H: (_ <= _)%nat |- _ =>
          destruct (IHHMultistepBeh a _ _ H eq_refl)          
      end;
      unfold withIndex, withPrefix in *;
      simpl in *;
      repeat
        match goal with
          | H': ?y === ?n .[ ?s] , H: ?v === ?n .[ ?s] |- _ =>
            rewrite H' in H;
              apply invSome in H;
              apply Eqdep.EqdepTheory.inj_pair2 in H; subst; intros (*
            intros; constructor 1 with (x := y);
            (* exists y; *)
            split; [assumption|]; intros *)
          | |- _ /\ _ => split; intros
          | |- _ => auto
        end; dest;
      repeat match goal with
               | H: ?v = true -> False |- _ =>
                 apply true_False_false in H
               | H: ?v = false -> False |- _ =>
                 apply false_False_true in H
             end;
      match goal with
        | H: (?x <= wordToNat _)%nat, H': (c <= wordToNat _)%nat |-
          nmemCache_invariants_rec (M.union ?m ?n) ?a
                                   ?cword c =>
          destruct (eq_nat_dec c x);
            [subst|
             let ls := mkAddList m in
             replace m with (doUpds x ls) by
                 reflexivity;
               apply nmemCache_invariants_same; auto]
        | _ => idtac
      end.

      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
        * discriminate.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
        * left; intuition auto.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
        * right; intuition auto.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
        * discriminate.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
        * discriminate.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + allRules; (reflexivity || eassumption || intros); exfalso; unfold isCWait in *.
        * dest; discriminate.
        * pose proof (i16a _ H2) as sth1.
          destruct sth1 as [sth2 sth3].
          pose proof (i16 sth2) as sth4.
          dest.
          destruct H12; dest; [| specialize (H19 _ H2); assumption].
          simpl in *.
          unfold addFirstBoundedIndex, StringBound.IndexBound_tail,
          StringBound.IndexBound_head in *; simpl in *.
          rewrite H6 in H4.
          simpl in H4.
          unfold getCs, getIdxS, getTagS in H4.
          rewrite H17 in H8, H10.
          rewrite H8 in H4.
          match goal with
            | H: context[weq ?p ?p] |- _ =>
              destruct (weq p p); intuition auto
          end.
        * pose proof (i16b _ H2) as sth1.
          destruct sth1 as [sth2 sth3].
          pose proof (i16 sth2) as sth4.
          dest.
          destruct H12; dest; [specialize (H19 _ H2); congruence|].
          simpl in *.
          unfold addFirstBoundedIndex, StringBound.IndexBound_tail,
          StringBound.IndexBound_head in *; simpl in *.
          rewrite H6 in H4.
          simpl in H4.
          unfold getCs, getIdxS, getTagS in H4.
          rewrite H17 in H8, H10.
          rewrite H8 in H4.
          match goal with
            | H: context[weq ?p ?p] |- _ =>
              destruct (weq p p); intuition auto
          end.
        * discriminate.
      + allRules; (reflexivity || eassumption || intros); exfalso; unfold isCWait in *.
        * dest; discriminate.
        * pose proof (i16a _ H2) as sth1.
          destruct sth1 as [sth2 sth3].
          pose proof (i16 sth2) as sth4.
          dest.
          destruct H12; dest; [| specialize (H19 _ H2); assumption].
          simpl in *.
          unfold addFirstBoundedIndex, StringBound.IndexBound_tail,
          StringBound.IndexBound_head in *; simpl in *.
          rewrite H6 in H4.
          simpl in H4.
          unfold getCs, getIdxS, getTagS in H4.
          rewrite H17 in H8, H10.
          rewrite H8 in H4.
          match goal with
            | H: context[weq ?p ?p] |- _ =>
              destruct (weq p p); [|intuition auto]
          end.
          rewrite H10 in H4.
          Nomega.pre_nomega; Nomega.nomega.
        * pose proof (i16b _ H2) as sth1.
          destruct sth1 as [sth2 sth3].
          pose proof (i16 sth2) as sth4.
          dest.
          destruct H12; dest; [specialize (H19 _ H2); congruence|].
          simpl in *.
          unfold addFirstBoundedIndex, StringBound.IndexBound_tail,
          StringBound.IndexBound_head in *; simpl in *.
          rewrite H6 in H4.
          simpl in H4.
          unfold getCs, getIdxS, getTagS in H4.
          rewrite H17 in H8, H10.
          rewrite H8 in H4.
          match goal with
            | H: context[weq ?p ?p] |- _ =>
              destruct (weq p p); [|intuition auto]
          end.
          rewrite H10 in H4.
          Nomega.pre_nomega; Nomega.nomega.
        * discriminate.
      + admit.
      + admit.
      + admit.
      + match goal with
          | H: (?x <= wordToNat _)%nat,
               H': (c <= wordToNat _)%nat
            |-
            nmemCache_invariants_rec (M.union ?m ?n) ?a
                                     ?cword c =>
            unfold listIsEmpty, listFirstElt, listEnq, listDeq in *;
              destruct rqToPList; simpl in *;
              [discriminate |
              destruct (eq_nat_dec c x); [subst; allRules; (reflexivity || eassumption ||
                                           (try rewrite <- rqFromCToP_unchanged); auto) | ]]
        end.

        rewrite <- rqFromCToP_unchanged with (t := g) (rqFromCList := rqFromCList)
                                                      (rqToPList := rqToPList)
                                                      (x := x).
                                                               .
        Focus 7.
        simpl.
              destruct rqToPList; simpl in *;
              [discriminate |
              destruct (eq_nat_dec c x); [subst; allRules; (reflexivity || eassumption ||
                                           rewrite <- rqFromCToP_unchanged; auto) | ]]
        end.
        clear - IHHMultistepBeh n0 H H1 H0 H3.
        destruct IHHMultistepBeh; allRules;
        match goal with
          | |- ?p === ?n.[?s] => eassumption
          | _ => auto
        end;
        unfold withIndex, withPrefix in *;
        match goal with
          | H: ?p1 === ?n.[?s], H': ?p2 === ?n.[?s] |- _ =>
            rewrite H' in H;
              apply invSome in H;
              simpl in H;
              destruct_existT
        end;
        try rewrite <- rqFromCToP_unchanged_diff; auto.
        * destruct (eq_nat_dec c x).
          specialize (n0 e); exfalso; assumption.
          eassumption.
        * auto.
      + match goal with
          | H: (?x <= wordToNat _)%nat,
               H': (c <= wordToNat _)%nat
            |-
            nmemCache_invariants_rec (M.union ?m ?n) ?a
                                     ?cword c =>
            unfold listIsEmpty, listFirstElt, listEnq, listDeq in *;
              destruct rsToPList; simpl in *;
              [discriminate |
              destruct (eq_nat_dec c x); [subst; allRules; (reflexivity || eassumption ||
                                           rewrite <- rsFromCToP_unchanged; auto) | ]]
        end.
        clear - IHHMultistepBeh n0 H H1 H0 H3.
        destruct IHHMultistepBeh; allRules;
        match goal with
          | |- ?p === ?n.[?s] => eassumption
          | _ => auto
        end;
        match goal with
          | H: ?p1 === ?n.[?s], H': ?p2 === ?n.[?s] |- _ =>
            rewrite H' in H;
              apply invSome in H;
              simpl in H;
              destruct_existT
        end;
        try rewrite <- rsFromCToP_unchanged_diff; auto.
        * destruct (eq_nat_dec c x).
          specialize (n0 e); exfalso; assumption.
          eassumption.
        * auto.
        * auto.
      + match goal with
          | H: (?x <= wordToNat _)%nat,
               H': (c <= wordToNat _)%nat
            |-
            nmemCache_invariants_rec (M.union ?m ?n) ?a
                                     ?cword c =>
            unfold listIsEmpty, listFirstElt, listEnq, listDeq in *;
              destruct toCList; simpl in *;
              [discriminate |
               destruct (eq_nat_dec c x);
                 [subst; allRules; (reflexivity || eassumption ||
                                                rewrite <- fromPToC_unchanged; auto) | ]]
        end.
        clear - IHHMultistepBeh n0 H H1 H4 H0 H3.
        destruct IHHMultistepBeh; allRules;
        match goal with
          | |- ?p === ?n.[?s] => eassumption
          | _ => auto
        end;
        match goal with
          | H: ?p1 === ?n.[?s], H': ?p2 === ?n.[?s] |- _ =>
            rewrite H' in H;
              apply invSome in H;
              simpl in H;
              destruct_existT
        end; try erewrite fromPToC_unchanged_diff; eauto;
        match goal with
          | neq: ?c <> ?x |- context [eq_nat_dec ?c ?x] =>
            destruct (eq_nat_dec c x) as [isEq | notEq];
              [specialize (neq isEq); exfalso; assumption | eassumption]
          | _ => idtac
        end; auto.
      + admit.
      + admit.
      + admit.
      + admit.
  Qed.
*)
