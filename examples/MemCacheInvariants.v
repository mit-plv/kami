Require Import Lib.FMap Lib.Word Lib.WordSupport Ex.MemTypes Lib.Indexer Lib.Struct Ex.Msi
        Ex.NativeFifo Lts.Notations String Ex.MemCacheInl Lts.Syntax List Lts.Semantics
        ParametricSyntax Lib.CommonTactics Lts.SemFacts Lib.FMap Lib.Concat Arith
        FunctionalExtensionality Program.Equality Lts.Tactics Ex.MapVReify Lts.SymEval
        Lts.SymEvalTac Lib.StringExtension Lib.StringBound Lib.ListSupport Lib.Misc Lib.StructNotation.

Set Implicit Arguments.

Local Notation "<| t |>" := (fullType type (SyntaxKind t)).

Local Notation "<[ t ]>" := (fullType type (@NativeKind t nil)).

Section MemCacheInl.
  Variables IdxBits TagBits LgNumDatas LgDataBytes: nat.
  Variable Id: Kind.

  Variable LgNumChildren: nat.

  Definition getTagS (x: word (TagBits + IdxBits)):
    word TagBits :=
    split1 TagBits IdxBits x.

  Definition getIdxS (x: word (TagBits + IdxBits)):
    word IdxBits :=
    split2 TagBits IdxBits x.

  Definition AddrBits := TagBits + IdxBits.
  
  Definition getAddrS (tag: word TagBits) (idx: word IdxBits): word AddrBits :=
    Word.combine tag idx.

  Open Scope string.

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
      | x :: xs => if weq c (x ``"child")
                   then if weq a (x ``"rs" ``"addr")
                        then x ``"rs" :: filtRsFromC c a xs
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
      | x :: xs => if weq c (x ``"child")
                   then if weq a (x ``"msg" ``"addr")
                        then x ``"msg" :: filtToC c a xs
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
      | x :: xs => if weq a (x ``"addr")
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
      | x :: xs => if weq a (x ``"addr")
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
      | x :: xs => if weq a (x ``"addr")
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

  Fixpoint rsLessTo (ls: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))) :=
    match ls with
      | x :: xs =>
        match xs with
          | y :: xs' =>
            x ``"to" > y ``"to" /\ rsLessTo xs
          | nil => True
        end
      | _ => True
    end.

  Definition isCWait a procV
             (procRq: type (RqFromProc LgDataBytes (Bit (TagBits + IdxBits + LgNumDatas))))
             csw :=
    procV = true /\ a = split1 (TagBits + IdxBits) LgNumDatas (procRq ``"addr") /\
    csw = true.

  Lemma isCWait_dec: forall a procV procRq csw, isCWait a procV procRq csw \/
                                                ~ isCWait a procV procRq csw.
  Proof.
    intros.
    unfold isCWait in *; simpl in *.
    destruct procV, csw; try intuition discriminate.
    match goal with
      | |- context[?p = ?q] => match type of p with
                                 | word _ => destruct (weq p q); intuition auto
                               end
    end.
  Qed.

  Definition isPWait a cRqValid
             (rqFromCList: list (type (RqFromC LgNumChildren (Bit (TagBits + IdxBits)) Id)))
             dirw (cword: word LgNumChildren) :=
    cRqValid = true /\
    dirw cword = true /\
    match hd_error rqFromCList with
      | Some cRq => a = cRq ``"rq" ``"addr"
      | _ => False
    end.

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
  
  Definition cache := nat.
  
  Record nmemCache_invariants_rec (s: RegsT)
         a cword (c: cache): Prop :=
    {
      dir: <| Vector (Vector Msi LgNumChildren) (TagBits + IdxBits) |> ;
      dirFind: dir === s.["dataArray.mcs"];
      mline: <|Vector (Line LgDataBytes LgNumDatas) (TagBits + IdxBits) |> ;
      mlineFind: mline === s.["dataArray.mline"];
      cRqValid: <| Bool |> ;
      cRqValidFind: cRqValid === s.["cRqValid"];
      dirw: <| Vector Bool LgNumChildren |> ;
      dirwFind: dirw === s.["cRqDirw"];
      rqFromCList: <[ list (type (RqFromC LgNumChildren (Bit AddrBits) Id)) ]> ;
      rqFromCListFind: rqFromCList === s.["elt.rqFromChild"];
      rsFromCList: <[ list (type (RsFromC LgDataBytes LgNumDatas LgNumChildren
                                          (Bit AddrBits))) ]> ;
      rsFromCListFind: rsFromCList === s.["elt.rsFromChild"];
      toCList: <[ list (type
                          (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))
                ]> ;
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
      rqToPList: <[ list (type (RqToP (Bit AddrBits) Id)) ]> ;
      rqToPListFind:  rqToPList === s.["elt.rqToParent" __ c];
      rsToPList: <[ list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits))) ]> ;
      rsToPListFind: rsToPList === s.["elt.rsToParent" __ c];
      fromPList: <[ list (type (FromP LgDataBytes LgNumDatas
                                      (Bit AddrBits) Id)) ]> ;
      fromPListFind: fromPList === s.["elt.fromParent" __ c] ;
      cRq: <| RqFromC LgNumChildren (Bit (TagBits + IdxBits)) Id |> ;
      cRqFind: cRq === s.["cRq"];

      i5: (dir a cword >= getCs cs tag a);
      
      i7: match find (fun _ => true) (rsFromCToP cword a rsFromCList rsToPList) with
            | Some rs => getCs cs tag a <= rs ``"to" /\
                         dir a cword > rs ``"to"
            | None => True
          end ;

      i8: match find (fun msg: type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id) => msg ``"isRq")
                     (fromPToC cword a fromPList toCList) with
            | Some msg => getCs cs tag a < msg ``"to" /\
                          dir a cword = msg ``"to"
            | None => True
          end ;

      i9: match find (fun rq: type (RqToP (Bit AddrBits) Id) => if wlt_dec (rq ``"from") (dir a cword)
                                                                then false
                                                                else true)
                     (rqFromCToP cword a rqFromCList rqToPList),
                find (fun _ => true) (rsFromCToP cword a rsFromCList rsToPList) with
            | Some rq, Some rs => isPWait a cRqValid rqFromCList dirw cword
            | _, _ => True
          end ;

      i10: (forall beg mid last msg1 msg2,
              fromPToC cword a fromPList toCList = beg ++ msg1 :: mid ++ msg2 :: last ->
              msg1 ``"isRq" = false ->
              msg2 ``"isRq" = false ->
              False)%list ;
      
      i11: rsFromCToP cword a rsFromCList rsToPList = nil ->
           dir a cword <= getCs cs tag a ;
      
      i12: match find (fun msg : type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id) =>
                         negb (msg ``"isRq"))
                      (fromPToC cword a fromPList toCList), find (fun _ => true) (rsFromCToP cword a rsFromCList rsToPList) with
             | Some _, Some _ => False
             | _, _ => True
           end ;
    
      i13: rsLessTo (rsFromCToP cword a rsFromCList rsToPList) ;

      i14: (forall beg cToPRsLast,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ [cToPRsLast] ->
              cToPRsLast ``"to" = getCs cs tag a)%list ;

      i15: (forall beg mid last pToCRq pToCRs,
              fromPToC cword a fromPList toCList = beg ++ pToCRq :: mid ++ pToCRs :: last ->
              pToCRq ``"isRq" = true ->
              pToCRs ``"isRq" = false ->
              getCs cs tag a = $ Msi.Inv)%list ;

      i16: isCWait a procV procRq csw ->
           (getCs cs tag a < if (procRq ``"op"):bool
                             then $ Msi.Mod else $ Msi.Sh)
           /\
           match find (fun _ => true) (rqFromCToP cword a rqFromCList rqToPList),
                 find
                   (fun (msg: type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id)) =>
                      if (msg ``"isRq"):bool then false else true)
                   (fromPToC cword a fromPList toCList) with
             | Some rq, None => rq ``"to" =
                                (if (procRq ``"op"):bool then $ Msi.Mod
                                 else $ Msi.Sh)
                                /\ rq ``"from" >= getCs cs tag a
             | None, Some rs => rs ``"to" = 
                                if (procRq ``"op"):bool then $ Msi.Mod
                                else $ Msi.Sh
             | _, _ => False
           end ;

      i16a: match find (fun _ => true) (rqFromCToP cword a rqFromCList rqToPList) with
              | Some rq => isCWait a procV procRq csw
                           /\ (getCs cs tag a < if (procRq ``"op" ):bool
                                                then $ Msi.Mod else $ Msi.Sh)
                           /\ rq ``"to" =
                              (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh)
                           /\ rq ``"from" >= getCs cs tag a
              | None => True
            end ;

      i16b: match find (fun msg: type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id) =>
                          if (msg ``"isRq"):bool then false else true)
                       (fromPToC cword a fromPList toCList) with
              | Some rs => isCWait a procV procRq csw
                           /\ (getCs cs tag a < if (procRq {| bindex := "op" |}):bool
                                                then $ Msi.Mod else $ Msi.Sh)
                           /\ rs {| bindex := "isRq" |} = false
                           /\ rs {| bindex := "to" |} =
                              (if (procRq {| bindex := "op" |}):bool then $ Msi.Mod else $ Msi.Sh)
              | None => True
            end ;

      i17: match find (fun rq: type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id) =>
                         rq ``"isRq") (fromPToC cword a fromPList toCList) with
             | Some rq => isPWait a cRqValid rqFromCList dirw cword \/ getCs cs tag a = $ Msi.Inv
             | None => True
           end ;

      i18: match find (fun rq: type (FromP LgDataBytes LgNumDatas (Bit AddrBits) Id) =>
                         rq ``"isRq") (fromPToC cword a fromPList toCList),
                 find (fun _ => true) (rsFromCToP cword a rsFromCList rsToPList) with
             | Some rq, Some rs  => rs ``"to" = $ Msi.Inv
             | _, _ => True
           end ;

      i19: (forall beg mid last pToCRq pToCRs,
              fromPToC cword a fromPList toCList = beg ++ pToCRs :: mid ++ pToCRq :: last ->
              pToCRs ``"isRq" = false ->
              pToCRq ``"isRq" = true ->
              isPWait a cRqValid rqFromCList dirw cword)%list ;

      i20: (forall beg mid last pToCRq1 pToCRq2,
              fromPToC cword a fromPList toCList = beg ++ pToCRq1 :: mid ++ pToCRq2 :: last ->
              pToCRq1 ``"isRq" = true ->
              pToCRq2 ``"isRq" = true ->
              getCs cs tag a = $ Msi.Inv)%list ;

      i21: match find (fun rs: type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)) =>
                         if (rs ``"isVol"):bool then false else true)
                      (rsFromCToP cword a rsFromCList rsToPList) with
             | Some rs => isPWait a cRqValid rqFromCList dirw cword
             | None => True
           end ;

      i22: (forall beg mid last cToPRs1 cToPRs2,
              rsFromCToP cword a rsFromCList rsToPList =
              beg ++ cToPRs1 :: mid ++ cToPRs2 :: last ->
              cToPRs1 {| bindex := "isVol" |} = true \/
              cToPRs2 {| bindex := "isVol" |} = true)%list ;

      i23: match find (fun rq: type (RqToP (Bit AddrBits) Id) =>
                         if wlt_dec (rq ``"from") (dir a cword) then false else true)
                      (rqFromCToP cword a rqFromCList rqToPList),
                 find (fun _ => true) (rsFromCToP cword a rsFromCList rsToPList) with
             | Some rq, Some rs => rs ``"isVol" = false
             | _, _ => True
           end ;

      i25: match find (fun _ => true) (rqFromCToP cword a rqFromCList rqToPList) with
             | Some rq => rq ``"from" < rq ``"to"
             | None => True
           end ;

      i26: match find (fun rs: type (RsToP LgDataBytes LgNumDatas (Bit (AddrBits))) => rs ``"isVol")
                      (rsFromCToP cword a rsFromCList rsToPList) with
             | Some rs => rs ``"to" = $ Msi.Inv
             | None => True
           end ;

      i27: procV = true -> procRqReplace = true ->
           tag (split2 TagBits IdxBits
                       (split1 AddrBits LgNumDatas
                               (procRq ``"addr"))) <>
           split1 TagBits IdxBits (split1 AddrBits LgNumDatas
                                          (procRq ``"addr")) \/
           cs (split2 TagBits IdxBits
                      (split1 AddrBits LgNumDatas
                              (procRq {| bindex := "addr" |}))) = $ Msi.Inv ;

      i28: cRqValid = true -> hd_error rqFromCList = Some cRq ;

      i29: match find (fun rs: type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)) => rs ``"isVol")
                      (rsFromCToP cword a rsFromCList rsToPList),
                 find (fun _ => true) (rqFromCToP cword a rqFromCList rqToPList) with
             | Some rs, Some rq => rq ``"from" = $ Msi.Inv
             | _, _ => True
           end ;


      i30: match find (fun rs: type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)) =>
                         if weq (rs ``"to") ($ Msi.Inv)
                         then true
                         else false) (rsFromCToP ($ c) a rsFromCList rsToPList) with
             | Some rs => getCs cs tag a = $ Msi.Inv
             | None => True
           end ;

      i31: match find (fun rs: type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)) =>
                         rs ``"isVol") (rsFromCToP ($ c) a rsFromCList rsToPList) with
             | Some rs => getCs cs tag a = $ Msi.Inv
             | None => True
           end
    }.

  Definition nmemCache_invariants (s: RegsT) :=
    forall a cword (c: cache),
      (c <= wordToNat (wones LgNumChildren))%nat ->
      cword = natToWord _ c ->
      nmemCache_invariants_rec s a cword c.

  Lemma rsLessTo_less_app:
    forall ls
           (v1: type (RsToP LgDataBytes LgNumDatas (Bit (TagBits + IdxBits)))),
      rsLessTo (ls ++ [v1]) ->
      forall (v2: type (RsToP _ _ _)),
        v1 {| bindex := "to";
              indexb :=
                {| boundi := eq_refl:
                               nth_error (map (@attrName _)
                                              (mapAttr type ("addr" :: Bit (TagBits + IdxBits))%struct ::
                                                       mapAttr type ("to" :: Msi)%struct ::
                                                       mapAttr type ("line" :: Line LgDataBytes LgNumDatas)%struct ::
                                                       mapAttr type ("isVol" :: Bool)%struct :: nil))
                                         1 = Some "to" |} |} >
        v2 {| bindex := "to";
              indexb :=
                {| boundi := eq_refl:
                               nth_error (map (@attrName _)
                                              (mapAttr type ("addr" :: Bit (TagBits + IdxBits))%struct ::
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
  
  Lemma nmemCache_invariants_same' s a c x (pf: c <> x) k v:
    nmemCache_invariants_rec s a ($ c) c ->
    nmemCache_invariants_rec s[k __ x |--> v] a ($ c) c.
  Proof.
    intros.
    destruct H.
    esplit;
      match goal with
        | |- ?v' === (?s) [?k __ ?x |--> ?v] .[?k'] =>
          assert (k' <> k __ x) by (apply not_in_string_uneq; reflexivity);
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
    nmemCache_invariants_rec (M.union (do_upd_map_key_instance x ls) s) a ($ c) c.
  Proof.
    induction ls; unfold do_upd_map_key_instance; simpl; auto; intros;
    fold (do_upd_map_key_instance x ls).
    rewrite M.union_add.
    apply nmemCache_invariants_same' with (s := M.union (do_upd_map_key_instance x ls) s); auto.
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
    simpl in *; subst; unfold getActionFromSin, getSinAction in *; subst;
    SymEval; subst; simpl;
    match goal with
      | a: word (TagBits + IdxBits), H: (_ <= _)%nat, H': (c <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl);
          specialize (HInd a _ _ H' eq_refl)
      | a: word (TagBits + IdxBits), H: (_ <= _)%nat |- _ =>
        destruct (HInd a _ _ H eq_refl)          
    end;
    unfold withIndex, withPrefix in *;
    simpl in *;
    repeat substFind; dest;
    repeat simplBool;
    elimDiffC c; mkStruct.

  Ltac normalInit :=
    intros HInd HInRule HS;
    simpl in HInRule; apply invSome in HInRule;
    unfold getActionFromSin, getSinAction at 1 in HInRule; simpl in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ?; destructRules c HInd.
  
  Ltac metaInit :=
    intros HInd HInRule x xcond HS;
    simpl in HInRule; apply invSome in HInRule; apply invRepRule in HInRule;
    rewrite <- HInRule in HS; clear HInRule;
    intros ? ? c ? ?; destructRules c HInd.

  Lemma isPWait_addRq a cRqValid
        (rqFromCList: list (type (RqFromC LgNumChildren (Bit (TagBits + IdxBits)) Id)))
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

  Lemma isPWait_addRq_contra a cRqValid
        (rqFromCList: list (type (RqFromC LgNumChildren (Bit (TagBits + IdxBits)) Id)))
        dirw (cword: word LgNumChildren) rq:
    ~ isPWait a cRqValid (rqFromCList ++ [rq]) dirw cword ->
    ~ isPWait a cRqValid rqFromCList dirw cword.
  Proof.
    unfold not at 2; intros.
    eapply isPWait_addRq in H0; eauto.
  Qed.

  Lemma rsLessTo_in_I_last ls:
    forall rs,
      In rs ls ->
      rsLessTo ls ->
      rs {| bindex := "to";
            indexb :=
              {| boundi := eq_refl:
                             nth_error (map (@attrName _)
                                            (mapAttr type ("addr" :: Bit (TagBits + IdxBits))%struct ::
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

  Lemma cs_sameAddr_upd: forall cs tag a0 a upd,
                           a0 = a ->
                           tag (split2 TagBits IdxBits a) = split1 TagBits IdxBits a ->
                           getCs
                             (fun a' => if weq a' (split2 TagBits IdxBits a)
                                        then upd
                                        else cs a') tag a0 = upd.
  Proof.
    intros.
    unfold getCs, getIdxS, getTagS; subst.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; intuition auto
           end.
  Qed.

  Lemma cs_sameAddr_no_upd: forall cs tag a,
                              tag (split2 TagBits IdxBits a) = split1 TagBits IdxBits a ->
                              getCs cs tag a = cs (split2 TagBits IdxBits a).
  Proof.
    intros.
    unfold getCs, getIdxS, getTagS; subst.
    repeat match goal with
             | |- (if ?p then _ else _) = _ => destruct p; intuition auto
           end.
  Qed.

  Lemma rsFromCToP_sameAddr_revcons:
    forall x (a: word AddrBits)
           (rsFromCList:
              list
                (type (RsFromC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits))))
           (rsToPList: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))) v,
      a = ((mkStruct v): type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))
            {| bindex := "addr" |} ->
      rsFromCToP x a rsFromCList (rsToPList ++ [mkStruct v]) =
      (rsFromCToP x a rsFromCList rsToPList ++ [mkStruct v])%list.
  Proof.
    unfold IndexBound_head, AddrBits; simpl; intros.
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
    forall x (a: word AddrBits)
           (rsFromCList:
              list
                (type (RsFromC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits))))
           (rsToPList: list (type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))) v,
      a <> ((mkStruct v): type (RsToP LgDataBytes LgNumDatas (Bit AddrBits)))
             {| bindex := "addr" |} ->
      rsFromCToP x a rsFromCList (rsToPList ++ [mkStruct v]) =
      rsFromCToP x a rsFromCList rsToPList.
  Proof.
    unfold IndexBound_head, AddrBits; simpl; intros.
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

  Lemma cs_diffAddr_upd: forall cs tag a0 a upd,
                           a0 <> a ->
                           tag (split2 TagBits IdxBits a) = split1 TagBits IdxBits a ->
                           getCs
                             (fun a' => if weq a' (split2 TagBits IdxBits a)
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
    rewrite <- (Word.combine_split TagBits IdxBits a0) in H.
    rewrite <- (Word.combine_split TagBits IdxBits a) in H.
    rewrite H0, e0 in H.
    intuition auto.
  Qed.

  Lemma getCs_cs_matches cs tag a:
    cs (split2 TagBits IdxBits a) = WO~0~0 \/
    tag (split2 TagBits IdxBits a) = split1 TagBits IdxBits a ->
    getCs cs tag a = cs (split2 TagBits IdxBits a).
  Proof.
    unfold getCs; intros; unfold getTagS, getIdxS.
    destruct H, (weq (tag (split2 TagBits IdxBits a)) (split1 TagBits IdxBits a));
      intuition auto.
  Qed.

  Lemma rsFromCToP_sameAddr_sameChild_cons_prop a c P:
    forall rsFromCList g rsToPList,
      (forall rs, In rs (rsFromCToP ($ c) a (g :: rsFromCList) rsToPList) ->
                  P rs) ->
      a = g {| bindex := "rs" |} {| bindex := "addr" |} ->
      $ c = g {| bindex := "child" |} ->
      P (g {| bindex := "rs" |}).
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
                                         (Bit (TagBits + IdxBits))))  rsToPList,
      a = g {| bindex := "rs" |} {| bindex := "addr" |} ->
      $ c = g {| bindex := "child" |} ->
      rsFromCToP ($ c) a (g :: rsFromCList) rsToPList =
      g {| bindex := "rs" |} :: rsFromCToP ($ c) a rsFromCList rsToPList.
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
                                                    LgNumChildren (Bit (TagBits + IdxBits)))):
    a <> g {| bindex := "rs" |} {| bindex := "addr" |} ->
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
                                                    LgNumChildren (Bit (TagBits + IdxBits)))):
    c <> g {| bindex := "child" |} ->
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
      rs {| bindex := "to" |} < g {| bindex := "to" |}.
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

  Ltac invariant_simpl :=
    subst;
    try match goal with
        | [ H : nmemCache_invariants_rec _ _ _ ?c |- _ ] =>
          match goal with
          | [ _ : context[addIndexToStr _ c _] |- _ ] => clear H
          | _ => destruct H
          end
        end;
    unfold withIndex, withPrefix, listIsEmpty,
    listFirstElt, listEnq, listDeq in *; simpl in *;
    repeat substFind; dest; repeat simplBool; mkStruct;
    repeat match goal with
           | [ H : evalConstT match ?E with _ => _ end = _ |- _ ] =>
             destruct E; try discriminate; [ clear H ]
           end; autorewrite with invariant in *.

  Ltac addr_eq := 
    try rewrite cs_sameAddr_upd in *;
    try rewrite rsFromCToP_sameAddr_revcons in *; auto;
    subst; try rewrite cs_sameAddr_no_upd in * by auto.
  
  Ltac addr_neq :=
    try rewrite cs_diffAddr_upd in *;
    try rewrite rsFromCToP_diffAddr_revcons in *; auto.

  Ltac destruct_addr :=
    repeat match goal with
             | H: context [@weq (TagBits + IdxBits) ?a ?b] |- _ =>
               destruct (@weq (TagBits + IdxBits) a b); [addr_eq | addr_neq]
             | |- context [@weq (TagBits + IdxBits) ?a ?b] =>
               destruct (@weq (TagBits + IdxBits) a b); [addr_eq | addr_neq]
             | H: context [@weq AddrBits ?a ?b] |- _ =>
               destruct (@weq AddrBits a b); [addr_eq | addr_neq]
             | |- context [@weq AddrBits ?a ?b] =>
               destruct (@weq AddrBits a b); [addr_eq | addr_neq]
           end.
  
  Lemma find_some A f: forall l (x: A), find f l = Some x -> In x l /\ f x = true.
  Proof.
    induction l; simpl; auto; try discriminate; intros.
    case_eq (f a); intro H'; rewrite H' in *.
    - inv H; tauto.
    - apply IHl in H; tauto.
  Qed.
    
  Lemma find_none A f: forall l, find f l = None -> forall x: A, In x l -> f x = false.
  Proof.
    induction l; simpl; auto; try discriminate; try tauto; intros.
    case_eq (f a); intro H'; rewrite H' in *; try discriminate.
    specialize (IHl H x); dest.
    destruct H0; subst; tauto.
  Qed.

  Lemma find_none_revcons A l: forall v: A, find (fun _ => true) (l ++ [v])%list = None -> False.
  Proof.
    induction l; simpl; auto; try discriminate; intros.
  Qed.

  Ltac find_simpl :=
    repeat match goal with
             | H: context [match @find ?T ?a ?b with _ => _ end] |- _ =>
               let x := fresh in
               let H' := fresh in
               case_eq (@find T a b);
                 [intros x H'; pose proof (find_some _ _ H') |
                  intros H';
                    ((pose proof (find_none_revcons _ _ H')) || pose proof (find_none _ _ H')) ];
                 try rewrite H' in H; simpl in H
             | |- context [match @find ?T ?a ?b with _ => _ end] =>
               let x := fresh in
               let H' := fresh in
               case_eq (@find T a b);
                 [intros x H'; pose proof (find_some _ _ H') |
                  intros H';
                    ((pose proof (find_none_revcons _ _ H')) || pose proof (find_none _ _ H')) ];
                 try rewrite H'; simpl
           end.


  Hint Resolve isPWait_addRq isPWait_addRq_contra hd_error_revcons_same.
  Hint Rewrite <- rqFromCToP_xfer rqFromCToP_xfer_diffAddr using congruence : invariant.
  Hint Rewrite <- rsFromCToP_xfer rsFromCToP_xfer_diffAddr using congruence : invariant.

  Lemma fromPToC_xfer_diffAddr_packaged:
    forall c a (t: type (ToC LgDataBytes LgNumDatas LgNumChildren (Bit AddrBits) Id))
           fromPList toCList,
      (exists x, c <> x
                 /\ ($ x = t {| bindex := "child" |}
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

  Hint Rewrite <- fromPToC_xfer fromPToC_xfer_diffAddr_packaged using
       (tauto || (eexists; split; [ | split; eassumption ]; congruence)) : invariant.

  Lemma rqFromCToP_revcons a c:
    forall l1 l2
           (v: type (RqToP (Bit (TagBits + IdxBits)) Id)),
      rqFromCToP c a l1 (l2 ++ [v]) =
      (rqFromCToP c a l1 l2 ++
                  if weq a (v {| bindex := "addr" |}) then [v] else nil)%list.
  Proof.
    unfold rqFromCToP.
    intros.
    rewrite filtRqToP_commute_app.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Hint Rewrite rqFromCToP_revcons : invariant.
  Hint Resolve in_app_or in_or_app in_single.

  Lemma fromPToC_rm a c g:
    forall l1 l2,
      fromPToC c a (g :: l1) l2 = if weq a (g {| bindex := "addr" |}) then
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

  Hint Rewrite fromPToC_rm : invariant.

  Ltac unfold_index :=
    do 2 (unfold IndexBound_head, IndexBound_tail, nth_error, addFirstBoundedIndex in *;
           simpl in *).

  Hint Resolve f_equal app_single_r in_pre_suf in_single in_app_or app_cons_not_nil rsLessTo_less_app rsLessTo_in_I_last.

  Ltac rmBadHyp :=
    repeat match goal with
             | [H: ?a === ?s .[ ?v ] |- _] =>
               clear H
             | [H: ?v = ?v |- _] => clear H
           end.

  Ltac solve_simpl := try (discriminate || tauto || word_omega).

  Ltac rewrite_getCs := try (rewrite getCs_cs_matches in * by tauto).

  Lemma beg_mid_last_add_eq A ls:
    (forall (v: A) v1 v2 beg mid last,
       ls ++ [v] = beg ++ v1 :: mid ++ v2 :: last ->
       (last = nil /\ v = v2 /\ ls = beg ++ v1 :: mid) \/
       (exists last', last = last' ++ [v] /\ ls = beg ++ v1 :: mid ++ v2 :: last'))%list.
  Proof.
    intros.
    pose proof (list_nil_revcons last) as [sth1 | sth2].
    - subst.
      left.
      rewrite app_comm_cons in H.
      rewrite app_assoc in H.
      apply app_single_r in H.
      dest.
      repeat (constructor; auto).
    - dest.
      right.
      exists x.
      subst.
      rewrite app_comm_cons in H.
      rewrite app_assoc in H.
      rewrite app_comm_cons in H.
      rewrite app_assoc in H.
      apply app_single_r in H; dest; subst.
      repeat (constructor; auto).
      rewrite app_comm_cons.
      rewrite app_assoc.
      reflexivity.
  Qed.


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
  
  Ltac solve_complex := 
    dest; repeat split; specialize_msgs; specialize_in; dest; solve_simpl.

  Lemma nmemCache_invariants_hold_9 s a u cs:
    nmemCache_invariants s ->
    "pProcess" metaIs a ->
    forall x: cache,
      (x <= wordToNat (wones LgNumChildren))%nat ->
      SemAction s (getActionFromGen string_of_nat (natToWordConst LgNumChildren) a x type)
                u cs WO ->
      nmemCache_invariants (M.union u s).
  Proof.
    Reset Ltac Profile.
    Set Ltac Profiling.
    metaInit;
    try match goal with
            | [ x : cache, c : cache |- _ ] => destruct (eq_nat_dec c x)
          end; invariant_simpl;
    simplMapUpds
      ltac:(autorewrite with invariant in *; eauto;
            intros; unfold isCWait, isPWait, GetAttrType in *;
                    simpl in *;
            destruct_addr;
            unfold_index;
            rmBadHyp;
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
           (v: type (RqToP (Bit (TagBits + IdxBits)) Id)),
      a = v {| bindex := "addr" |} ->
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
           (v: type (RqToP (Bit (TagBits + IdxBits)) Id)),
      a = v {| bindex := "addr" |} ->
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
    Notation "a `` b" := (a {| bindex := b; indexb := _ |}) (at level 0).
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
        | H: procV = true, H': procRqReplace = true |- _ =>
          specialize (i27 H H'); destruct i27 as [sth1 | sth2]; [intuition auto | ]
      end.
      right.
      match goal with
        | |- (if ?p then _ else _) = _ => destruct p as [sth3 | sth4]; [rewrite sth3 in *| auto]
      end.
      rewrite sth2 in *.
      word_omega.
    - match goal with
        | H: procV = true, H': procRqReplace = true |- _ =>
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