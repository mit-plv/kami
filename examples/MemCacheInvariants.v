Require Import Lib.FMap Lib.Word Ex.MemTypes Lib.Indexer Lib.Struct Ex.Msi
        Ex.NativeFifo Lts.Notations String Ex.MemCacheInl Lts.Syntax List Lts.Semantics
        ParametricSyntax Lib.CommonTactics Lts.SemFacts Lib.FMap Lib.Concat
        FunctionalExtensionality Program.Equality Lts.Tactics Arith Ex.MapVReify Lts.SymEval
        Lts.SymEvalTac Lib.StringExtension.

Set Implicit Arguments.

(* Local Notation "x 'is' y 'of' s" := (M.find y%string s = Some (existT _ _ x)) (at level 12). *)

Ltac mapVReify f2 f n m :=
  match m with
    | M.union
        (repMap _ _ (fun i => (addIndexToStr _
                                             i ?s :: ?v)%struct) _) ?m
      =>
      let mr := mapVReify f2 f n m in
      constr:(MVRVar s eq_refl v mr)
    | M.empty _ => constr:(MVREmpty n _ f2 f)
    | M.add (addIndexToStr _ ?i ?k) ?v ?m' =>
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

Ltac mapVR_Regs n m := mapVReify (fullType type) evalConstFullT
                                 n m.

Ltac mapVR_Others t n m := mapVReify t (fun k (v: t k) => v)
                                     n m.

Ltac mapVR_Meths n m := mapVReify SignT (fun k (v: SignT k) => v)
                                  n m.

Ltac mkStruct :=
  repeat match goal with
           | H: context[mkStruct ?p ?q] |- _ => rewrite (mkStruct_eq p q) in H;
               simpl in H; unfold StringBound.ith_Bounded in H; simpl in H
           | |- context[mkStruct ?p ?q] => rewrite (mkStruct_eq p q);
               simpl; unfold StringBound.ith_Bounded; simpl
         end.

Ltac existRegs n :=
  match goal with
    | |- ?inv ?s =>
      unfold inv;
        intros;
        let mr := mapVR_Regs (wordToNat (wones n)) s in
        esplit;
          unfold withIndex;
          match goal with
            | cond: (_ <= _)%nat |- _ =>
              match goal with
                | |- M.find (addIndexToStr _ ?c ?k) _ = _ =>
                  rewrite <- (findMVR_find_var mr k eq_refl cond); simpl; eauto
                | |- M.find ?k _ = _ =>
                  rewrite <- (findMVR_find_string mr k eq_refl); simpl; eauto
                | _ => simpl; auto
              end
          end
  end.

Ltac simplifyInvs :=
  repeat autounfold with MethDefs in *;
  intros; try (exfalso; assumption);
  repeat (rewrite ?mapVec_replicate_commute, ?evalVec_replicate in *; simpl in *);
  dest; auto; try discriminate;
  repeat match goal with
           | H: nil = (?a ++ ?b :: ?c)%list |- _ => apply app_cons_not_nil in H
           | H: False |- _ => exfalso; auto
           | |- context[weq ?p ?q] => destruct (weq p q)
           | H: context[weq ?p ?q] |- _ => destruct (weq p q)
           | H: andb ?a ?b = true |- _ =>
             apply Bool.andb_true_iff in H; dest
           | _ => (Nomega.pre_nomega; omega) || discriminate
         end.

Ltac prelimSimplRegs n :=
  existRegs n; simplifyInvs.

Ltac allRules :=
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
  end; simpl;
  match goal with
    | |- context [eq_nat_dec ?x ?x] =>
      let isEq := fresh in
      destruct (eq_nat_dec x x) as [isEq | isEq];
        [ | clear - isEq; intuition auto]
    | _ => idtac
  end.


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
             (cRq: type (RqFromC LgNumChildren (Bit (TagBits + IdxBits)) Id))
             dirw (cword: word LgNumChildren) :=
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
         a cword c: Prop :=
    {
      dir: <| Vector (Vector Msi LgNumChildren) (TagBits + IdxBits) |> ;
      dirFind: dir === s.["dataArray.mcs"];
      mline: <|Vector (Line LgDataBytes LgNumDatas) (TagBits + IdxBits) |> ;
      mlineFind: mline === s.["dataArray.mline"];
      cRqValid: <| Bool |> ;
      cRqValidFind: cRqValid === s.["cRqValid"];
      cRq: <| RqFromC LgNumChildren (Bit AddrBits) Id |> ;
      cRqFind: cRq === s.["cRq"];
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

      i5: (dir (getTagIdxS a) cword >= getCs cs tag a);
      
      (* i6: (isCompat cword (dir (getTagIdxS a))); *)
      
      i7: (forall rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                        getCs cs tag a <= rs ``"to" /\ dir (getTagIdxS a) cword > rs ``"to");

      i8: (forall msg, In msg (fromPToC cword a fromPList toCList) ->
                         msg ``"isRq" = false ->
                         getCs cs tag a < msg ``"to" /\ dir (getTagIdxS a) cword = msg ``"to");

      i9: (forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                        dir (getTagIdxS a) cword <= rq ``"from" ->
                        forall rs,
                          In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                          isPWait a cRqValid cRq dirw cword);

      i10: (forall msg1 msg2 beg mid last,
              fromPToC cword a fromPList toCList = beg ++ msg1 :: mid ++ msg2 :: last ->
              msg1 ``"isRq" = false ->
              msg2 ``"isRq" = false ->
              False)%list;
      
      i11: (dir (getTagIdxS a) cword > getCs cs tag a ->
                      rsFromCToP cword a rsFromCList rsToPList <> nil);
      
      i12: (
              rsFromCToP cword a rsFromCList rsToPList = nil \/
              forall msg, In msg (fromPToC cword a fromPList toCList) -> msg ``"isRq" = true);

      i13: (rsLessTo (rsFromCToP cword a rsFromCList rsToPList));

      i14: (forall cToPRsLast beg,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ [cToPRsLast] ->
              cToPRsLast ``"to" = getCs cs tag a)%list;

      i15: (forall pToCRq pToCRs beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRq :: mid ++ pToCRs :: last ->
              pToCRq ``"isRq" = true ->
              pToCRs ``"isRq" = false ->
              getCs cs tag a = $ Msi.Inv)%list;

      i16: (
             isCWait a procv procRq csw ->
             (getCs cs tag a < if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh) /\
             (((exists rq, In rq (rqFromCToP cword a rqFromCList rqToPList)
                              /\ rq ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod
                                              else $ Msi.Sh)
                              /\ rq ``"from" >= getCs cs tag a) /\
               forall msg, In msg (fromPToC cword a fromPList toCList) -> msg ``"isRq" = true)
              \/
              ((exists rs, In rs (fromPToC cword a fromPList toCList)
                              /\ rs ``"isRq" = false
                              /\ rs ``"to" = if (procRq ``"op"):bool then $ Msi.Mod
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
                        isCWait a procv procRq csw
                        /\ (getCs cs tag a < if (procRq ``"op"):bool
                                             then $ Msi.Mod else $ Msi.Sh)
                          /\ rq ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh)
                          /\ rq ``"from" >= getCs cs tag a);

      i16b: (forall rs, In rs (fromPToC cword a fromPList toCList) ->
                          isCWait a procv procRq csw
                          /\ (getCs cs tag a < if (procRq ``"op"):bool
                                               then $ Msi.Mod else $ Msi.Sh)
                          /\ rs ``"isRq" = false
                          /\ rs ``"to" = (if (procRq ``"op"):bool then $ Msi.Mod else $ Msi.Sh));

      i17: (forall pToCRq,
              In pToCRq (fromPToC cword a fromPList toCList) ->
              pToCRq ``"isRq" = true ->
              isPWait a cRqValid cRq dirw cword ->
              getCs cs tag a = $ Msi.Inv);

      i18: (forall pToCRq cToPRs,
              In pToCRq (fromPToC cword a fromPList toCList) ->
              pToCRq ``"isRq" = true ->
              In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
              cToPRs ``"to" = $ Msi.Inv);

      i19: (forall pToCRs pToCRq beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRs :: mid ++ pToCRq :: last ->
              pToCRs ``"isRq" = false ->
              pToCRq ``"isRq" = true ->
              isPWait a cRqValid cRq dirw cword)%list;

      i20: (forall pToCRq1 pToCRq2 beg mid last,
              fromPToC cword a fromPList toCList = beg ++ pToCRq1 :: mid ++ pToCRq2 :: last ->
              pToCRq1 ``"isRq" = true ->
              pToCRq2 ``"isRq" = true ->
              getCs cs tag a = $ Msi.Inv)%list;

      i21: (forall rs,
              In rs (rsFromCToP cword a rsFromCList rsToPList) ->
              rs ``"isVol" = false ->
              isPWait a cRqValid cRq dirw cword);

      i22: (forall cToPRs1 cToPRs2 beg mid last,
              rsFromCToP cword a rsFromCList rsToPList = beg ++ cToPRs1 :: mid ++ cToPRs2 :: last ->
              cToPRs1 ``"isVol" = true \/ cToPRs2 ``"isVol" = true)%list;

      i23: (forall cToPRq,
              In cToPRq (rqFromCToP cword a rqFromCList rqToPList) ->
              dir (getTagIdxS a) cword <= cToPRq ``"from" ->
              forall cToPRs,
                In cToPRs (rsFromCToP cword a rsFromCList rsToPList) ->
                cToPRs ``"isVol" = false);

      i24: (length (rsFromCToP cword a rsFromCList rsToPList) <= 2)%nat;

      i25: forall rq, In rq (rqFromCToP cword a rqFromCList rqToPList) ->
                        rq ``"from" < rq ``"to";

      i26: forall rs, In rs (rsFromCToP cword a rsFromCList rsToPList) ->
                        rs ``"isVol" = true ->
                        rs ``"to" = $ Msi.Inv
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
      $ x = t ``"child" ->
      fromPToC $ x a fromPList (t :: toCList) =
      fromPToC $ x a
        (fromPList ++
         [t
            (addFirstBoundedIndex
               (mapAttr type ("child" :: Bit LgNumChildren)%struct) ``
               ("msg"))]) toCList.
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

      (*
      Focus 6.

      + allRules; (reflexivity || eassumption || unfold listEltT, listEnq, listDeq, listFirstElt,
                   listIsEmpty, getCs, getIdxS, getTagS in *; mkStruct).
        *) 

      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
      + allRules; (reflexivity || eassumption || intros); unfold isCWait in *.
        * dest; discriminate.
        * apply i16a in H2; dest; discriminate.
        * apply i16b in H2; dest; discriminate.
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
