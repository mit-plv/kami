Require Import Kami.Syntax String Compile.Rtl Lib.ilist Lib.Struct Lib.StringEq List Compare_dec Compile.Helpers Coq.Strings.Ascii PeanoNat.

Set Implicit Arguments.
Set Asymmetric Patterns.


Open Scope string.
Definition getRegActionRead a s := a ++ "$" ++ s ++ "$read".
Definition getRegActionWrite a s := a ++ "$" ++ s ++ "$write".
Definition getRegActionEn a s := a ++ "$" ++ s ++ "$en".

Definition getMethCallRet f := f ++ "$ret".
Definition getMethCallActionArg a f := a ++ "$" ++ f ++ "$arg".
Definition getMethCallActionEn a f := a ++ "$" ++ f ++ "$en".

Definition getMethDefRet f := f ++ "$ret".
Definition getMethDefArg f := f ++ "$arg".
Definition getMethDefGuard f := f ++ "$g".

Definition getRuleGuard r := r ++ "$g".
Definition getRuleEn r := r ++ "$en".

Definition getRegIndexWrite r i := r ++ "$write$" ++ String (ascii_of_nat i) "".
Definition getRegIndexWriteEn r i := r ++ "$writeEn$" ++ String (ascii_of_nat i) "".
Definition getRegIndexRead r i := r ++ "$read" ++ String (ascii_of_nat i) "".

Close Scope string.

Local Definition inc ns := match ns with
                             | nil => nil
                             | x :: xs => S x :: xs
                           end.

Local Notation cast k' v := match k' with
                              | SyntaxKind k => v
                              | NativeKind _ c => c
                            end.

Section Compile.
  Variable name: string.
  Fixpoint convertExprToRtl k (e: Expr (fun _ => list nat) (SyntaxKind k)): RtlExpr k :=
    match e in Expr _ (SyntaxKind k) return RtlExpr k with
      | Var k' x' =>   match k' return
                             (forall x,
                                match k' return (Expr (fun _ => list nat) k' -> Set) with
                                  | SyntaxKind k => fun _ => RtlExpr k
                                  | NativeKind _ _ => fun _ => IDProp
                                end (Var (fun _ : Kind => list nat) k' x))
                       with
                         | SyntaxKind k => fun x => RtlReadWire k (name, x)
                         | NativeKind t c => fun _ => idProp
                       end x'
      | Const k x => RtlConst x
      | UniBool x x0 => RtlUniBool x (@convertExprToRtl _ x0)
      | BinBool x x0 x1 => RtlBinBool x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | UniBit n1 n2 x x0 => RtlUniBit x (@convertExprToRtl _ x0)
      | BinBit n1 n2 n3 x x0 x1 => RtlBinBit x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | BinBitBool n1 n2 x x0 x1 => RtlBinBitBool x (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | Eq k x x0 => RtlEq (@convertExprToRtl _ x) (@convertExprToRtl _ x0)
      | ReadIndex i k x x0 => RtlReadIndex (@convertExprToRtl _ x) (@convertExprToRtl _ x0)
      | ReadField n ls i x => RtlReadField i (@convertExprToRtl _ x)
      | BuildVector k n x => RtlBuildVector (mapVec (@convertExprToRtl k) x)
      | BuildStruct n attrs x =>
        RtlBuildStruct
          ((fix buildStruct n attrs x :=
              match x in ilist _ attrs return ilist (fun a => RtlExpr (attrType a)) attrs with
                | inil => inil (fun a => RtlExpr (attrType a))
                | icons a na vs h t => icons a (@convertExprToRtl (attrType a) h) (buildStruct na vs t)
              end) n attrs x)
      | UpdateVector i k x x0 x1 => RtlUpdateVector (@convertExprToRtl _ x) (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
      | ITE k' x x0' x1' =>
        match k' return
              (forall x0 x1,
                 match k' return (Expr (fun _ => list nat) k' -> Set) with
                   | SyntaxKind k => fun _ => RtlExpr k
                   | NativeKind _ _ => fun _ => IDProp
                 end (ITE x x0 x1))
        with
          | SyntaxKind k => fun x0 x1 => RtlITE (@convertExprToRtl _ x) (@convertExprToRtl _ x0) (@convertExprToRtl _ x1)
          | NativeKind t c => fun _ _ => idProp
        end x0' x1'
    end.

  Fixpoint convertActionToRtl_noGuard k (a: ActionT (fun _ => list nat) k) enable startList retList :=
    match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        (getMethCallActionArg name meth, nil, existT _ (arg k) (convertExprToRtl argExpr)) ::
        (getMethCallActionEn name meth, nil, existT _ Bool enable) ::
        (name, startList, existT _ (ret k) (RtlReadWire (ret k) (getMethCallRet meth, nil))) ::
        convertActionToRtl_noGuard (cont startList) enable (inc startList) retList
      | Let_ k' expr cont =>
        let wires := convertActionToRtl_noGuard (cont (cast k' startList)) enable (inc startList) retList in
        match k' return Expr (fun _ => list nat) k' -> list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => fun expr => (name, startList, existT _ k (convertExprToRtl expr)) :: wires
          | _ => fun _ => wires
        end expr
      | ReadReg r k' cont =>
        let wires := convertActionToRtl_noGuard (cont (cast k' startList)) enable (inc startList) retList in
        match k' return list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => (name, startList,
                             existT _ k (RtlReadReg k (getRegActionRead name r))) :: wires
          | _ => wires
        end
      | WriteReg r k' expr cont =>
        let wires := convertActionToRtl_noGuard cont enable startList retList in
        match k' return Expr (fun _ => list nat) k' -> list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => fun expr => (getRegActionWrite name r, nil, existT _ k (convertExprToRtl expr)) ::
                                        (getRegActionEn name r, nil, existT _ Bool enable) :: wires
          | _ => fun _ => wires
        end expr
      | Assert_ pred cont => convertActionToRtl_noGuard cont enable startList retList
      | Return x => (name, retList, existT _ k (convertExprToRtl x)) :: nil
      | IfElse pred ktf t f cont =>
        convertActionToRtl_noGuard t (RtlBinBool And enable (convertExprToRtl pred)) (0 :: startList) (startList) ++
        convertActionToRtl_noGuard t
          (RtlBinBool And enable (RtlUniBool Neg (convertExprToRtl pred))) (0 :: inc startList) (inc startList) ++
        (name, inc (inc startList),
         existT _ ktf (RtlITE (convertExprToRtl pred) (RtlReadWire ktf (name, startList)) (RtlReadWire ktf (name, inc startList)))) ::
        convertActionToRtl_noGuard (cont (inc (inc startList))) enable (inc (inc (inc startList))) retList
    end.

  Fixpoint convertActionToRtl_guard k (a: ActionT (fun _ => list nat) k) startList: RtlExpr Bool :=
    match a in ActionT _ _ with
      | MCall meth k argExpr cont =>
        convertActionToRtl_guard (cont startList) (inc startList)
      | Let_ k' expr cont =>
        convertActionToRtl_guard (cont (cast k' startList)) (inc startList)
      | ReadReg r k' cont =>
        convertActionToRtl_guard (cont (cast k' startList)) (inc startList)
      | WriteReg r k' expr cont =>
        convertActionToRtl_guard cont startList
      | Assert_ pred cont => RtlBinBool And (convertExprToRtl pred)
                                        (convertActionToRtl_guard cont startList)
      | Return x => RtlConst (ConstBool true)
      | IfElse pred ktf t f cont =>
        RtlBinBool And
                   (RtlITE (convertExprToRtl pred) (convertActionToRtl_guard t (0 :: startList))
                           (convertActionToRtl_guard t (0 :: inc startList)))
                   (convertActionToRtl_guard (cont (inc (inc startList))) (inc (inc (inc startList))))
    end.
End Compile.
  
Definition convertRuleToRtl (r: Attribute (Action Void)) :=
  (getRuleGuard (attrName r), nil,
   existT _ Bool (convertActionToRtl_guard (attrName r) (attrType r (fun _ => list nat)) (1 :: nil))) ::
  convertActionToRtl_noGuard (attrName r) (attrType r (fun _ => list nat)) (RtlConst (ConstBool true)) (1 :: nil) (0 :: nil).

Definition convertMethodToRtl_wire (f: DefMethT) :=
  (getMethDefGuard (attrName f), nil,
   existT _ Bool (convertActionToRtl_guard (attrName f) (projT2 (attrType f) (fun _ => list nat) (1 :: nil)) (2 :: nil))) ::
  (attrName f, 1 :: nil,
   existT _ (arg (projT1 (attrType f))) (RtlReadWire (arg (projT1 (attrType f))) (getMethDefArg (attrName f), nil))) ::
  convertActionToRtl_noGuard (attrName f) (projT2 (attrType f) (fun _ => list nat) (1 :: nil))
   (RtlConst (ConstBool true)) (2 :: nil) (0 :: nil).

Definition convertMethodToRtl_output (f: DefMethT) :=
  (getMethDefRet (attrName f), existT _ _ (RtlReadWire (ret (projT1 (attrType f))) (attrName f, 0 :: nil))).

Fixpoint getWritesAction k (a: ActionT typeUT k) :=
  match a with
    | MCall meth k argExpr cont => getWritesAction (cont tt)
    | Let_ k' expr cont => getWritesAction (cont (cast k' tt))
    | ReadReg r k' cont => getWritesAction (cont (cast k' tt))
    | WriteReg r k expr cont => r :: getWritesAction cont
    | IfElse _ _ t f cont => getWritesAction t ++ getWritesAction f ++ getWritesAction (cont tt)
    | Assert_ x cont => getWritesAction cont
    | Return x => nil
  end.

Fixpoint getReadsAction k (a: ActionT typeUT k) :=
  match a with
    | MCall meth k argExpr cont => getReadsAction (cont tt)
    | Let_ k' expr cont => getReadsAction (cont (cast k' tt))
    | ReadReg r k' cont => r :: getReadsAction (cont (cast k' tt))
    | WriteReg r k expr cont => getReadsAction cont
    | IfElse _ _ t f cont => getReadsAction t ++ getReadsAction f ++ getReadsAction (cont tt)
    | Assert_ x cont => getReadsAction cont
    | Return x => nil
  end.

Definition getReadsRule (r: Attribute (Action Void)) :=
  (getReadsAction (attrType r typeUT)).

Definition getReadsMeth (f: DefMethT) :=
  (getReadsAction (projT2 (attrType f) typeUT tt)).

Definition getWritesRule (r: Attribute (Action Void)) :=
  (getWritesAction (attrType r typeUT)).

Definition getWritesMeth (f: DefMethT) :=
  (getWritesAction (projT2 (attrType f) typeUT tt)).

Section UsefulFunctions.
  Variable m: Modules.
  Variable totalOrder: list string.
  Variable ignoreLess: list (string * string).

  Local Notation getFromName getObjects getRegs r :=
    match find (fun a => string_eq r (attrName a)) (getObjects m) with
      | None => nil
      | Some rule => getRegs rule
    end.

  Definition getReadsRuleName r := (getFromName getRules getReadsRule r).
  Definition getWritesRuleName r := (getFromName getRules getWritesRule r).
  Definition getReadsMethName f := (getFromName getDefsBodies getReadsMeth f).
  Definition getWritesMethName f := (getFromName getDefsBodies getWritesMeth f).

  Definition getReads x := getReadsRuleName x ++ getReadsMethName x.
  Definition getWrites x := getWritesRuleName x ++ getWritesMethName x.
  
  Definition getCallGraph :=
    fold_left (fun g (r: Attribute (Action Void)) => (attrName r, getCallsRule r) :: g) (getRules m) nil
              ++
              fold_left (fun g (f: DefMethT) => (attrName f, getCallsDm f) :: g) (getDefsBodies m) nil.

  Definition getAllCalls a := getConnectedChain string_dec (getCallGraph) a.

  Definition getAllReads a :=
    fold_left (fun regs f => regs ++ getReads f) (getAllCalls a) (getReads a).

  Definition getAllWrites a :=
    fold_left (fun regs f => regs ++ getWrites f) (getAllCalls a) (getWrites a).

  Definition correctIgnoreLess :=
    filter (fun x => is_nil (intersect string_dec (getAllCalls (fst x))
                            (getAllCalls (snd x)))) ignoreLess.

  Section GenerateRegIndicies.
    Variable reg: string.

    Section FindWritePrevPos.
      Variable pos: nat.

      Local Fixpoint find_write_prev_pos' currPos (ls: list string) :=
        match ls with
          | nil => None
          | x :: xs => match find_write_prev_pos' (S currPos) xs with
                         | None =>
                           if in_dec string_dec reg (getAllWrites x)
                           then if lt_dec currPos pos
                                then Some (currPos, x)
                                else None
                           else None
                         | Some y => Some y
                       end
        end.

      Local Lemma find_write_prev_pos'_correct:
        forall ls currPos i x, Some (i, x) = find_write_prev_pos' currPos ls  -> i < pos.
      Proof.
        induction ls; simpl; intros; try congruence.
        specialize (IHls (S currPos) i x).
        repeat match goal with
                 | H: context [match ?P with _ => _ end] |- _ => destruct P
               end; try solve [congruence || eapply IHls; eauto].
      Qed.

      Local Definition find_write_prev_pos := find_write_prev_pos' 0 totalOrder.
      
      Local Lemma find_write_prev_pos_correct:
        forall i x, Some (i, x) = find_write_prev_pos  -> i < pos.
      Proof.
        eapply find_write_prev_pos'_correct.
      Qed.
    End FindWritePrevPos.

    Definition regIndex: nat -> nat :=
      Fix
        Wf_nat.lt_wf (fun _ => nat)
        (fun (pos: nat)
             (findRegIndex: forall pos', pos' < pos -> nat) =>
           match pos return (forall pos', pos' < pos -> nat) -> nat with
             | 0 => fun _ => 0
             | S m =>
               fun findRegIndex =>
                 match nth_error totalOrder (S m) with
                   | Some a =>
                     if in_dec string_dec reg (getAllReads a ++ getAllWrites a)%list
                     then
                       match
                         find_write_prev_pos (S m) as val
                         return (forall i x, Some (i, x) = val -> i < S m) -> nat with
                         | None => fun _ => findRegIndex m (ltac:(abstract Omega.omega))
                         | Some (prev_pos, a') =>
                           if in_dec string_dec reg (getAllWrites a')
                           then if in_dec (prod_dec string_dec string_dec) (a, a') correctIgnoreLess
                                then fun pf => max (S (findRegIndex  prev_pos (pf _ _ eq_refl)))
                                                   (findRegIndex m (ltac:(abstract Omega.omega)))
                                else fun _ => findRegIndex m (ltac:(abstract Omega.omega))
                           else fun _ => findRegIndex m (ltac:(abstract Omega.omega))
                       end (find_write_prev_pos_correct (S m))
                     else findRegIndex m (ltac:(abstract Omega.omega))
                   | None => 0
                 end
           end findRegIndex).

    Definition maxRegIndex :=
      match length totalOrder with
        | 0 => 0
        | S m => regIndex m
      end.
  End GenerateRegIndicies.


  Local Fixpoint methPos' f ls n :=
    match ls with
      | nil => nil
      | x :: xs => if in_dec string_dec f (getAllCalls x)
                   then n :: methPos' f xs (S n)
                   else methPos' f xs (S n)
    end.

  Definition methPos f := methPos' f totalOrder 0.

  Definition noMethContradiction f :=
    fold_left (fun prev r =>
                 andb prev (sameList Nat.eq_dec (map (regIndex r) (methPos f))))
              (getAllReads f ++ getAllWrites f) true.

  Definition shareRegDisable posFirst posSecond :=
    fold_left (fun disable reg => if Nat.eq_dec (regIndex reg posFirst) (regIndex reg posSecond)
                                  then true
                                  else disable) (intersect
                                                   string_dec
                                                   (nth posFirst (map getAllWrites totalOrder) nil)
                                                   (nth posSecond (map getAllReads totalOrder) nil
                                                        ++
                                                        nth posSecond (map getAllWrites totalOrder) nil)) false.

  Definition shareMethDisable posFirst posSecond :=
    not_nil (intersect string_dec (nth posFirst (map getAllCalls totalOrder) nil)
                       (nth posSecond (map getAllCalls totalOrder) nil)).

  Definition shareDisable posFirst posSecond := orb (shareRegDisable posFirst posSecond) (shareMethDisable posFirst posSecond).

  Local Fixpoint disables' posFirst posSecond :=
    if lt_dec posFirst posSecond
    then
      match posFirst with
        | 0 => if shareDisable posFirst posSecond
               then match nth_error totalOrder posFirst with
                      | None => nil
                      | Some r => r :: nil
                    end
               else nil
        | S m => if shareDisable posFirst posSecond
                 then match nth_error totalOrder posFirst with
                        | None => disables' m posSecond
                        | Some r => r :: disables' m posSecond
                      end
                 else disables' m posSecond
      end
    else nil.

  Definition disables rule : list string :=
    match find_pos string_dec rule totalOrder with
      | None => nil
      | Some posSecond => disables' (pred posSecond) posSecond
    end.

  Definition computeRuleEnAssign rule :=
    (getRuleEn rule, nil: list nat,
     existT RtlExpr Bool
            (fold_left (fun (e: RtlExpr Bool) r => RtlBinBool And e (RtlReadWire Bool (getRuleEn r, nil)))
                       (disables rule) (RtlConst true))).

  Definition getRulePos r := find_pos string_dec r totalOrder.

  Definition getRuleRegIndex rule reg :=
    match getRulePos rule with
      | None => 0
      | Some x => regIndex reg x
    end.
  
  Definition getRegIndexWriteRules reg idx :=
    fold_left (fun rest x => match getRulePos x with
                               | None => rest
                               | Some p => if Nat.eq_dec (regIndex reg p) idx
                                           then if find (string_eq reg) (getWritesRuleName x)
                                                then x :: rest
                                                else rest
                                           else rest
                             end) (map (@attrName _) (getRules m)) nil.
  
  Definition computeRegIndexWrite ty reg idx :=
    (getRegIndexWrite reg idx, (nil: list nat),
     existT RtlExpr ty
            (fold_left (fun expr r => RtlITE (RtlReadWire Bool (getRuleEn r, nil))
                                             (RtlReadWire ty (getRegActionWrite r reg, nil)) expr) (getRegIndexWriteRules reg idx)
                       (RtlReadWire ty (getRegIndexRead reg idx, nil)))).

  Definition computeRegFinalWrite ty reg := (reg, existT RtlExpr ty (RtlReadWire ty (getRegIndexWrite reg (maxRegIndex reg), nil))).

  (*
  Local Fixpoint computeLastRegWrite' ty reg n :=
    match maxRegIndex reg with
      | 0 => RtlReadReg ty (getRegIndexWrite reg 0)
      | S m => RtlExpr ty (RtlITE (RtlReadWire Bool (getRegIndexWriteEn reg (S m))) (RtlReadWire ty (getRegIndexWrite reg (S m)))
                                  (computeLastRegWrite' ty reg m))
    end.
   *)
  
End UsefulFunctions.

Require Import Kami.Tutorial.

Eval compute in match head (getDefsBodies consumer) with
                  | Some t => getCallsDm t
                  | None => nil
                end.
