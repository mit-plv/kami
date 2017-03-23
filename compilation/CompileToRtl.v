Require Import Kami.Syntax String Compile.Rtl Lib.ilist Lib.Struct Lib.StringEq List Compare_dec Compile.Helpers Coq.Strings.Ascii PeanoNat.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.
Fixpoint string_of_nat n :=
  match n with
    | 0 => "0"
    | S m => "S" ++ string_of_nat m
  end.

Local Notation nil_nat := (nil: list nat).
Definition getRegActionRead a s := (a ++ "$" ++ s ++ "$read", nil_nat).
Definition getRegActionWrite a s := (a ++ "$" ++ s ++ "$write", nil_nat).
Definition getRegActionEn a s := (a ++ "$" ++ s ++ "$en", nil_nat).

Definition getMethCallActionArg a f := (a ++ "$" ++ f ++ "$arg", nil_nat).
Definition getMethCallActionEn a f := (a ++ "$" ++ f ++ "$en", nil_nat).

Definition getMethRet f := (f ++ "$ret", nil_nat).
Definition getMethArg f := (f ++ "$arg", nil_nat).

Definition getActionGuard r := (r ++ "$g", nil_nat).
Definition getActionEn r := (r ++ "$en", nil_nat).

Definition getRegIndexWrite r i := (r ++ "$write$" ++ string_of_nat i, nil_nat).
Definition getRegIndexWriteEn r i := (r ++ "$writeEn$" ++ string_of_nat i, nil_nat).
Definition getRegIndexRead r i := (r ++ "$read$" ++ string_of_nat i, nil_nat).

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
        (getMethCallActionArg name meth, existT _ (arg k) (convertExprToRtl argExpr)) ::
        (getMethCallActionEn name meth, existT _ Bool enable) ::
        (name, startList, existT _ (ret k) (RtlReadWire (ret k) (getMethRet meth))) ::
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
                             existT _ k (RtlReadWire k (getRegActionRead name r))) :: wires
          | _ => wires
        end
      | WriteReg r k' expr cont =>
        let wires := convertActionToRtl_noGuard cont enable startList retList in
        match k' return Expr (fun _ => list nat) k' -> list (string * list nat * sigT RtlExpr) with
          | SyntaxKind k => fun expr => (getRegActionWrite name r, existT _ k (convertExprToRtl expr)) ::
                                        (getRegActionEn name r, existT _ Bool enable) :: wires
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
  
Definition computeRuleAssigns (r: Attribute (Action Void)) :=
  (getActionGuard (attrName r),
   existT _ Bool (convertActionToRtl_guard (attrName r) (attrType r (fun _ => list nat)) (1 :: nil))) ::
  convertActionToRtl_noGuard (attrName r) (attrType r (fun _ => list nat)) (RtlConst (ConstBool true)) (1 :: nil) (0 :: nil).

Definition computeMethAssigns (f: DefMethT) :=
  (getActionGuard (attrName f),
   existT _ Bool (convertActionToRtl_guard (attrName f) (projT2 (attrType f) (fun _ => list nat) (1 :: nil)) (2 :: nil))) ::
  (attrName f, 1 :: nil,
   existT _ (arg (projT1 (attrType f))) (RtlReadWire (arg (projT1 (attrType f))) (getMethArg (attrName f)))) ::
  convertActionToRtl_noGuard (attrName f) (projT2 (attrType f) (fun _ => list nat) (1 :: nil))
   (RtlConst (ConstBool true)) (2 :: nil) (0 :: nil).

Definition computeMethRets (f: DefMethT) :=
  (getMethRet (attrName f), existT _ _ (RtlReadWire (ret (projT1 (attrType f))) (attrName f, 0 :: nil))).

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

Definition getReadsRuleBody (r: Attribute (Action Void)) :=
  (getReadsAction (attrType r typeUT)).

Definition getReadsMethBody (f: DefMethT) :=
  (getReadsAction (projT2 (attrType f) typeUT tt)).

Definition getWritesRuleBody (r: Attribute (Action Void)) :=
  (getWritesAction (attrType r typeUT)).

Definition getWritesMethBody (f: DefMethT) :=
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

  Definition getReadsRule r := (getFromName getRules getReadsRuleBody r).
  Definition getWritesRule r := (getFromName getRules getWritesRuleBody r).
  Definition getReadsMeth f := (getFromName getDefsBodies getReadsMethBody f).
  Definition getWritesMeth f := (getFromName getDefsBodies getWritesMethBody f).

  Definition getReads x := getReadsRule x ++ getReadsMeth x.
  Definition getWrites x := getWritesRule x ++ getWritesMeth x.
  
  Definition getCallGraph :=
    fold_left (fun g (r: Attribute (Action Void)) => (attrName r, getCallsRule r) :: g) (getRules m) nil
              ++
              fold_left (fun g (f: DefMethT) => (attrName f, getCallsDm f) :: g) (getDefsBodies m) nil.

  Definition getCallers f := map fst (filter (fun x => if find (string_eq f) (snd x) then true else false) getCallGraph).

  Definition getAllCalls a := getConnectedChain string_dec (getCallGraph) a.

  Definition getExternalCalls :=
    filter (fun f => if find (string_eq (fst f)) (getDefs m) then false else true) (getCalls_Sig m).
  
  Definition getAllReads a :=
    fold_left (fun regs f => regs ++ getReads f) (getAllCalls a) (getReads a).

  Definition getAllWrites a :=
    fold_left (fun regs f => regs ++ getWrites f) (getAllCalls a) (getWrites a).

  Definition correctIgnoreLess :=
    filter (fun x => is_nil (intersect string_dec (getAllCalls (fst x))
                                       (getAllCalls (snd x)))) ignoreLess.

  Definition getWritesWhichCall reg calls := find (fun call => if find (string_eq reg) (getWritesMeth call) then true else false) calls.

  Definition getWhoWrote rule reg := if in_dec string_dec reg (getWritesRule rule)
                                     then Some rule
                                     else getWritesWhichCall reg (getAllCalls rule).

  Section GenerateRegIndicies.
    Variable reg: string.

    Section FindWritePrevPos.
      Variable pos: nat.

      Local Fixpoint find_write_prev_pos' currPos (ls: list string) :=
        match ls with
          | nil => None
          | x :: xs => match find_write_prev_pos' (S currPos) xs with
                         | None =>
                           if find (string_eq reg) (getAllWrites x)
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
                     if find (string_eq reg) (getAllReads a ++ getAllWrites a)%list
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

  Definition getRegType reg :=
    match attrType reg with
      | RegInitCustom (existT (SyntaxKind k) _) => k
      | RegInitDefault (SyntaxKind k) => k
      | _ => Void
    end.

  Section OneRule.
    Variable rule: string.

    Definition disables: list string :=
      match find_pos string_dec rule totalOrder with
        | None => nil
        | Some posSecond => disables' (pred posSecond) posSecond
      end.

    Definition computeRuleEn :=
      (getActionEn rule,
       existT RtlExpr Bool
              (fold_left (fun (e: RtlExpr Bool) r => RtlBinBool And e (RtlUniBool Neg (RtlReadWire Bool (getActionEn r))))
                         disables (RtlReadWire Bool (getActionGuard rule)))).

    Definition getRulePos := find_pos string_dec rule totalOrder.

    Definition getRuleRegIndex reg :=
      match getRulePos with
        | None => 0
        | Some x => regIndex reg x
      end.
  End OneRule.

  Local Fixpoint methPos' f ls n :=
    match ls with
      | nil => nil
      | x :: xs => if find (string_eq f) (getAllCalls x)
                   then n :: methPos' f xs (S n)
                   else methPos' f xs (S n)
    end.

  Definition methPos f := methPos' f totalOrder 0.

  Definition noMethContradiction f :=
    fold_left (fun prev r =>
                 andb prev (sameList Nat.eq_dec (map (regIndex r) (methPos f))))
              (getAllReads f ++ getAllWrites f) true.

  Definition getPos a := match getRulePos a, head (methPos a) with
                           | Some x, _ => Some x
                           | _, Some y => Some y
                           | None, None => None
                         end.
  
  Definition computeActionReadIndices a :=
    fold_left (fun rest reg => match getPos a with
                                 | None => rest
                                 | Some idx =>
                                   if find (string_eq (attrName reg)) (getReads a)
                                   then
                                     (getRegActionRead a (attrName reg),
                                      existT RtlExpr (getRegType reg)
                                             (RtlReadWire (getRegType reg)
                                                          (getRegIndexRead (attrName reg) (regIndex (attrName reg) idx))))
                                       ::
                                       rest
                                   else rest
                               end) (getRegInits m) nil.

  
  Section OneReg.
    Variable ty: Kind.
    Variable reg: string.
    
    Local Definition getRegIndexWriters idx :=
      fold_left (fun rest x => match getRulePos x with
                                 | None => rest
                                 | Some p => if Nat.eq_dec (regIndex reg p) idx
                                             then match getWhoWrote x reg with
                                                    | None => rest
                                                    | Some y => y :: rest
                                                  end
                                             else rest
                               end) (map (@attrName _) (getRules m)) nil.
    
    Local Definition getComputeRegIndexWrite' idx :=
      (getRegIndexWrite reg idx,
       existT RtlExpr ty
              (fold_left (fun expr r => RtlITE (RtlReadWire Bool (getActionEn r))
                                               (RtlReadWire ty (getRegActionWrite r reg)) expr) (getRegIndexWriters idx)
                         (RtlReadWire ty (getRegIndexRead reg idx)))).

    Local Fixpoint computeRegIndexWrite' n :=
      match n with
        | 0 => getComputeRegIndexWrite' n :: nil
        | S m => getComputeRegIndexWrite' n :: computeRegIndexWrite' m
      end.

    Definition computeRegIndexWrite := computeRegIndexWrite' (maxRegIndex reg).
    
    Definition computeRegFinalWrite := (reg, existT RtlExpr ty (RtlReadWire ty (getRegIndexWrite reg (maxRegIndex reg)))).

    (*
    Local Fixpoint computeLastRegWrite' n :=
      match n with
        | 0 => RtlReadWire ty (getRegIndexWrite reg 0)
        | S m => RtlITE (RtlReadWire Bool (getRegIndexWriteEn reg (S m))) (RtlReadWire ty (getRegIndexWrite reg (S m)))
                        (computeLastRegWrite' m)
      end.

    Definition computeLastRegWrite := computeLastRegWrite' (maxRegIndex reg).
     *)

    Local Fixpoint connectRegWritesToReads' n :=
      match n with
        | 0 => (getRegIndexRead reg 0, existT RtlExpr ty (RtlReadReg ty reg))
        | S m => (getRegIndexRead reg (S m), existT RtlExpr ty (RtlReadWire ty (getRegIndexWrite reg m)))
      end.

    Definition connectRegWritesToReads := connectRegWritesToReads' (maxRegIndex reg).  
  End OneReg.

  Section Meth.
    Variable meth: string.
    Variable argT: Kind.

    Definition computeMethArg :=
      (getMethArg meth,
       existT RtlExpr argT
              (fold_left (fun expr r => RtlITE (RtlReadWire Bool (getActionEn r))
                                               (RtlReadWire argT (getMethCallActionArg r meth)) expr) (getCallers meth)
                         (RtlConst (getDefaultConst argT)))).
    
    Definition computeMethEn :=
      (getActionEn meth,
       existT RtlExpr Bool
              (fold_left (fun expr r => RtlBinBool Or
                                                   (RtlReadWire Bool (getActionEn r))
                                                   expr) (getCallers meth)
                         (RtlConst false))).
  End Meth.

  Definition computeAllAssigns :=
    concat (map computeRuleAssigns (getRules m))
           ++
           map computeRuleEn (map (@attrName _) (getRules m))
           ++
           concat (map computeMethAssigns (getDefsBodies m))
           ++
           map computeMethRets (getDefsBodies m)
           ++
           map (fun x => computeMethArg (attrName x) (arg (projT1 (attrType x)))) (getDefsBodies m)
           ++
           map computeMethEn (getDefs m)
           ++
           concat (map computeActionReadIndices (map (@attrName _) (getRules m) ++ getDefs m))
           ++
           concat (map (fun x => computeRegIndexWrite (getRegType x) (attrName x)) (getRegInits m))
           ++
           map (fun x => connectRegWritesToReads (getRegType x) (attrName x)) (getRegInits m).

  Definition computeAllRegWrites :=
    map (fun x => computeRegFinalWrite (getRegType x) (attrName x)) (getRegInits m).

  Definition computeAllOutputs :=
    map (fun x => fst (getMethArg (fst x))) getExternalCalls
        ++
        map (fun x => fst (getActionEn (fst x))) getExternalCalls.

  Definition computeAllInputs :=
    map (fun x => (fst (getActionGuard (fst x)), Bool)) getExternalCalls
        ++
        map (fun x => (fst (getMethRet (fst x)), ret (snd x))) getExternalCalls.

  Definition computeModule :=
    {| inputs := computeAllInputs;
       outputs := computeAllOutputs;
       regWrites := computeAllRegWrites;
       wires := computeAllAssigns |}.
End UsefulFunctions.

(*
Require Import Kami.Tutorial.

Eval compute in match head (getDefsBodies consumer) with
                  | Some t => getCallsDm t
                  | None => nil
                end.
*)