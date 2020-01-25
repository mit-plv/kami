Require Import String List.
Require Import Lib.Word Lib.ilist Lib.Struct Lib.Indexer.
Require Import Kami.Syntax Kami.Synthesize.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section VecFunc.
  Variables A B: Type.
  Variable map: A -> B.

  Fixpoint mapVec n (vec: Vec A n): Vec B n :=
    match vec in Vec _ n return Vec B n with
    | Vec0 e => Vec0 (map e)
    | VecNext n' v1 v2 => VecNext (mapVec v1) (mapVec v2)
    end.
End VecFunc.

Section BluespecSubset.

  Inductive BExpr: Type :=
  | BVar: nat -> BExpr
  | BConst k: ConstT k -> BExpr
  | BUniBool: UniBoolOp -> BExpr -> BExpr
  | BBinBool: BinBoolOp -> BExpr -> BExpr -> BExpr
  | BUniBit n1 n2: UniBitOp n1 n2 -> BExpr -> BExpr
  | BBinBit n1 n2 n3: BinBitOp n1 n2 n3 -> BExpr -> BExpr -> BExpr
  | BBinBitBool n1 n2: BinBitBoolOp n1 n2 -> BExpr -> BExpr -> BExpr
  | BITE: BExpr -> BExpr -> BExpr -> BExpr
  | BEq: BExpr -> BExpr -> BExpr
  | BReadIndex: BExpr -> BExpr -> BExpr
  | BReadField: string -> BExpr -> BExpr
  | BBuildVector lgn: Vec BExpr lgn -> BExpr
  | BBuildStruct: forall n, Vector.t (Attribute Kind) n -> list (Attribute BExpr) -> BExpr
  | BUpdateVector: BExpr -> BExpr -> BExpr -> BExpr
  | BReadReg: string -> BExpr
  | BReadArrayIndex: BExpr -> BExpr -> BExpr
  | BBuildArray n: Vector.t BExpr n -> BExpr
  | BUpdateArray: BExpr -> BExpr -> BExpr -> BExpr.

  (* NOTE: BBCall is not used for translation from Kami to Bluespec,
   * but defined in order to support multi-parameter methods.
   *)
  Inductive BAction: Type :=
  | BMCall: nat (* binder *) -> string (* meth *) -> SignatureT -> BExpr -> BAction
  | BBCall: nat (* binder *) -> string (* meth *) -> bool (* Action in Bluespec? *) ->
            list BExpr -> BAction
  | BLet: nat (* binder *) -> option Kind (* type annotation, if possible *) ->
          BExpr -> BAction
  | BWriteReg: string -> BExpr -> BAction
  | BIfElse: BExpr -> nat (* branch return binder *) -> Kind (* return type *) ->
             list BAction -> list BAction -> BAction
  | BAssert: BExpr -> BAction
  | BReturn: BExpr -> BAction.

  Definition BRule := Attribute (list BAction).
  Definition BMethod := Attribute (SignatureT * list BAction).

  Inductive BModule :=
  | BModulePrim (primModName: string) (ifc: list (Attribute SignatureT)): BModule
  | BModuleB (bregs: list RegInitT)
             (brules: list BRule)
             (bdms: list BMethod): BModule.

  Definition BModules := list BModule.

  (** Conversion from Kami modules to BModules *)

  Definition bind {A B} (oa: option A) (f: A -> option B): option B :=
    match oa with
    | Some a => f a
    | None => None
    end.
  Infix ">>=" := bind (at level 0).

  Fixpoint bindVec {A n} (v: @Vec (option A) n): option (@Vec A n) :=
    match v with
    | Vec0 oa => oa >>= (fun a => Some (Vec0 a))
    | VecNext _ v1 v2 =>
      (bindVec v1) >>= (fun bv1 => (bindVec v2) >>= (fun bv2 => Some (VecNext bv1 bv2)))
    end.

  Fixpoint bindVector {A n} (v: Vector.t (option A) n): option (Vector.t A n) :=
    match v with
    | Vector.nil => Some (Vector.nil _)
    | Vector.cons a n vs =>
      a >>= (fun bv1 => (bindVector vs) >>= (fun bv2 => Some (Vector.cons _ bv1 _ bv2)))
    end.

  Fixpoint bindList n attrs (il: @ilist _ (fun _ : Attribute Kind => option BExpr) n attrs):
    option (ilist (fun _ : Attribute Kind => BExpr) attrs) :=
    match il with
    | inil => Some (inil _)
    | icons a n ats (Some e) t =>
      (bindList t) >>= (fun bl => Some (icons a e bl))
    | _ => None
    end.

  Fixpoint exprSToBExpr {k} (e: ExprS k) {struct e}: option BExpr :=
    match e with
    | Var vk i =>
      (match vk return (fullType tyS vk -> option BExpr) with
       | SyntaxKind sk => fun f => Some (BVar f)
       | NativeKind _ _ => fun _ => None
       end) i
    | Const k c => Some (BConst c)
    | UniBool op se => (@exprSToBExpr _ se) >>= (fun be => Some (BUniBool op be))
    | BinBool op e1 e2 =>
      (@exprSToBExpr _ e1)
        >>= (fun be1 => (@exprSToBExpr _ e2) >>= (fun be2 => Some (BBinBool op be1 be2)))
    | UniBit n1 n2 op e => (@exprSToBExpr _ e) >>= (fun be => Some (BUniBit op be))
    | BinBit n1 n2 n3 op e1 e2 =>
      (@exprSToBExpr _ e1) >>= (fun be1 => (@exprSToBExpr _ e2)
                                             >>= (fun be2 => Some (BBinBit op be1 be2)))
    | BinBitBool n1 n2 op e1 e2 =>
      (@exprSToBExpr _ e1) >>= (fun be1 => (@exprSToBExpr _ e2)
                                             >>= (fun be2 => Some (BBinBitBool op be1 be2)))
    | ITE _ ce te fe =>
      (@exprSToBExpr _ ce)
        >>= (fun bce =>
               (@exprSToBExpr _ te)
                 >>= (fun bte => 
                        (@exprSToBExpr _ fe)
                          >>= (fun bfe => Some (BITE bce bte bfe))))
    | Eq _ e1 e2 =>
      (@exprSToBExpr _ e1) >>= (fun be1 => (@exprSToBExpr _ e2) >>= (fun be2 => Some (BEq be1 be2)))
    | ReadIndex _ _ ie ve =>
      (@exprSToBExpr _ ie) >>= (fun bie => (@exprSToBExpr _ ve)
                                             >>= (fun bve => Some (BReadIndex bie bve)))
    | ReadField _ ls i e => (@exprSToBExpr _ e) >>= (fun be => Some (BReadField (Vector.nth (Vector.map (@attrName _) ls) i) be))
    | BuildVector _ lgn v =>
      (bindVec (mapVec (@exprSToBExpr _) v)) >>= (fun bv => Some (BBuildVector bv))
    | UpdateVector _ _ ve ie ke =>
      (@exprSToBExpr _ ve)
        >>= (fun bve =>
               (@exprSToBExpr _ ie)
                 >>= (fun bie => 
                        (@exprSToBExpr _ ke)
                          >>= (fun bke => Some (BUpdateVector bve bie bke))))
    | BuildStruct n attrs st =>
      ((fix help n attrs st: option (list (Attribute BExpr)) :=
          match st in ilist _ attrs1 return option (list (Attribute BExpr)) with
          | inil => Some nil
          | icons k na vs h t =>
            match @exprSToBExpr _ h with
            | Some v => (@help _ vs t) >>= (fun bl => Some (cons (attrName k :: v)%struct bl))
            | None => None
            end
          end) n attrs st) >>= (fun bl => Some (BBuildStruct attrs bl))
    | ReadArrayIndex _ _ _ ie ve =>
      (@exprSToBExpr _ ie) >>= (fun bie => (@exprSToBExpr _ ve)
                                             >>= (fun bve =>
                                                    Some (BReadArrayIndex bie bve)))
    | BuildArray _ n v =>
      (bindVector (Vector.map (@exprSToBExpr _) v)) >>= (fun bv => Some (BBuildArray bv))
    | UpdateArray _ _ _ ve ie ke =>
      (@exprSToBExpr _ ve)
        >>= (fun bve =>
               (@exprSToBExpr _ ie)
                 >>= (fun bie => 
                        (@exprSToBExpr _ ke)
                          >>= (fun bke => Some (BUpdateArray bve bie bke))))
      
    end.

  Fixpoint actionSToBAction {k} (e: ActionS k): option (list BAction) :=
    match e with
    | MCallS name msig arge idx cont =>
      (actionSToBAction cont)
        >>= (fun bc =>
               (exprSToBExpr arge)
                 >>= (fun be => Some (BMCall idx name msig be :: bc)))
    | LetS_ (SyntaxKind k) e idx cont =>
      (actionSToBAction cont)
        >>= (fun bc =>
               (exprSToBExpr e)
                 >>= (fun be => Some (BLet idx (Some k) be :: bc)))
    | LetS_ (NativeKind _ _) _ _ _ => None
    (* Currently nondeterministic reads are not allowed to be synthesized. *)
    | ReadNondetS _ _ => None 
    | ReadRegS reg idx cont =>
      (actionSToBAction cont)
        >>= (fun bc => Some (BLet idx None (BReadReg reg) :: bc))
    | WriteRegS reg _ e cont =>
      (actionSToBAction cont)
        >>= (fun bc =>
               (exprSToBExpr e)
                 >>= (fun be => Some (BWriteReg reg be :: bc)))
    | IfElseS ce iretK ta fa idx cont =>
      (actionSToBAction cont)
        >>= (fun bc =>
               (exprSToBExpr ce)
                 >>= (fun bce =>
                        (actionSToBAction ta)
                          >>= (fun bta =>
                                 (actionSToBAction fa)
                                   >>= (fun bfa => Some (BIfElse bce idx iretK bta bfa :: bc)))))
    | AssertS_ e cont =>
      (actionSToBAction cont)
        >>= (fun bc => (exprSToBExpr e) >>= (fun be => Some (BAssert be :: bc)))
    | ReturnS e => (exprSToBExpr e) >>= (fun be => Some (BReturn be :: nil))
    end.

  Fixpoint rulesToBRules (rules: list (Attribute (ActionS Void))) :=
    match rules with
    | nil => Some nil
    | {| attrName := rn; attrType := rb |} :: rs =>
      (rulesToBRules rs)
        >>= (fun brs =>
               (actionSToBAction rb)
                 >>= (fun brb => Some ({| attrName := rn; attrType := brb |} :: brs)))
    end.

  Fixpoint methsToBMethods (meths: list DefMethTS): option (list BMethod) :=
    match meths with
    | nil => Some nil
    | {| attrName := mn; attrType := existT sig mb |} :: ms =>
      (methsToBMethods ms)
        >>= (fun bms =>
               (actionSToBAction mb)
                 >>= (fun bmb => Some ({| attrName := mn; attrType := (sig, bmb) |} :: bms)))
    end.

  Fixpoint ModulesSToBModules (m: ModulesS): option (list BModule) :=
    match m with
    | PrimModS pname ifc => Some (BModulePrim pname ifc :: nil)
    | ModS regs rules dms =>
      (rulesToBRules rules)
        >>= (fun brules =>
               (methsToBMethods dms)
                 >>= (fun bdms => Some (BModuleB regs brules bdms :: nil)))
    | ConcatModsS m1 m2 =>
      (ModulesSToBModules m1)
        >>= (fun bm1 =>
               (ModulesSToBModules m2)
                 >>= (fun bm2 => Some (bm1 ++ bm2)))
    end.

End BluespecSubset.

