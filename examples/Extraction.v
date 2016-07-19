Require Import String List.
Require Import Lib.ilist Lib.Struct Lib.Indexer Lib.StringBound.
Require Import Lts.Syntax Lts.Synthesize Lts.ParametricSyntax.
Require Import Ex.Fifo Ex.Isa.
(* Require Import Ex.ProcMemCorrect. *)

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(* Definition exInsts: ConstT (Vector (MemTypes.Data rv32iLgDataBytes) rv32iAddrSize) := *)
(*   getDefaultConst _. *)

(* Definition exIdxBits := 20. *)
(* Definition exTagBits := 10. *)
(* Definition exLgNumDatas := 2. *)
(* Definition exLgNumChildren := 2. *)
(* Definition exFifoSize := 4. *)

(* Definition exProcMem := ((pdecN exIdxBits exTagBits exLgNumDatas *)
(*                                 (rv32iDecode exInsts) rv32iExecState rv32iExecNextPc *)
(*                                 rv32iLd rv32iSt rv32iHt exLgNumChildren) *)
(*                            ++ (pmFifos exIdxBits exTagBits exLgNumDatas *)
(*                                        rv32iLgDataBytes exLgNumChildren) *)
(*                            ++ (modFromMeta (mcache exFifoSize exIdxBits exTagBits *)
(*                                                    exLgNumDatas rv32iLgDataBytes *)
(*                                                    Void exLgNumChildren)) *)
(*                         )%kami. *)

(* Definition exProcMemS := (getModuleS exProcMem). *)

(* Extraction "ExtractionResult.ml" exProcMemS. *)

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
  | BBuildStruct:
      forall attrs,
        ilist.ilist (fun _:Attribute Kind => BExpr) attrs -> BExpr
  (* if we use list instead of "ilist" in BExpr,
   * then Coq cannot find the decreasing factor while converting ExprS to BExpr
   *)
  (* | BBuildStruct: list (Attribute BExpr) -> BExpr *)
  | BUpdateVector: BExpr -> BExpr -> BExpr -> BExpr
  | BReadReg: string -> BExpr.

  Inductive BAction: Type :=
  | BMCall: nat (* binder *) -> string (* meth *) -> SignatureT -> BExpr -> BAction
  | BLet: nat (* binder *) -> option Kind (* type annotation, if possible *) ->
          BExpr -> BAction
  | BWriteReg: string -> BExpr -> BAction
  | BIfElse: BExpr -> list BAction -> list BAction -> BAction
  | BAssert: BExpr -> BAction
  | BReturn: BExpr -> BAction.

  Definition BRule := Attribute (list BAction).
  Definition BMethod := Attribute (SignatureT * list BAction).

  Record BModule := { bregs : list RegInitT;
                      brules : list BRule;
                      bdms : list BMethod }.

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

  (* Fixpoint bindList {A} (l: list (Attribute (option A))): option (list (Attribute A)) := *)
  (*   match l with *)
  (*   | nil => Some nil *)
  (*   | {| attrName:= an; attrType:= Some ab |} :: t => *)
  (*     (bindList t) >>= (fun bl => Some ({| attrName:= an; attrType:= ab |} :: bl)) *)
  (*   | _ => None *)
  (*   end. *)

  Fixpoint bindList attrs (il: ilist (fun _ : Attribute Kind => option BExpr) attrs):
    option (ilist (fun _ : Attribute Kind => BExpr) attrs) :=
    match il with
    | inil => Some (inil _)
    | icons a ats (Some e) t =>
      (bindList ats t) >>= (fun bl => Some (icons a e bl))
    | _ => None
    end.
  
  Fixpoint exprSToBExpr {k} (e: ExprS k): option BExpr :=
    match e with
    | Var vk i =>
      (match vk return (fullType tyS vk -> option BExpr) with
       | SyntaxKind sk => fun f => Some (BVar f)
       | NativeKind _ _ => fun _ => None
       end) i
    | Const k c => Some (BConst k c)
    | UniBool op se => (exprSToBExpr se) >>= (fun be => Some (BUniBool op be))
    | BinBool op e1 e2 =>
      (exprSToBExpr e1)
        >>= (fun be1 => (exprSToBExpr e2) >>= (fun be2 => Some (BBinBool op be1 be2)))
    | UniBit n1 n2 op e => (exprSToBExpr e) >>= (fun be => Some (BUniBit n1 n2 op be))
    | BinBit n1 n2 n3 op e1 e2 =>
      (exprSToBExpr e1) >>= (fun be1 => (exprSToBExpr e2)
                                          >>= (fun be2 => Some (BBinBit n1 n2 n3 op be1 be2)))
    | BinBitBool n1 n2 op e1 e2 =>
      (exprSToBExpr e1) >>= (fun be1 => (exprSToBExpr e2)
                                          >>= (fun be2 => Some (BBinBitBool n1 n2 op be1 be2)))
    | ITE _ ce te fe =>
      (exprSToBExpr ce)
        >>= (fun bce =>
               (exprSToBExpr te)
                 >>= (fun bte => 
                        (exprSToBExpr fe)
                          >>= (fun bfe => Some (BITE bce bte bfe))))
    | Eq _ e1 e2 =>
      (exprSToBExpr e1) >>= (fun be1 => (exprSToBExpr e2) >>= (fun be2 => Some (BEq be1 be2)))
    | ReadIndex _ _ ie ve =>
      (exprSToBExpr ie) >>= (fun bie => (exprSToBExpr ve)
                                          >>= (fun bve => Some (BReadIndex bie bve)))
    | ReadField _ s e => (exprSToBExpr e) >>= (fun be => Some (BReadField (bindex s) be))
    | BuildVector _ lgn v =>
      (bindVec (mapVec (exprSToBExpr) v)) >>= (fun bv => Some (BBuildVector lgn bv))
    | UpdateVector _ _ ve ie ke =>
      (exprSToBExpr ve)
        >>= (fun bve =>
               (exprSToBExpr ie)
                 >>= (fun bie => 
                        (exprSToBExpr ke)
                          >>= (fun bke => Some (BUpdateVector bve bie bke))))
    | BuildStruct attrs st =>
      (bindList attrs (ilist.imap _ (fun a (e: Expr tyS (SyntaxKind (attrType a)))
                                     => exprSToBExpr e) st))
        >>= (fun bl => Some (BBuildStruct attrs bl))
        (* cannot find the decreasing factor because of "ilist.map_ilist" *)
        (* (bindList (ilist.map_ilist (fun a (e: Expr tyS (SyntaxKind (attrType a))) *)
        (*                             => {| attrName:= attrName a; *)
        (*                                   attrType:= exprSToBExpr e |}) st)) *)
        (*   >>= (fun bl => Some (BBuildStruct bl)) *)
    end.

  Fixpoint actionSToBAction {k} (e: ActionS k): option (list BAction) :=
    match e with
    | MCallS name msig arge idx cont =>
      (* TODO: need to correct name like Bluespec-style *)
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
    | ReadRegS reg idx cont =>
      (actionSToBAction cont)
        >>= (fun bc => Some (BLet idx None (BReadReg reg) :: bc))
    | WriteRegS reg _ e cont =>
      (actionSToBAction cont)
        >>= (fun bc =>
               (exprSToBExpr e)
                 >>= (fun be => Some (BWriteReg reg be :: bc)))
    | IfElseS ce _ ta fa idx cont =>
      (actionSToBAction cont)
        >>= (fun bc =>
               (exprSToBExpr ce)
                 >>= (fun bce =>
                        (actionSToBAction ta)
                          >>= (fun bta =>
                                 (actionSToBAction fa)
                                   >>= (fun bfa => Some (BIfElse bce bta bfa :: bc)))))
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

  Fixpoint ModulesSToBModules (m: ModulesS) :=
    match m with
    | ModS regs rules dms =>
      (rulesToBRules rules)
        >>= (fun brules =>
               (methsToBMethods dms)
                 >>= (fun bdms => Some ((Build_BModule regs brules bdms) :: nil)))
    | ConcatModsS m1 m2 =>
      (ModulesSToBModules m1)
        >>= (fun bm1 =>
               (ModulesSToBModules m2)
                 >>= (fun bm2 => Some (bm1 ++ bm2)))
    end.

End BluespecSubset.

(* Extraction "BModules.ml" BModules. *)

(* Require Import Fifo. *)

(* Definition testFifo := fifo "fifo" 4 (Bit 2). *)
(* Definition testFifoS := getModuleS testFifo. *)
(* Definition testFifoB := ModulesSToBModules testFifoS. *)

(* Eval compute in testFifo. *)
(* Eval compute in testFifoS. *)
(* Eval compute in testFifoB. *)

(* Extraction "ExtractionTest.ml" testFifoB. *)

Require Import Isa ProcDec.

Definition exInsts: ConstT (Vector (MemTypes.Data rv32iLgDataBytes) rv32iAddrSize) :=
  getDefaultConst _.

Definition testProcDecM := pdec (rv32iDecode exInsts) rv32iExecState rv32iExecNextPc
                                rv32iLd rv32iSt rv32iHt.
Definition testProcDecMS := getModuleS testProcDecM.
Definition testProcDecMB := ModulesSToBModules testProcDecMS.

Extraction "ExtractionTest2.ml" testProcDecMB.

