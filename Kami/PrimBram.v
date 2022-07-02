Require Import Arith.Peano_dec Bool String List.
Require Import Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.

Import ListNotations.

Set Implicit Arguments.

Definition isSomeB {A} (a: option A) :=
  match a with
  | Some _ => true
  | None => false
  end.

Definition isNoneB {A} (a: option A) :=
  match a with
  | Some _ => false
  | None => true
  end.

Definition optionVal {ty dType} (ov: option (ty dType)):
  Expr ty (SyntaxKind dType) :=
  match ov with
  | Some v => (#v)%kami_expr
  | None => ($$Default)%kami_expr
  end.

Definition liftSome {A} (a: A): option A :=
  Some a.

Definition primBramName: string := "BRAM".

Section PrimBram.
  Variables (bramName: string)
            (addrSize: nat)
            (dType: Kind).

  Local Notation "^ s" := (bramName -- s) (at level 0).

  Definition bramReadValT (ty: Kind -> Type) := option (ty dType).
  Definition bramReadValK ty := @NativeKind (bramReadValT ty) None.
  Definition bramReadVal ty :=
    (^"rss" :: (@NativeConst (bramReadValT ty) None None))%struct.

  Definition BramRq :=
    STRUCT {
        "write" :: Bool;
        "addr" :: Bit addrSize;
        "datain" :: dType
      }.
  
  Definition bramPutRq: forall ty (rq: ty (Struct BramRq)), ActionT ty Void :=
    fun ty rq =>
      (Read bram <- ^"bram";
       If #rq!BramRq@."write" then
         LET writev <- #rq!BramRq@."datain";
         Write ^"bram" <- #bram@[#rq!BramRq@."addr" <- #writev];
         Retv
       else
         ReadN readVal: bramReadValK ty <- ^"readVal";
         Assert $$(isNoneB readVal);
         LET readv: dType <- #bram@[#rq!BramRq@."addr"];
         Write ^"readVal" <- Var _ (bramReadValK ty) (liftSome readv);
         Retv;
       Retv)%kami_action.

  Definition bramGetRs: forall ty (_: ty Void), ActionT ty dType :=
    fun ty _ =>
      (ReadN readVal: bramReadValK ty <- ^"readVal";
       Assert $$(isSomeB readVal);
       Write ^"readVal" <- (Var _ (bramReadValK ty) None);
       Ret (optionVal readVal)%kami_action)%kami_action.
  
  Definition bram1: Modules :=
    PrimMod
      {| pm_name := primBramName;
         pm_regInits :=
           [(^"bram" :: (RegInitDefault (SyntaxKind (Vector dType addrSize))))%struct;
              (^"readVal" :: (RegInitCustom (existT ConstFullT (bramReadValK type)
                                                    (NativeConst None None))))%struct];
         pm_rules := nil;
         pm_methods :=
           [(^"putRq" :: (existT _ {| arg:= _; ret:= _ |} bramPutRq))%struct;
              (^"getRs" :: (existT _ {| arg:= _; ret:= _ |} bramGetRs))%struct]
      |}.

End PrimBram.

#[global] Hint Unfold bram1 : ModuleDefs.
#[global] Hint Unfold primBramName
     bramReadValT bramReadValK bramReadVal
     BramRq bramPutRq bramGetRs: MethDefs.

Section Facts.
  Variables (bramName: string)
            (addrSize: nat)
            (dType: Kind).

  Lemma bram1_ModEquiv:
    ModPhoasWf (bram1 bramName addrSize dType).
  Proof.
    kequiv.
  Qed.
  #[local] Hint Resolve bram1_ModEquiv.

  Lemma bram1_ValidRegs:
    ModRegsWf (bram1 bramName addrSize dType).
  Proof.
    kvr.
  Qed.
  #[local] Hint Resolve bram1_ValidRegs.

End Facts.

#[global] Hint Resolve bram1_ModEquiv.
#[global] Hint Resolve bram1_ValidRegs.

