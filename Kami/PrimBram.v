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

Definition primBramName1: string := "BRAM1".
Definition primBramName2: string := "BRAM2".

Section PrimBram.
  Variables (bramName: string)
            (addrSize: nat)
            (dType: Kind).

  Local Notation "^ s" := (bramName -- s) (at level 0).

  Definition bramReadAddrT (ty: Kind -> Type) := option (ty (Bit addrSize)).
  Definition bramReadAddrK ty := @NativeKind (bramReadAddrT ty) None.

  Definition BramRq :=
    STRUCT { "write" :: Bool;
             "addr" :: Bit addrSize;
             "datain" :: dType }.

  Definition bramPutReq: forall ty (rq: ty (Struct BramRq)), ActionT ty Void :=
    fun ty rq =>
      (If #rq!BramRq@."write"
       then (LET writev <- #rq!BramRq@."datain";
            Read bram <- ^"bram";
            Write ^"bram" <- #bram@[#rq!BramRq@."addr" <- #writev];
            Retv)
       else (ReadN readAddr: bramReadAddrK ty <- ^"readAddr";
            Assert $$(isNoneB readAddr);
            LET raddr <- #rq!BramRq@."addr";
            Write ^"readAddr" <- Var _ (bramReadAddrK ty) (liftSome raddr);
            Retv);
      Retv)%kami_action.

  Definition bramRdResp: forall ty (_: ty Void), ActionT ty dType :=
    fun ty _ =>
      (ReadN oreadAddr: bramReadAddrK ty <- ^"readAddr";
      Assert $$(isSomeB oreadAddr);
      Write ^"readAddr" <- (Var _ (bramReadAddrK ty) None);
      Read bram: Vector dType addrSize <- ^"bram";
      LET reada <- optionVal oreadAddr;
      LET readv: dType <- #bram@[#reada];
      Ret #readv)%kami_action.

  Definition bram1: Modules :=
    PrimMod
      {| pm_name := primBramName1;
         pm_args := ["addrSize" :: Bit addrSize; "dType" :: dType]%struct;
         pm_regInits :=
           [(^"bram" :: (RegInitDefault (SyntaxKind (Vector dType addrSize))))%struct;
           (^"readAddr" :: (RegInitCustom (existT ConstFullT (bramReadAddrK type)
                                                  (NativeConst None None))))%struct];
         pm_rules := nil;
         pm_methods :=
           [(^"putReq" :: (existT _ {| arg:= _; ret:= _ |} bramPutReq))%struct;
           (^"rdResp" :: (existT _ {| arg:= _; ret:= _ |} bramRdResp))%struct]
      |}.

  Definition bramRdReq: forall ty (addr: ty (Bit addrSize)), ActionT ty Void :=
    fun ty addr =>
      (ReadN readAddr: bramReadAddrK ty <- ^"readAddr";
      Assert $$(isNoneB readAddr);
      Write ^"readAddr" <- Var _ (bramReadAddrK ty) (liftSome addr);
      Retv)%kami_action.

  Definition BramWriteReq :=
    STRUCT { "addr" :: Bit addrSize; "datain" :: dType }.

  Definition bramWrReq: forall ty (rq: ty (Struct BramWriteReq)), ActionT ty Void :=
    fun ty rq =>
      (LET writev <- #rq!BramWriteReq@."datain";
      Read bram <- ^"bram";
      Write ^"bram" <- #bram@[#rq!BramWriteReq@."addr" <- #writev];
      Retv)%kami_action.

  Definition bram2: Modules :=
    PrimMod
      {| pm_name := primBramName1;
         pm_args := ["addrSize" :: Bit addrSize; "dType" :: dType]%struct;
         pm_regInits :=
           [(^"bram" :: (RegInitDefault (SyntaxKind (Vector dType addrSize))))%struct;
           (^"readAddr" :: (RegInitCustom (existT ConstFullT (bramReadAddrK type)
                                                  (NativeConst None None))))%struct];
         pm_rules := nil;
         pm_methods :=
           [(^"rdReq" :: (existT _ {| arg:= _; ret:= _ |} bramRdReq))%struct;
           (^"wrReq" :: (existT _ {| arg:= _; ret:= _ |} bramWrReq))%struct;
           (^"readRs" :: (existT _ {| arg:= _; ret:= _ |} bramRdResp))%struct]
      |}.

End PrimBram.

Hint Unfold bram1 bram2: ModuleDefs.
Hint Unfold primBramName1 primBramName2
     bramReadAddrT bramReadAddrK
     BramRq bramPutReq bramRdResp bramRdReq BramWriteReq bramWrReq: MethDefs.

Section Facts.
  Variables (bramName: string)
            (addrSize: nat)
            (dType: Kind).

  Lemma bram1_ModEquiv:
    ModPhoasWf (bram1 bramName addrSize dType).
  Proof.
    kequiv.
  Qed.
  Hint Resolve bram1_ModEquiv.

  Lemma bram1_ValidRegs:
    ModRegsWf (bram1 bramName addrSize dType).
  Proof.
    kvr.
  Qed.
  Hint Resolve bram1_ValidRegs.

  Lemma bram2_ModEquiv:
    ModPhoasWf (bram2 bramName addrSize dType).
  Proof.
    kequiv.
  Qed.
  Hint Resolve bram2_ModEquiv.

  Lemma bram2_ValidRegs:
    ModRegsWf (bram2 bramName addrSize dType).
  Proof.
    kvr.
  Qed.
  Hint Resolve bram2_ValidRegs.

End Facts.

Hint Resolve bram1_ModEquiv bram2_ModEquiv.
Hint Resolve bram1_ValidRegs bram2_ValidRegs.
