Require Import Arith.Peano_dec Bool String List.
Require Import Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.
Require Import Kami.PrimFifo.

Set Implicit Arguments.

Definition primBramName: string := "BRAM".

Section PrimBram.
  Variables (bramName: string)
            (outFIFODepth: nat)
            (addrSize: nat)
            (dType: Kind).

  Local Notation "^ s" := (bramName -- s) (at level 0).

  Definition bramRssT ty := list (ty dType).
  Definition bramRssK ty := @NativeKind (bramRssT ty) nil.
  Definition bramRss ty :=
    (^"rss" :: (@NativeConst (bramRssT ty) nil nil))%struct.

  Definition BramRq :=
    STRUCT {
        "write" :: Bool;
        "addr" :: Bit addrSize;
        "datain" :: dType
      }.
  
  Definition bramPutRq: forall ty (rq: ty (Struct BramRq)), ActionT ty Void :=
    fun ty rq =>
      (Read bram <- ^"bram";
       ReadN rss: bramRssK ty <- ^"rss";
       Assert !$$(listIsFull outFIFODepth rss);
       If #rq!BramRq@."write" then
         LET writev <- #rq!BramRq@."datain";
         Write ^"bram" <- #bram@[#rq!BramRq@."addr" <- #writev];
         Write ^"rss" <- (Var _ (bramRssK ty) (listEnq writev rss));
         Retv
       else
         LET readv <- #bram@[#rq!BramRq@."addr"];
         Write ^"rss" <- (Var _ (bramRssK ty) (listEnq readv rss));
         Retv;
       Retv)%kami_action.

  Definition bramGetRs: forall ty (_: ty Void), ActionT ty dType :=
    fun ty _ =>
      (ReadN rss: bramRssK ty <- ^"rss";
       Assert !$$(listIsEmpty rss);
       Write ^"rss" <- (Var _ (bramRssK ty) (listDeq rss));
       Ret (listFirstElt rss))%kami_action.
  
  Definition bram1: Modules :=
    PrimMod
      {| pm_name := primBramName;
         pm_regInits :=
           [(^"bram" :: (RegInitDefault (SyntaxKind (Vector dType addrSize))))%struct;
              (^"rss" :: (RegInitCustom (existT ConstFullT (bramRssK type)
                                                (NativeConst nil nil))))%struct];
         pm_rules := nil;
         pm_methods :=
           [(^"putRq" :: (existT _ {| arg:= _; ret:= _ |} bramPutRq))%struct;
              (^"getRs" :: (existT _ {| arg:= _; ret:= _ |} bramGetRs))%struct]
      |}.

End PrimBram.

Hint Unfold bram1 : ModuleDefs.
Hint Unfold primBramName
     bramRssT bramRssK bramRss
     BramRq bramPutRq bramGetRs: MethDefs.

Section Facts.
  Variables (bramName: string)
            (outFIFODepth: nat)
            (addrSize: nat)
            (dType: Kind).

  Lemma bram1_ModEquiv:
    ModPhoasWf (bram1 bramName outFIFODepth addrSize dType).
  Proof.
    kequiv.
  Qed.
  Hint Resolve bram1_ModEquiv.

  Lemma bram1_ValidRegs:
    ModRegsWf (bram1 bramName outFIFODepth addrSize dType).
  Proof.
    kvr.
  Qed.
  Hint Resolve bram1_ValidRegs.

End Facts.

Hint Resolve bram1_ModEquiv.
Hint Resolve bram1_ValidRegs.

