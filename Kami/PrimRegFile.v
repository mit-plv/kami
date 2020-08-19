Require Import Arith.Peano_dec Bool String List.
Require Import Lib.Word Lib.Indexer.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.

Import ListNotations.

Set Implicit Arguments.

Definition primRfName1: string := "RegFile1".

Section PrimRegFile.
  Variables (rfName: string)
            (addrSize: nat)
            (dType: Kind).

  Local Notation "^ s" := (rfName -- s) (at level 0).

  Definition RfUpd :=
    STRUCT { "addr" :: Bit addrSize; "datain" :: dType }.

  Definition rfSub: forall ty (addr: ty (Bit addrSize)), ActionT ty dType :=
    fun ty addr =>
      (Read rf <- ^"rf"; LET val <- #rf@[#addr]; Ret #val)%kami_action.

  Definition rfUpd: forall ty (rq: ty (Struct RfUpd)), ActionT ty Void :=
    fun ty rq =>
      (Read rf <- ^"rf";
      Write ^"rf" <- #rf@[#rq!RfUpd@."addr" <- #rq!RfUpd@."datain"];
      Retv)%kami_action.

  Definition rf1: Modules :=
    PrimMod
      {| pm_name := primRfName1;
         pm_args := ["addrSize" :: Bit addrSize; "dType" :: dType]%struct;
         pm_consts := nil;
         pm_regInits :=
           [(^"rf" :: (RegInitDefault (SyntaxKind (Vector dType addrSize))))%struct];
         pm_rules := nil;
         pm_methods :=
           [(^"sub" :: (existT _ {| arg:= _; ret:= _ |} rfSub))%struct;
           (^"upd" :: (existT _ {| arg:= _; ret:= _ |} rfUpd))%struct]
      |}.

End PrimRegFile.

Hint Unfold rf1: ModuleDefs.
Hint Unfold primRfName1 RfUpd rfSub rfUpd: MethDefs.

Section Facts.
  Variables (rfName: string)
            (addrSize: nat)
            (dType: Kind).

  Lemma rf1_ModEquiv:
    ModPhoasWf (rf1 rfName addrSize dType).
  Proof.
    kequiv.
  Qed.
  Hint Resolve rf1_ModEquiv.

  Lemma rf1_ValidRegs:
    ModRegsWf (rf1 rfName addrSize dType).
  Proof.
    kvr.
  Qed.
  Hint Resolve rf1_ValidRegs.

End Facts.

Hint Resolve rf1_ModEquiv.
Hint Resolve rf1_ValidRegs.
