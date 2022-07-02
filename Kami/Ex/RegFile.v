Require Import String Lib.CommonTactics Lib.Indexer Lib.StringAsList.
Require Import Kami.Syntax Kami.Notations Kami.Semantics.
Require Import Kami.Wf Kami.Tactics.

Set Implicit Arguments.

Section RegFile.
  Variable name: string.
  Variable IdxBits: nat.
  Variable Data: Kind.

  Definition DataArray := Vector Data IdxBits.
  Definition Addr := Bit IdxBits.

  Definition WritePort :=
    STRUCT {
        "addr" :: Addr;
        "data" :: Data
      }.
  Notation "^ s" := (name -- s) (at level 0).

  Variable init: ConstT DataArray.

  Definition regFile :=
    MODULE {
        Register ^"dataArray": DataArray <- init
                                       
        with Method ^"read" (a: Addr): Data :=
          Read full: DataArray <- ^"dataArray";
        Ret (#full@[#a])
            
        with Method ^"write" (w: Struct WritePort): Void :=
          Read full: DataArray <- ^"dataArray";
        Write ^"dataArray" <- #full@[ #w!WritePort@."addr" <- #w!WritePort@."data" ];
        Retv
      }.

End RegFile.

#[global] Hint Unfold DataArray Addr WritePort : MethDefs.
#[global] Hint Unfold regFile : ModuleDefs.

Section Facts.
  Variable name: string.
  Variable IdxBits: nat.
  Variable Data: Kind.
  Variable init: ConstT (DataArray IdxBits Data).

  Lemma regFile_ModEquiv:
    ModPhoasWf (regFile name init).
  Proof.
    kequiv.
  Qed.

  Lemma regFile_ValidRegs:
    ModRegsWf (regFile name init).
  Proof.
    kvr.
  Qed.

End Facts.

#[global] Hint Resolve regFile_ModEquiv.
#[global] Hint Resolve regFile_ValidRegs.

