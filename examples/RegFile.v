Require Import String Lib.Struct.
Require Import Lts.Syntax Lts.Semantics Lts.Equiv Lts.Tactics.

Section RegFile.
  Variable name: string.
  Variable IdxBits: nat.
  Variable Data: Kind.

  Definition DataArray := Vector Data IdxBits.
  Definition Addr := Bit IdxBits.

  Definition WritePort := STRUCT {
                              "addr" :: Addr;
                              "data" :: Data
                            }.
  Notation "^ s" := (name -n- s) (at level 0).

  Variable init: ConstT DataArray.
  
  Definition regFile :=
    MODULE {
        Register ^"dataArray": DataArray <- init

        with Method ^"read" (a: Addr): Data :=
          Read full: DataArray <- ^"dataArray";
          Ret (#full@[#a])
            
        with Method ^"write" (w: WritePort): Void :=
          Read full: DataArray <- ^"dataArray";
          Write ^"dataArray" <- #full@[ #w@."addr" <- #w@."data" ];
          Retv
      }.
End RegFile.

Hint Unfold DataArray Addr WritePort : MethDefs.
Hint Unfold regFile : ModuleDefs.

Section Facts.
  Variable name: string.
  Variable IdxBits: nat.
  Variable Data: Kind.
  Variable init: ConstT (DataArray IdxBits Data).

  Lemma regFile_ModEquiv:
    ModEquiv type typeUT (regFile name _ _ init).
  Proof.
    kequiv.
  Qed.

End Facts.

Hint Immediate regFile_ModEquiv.

