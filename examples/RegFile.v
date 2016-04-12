Require Import Lts.Syntax Lts.Semantics String Lib.Struct.

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
  
  Definition RegFile :=
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
