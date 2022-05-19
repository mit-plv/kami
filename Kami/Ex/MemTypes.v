Require Import Kami.Syntax Kami.Notations String.
Require Import Names.

Definition MemOp := Bool.

Section MsgTypes.
  Variables DataBytes LgNumDatas LgNumChildren: nat.
  Variable Addr Id: Kind.
  Definition Child := Bit LgNumChildren.
  Definition BitsPerByte := 8.
  Definition Data := Bit (DataBytes * BitsPerByte).
  Definition Line := Vector Data LgNumDatas.

  Definition RqFromProc :=
    STRUCT { "addr" :: Addr;
             "op" :: MemOp;
             "byteEn" :: Array Bool DataBytes;
             "data" :: Data
           }.

  Definition RsToProc :=
    STRUCT { "data" :: Data }.

End MsgTypes.

#[global] Hint Unfold MemOp Child Data Line : MethDefs.
#[global] Hint Unfold RqFromProc RsToProc : MethDefs.

