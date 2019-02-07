Require Import Kami.Syntax Kami.Notations String.
Require Import Names.

Definition MemOp := Bool.

Section FieldDefns.
  Local Open Scope string.
  Definition op := "op".
  Definition byteEn := "byteEn".
  Definition data := "data".
  Definition id := "id".
  Definition isRq := "isRq".
  Definition line := "line".
  Definition from := "from".
  Definition to := "to".
  Definition isVol := "isVol".
  Definition child := "child".
  Definition rq := "rq".
  Definition rs := "rs".
  Definition msg := "msg".
  Close Scope string.
End FieldDefns.

Section MsgTypes.
  Variables DataBytes LgNumDatas LgNumChildren: nat.
  Variable Addr Id: Kind.
  Definition Child := Bit LgNumChildren.
  Definition BitsPerByte := 8.
  Definition Data := Bit (DataBytes * BitsPerByte).
  Definition Line := Vector Data LgNumDatas.

  Definition RqFromProc := STRUCT {
                               addr :: Addr;
                               op :: MemOp;
                               (* byteEn :: Vector Bool DataBytes; *)
                               data :: Data
                               (* id :: Id *)
                             }.

  Definition RsToProc := STRUCT {
                             data :: Data
                             (* id :: Id *)
                           }.

End MsgTypes.

Definition RqState := Bit 3.
Definition Empty := 0.
Definition Init := 1.
Definition WaitOldTag := 2.
Definition WaitNewTag := 3.
Definition WaitSt := 4.
Definition Processing := 5.
Definition Depend := 6.
Definition Done := 7.

Hint Unfold MemOp Child Data Line : MethDefs.
Hint Unfold RqFromProc RsToProc : MethDefs.
Hint Unfold RqState Empty Init WaitOldTag WaitNewTag WaitSt
     Processing Depend Done : MethDefs.

