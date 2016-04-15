Require Import Lts.Syntax.

Set Implicit Arguments.

Definition Msi := Bit 2.
Definition Mod := 3.
Definition Sh := 1.
Definition Inv := 0.

Section HelperFunctions.
  Variable var: Kind -> Type.

  Definition toCompat (x: (Msi @ var)%kami): (Msi @ var)%kami :=
    (IF (x == $ Mod)
     then $ Inv
     else (IF (x == $ Sh)
           then $ Sh
           else $ Mod))%kami.

  Definition isCompat (x y: (Msi @ var)%kami) := (x <= toCompat y)%kami.
End HelperFunctions.



