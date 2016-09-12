Require Import Kami.Syntax Kami.Notations.

Set Implicit Arguments.

Definition Msi := Bit 2.
Definition Mod := 3.
Definition Sh := 1.
Definition Inv := 0.

Section HelperFunctions.
  Variable var: Kind -> Type.

  Definition toCompat (x: Msi @ var): Msi @ var :=
    (IF (x == $ Mod)
     then $ Inv
     else (IF (x == $ Sh)
           then $ Sh
           else $ Mod))%kami_expr.

  Definition isCompat (x y: Msi @ var) := (x <= toCompat y)%kami_expr.
End HelperFunctions.

Hint Unfold Msi Mod Sh Inv : MethDefs.
Hint Unfold toCompat isCompat : MethDefs.

