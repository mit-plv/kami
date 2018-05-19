Require Import List.
Require Import Notations.
Require Import Lib.Word.
Require Import Kami.Ex.Timing.Specification Kami.Ex.Timing.AbstractTaint.
Require Import Kami.Ex.IsaRv32.
Require Import Kami.Syntax.
Require Import Logic.FunctionalExtensionality.

(* A very silly "encryption" algorithm.  We read in the "key", and
then read in words of plaintext which we "encrypt" with the key and
send back out. *)
Definition sampleCode :=
  [
    FROMHOST x1;
      FROMHOST x2;
      ADD x1 x2 x2;
      TOHOST x2;
      J (^~ $(6)) (* jump back 3 instructions *)
  ].

Definition initrf : regfile := (fun _ => $0).
Definition pm : progMem := fun a => rv32iToRaw (nth (wordToNat a) sampleCode NOP).
Definition initpc : address := $0.
Definition initmem : memory := (fun _ => $0).

Theorem safe : abstractHiding initrf pm initpc initmem.
  replace initrf with (mask (sz := 5) (fun _ => None) (fun _ => $0)) by (extensionality a; reflexivity).
  replace initmem with (mask (sz := 16) (fun _ => None) (fun _ => $0)) by (extensionality a; reflexivity).
  apply abstractHiding_tainted_normal.
  apply (segmentSafeHiding 1 _ _ _ _ (fun _ => None) $4 (fun _ => None)).
  - reflexivity.
  - apply (loopSafeHiding 4). (* we don't actually need to skimp on fuel, any larger number also works *)
    reflexivity.
Qed.