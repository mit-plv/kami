Require Import List String.
Require Import Ext.BSyntax.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(** Extraction steps:
 * 1) Define the target module.
 * 2) Change the definition "targetM" to your module.
 * 3) Compile.
 *)
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Synthesize Ex.Isa Ex.MemCache.

Definition l1Con := ((modFromMeta (l1Cache 2 2 2 2 (Bit 1) 1))
                       ++ ((modFromMeta (l1cs 2 1))
                             ++ (modFromMeta (l1tag 2 2 1))
                             ++ (modFromMeta (l1line 2 2 2 1)))
                       ++ ((modFromMeta (fifoRqToP 2 2 (Bit 1) 2 1))
                             ++ (modFromMeta (fifoRsToP 2 2 2 2 2 1))
                             ++ (modFromMeta (fifoFromP 2 2 2 2 (Bit 1) 2 1))))%kami.

Definition memDirCCon := ((modFromMeta (memDir 2 2 2 2 (Bit 1) 1))
                            ++ (modFromMeta (mline 2 2 2 2))
                            ++ (modFromMeta (mdir 2 2 1)))%kami.

Definition childParentCCon := ((modFromMeta (childParent 2 2 2 2 (Bit 1) 1))
                                 ++ (modFromMeta (fifoRqFromC 2 2 (Bit 1) 2 1))
                                 ++ (modFromMeta (fifoRsFromC 2 2 2 2 2 1))
                                 ++ (modFromMeta (fifoToC 2 2 2 2 (Bit 1) 2 1)))%kami.


(** DON'T REMOVE BELOW LINES *)
Definition targetM := (l1Con ++ childParentCCon ++ memDirCCon)%kami.
Definition targetS := getModuleS targetM.
Definition targetB := ModulesSToBModules targetS.

(* Extraction "./Ocaml/Target.ml" targetB. *)

