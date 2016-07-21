Require Import List String.
Require Import Ext.BSyntax.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extraction "BModules.ml" BModules.

(* Require Import Isa MemDir. *)

(* Definition exInsts: ConstT (Vector (MemTypes.Data rv32iLgDataBytes) rv32iAddrSize) := *)
(*   getDefaultConst _. *)

(* Definition testM := modFromMeta (memDir 2 2 2 2 (Bit 1)). *)
(* Definition testS := getModuleS testM. *)
(* Definition testB := ModulesSToBModules testS. *)

(* Extraction "ExtractionTest.ml" testB. *)
