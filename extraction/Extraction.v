Require Import List String.
Require Import Ext.BSyntax.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extraction "BModules.ml" BModules.

(* Require Import Lts.Syntax Lts.ParametricSyntax Lts.Synthesize Ex.Isa Ex.MemCache. *)

(* Definition memDirCC := ((modFromMeta (memDir 2 2 2 2 (Bit 1) 1)) *)
(*                           ++ (modFromMeta (mline 2 2 2 2)) *)
(*                           ++ (modFromMeta (mdir 2 2 1)))%kami. *)

(* Definition testM := memDirCC. *)
(* Definition testS := getModuleS testM. *)
(* Definition testB := ModulesSToBModules testS. *)

(* Extraction "ExtractionTest.ml" testB. *)
