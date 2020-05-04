Require Import Kami.

Require Export Kami.Synthesize.
Require Export Ext.BSyntax.
Require Export ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(*! [targetM] should be the module to extract. *)
(* Definition targetM: Modules := .. *)
(* Definition targetS := getModuleS targetM. *)
(* Definition targetB := ModulesSToBModules targetS. *)

(* If you are testing directly on this file with ProofGeneral or CoqIde, 
 * then use the below extraction command, instead of the one at the last line.
 *)
(* Extraction "./Ocaml/Target.ml" targetB. *)

(* [Target.ml] will be generated after executing the below extraction command.
 * To generate the corresponding Bluespec program, do [make] in the directory
 * [./extraction/Ocaml/]. See [./extraction/Ocaml/README.md] for details.
 *)
(* Extraction "./Kami/Ext/Ocaml/Target.ml" targetB. *)

