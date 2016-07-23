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
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Synthesize Ex.Isa.

(** memCache test *)
Require Import Ex.MemCache.

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

Definition memCache := (l1Con ++ childParentCCon ++ memDirCCon)%kami.

(* Require Import ProcMemCorrect. *)

(* Definition insts : ConstT (Vector (MemTypes.Data rv32iLgDataBytes) *)
(*                                   rv32iAddrSize) := getDefaultConst _. *)

(* (** procDec + memCache test *) *)
(* Definition pdecN := pdecN 1 1 0 *)
(*                           (rv32iDecode insts) rv32iExecState rv32iExecNextPc *)
(*                           rv32iLd rv32iSt rv32iHt 1. *)
(* Definition pmFifos := pmFifos 1 1 0 2 1. *)
(* Definition mcache := mcache 2 1 1 0 2 (Bit 1) 1. *)

(* Definition procMemCache := (pdecN ++ pmFifos ++ modFromMeta mcache)%kami. *)

(** DON'T REMOVE BELOW LINES *)
Definition targetM := memCache.
Definition targetS := getModuleS targetM.
Definition targetB := ModulesSToBModules targetS.

(* Extraction "./Ocaml/Target.ml" targetB. *)

