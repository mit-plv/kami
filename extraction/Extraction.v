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
Require Import Kami.Syntax Kami.ParametricSyntax Kami.Synthesize Ex.Isa.

(** procDec + memCache test *)
Require Import Ex.ProcDecSCN Ex.MemCache Ex.ProcMemCorrect.

(* AddrSize = IdxBits + TagBits + LgNumDatas *)
Definition idxBits := 2.
Definition tagBits := 1.
Definition lgNumDatas := 1.
Definition lgNumChildren := 1. (* 2 cores *)
Definition lgDataBytes := idxBits + tagBits + lgNumDatas.
Definition fifoSize := 2.
Definition idK := Bit 1.

(* Temporary; just for experiment *)
Definition pdecAN := pdecAN fifoSize rv32iDecode rv32iExecState rv32iExecNextPc
                            rv32iOpLOAD rv32iOpSTORE rv32iOpTOHOST lgNumChildren.

Definition pdecN := pdecN idxBits tagBits lgNumDatas
                          rv32iDecode rv32iExecState rv32iExecNextPc
                          rv32iOpLOAD rv32iOpSTORE rv32iOpTOHOST lgNumChildren.
Definition pmFifos := pmFifos fifoSize idxBits tagBits lgNumDatas lgDataBytes lgNumChildren.

Definition l1Con := ((modFromMeta (l1Cache idxBits tagBits lgNumDatas lgDataBytes
                                           idK lgNumChildren))
                       ++ ((modFromMeta (l1cs idxBits lgNumChildren))
                             ++ (modFromMeta (l1tag idxBits tagBits lgNumChildren))
                             ++ (modFromMeta (l1line idxBits lgNumDatas lgDataBytes lgNumChildren)))
                       ++ ((modFromMeta (fifoRqToP idxBits tagBits idK fifoSize lgNumChildren))
                             ++ (modFromMeta (fifoRsToP idxBits tagBits lgNumDatas lgDataBytes
                                                        fifoSize lgNumChildren))
                             ++ (modFromMeta (fifoFromP idxBits tagBits lgNumDatas lgDataBytes
                                                        idK fifoSize lgNumChildren))))%kami.

Definition memDirCCon := ((modFromMeta (memDir idxBits tagBits lgNumDatas lgDataBytes
                                               idK lgNumChildren))
                            ++ (modFromMeta (mline idxBits tagBits lgNumDatas lgDataBytes))
                            ++ (modFromMeta (mdir idxBits tagBits lgNumChildren)))%kami.

Definition childParentCCon := ((modFromMeta (childParent idxBits tagBits lgNumDatas lgDataBytes
                                                         idK lgNumChildren))
                                 ++ (modFromMeta (fifoRqFromC idxBits tagBits
                                                              idK fifoSize lgNumChildren))
                                 ++ (modFromMeta (fifoRsFromC idxBits tagBits lgNumDatas lgDataBytes
                                                              fifoSize lgNumChildren))
                                 ++ (modFromMeta (fifoToC idxBits tagBits lgNumDatas lgDataBytes
                                                          idK fifoSize lgNumChildren)))%kami.

Definition memCache := (l1Con ++ childParentCCon ++ memDirCCon)%kami.

Definition procMemCache := (pdecN ++ pmFifos ++ memCache)%kami.

(** MODIFY targetPgm to your target program *)
Definition targetPgm := pgmFibonacci 10.

(** MODIFY targetM to your target module *)
Definition targetProcM := pdecAN.

(** DON'T REMOVE OR MODIFY BELOW LINES *)
Definition targetProcS := getModuleS targetProcM.
Definition targetProcB := ModulesSToBModules targetProcS.

Definition target := (targetPgm, targetProcB).

(* Extraction "./Ocaml/Target.ml" target. *)

