Require Import Lts.Syntax Lts.Synthesize Lts.ParametricSyntax.
Require Import Ex.Fifo Ex.Isa Ex.ProcMemCorrect.

Definition exInsts: ConstT (Vector (MemTypes.Data rv32iLgDataBytes) rv32iAddrSize) :=
  getDefaultConst _.

Definition exIdxBits := 20.
Definition exTagBits := 10.
Definition exLgNumDatas := 2.
Definition exLgNumChildren := 2.
Definition exFifoSize := 4.

Definition exProcMem := ((pdecN exIdxBits exTagBits exLgNumDatas
                                (rv32iDecode exInsts) rv32iExecState rv32iExecNextPc
                                rv32iLd rv32iSt rv32iHt exLgNumChildren)
                           ++ (pmFifos exIdxBits exTagBits exLgNumDatas
                                       rv32iLgDataBytes exLgNumChildren)
                           ++ (modFromMeta (mcache exFifoSize exIdxBits exTagBits
                                                   exLgNumDatas rv32iLgDataBytes
                                                   Void exLgNumChildren))
                        )%kami.

Definition exProcMemS := (getModuleS exProcMem).

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(* Extraction "ExtractionResult.ml" exProcMemS. *)

