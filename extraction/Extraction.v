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
Require Import Kami.Syntax Kami.ParametricSyntax Kami.Duplicate
        Kami.Notations Kami.Synthesize Ex.Isa.

(** p2st + memAtomic test *)
Require Import Ex.ProcTwoStage Ex.ProcTwoStDec Ex.MemAtomic.

(* AddrSize = IdxBits + TagBits + LgNumDatas *)
Definition idxBits := 2.
Definition tagBits := 1.
Definition lgNumDatas := 1.
Definition lgNumChildren := 1. (* 2 cores *)
Definition lgDataBytes := idxBits + tagBits + lgNumDatas.
Definition fifoSize := 2.
Definition idK := Bit 1.

Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
  (#ppc + $1)%kami_expr.

Definition p2st := p2st rv32iGetOptype
                        rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
                        rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
                        rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
                        predictNextPc (@d2ePackI _ _ _)
                        (@d2eOpTypeI _ _ _) (@d2eDstI _ _ _) (@d2eAddrI _ _ _) (@d2eValI _ _ _)
                        (@d2eRawInstI _ _ _) (@d2eCurPcI _ _ _) (@d2eNextPcI _ _ _)
                        (@d2eEpochI _ _ _).

Definition p2stN := duplicate p2st lgNumChildren.
Definition memAtomic := memAtomic rv32iAddrSize fifoSize rv32iLgDataBytes lgNumChildren.

Definition procMemAtomic := (p2stN ++ memAtomic)%kami.

(** MODIFY targetPgm to your target program *)
Definition targetPgm := pgmFibonacci 10.

(** MODIFY targetM to your target module *)
Definition targetProcM := procMemAtomic.

(** DON'T REMOVE OR MODIFY BELOW LINES *)
Definition targetProcS := getModuleS targetProcM.
Definition targetProcB := ModulesSToBModules targetProcS.

Definition target := (targetPgm, targetProcB).

(* Extraction "./Ocaml/Target.ml" target. *)

