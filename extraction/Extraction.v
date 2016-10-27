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
        Kami.Notations Kami.Synthesize Ex.Isa Ex.IsaTest.

(** p4st + mem (memAtomic or memCache) test *)
Require Import Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcFourStDec.
Require Import Ex.MemAtomic Ex.MemCorrect Ex.ProcMemCorrect.

(* (IdxBits + TagBits + LgNumDatas) should equal to rv32iAddrSize (= 12) *)
Definition idxBits := 3.
Definition tagBits := 3.
Definition lgNumDatas := 1.
Definition lgNumChildren := 1. (* 2^1 = 2 cores *)
Definition fifoSize := 2.
Definition idK := Bit 1.

Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
  (#ppc + $4)%kami_expr.

Definition p4st := p4st rv32iGetOptype
                        rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
                        rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
                        rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
                        rv32iAlignPc predictNextPc (@d2ePackI _ _ _)
                        (@d2eOpTypeI _ _ _) (@d2eDstI _ _ _) (@d2eAddrI _ _ _)
                        (@d2eVal1I _ _ _) (@d2eVal2I _ _ _)
                        (@d2eRawInstI _ _ _) (@d2eCurPcI _ _ _) (@d2eNextPcI _ _ _)
                        (@d2eEpochI _ _ _)
                        (@f2dPackI _ _) (@f2dRawInstI _ _) (@f2dCurPcI _ _)
                        (@f2dNextPcI _ _) (@f2dEpochI _ _)
                        (@e2wPackI _ _ _) (@e2wDecInstI _ _ _) (@e2wValI _ _ _).

Definition p4stN := duplicate p4st (Word.wordToNat (Word.wones lgNumChildren)).

(* Definition memAtomic := memAtomic rv32iAddrSize fifoSize rv32iLgDataBytes *)
(*                                   (Word.wordToNat (Word.wones lgNumChildren)). *)
Definition memCache := memCacheMod idxBits tagBits lgNumDatas rv32iLgDataBytes (Bit 1)
                                   fifoSize lgNumChildren.
Definition pmFifos := pmFifos fifoSize idxBits tagBits lgNumDatas rv32iLgDataBytes lgNumChildren.

(* Definition procMemAtomic := (p4stN ++ memAtomic)%kami. *)
Definition procMemCache := (p4stN ++ pmFifos ++ memCache)%kami.

(** MODIFY targetPgm to your target program *)
Definition targetPgm := pgmJalTest1.

(** MODIFY targetM to your target module *)
Definition targetProcM := procMemCache.

(** DON'T REMOVE OR MODIFY BELOW LINES *)
Definition targetProcS := getModuleS targetProcM.
Definition targetProcB := ModulesSToBModules targetProcS.

Definition target := (targetPgm, targetProcB).

(* Extraction "./Ocaml/Target.ml" target. *)

