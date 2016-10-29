Require Import List String.
Require Import Lib.Word Kami.Syntax Kami.ParametricSyntax Kami.Duplicate
        Kami.Notations Kami.Synthesize Ex.IsaRv32 Ex.IsaRv32Pgm.
Require Import Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcFourStDec.
Require Import Ex.MemTypes Ex.MemAtomic Ex.MemCorrect Ex.ProcMemCorrect.
Require Import Ext.BSyntax.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(** p4st + mem (memAtomic or memCache) extraction *)

(* (IdxBits + TagBits + LgNumDatas) should equal to rv32iAddrSize (= 7) *)
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

(* Definition memAtomic := memAtomic rv32iAddrSize fifoSize rv32iDataBytes *)
(*                                   (Word.wordToNat (Word.wones lgNumChildren)). *)
Definition memCache := memCacheMod idxBits tagBits lgNumDatas rv32iDataBytes (Bit 1)
                                   fifoSize lgNumChildren.
Definition pmFifos := pmFifos fifoSize idxBits tagBits lgNumDatas rv32iDataBytes lgNumChildren.

(* Definition procMemAtomic := (p4stN ++ memAtomic)%kami. *)
Definition procMemCache := (p4stN ++ pmFifos ++ memCache)%kami.

(** MODIFY: targetPgm should be your target program *)
Definition targetPgm := pgmJalTest1.

(** MODIFY: targetM should be your target module *)
Definition targetProcM := procMemCache.

(** MODIFY: targetRfs should be a list of initial values of processors' register files *)
Definition rfWithSpInit (sp: ConstT (Data rv32iDataBytes))
  : ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx).
  refine
    (ConstVector (VecNext
                    (VecNext
                       (VecNext
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 sp) (Vec0 _)))
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))
                       (VecNext
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))))
                    (VecNext
                       (VecNext
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _))))
                       (VecNext
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))
                          (VecNext (VecNext (Vec0 _) (Vec0 _)) (VecNext (Vec0 _) (Vec0 _)))))));
    exact $0.
Defined.

Definition targetRfs : list (ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx)) :=
  (rfWithSpInit (ConstBit (natToWord _ 48)))
    :: (rfWithSpInit (ConstBit (natToWord _ 96)))
    :: nil.

(** DON'T REMOVE OR MODIFY BELOW LINES *)
Definition targetProcS := getModuleS targetProcM.
Definition targetProcB := ModulesSToBModules targetProcS.

(** What to extract *)
Record ExtTarget :=
  { extPgm : ConstT (Vector (Data rv32iDataBytes) rv32iIAddrSize);
    extProc : option (list BModule);
    extRfs : list (ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx))
  }.

Definition target : ExtTarget :=
  {| extPgm := targetPgm;
     extProc := targetProcB;
     extRfs := targetRfs |}.

(** Ocaml/Target.ml is used with Ocaml/PP.ml and Main.ml to build a converter to Bluespec. *)
(* Extraction "./Ocaml/Target.ml" target. *)

