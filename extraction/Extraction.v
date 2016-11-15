Require Import List String.
Require Import Lib.Word Kami.Syntax Kami.Semantics Kami.Duplicate
        Kami.Notations Kami.Synthesize Ex.IsaRv32 Ex.IsaRv32Pgm.
Require Import Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcFourStDec.
Require Import Ex.MemTypes Ex.MemAtomic Ex.MemCorrect Ex.ProcMemCorrect.
Require Import Ext.BSyntax.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(** p4st + pmFifos ++ memCache extraction *)

(* (idxBits + tagBits + lgNumDatas) should be equal to rv32iAddrSize (= 10) *)
Definition idxBits := 4.
Definition tagBits := 3.
Definition lgNumDatas := 3.
Definition lgNumChildren := 2. (* 2^2 = 4 cores *)
Definition fifoSize := 2.
Definition idK := Bit 1.

Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
  (#ppc + $4)%kami_expr.

Definition p4stNMemCache :=
  ProcMemCorrect.p4stNMemCache
    fifoSize idxBits tagBits lgNumDatas idK
    rv32iGetOptype rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
    rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
    rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
    rv32iAlignPc rv32iAlignAddr predictNextPc lgNumChildren.

(** The correctness of the extraction target is proven! Trust us! *)
Section Correctness.

  (* Spec: sequential consistency for multicore *)
  Definition scN :=
    ProcMemCorrect.scN
      idxBits tagBits lgNumDatas
      rv32iGetOptype rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
      rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
      rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
      rv32iAlignPc rv32iAlignAddr lgNumChildren.

  Theorem p4stNMemCache_refines_scN: p4stNMemCache <<== scN.
  Proof.
    apply p4stN_mcache_refines_scN.
  Qed.

End Correctness.

(** MODIFY: targetPgms should be your target program *)
Require Import Ex.IsaRv32PgmExt.
Definition targetPgms :=
  IsaRv32PgmMatMulInit.pgmExt
    :: IsaRv32PgmMatMulNormal1.pgmExt
    :: IsaRv32PgmMatMulNormal2.pgmExt
    :: IsaRv32PgmMatMulReport.pgmExt :: nil.

(** MODIFY: targetM should be your target module *)
Definition targetProcM := p4stNMemCache.

(* A utility function for setting the stack pointer in rf *)
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

(** MODIFY: targetRfs should be a list of initial values of processors' register files *)
Definition targetRfs : list (ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx)) :=
  (rfWithSpInit (ConstBit (natToWord _ 64)))
    :: (rfWithSpInit (ConstBit (natToWord _ 128)))
    :: (rfWithSpInit (ConstBit (natToWord _ 192)))
    :: (rfWithSpInit (ConstBit (natToWord _ 256)))
    :: nil.

(** DON'T REMOVE OR MODIFY BELOW LINES *)
Definition targetProcS := getModuleS targetProcM.
Definition targetProcB := ModulesSToBModules targetProcS.

(** What to extract *)
Record ExtTarget :=
  { extPgms : list (ConstT (Vector (Data rv32iDataBytes) rv32iIAddrSize));
    extProc : option (list BModule);
    extRfs : list (ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx))
  }.

Definition target : ExtTarget :=
  {| extPgms := targetPgms;
     extProc := targetProcB;
     extRfs := targetRfs |}.

(** Ocaml/Target.ml is used with Ocaml/PP.ml and Main.ml to build a converter to Bluespec. *)
(* Extraction "./Ocaml/Target.ml" target. *)

