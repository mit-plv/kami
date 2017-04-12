Require Import List String.
Require Import Lib.Word Kami.Syntax Kami.Semantics Kami.Duplicate
        Kami.Notations Kami.Synthesize Ex.IsaRv32 Ex.IsaRv32Pgm.
Require Import Ex.SC Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcFourStDec.
Require Import Ex.MemTypes Ex.MemAtomic Ex.MemCorrect Ex.ProcMemCorrect.
Require Import Ext.BSyntax.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(** * p4st + pmFifos ++ memCache extraction *)

(** Some numbers *)

(* (idxBits + tagBits + lgNumDatas) should be equal to rv32iAddrSize (= 16) *)
Definition idxBits := 8.
Definition tagBits := 4.
Definition lgNumDatas := 4.
Definition lgNumChildren := 1. (* 2^2 = 4 cores *)
Definition fifoSize := 2.
Definition idK := Bit 1.

(** Some initial values *)
Eval compute in ((numChildren lgNumChildren) + 1).

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

Require Import Ex.IsaRv32PgmExt.

Definition procInits : list (ProcInit rv32iAddrSize rv32iIAddrSize rv32iDataBytes rv32iRfIdx) :=
  {| pcInit := Default;
     rfInit := rfWithSpInit (ConstBit (natToWord _ 64));
     pgmInit := IsaRv32PgmDekker1.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ 128));
          pgmInit := IsaRv32PgmDekker2.pgmExt |} :: nil.
(*
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ 192));
          pgmInit := IsaRv32PgmDekker1.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ 256));
          pgmInit := IsaRv32PgmDekker2.pgmExt |}
    :: nil.
*)

Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
  (#ppc + $4)%kami_expr.

Definition p4stNMemCache :=
  ProcMemCorrect.p4stNMemCache
    fifoSize idxBits tagBits lgNumDatas idK
    rv32iGetOptype rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
    rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
    rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
    rv32iAlignPc rv32iAlignAddr predictNextPc lgNumChildren procInits.

(** * The correctness of the extraction target is proven! Trust us! *)
Section Correctness.

  (* Spec: sequential consistency for multicore *)
  Definition scN :=
    ProcMemCorrect.scN
      idxBits tagBits lgNumDatas
      rv32iGetOptype rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
      rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
      rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
      rv32iAlignPc rv32iAlignAddr lgNumChildren procInits.

  Theorem p4stNMemCache_refines_scN: p4stNMemCache <<== scN.
  Proof.
    apply p4stN_mcache_refines_scN.
  Qed.

End Correctness.

(** DON'T REMOVE OR MODIFY BELOW LINES *)
(* targetM should be your target module *)
Definition targetProcM := p4stNMemCache.
Definition targetProcS := getModuleS targetProcM.
Definition targetProcB := ModulesSToBModules targetProcS.

(** Ocaml/Target.ml is used with Ocaml/PP.ml and Main.ml to build a converter to Bluespec. *)
Extraction "./extraction/Ocaml/Target.ml" targetProcB.

