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

(** Extraction of
 *  "Four-stage pipelined processor [p4st] +
 *   FIFOs connecting processors and the memory subsystem [pmFifos] +
 *   2-level coherent caches and memory [memCache]"
 *)

(** Parameter instantiation *)

(* idxBits: #bits for the cache index
 * tagBits: #bits for the cache tag
 * lgNumDatas: the log number of data in a cache line
 *)
Definition idxBits := 6.
Definition tagBits := 3.
Definition lgNumDatas := 2.

(* NOTE: Some problems occur when synthesizing the processor on FPGA 
 * with large [rv32iAddrSize]. We checked the synthesis works when 
 * the address is "11", but failed to check with larger values.
 * 
 * Just for the Bluespec simulation, it works with the address size of "16",
 * probably also with larger values.
 *)

(* [idxBits + tagBits + lgNumDatas] should be equal to
 * [rv32iAddrSize] in examples/IsaRv32.v
 *)
Definition valid_rv32i_addr_size:
  idxBits + tagBits + lgNumDatas = rv32iAddrSize := eq_refl.

(* lgNumChildren: the log number of cores, e.g., 2 cores for [lgNumChildren = 1].
 * fifoSize: the log number of elements for FIFOs used in the memory subsystem
 *)
Definition lgNumChildren := 2.
Definition fifoSize := 2.

(* A utility function for setting the initial stack pointer values in rf *)
Definition rfWithSpInit (sp: ConstT (Data rv32iDataBytes))
  : ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx).
  refine
    (ConstVector
       (VecNext
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

Definition pgmSize := (wordToNat (wones rv32iIAddrSize) + 1) * 4.
Definition stackSize := 512. (* per core *)

(* The initial values (pc, register file, and program) for each processor *)
Definition procInits : list (ProcInit rv32iAddrSize rv32iIAddrSize rv32iDataBytes rv32iRfIdx) :=
  {| pcInit := Default;
     rfInit := rfWithSpInit (ConstBit (natToWord _ (pgmSize + stackSize)));
     pgmInit := IsaRv32.PgmMatMulInit.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ (pgmSize + 2 * stackSize)));
          pgmInit := IsaRv32.PgmMatMulNormal1.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ (pgmSize + 3 * stackSize)));
          pgmInit := IsaRv32.PgmMatMulNormal2.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ (pgmSize + 4 * stackSize)));
          pgmInit := IsaRv32.PgmMatMulReport.pgmExt |}
    :: nil.

Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
  (#ppc + $4)%kami_expr.

Definition p4stNMemCache :=
  ProcMemCorrect.p4stNMemCache
    fifoSize idxBits tagBits lgNumDatas (Bit 1)
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

(** * DON'T REMOVE OR MODIFY BELOW LINES *)

(* targetM should be your target module *)
Definition targetProcM := p4stNMemCache.
Definition targetProcS := getModuleS targetProcM.
Definition targetProcB := ModulesSToBModules targetProcS.

(* If you are testing directly on this file with ProofGeneral or CoqIde,
 * then use the below extraction command, instead of the one at the last line.
 *)
(* Extraction "./Ocaml/Target.ml" targetProcB. *)

(* [Target.ml] will be generated after executing the below extraction command.
 * To generate the corresponding Bluespec program, do [make] in the directory
 * [./Kami/Ext/Ocaml/]. See [./Kami/Ext/Ocaml/README.md] for details.
 *)
Extraction "./Kami/Ext/Ocaml/Target.ml" targetProcB.
