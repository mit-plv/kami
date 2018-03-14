Require Import List String.
Require Import Lib.Word Kami.Syntax Kami.Semantics
        Kami.Notations Lib.Struct.

Require Import ExtrHaskellBasic ExtrHaskellNatInt ExtrHaskellString.
Require Import Compile.CompileToRtlTryOpt Compile.Rtl.

Extraction Language Haskell.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extract Inductive sigT => "(,)" ["(,)"].
(* Extract Inductive word => "[Prelude.Bool]" ["([])" "(\ b x bs -> b : bs)"]. *)
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".
Extract Inlined Constant map => "Prelude.map".
Extract Inlined Constant concat => "Prelude.concat".

Extract Inductive Vector.t => "Vtor" ["NilV" "ConsV"].

(*
Require Import Kami.Tutorial.

Definition targetProcM := producerConsumerImpl.
*)


Require Import Ex.SC Ex.IsaRv32 Ex.IsaRv32Pgm Ex.ProcFetchDecode Ex.ProcThreeStage.
Require Import Ex.ProcFourStDec.
Require Import Ex.MemTypes Ex.MemAtomic Ex.MemCorrect Ex.ProcMemCorrect.

(** * p4st + pmFifos ++ memCache extraction *)

(** Some numbers *)

(* (idxBits + tagBits + lgNumDatas) should be equal to rv32iAddrSize (= 16) *)
Definition idxBits := 6.
Definition tagBits := 3.
Definition lgNumDatas := 2.
Definition lgNumChildren := 2. (* 2^2 = 4 cores *)
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
     pgmInit := IsaRv32.Matmul_init.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ 128));
          pgmInit := IsaRv32.Matmul_normal1.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ 192));
          pgmInit := IsaRv32.Matmul_normal2.pgmExt |}
    :: {| pcInit := Default;
          rfInit := rfWithSpInit (ConstBit (natToWord _ 256));
          pgmInit := IsaRv32.Matmul_report.pgmExt |}
    :: nil.

Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Bit rv32iAddrSize))) :=
  (#ppc + $4)%kami_expr.

(*
Definition p4stN :=
  ProcMemCorrect.p4stN
    idxBits tagBits lgNumDatas
    rv32iGetOptype rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
    rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
    rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
    rv32iAlignPc rv32iAlignAddr predictNextPc lgNumChildren procInits.

Definition pmFifos :=
  ProcMemCorrect.pmFifos fifoSize idxBits tagBits lgNumDatas rv32iDataBytes lgNumChildren.

Definition memCache :=
  fst (Kami.Inline.inlineF (ProcMemCorrect.memCacheMod fifoSize idxBits tagBits lgNumDatas rv32iDataBytes idK lgNumChildren)).

Definition p4stNMemCache := (p4stN ++ pmFifos ++ memCache)%kami.
*)


Definition p4stNMemCache :=
  ProcMemCorrect.p4stNMemCache
    fifoSize idxBits tagBits lgNumDatas idK
    rv32iGetOptype rv32iGetLdDst rv32iGetLdAddr rv32iGetLdSrc rv32iCalcLdAddr
    rv32iGetStAddr rv32iGetStSrc rv32iCalcStAddr rv32iGetStVSrc
    rv32iGetSrc1 rv32iGetSrc2 rv32iGetDst rv32iExec rv32iNextPc
    rv32iAlignPc rv32iAlignAddr predictNextPc lgNumChildren procInits.


(** targetM should be your target module *)
Definition targetMod := p4stNMemCache.

Definition target := computeModule targetMod (map (@attrName _) (getRules targetMod)) nil.

(*
Open Scope string.
Eval vm_compute in (getCallGraph mod).
Eval vm_compute in (methPos mod (map (@attrName _) (getRules mod)) "enq.f2d").
Close Scope string.
*)
Extraction "Target.hs" target.

