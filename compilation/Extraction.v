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

(*
Require Import Kami.Tutorial.

Definition targetProcM := producerConsumerImpl.
*)


Require Import Ex.IsaRv32 Ex.IsaRv32Pgm Ex.ProcFetchDecode Ex.ProcThreeStage Ex.ProcFourStDec.
Require Import Ex.MemTypes Ex.MemAtomic Ex.MemCorrect Ex.ProcMemCorrect.

(** p4st + pmFifos ++ memCache extraction *)

(* (idxBits + tagBits + lgNumDatas) should be equal to rv32iAddrSize (= 16) *)
Definition idxBits := 8.
Definition tagBits := 4.
Definition lgNumDatas := 4.
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

(** targetM should be your target module *)
Definition targetMod := p4stNMemCache.

(*
(** targetPgms should be your target program *)
Require Import Ex.IsaRv32PgmExt.
Definition targetPgms :=
  IsaRv32PgmBankerInit.pgmExt
    :: IsaRv32PgmBankerWorker1.pgmExt
    :: IsaRv32PgmBankerWorker2.pgmExt
    :: IsaRv32PgmBankerWorker3.pgmExt :: nil.

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

(** targetRfs should be a list of initial values of processors' register files *)
Definition targetRfs : list (ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx)) :=
  (rfWithSpInit (ConstBit (natToWord _ 64)))
    :: (rfWithSpInit (ConstBit (natToWord _ 128)))
    :: (rfWithSpInit (ConstBit (natToWord _ 192)))
    :: (rfWithSpInit (ConstBit (natToWord _ 256)))
    :: nil.

(* What to extract *)
Record ExtTarget :=
  { extPgms : list (ConstT (Vector (Data rv32iDataBytes) rv32iIAddrSize));
    extProc : option (list BRegModule);
    extRfs : list (ConstT (Vector (Data rv32iDataBytes) rv32iRfIdx))
  }.

Definition targetAll : ExtTarget :=
  {| extPgms := targetPgms;
     extProc := targetProcB;
     extRfs := targetRfs |}.

(** Ocaml/Target.ml is used with Ocaml/PP.ml and Main.ml to build a converter to Bluespec. *)
Extraction "./extraction/Ocaml/Target.ml" target.
*)




Definition target := computeModule targetMod (map (@attrName _) (getRules targetMod)) nil.

(*
Open Scope string.
Eval vm_compute in (getCallGraph mod).
Eval vm_compute in (methPos mod (map (@attrName _) (getRules mod)) "enq.f2d").
Close Scope string.
*)
Extraction "Target.hs" target.

