Require Import Kami.
Require Import Kami.Synthesize.
Require Import Ex.ProcMemSpec Ex.PipelinedProc.
Require Import Ext.BSyntax.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

(** Parameter instantiation *)

Definition rfSize := 5. (* 2^5 = 32 *)
Definition addrSize := 4. (* 2^4 = 16 cells *)
Definition InstStr :=
  STRUCT { "op" :: opK;
           "arithOp" :: opArithK;
           "src1" :: Bit rfSize;
           "src2" :: Bit rfSize;
           "dst" :: Bit rfSize;
           "addr" :: Bit addrSize
         }.

Definition decoderIns: Decoder (Struct InstStr) addrSize rfSize :=
  {| getOp := fun _ inst => (#inst!InstStr@."op")%kami_expr;
     getArithOp := fun _ inst => (#inst!InstStr@."arithOp")%kami_expr;
     getSrc1 := fun _ inst => (#inst!InstStr@."src1")%kami_expr;
     getSrc2 := fun _ inst => (#inst!InstStr@."src2")%kami_expr;
     getDst := fun _ inst => (#inst!InstStr@."dst")%kami_expr;
     getAddr := fun _ inst => (#inst!InstStr@."addr")%kami_expr
  |}.

Definition dataK := Bit 32.
Definition executerIns: Executer dataK :=
  {| execArith :=
       fun _ op src1 src2 =>
         (IF (#op == $$opArithAdd) then (#src1 + #src2)
          else IF (#op == $$opArithSub) then (#src1 - #src2)
          else IF (#op == $$opArithMul) then (#src1 * #src2)
          else (#src1 / #src2))%kami_expr |}.

Definition pgmSize := 4. (* 2^4 = 16 lines *)
Definition init: ProcInit (Struct InstStr) dataK rfSize pgmSize :=
  {| pcInit := getDefaultConst _;
     rfInit := getDefaultConst _;
     pgmInit := getDefaultConst _
  |}.

Definition procMemImpl := procMemImpl decoderIns executerIns init.

(** * DON'T REMOVE OR MODIFY BELOW LINES *)

(* targetM should be your target module *)
Definition targetProcM := procMemImpl.
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
(* Extraction "./Kami/Ext/Ocaml/Target.ml" targetProcB. *)
