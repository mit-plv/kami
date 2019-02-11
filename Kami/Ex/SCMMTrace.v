Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.Indexer Lib.ilist Lib.Word Lib.Struct Lib.FMap.
Require Import Kami.Syntax Kami.Notations.
Require Import Kami.Semantics Kami.Specialize Kami.Duplicate.
Require Import Kami.Wf Kami.Tactics.
Require Import Ex.MemTypes Ex.SC.

Set Implicit Arguments.

Open Scope fmap.

Section MMIOLabel.
  Variable addrSize: nat.
  Variable dataBytes: nat.

  Inductive MMIOLabelT :=
  | MMIOSilent
  | MMIOLd (addr: type (Bit addrSize)) (val: type (Data dataBytes))
  | MMIOSt (addr: type (Bit addrSize)) (val: type (Data dataBytes)).

  Definition MMIOLabelR (lbl: LabelT) (mlbl: MMIOLabelT): Prop.
  Proof.
    refine (match lbl.(defs)@["mmioExec"] with
            | Some sv => _
            | None => mlbl = MMIOSilent
            end).
    destruct sv as [[argT retT] [argV retV]].
    destruct (decKind argT (Struct (RqFromProc addrSize dataBytes)));
      [subst|exact False].
    destruct (decKind retT (Struct (RsToProc dataBytes)));
      [subst|exact False].

    destruct (argV (Fin.FS Fin.F1)).
    - (* MMIO-store *)
      exact (mlbl = MMIOSt (argV Fin.F1) (argV (Fin.FS (Fin.FS Fin.F1)))).
    - (* MMIO-load *)
      exact (mlbl = MMIOLd (argV Fin.F1) (retV Fin.F1)).
  Defined.

  Definition MMIOTrace := list MMIOLabelT.

  Inductive MMIOTraceR: LabelSeqT -> MMIOTrace -> Prop :=
  | MMIOTraceRNil: MMIOTraceR nil nil
  | MMIOTraceRCons:
      forall tr mtr lbl mlbl,
        MMIOTraceR tr mtr -> MMIOLabelR lbl mlbl ->
        MMIOTraceR (lbl :: tr) (mlbl :: mtr).
  
End MMIOLabel.

Close Scope fmap.

