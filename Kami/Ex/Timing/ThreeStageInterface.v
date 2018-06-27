Require Import Notations.
Require Import List.
Require Import Lib.Word Lib.Indexer Lib.FMap.
Require Import Kami.Syntax Kami.Semantics Kami.SymEvalTac Kami.Tactics Kami.ModularFacts Kami.SemFacts.
Require Import Ex.SC Ex.IsaRv32 Ex.ProcThreeStage Ex.OneEltFifo.
Require Import Ex.Timing.Specification.
Require Import Lib.CommonTactics.



Module Type ThreeStageInterface.
  Parameter p : Modules.
  Parameter m : Modules.

  Axiom pequiv : Wf.ModEquiv type typeUT p.
  Axiom mequiv : Wf.ModEquiv type typeUT m.
  Axiom reginits : FMap.DisjList (Struct.namesOf (getRegInits p))
                                 (Struct.namesOf (getRegInits m)).

  Axiom validRegs : Wf.ValidRegsModules type (p ++ m)%kami.

  Axiom defsDisj : FMap.DisjList (getDefs p) (getDefs m).
  Axiom callsDisj : FMap.DisjList (getCalls p) (getCalls m).

  Parameter ThreeStageProcRegs : regfile -> progMem -> address -> RegsT.
  Parameter ThreeStageMemRegs : memory -> RegsT.

  Parameter fhMeth : String.string.
  Parameter thMeth : String.string.
  Parameter rqMeth : String.string.
  Parameter rsMeth : String.string.

  Axiom methsDistinct : fhMeth <> thMeth /\ thMeth <> rqMeth /\ rqMeth <> fhMeth /\ rqMeth <> rsMeth /\ thMeth <> rsMeth /\ rsMeth <> fhMeth.
  Axiom mdrq : In rqMeth (getDefs m).
  Axiom mdrs : In rsMeth (getDefs m).
  Axiom pcrq : In rqMeth (getCalls p).
  Axiom pcrs : In rsMeth (getCalls p).
  Axiom pcfh : In fhMeth (getCalls p).
  Axiom pcth : In thMeth (getCalls p).
  Axiom pndfh : ~ In fhMeth (getDefs p).
  Axiom mndfh : ~ In fhMeth (getDefs m).
  Axiom pndth : ~ In thMeth (getDefs p).
  Axiom mndth : ~ In thMeth (getDefs m).

  Axiom pRegs : forall rf pm pc, FMap.M.KeysSubset (ThreeStageProcRegs rf pm pc) (Struct.namesOf (getRegInits p)).
  Axiom mRegs : forall mem, FMap.M.KeysSubset (ThreeStageMemRegs mem) (Struct.namesOf (getRegInits m)).

  Axiom pRqRs : forall rf u l,
      Step p rf u l ->
      (FMap.M.find rqMeth (calls l) = None \/
       FMap.M.find rsMeth (calls l) = None).

  Axiom mRqRs : forall rf u l,
      Step m rf u l ->
      (FMap.M.find rqMeth (defs l) = None \/
       FMap.M.find rsMeth (defs l) = None).

End ThreeStageInterface.
