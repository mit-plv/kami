Require Import Kami.
Require Import Lib.Struct Lib.Indexer.
Require Import Ex.ProcMemSpec Ex.PipelinedProc.

Set Implicit Arguments.

Section DecExec.
  Variables (instK dataK: Kind)
            (addrSize rfSize: nat)
            (pgmSize: nat).

  Variables (dec: Decoder instK addrSize rfSize)
            (exec: Executer dataK)
            (pcInit : ConstT (Bit pgmSize))
            (pgmInit : ConstT (Vector instK pgmSize)).

  Local Notation doMem := (doMem dataK addrSize).
  Local Notation toHost := (toHost dataK).
  Local Notation D2E := (D2E addrSize rfSize).
  Local Notation sbSearch1 := (sbSearch1 rfSize).
  Local Notation sbSearch2 := (sbSearch2 rfSize).
  Local Notation sbSearch3 := (sbSearch3 rfSize).
  Local Notation sbInsert := (sbInsert rfSize).
  Local Notation rfRead1 := (rfRead1 dataK rfSize).
  Local Notation rfRead2 := (rfRead2 dataK rfSize).
  Local Notation e2wEnq := (e2wEnq dataK rfSize).
  
  Definition decexec :=
    MODULE {
      Register "pc" : Bit pgmSize <- pcInit
      with Register "pgm" : Vector instK pgmSize <- pgmInit

      with Rule "deArith" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opArith);
      
        LET src1 <- getSrc1 dec inst;
        LET src2 <- getSrc2 dec inst;
        LET dst <- getDst dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Call srcOk2 <- sbSearch2(#src2);
        Call dstOk <- sbSearch3(#dst);
        Assert (#srcOk1 && #srcOk2 && #dstOk);

        LET arithOp <- getArithOp dec inst;
        Call val1 <- rfRead1(#src1);
        Call val2 <- rfRead2(#src2);
        LET execVal <- execArith exec arithOp val1 val2;
        Call sbInsert(#dst);
        Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #execVal });

        Write "pc" <- #pc + $1;
        Retv

      with Rule "deLd" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opLd);

        LET dst <- getDst dec inst;
        LET addr <- getAddr dec inst;
        Call val <- doMem(STRUCT { "isLoad" ::= $$true;
                                   "addr" ::= #addr;
                                   "data" ::= $$Default });
        Call dstOk <- sbSearch3(#dst);
        Assert #dstOk;

        Call sbInsert(#dst);
        Call e2wEnq (STRUCT { "idx" ::= #dst; "val" ::= #val });
        Write "pc" <- #pc + $1;
        Retv

      with Rule "deSt" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opSt);

        LET addr <- getAddr dec inst;
        LET src1 <- getSrc1 dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Assert #srcOk1;
          
        Call val <- rfRead1(#src1);
        Call doMem(STRUCT { "isLoad" ::= $$false;
                            "addr" ::= #addr;
                            "data" ::= $$Default });
        Write "pc" <- #pc + $1;
        Retv

      with Rule "deTh" :=
        Read pc: Bit pgmSize <- "pc";
        Read pgm <- "pgm";
        LET inst <- #pgm@[#pc];
        LET op <- getOp dec inst;
        Assert (#op == $$opTh);

        LET src1 <- getSrc1 dec inst;
        Call srcOk1 <- sbSearch1(#src1);
        Assert #srcOk1;

        Call val1 <- rfRead1(#src1);
        Call toHost(#val1);
        Write "pc" <- #pc + $1;
        Retv
    }.

  Definition decexecSep :=
    ((decoder dec pcInit pgmInit)
       ++ (d2e addrSize rfSize)
       ++ (executer addrSize rfSize exec))%kami.

  Hint Unfold decexecSep decexec: ModuleDefs.

  Lemma decexecSep_ModEquiv: ModEquiv type typeUT decexecSep.
  Proof.
    kequiv.
  Qed.
  Hint Resolve decexecSep_ModEquiv.

  Definition decexec_ruleMap (o: RegsT): string -> option string :=
    "execArith" |-> "deArith";
      "execLd" |-> "deLd";
      "execSt" |-> "deSt";
      "execTh" |-> "deTh"; ||.
  Hint Unfold decexec_ruleMap: MethDefs.

  (* Eval vm_compute in (namesOf (getRegInits decexecSep)). *)
  (* = ["pc"%string; "pgm"%string; "elt.d2e"%string; "full.d2e"%string] *)
  (*   : list string *)
  (* Eval vm_compute in (namesOf (getRegInits decexec)). *)
  (* = ["pc"%string; "pgm"%string] *)
  (*   : list string *)
  Definition decexec_regMap (r: RegsT): RegsT :=
    (mlet pcv : (Bit pgmSize) <- r |> "pc";
       mlet pgmv : (Vector instK pgmSize) <- r |> "pgm";
       mlet d2efullv : Bool <- r |> "d2e"--"full";
       mlet d2eeltv : Struct D2E <- r |> "d2e"--"elt";

       (["pgm" <- existT _ _ pgmv]
        +["pc" <- existT _ _ (if d2efullv then pcv ^+ $1 else pcv)])%fmap
    )%mapping.
  Hint Unfold decexec_regMap: MapDefs.

  Definition decexecSepInl: sigT (fun m: Modules => decexecSep <<== m).
  Proof.
    pose proof (inlineF_refines
                  decexecSep_ModEquiv
                  (Reflection.noDupStr_NoDup
                     (namesOf (getDefsBodies decexecSep))
                     eq_refl)) as Him.
    unfold MethsT in Him; rewrite <-SemFacts.idElementwiseId in Him.
    match goal with
    | [H: context[inlineF ?m] |- _] => set m as origm in H at 2
    end.
    kinline_compute_in Him.
    unfold origm in *.
    specialize (Him eq_refl).
    exact (existT _ _ Him).
  Defined.

  Theorem decexec_ok: decexecSep <<== decexec.
  Proof.
    intros.

    (* 1) inlining *)
    ketrans; [exact (projT2 decexecSepInl)|].

    (* 2) decomposition *)
    kdecompose_nodefs decexec_regMap decexec_ruleMap.

    (* 3) simulation *)
    (* let invs := (eval hnf in (invariants cfg)) in *)
    (* kinv_add_rep invs; *)
    kinvert.
    (* TODO: add at least the most basic invariant --
     * the state always has some register values. *)
    (* - kinv_magic_with idtac idtac. *)

  Admitted.
  
End DecExec.

