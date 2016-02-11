Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Refinement.
Require Import Lts.Decomposition Lts.Renaming Lts.Inline Lts.InlineFacts_2.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.

Section ProcDecSC.
  Variables addrSize fifoSize valSize rfIdx: nat.

  Variable dec: DecT 2 addrSize valSize rfIdx.
  Variable exec: ExecT 2 addrSize valSize rfIdx.

  Definition procDecM (n: nat) := procDecM fifoSize dec exec n.
  Definition sc (n: nat) := sc 2 _ _ _ dec exec opLd opSt opHt n.
  Hint Unfold procDecM sc : ModuleDefs.

  Section SingleCore.
    Variable i: nat. (* i-th core *)
    Notation "^ s" := (s __ i) (at level 0).

    Definition pdecfi := ProcDec.pdecfi fifoSize dec exec i.
    Definition pinsti := pinsti 2 _ _ _ dec exec opLd opSt opHt i.
    Hint Unfold pdecfi pinsti.

    Definition regRel: RegsT -> RegsT -> Prop.
      intros ir sr.
      refine (exists pcv: fullType type (SyntaxKind (Bit addrSize)),
                M.find ^"pc" ir = Some (existT _ _ pcv) /\
                _).
      refine (exists rfv: fullType type (SyntaxKind (Vector (Bit valSize) rfIdx)),
                M.find ^"rf" ir = Some (existT _ _ rfv) /\
                _).
      refine (exists eltsv: fullType type (SyntaxKind (Vector (atomK addrSize (Bit valSize))
                                                              fifoSize)),
                M.find (^"Outs" -n- "elt") ir = Some (existT _ _ eltsv) /\
                _).
      refine (exists deqPv: fullType type (SyntaxKind (Bit fifoSize)),
                M.find (^"Outs" -n- "deqP") ir = Some (existT _ _ deqPv) /\
                _).
      refine (exists emptyv: fullType type (SyntaxKind Bool),
                M.find (^"Outs" -n- "empty") ir = Some (existT _ _ emptyv) /\
                _).
      destruct emptyv.
      - exact (sr = M.add ^"pc" (existT _ _ pcv)
                                (M.add ^"rf" (existT _ _ rfv) (M.empty _))).
      - pose (eltsv deqPv ``"type") as opcond.
        destruct (weq opcond (evalConstT opLd)).
        + refine (sr =
                  M.add ^"pc" (existT _ _ (fst (exec _ rfv pcv (dec _ rfv pcv))))
                              (M.add ^"rf" (existT _ (SyntaxKind (Vector (Bit valSize) rfIdx)) _)
                                              (M.empty _))).
          exact (fun a => if weq a (dec _ rfv pcv ``"reg")
                          then eltsv deqPv ``"value"
                          else rfv a).
        + refine (sr =
                  M.add ("pc"__ i) (existT _ _ (fst (exec _ rfv pcv (dec _ rfv pcv))))
                        (M.add ("rf"__ i) (existT _ (SyntaxKind (Vector (Bit valSize) rfIdx))
                                             rfv) (M.empty _))).
    Defined.
    Hint Unfold regRel.

  End SingleCore.

  (* Theorem procDecM_SC: forall n, exists f, (procDecM n) <<=[f] (sc n). *)

End ProcDecSC.

