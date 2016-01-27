Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound Lib.FMap.
Require Import Lts.Syntax Lts.Semantics Lts.Inline.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic Ex.ProcDec.

Require Import FunctionalExtensionality.

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
                M.find ^"pc" ir = Some {| objVal := pcv |} /\
                _).
      refine (exists rfv: fullType type (SyntaxKind (Vector (Bit valSize) rfIdx)),
                M.find ^"rf" ir = Some {| objVal := rfv |} /\
                _).
      refine (exists eltsv: fullType type (SyntaxKind (Vector (atomK addrSize (Bit valSize))
                                                              fifoSize)),
                M.find (^"Outs" -n- "elt") ir = Some {| objVal := eltsv |} /\
                _).
      refine (exists deqPv: fullType type (SyntaxKind (Bit fifoSize)),
                M.find (^"Outs" -n- "deqP") ir = Some {| objVal := deqPv |} /\
                _).
      refine (exists emptyv: fullType type (SyntaxKind Bool),
                M.find (^"Outs" -n- "empty") ir = Some {| objVal := emptyv |} /\
                _).
      destruct emptyv.
      - exact (sr = M.add ^"pc" {| objVal := pcv |}
                                (M.add ^"rf" {| objVal := rfv |} (M.empty _))).
      - pose (eltsv deqPv ``"type") as opcond.
        destruct (weq opcond (evalConstT opLd)).
        + refine (sr =
                  M.add ^"pc" {| objVal := fst (exec _ rfv pcv (dec _ rfv pcv)) |}
                              (M.add ^"rf" {| objType := SyntaxKind (Vector (Bit valSize) rfIdx);
                                              objVal := _ |} (M.empty _))).
          exact (fun a => if weq a (dec _ rfv pcv ``"reg")
                          then eltsv deqPv ``"value"
                          else rfv a).
        + refine (sr =
                  M.add ("pc"__ i) {| objVal := fst (exec _ rfv pcv (dec _ rfv pcv)) |}
                        (M.add ("rf"__ i) {| objType := SyntaxKind (Vector (Bit valSize) rfIdx);
                                             objVal := rfv |} (M.empty _))).
    Defined.
    Hint Unfold regRel.

    (* Lemma procDec_SC_i: pdecfi <<=[f] pinsti. *)
  End SingleCore.

  (* Theorem procDecM_SC: forall n, exists f, (procDecM n) <<=[f] (sc n). *)

End ProcDecSC.

