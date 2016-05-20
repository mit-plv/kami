Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.StringBound Lib.FMap Lib.StringEq.
Require Import Lts.Syntax Lts.Semantics Lts.SemFacts Lts.Equiv Lts.Refinement Lts.Renaming Lts.Wf.
Require Import Lts.Renaming Lts.Specialize Lts.Tactics Lts.Duplicate.
Require Import Ex.SC Ex.Fifo Ex.MemAtomic.
Require Import Ex.ProcDec Ex.ProcDecInl Ex.ProcDecInv Ex.ProcDecSC.

Set Implicit Arguments.

Section ProcDecSCN.
  Variables addrSize fifoSize lgDataBytes rfIdx: nat.

  Variable dec: DecT 2 addrSize lgDataBytes rfIdx.
  Variable execState: ExecStateT 2 addrSize lgDataBytes rfIdx.
  Variable execNextPc: ExecNextPcT 2 addrSize lgDataBytes rfIdx.

  Variable n: nat.
  
  Definition pdecN := procDecM fifoSize dec execState execNextPc n.
  Definition scN := sc dec execState execNextPc opLd opSt opHt n.

  Lemma pdecN_refines_scN: pdecN <<== scN.
  Proof.
    admit.
  (*
    simple kmodular.
    - kequiv.
    - kequiv.
    - kequiv.
    - kequiv.
    - apply duplicate_meta_disj_regs_one; auto.
    - apply duplicate_meta_disj_regs_one; auto.
    - split.
      + apply duplicate_validRegsModules; auto.
      + constructor; [constructor|].
        simpl; rewrite app_nil_r.
        induction n; simpl; [repeat constructor|].
        repeat constructor; auto.
    - split.
      + apply duplicate_validRegsModules; auto.
      + constructor; [constructor|].
        simpl; rewrite app_nil_r.
        induction n; simpl; [repeat constructor|].
        repeat constructor; auto.
    - apply duplicate_meta_disj_defs_rep; auto.
    - apply duplicate_meta_disj_meth_calls_rep with (mregso:= nil); auto.
    - apply duplicate_meta_disj_defs_rep; auto.
    - apply duplicate_meta_disj_meth_calls_rep with (mregso:= nil); auto.
    - auto.
    - auto.
    - auto.
    - kduplicated.
      + kequiv.
      + kequiv.
      + apply pdec_refines_pinst.
    - krefl.
   *)
  Qed.

  Definition procDecN := pdecs dec execState execNextPc n.
  Definition memAtomic := memAtomic addrSize fifoSize lgDataBytes n.
  Definition pdecAN := (procDecN ++ memAtomic)%kami.

  Lemma pdecN_memAtomic_refines_scN: pdecAN <<== scN.
  Proof.
    admit.
  (*
    ktrans pdecN; [|unfold MethsT; rewrite <-idElementwiseId; apply pdecN_refines_scN].
    ktrans ((pdecs dec execState execNextPc n ++ ioms addrSize fifoSize lgDataBytes n)
              ++ minst addrSize lgDataBytes n)%kami; [apply traceRefines_assoc_2|].

    kmodular_sim_l.
    - simpl; unfold namesOf; rewrite map_app.
      apply NoDup_DisjList.
      + rewrite map_app; apply NoDup_DisjList.
        * apply duplicate_regs_NoDup; auto.
        * apply duplicate_regs_NoDup; auto.
        * apply duplicate_disj_regs; auto.
      + auto.
      + simpl; rewrite map_app; apply DisjList_app_4.
        * clear; induction n; simpl; [auto|].
          assert (forall s, ~ (In s (spDom (ProcDec.pdec dec execState execNextPc)) /\
                               In s (spImg (ProcDec.pdec dec execState execNextPc) (S n0)))).
          { apply specializable_disj_dom_img; auto. }
          repeat (rewrite specializer_dom; [|auto|vm_compute; tauto]).
          repeat (apply DisjList_string_cons; [intro Hx; CommonTactics.dest_in; discriminate|]).
          auto.
        * clear; induction n; simpl; [auto|].
          assert (forall s, ~ (In s (spDom (iom addrSize fifoSize lgDataBytes)) /\
                               In s (spImg (iom addrSize fifoSize lgDataBytes) (S n0)))).
          { apply specializable_disj_dom_img; auto. }
          repeat (rewrite specializer_dom; [|auto|vm_compute; tauto]).
          repeat (apply DisjList_string_cons; [intro Hx; CommonTactics.dest_in; discriminate|]).
          auto.
          
    - simpl; unfold namesOf; rewrite map_app.
      apply NoDup_DisjList.
      + apply duplicate_regs_NoDup; auto.
      + auto.
      + clear; induction n; simpl; [auto|].
        assert (forall s, ~ (In s (spDom (pdecf fifoSize dec execState execNextPc)) /\
                             In s (spImg (pdecf fifoSize dec execState execNextPc) (S n0)))).
        { apply specializable_disj_dom_img; auto. }
        repeat (rewrite specializer_dom; [|auto|vm_compute; tauto]).
        repeat (apply DisjList_string_cons; [intro Hx; CommonTactics.dest_in; discriminate|]).
        auto.
      
    - apply duplicate_regs_ConcatMod_2; auto; kequiv.
    - apply duplicate_regs_ConcatMod_1; auto; kequiv.
    - apply duplicate_rules_ConcatMod_2; auto; kequiv.
    - apply duplicate_rules_ConcatMod_1; auto; kequiv.
    - apply duplicate_defs_ConcatMod_2; auto; kequiv.
    - apply duplicate_defs_ConcatMod_1; auto; kequiv.
   *)
  Qed.
  
End ProcDecSCN.

