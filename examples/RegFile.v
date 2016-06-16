Require Import String Lib.CommonTactics Lib.Indexer Lib.StringExtension.
Require Import Lts.Syntax Lts.ParametricSyntax Lts.Notations Lts.Semantics.
Require Import Lts.Equiv Lts.ParametricEquiv Lts.Wf Lts.ParametricWf Lts.Tactics.

Set Implicit Arguments.

Section RegFile.
  Variable name: string.
  Variable IdxBits: nat.
  Variable Data: Kind.

  Definition DataArray := Vector Data IdxBits.
  Definition Addr := Bit IdxBits.

  Definition WritePort := STRUCT {
                              "addr" :: Addr;
                              "data" :: Data
                            }.
  Notation "^ s" := (name -- s) (at level 0).

  Variable init: ConstT DataArray.
  
  Definition regFile :=
    MODULE {
        Register ^"dataArray": DataArray <- init

        with Method ^"read" (a: Addr): Data :=
          Read full: DataArray <- ^"dataArray";
          Ret (#full@[#a])
            
        with Method ^"write" (w: WritePort): Void :=
          Read full: DataArray <- ^"dataArray";
          Write ^"dataArray" <- #full@[ #w@."addr" <- #w@."data" ];
          Retv
      }.

  (** SinAction version *)
  Hypothesis Hname: index 0 indexSymbol name = None.
  Lemma rfgn:
    forall s, index 0 indexSymbol s = None -> index 0 indexSymbol (^s) = None.
  Proof.
    unfold withPrefix; intros.
    apply index_not_in; apply index_not_in in H; apply index_not_in in Hname.
    intro Hx; elim H; clear H.
    apply S_in_app_or in Hx; destruct Hx; auto.
    apply S_in_app_or in H; destruct H.
    - inv H; inv H0.
    - elim Hname; auto.
  Qed.

  Definition regFileS :=
    SIN {
        Register { ^"dataArray" | rfgn "dataArray" eq_refl } : DataArray <- init

        with Method { ^"read" | rfgn "read" eq_refl } (a: Addr): Data :=
          Read full: DataArray <- { ^"dataArray" | rfgn "dataArray" eq_refl };
          Ret (#full@[#a])
            
        with Method { ^"write" | rfgn "write" eq_refl } (w: WritePort): Void :=
          Read full: DataArray <- { ^"dataArray" | rfgn "dataArray" eq_refl };
          Write { ^"dataArray" | rfgn "dataArray" eq_refl } <- #full@[ #w@."addr" <- #w@."data" ];
          Retv
      }.

  Definition regFileM :=
    META {
        Register { ^"dataArray" | rfgn "dataArray" eq_refl } : DataArray <- init

        with Method { ^"read" | rfgn "read" eq_refl } (a: Addr): Data :=
          Read full: DataArray <- { ^"dataArray" | rfgn "dataArray" eq_refl };
          Ret (#full@[#a])
            
        with Method { ^"write" | rfgn "write" eq_refl } (w: WritePort): Void :=
          Read full: DataArray <- { ^"dataArray" | rfgn "dataArray" eq_refl };
          Write { ^"dataArray" | rfgn "dataArray" eq_refl } <- #full@[ #w@."addr" <- #w@."data" ];
          Retv
      }.

End RegFile.

Hint Unfold DataArray Addr WritePort : MethDefs.
Hint Unfold regFile regFileM regFileS : ModuleDefs.

Section Facts.
  Variable name: string.
  Variable IdxBits: nat.
  Variable Data: Kind.
  Variable init: ConstT (DataArray IdxBits Data).

  Lemma regFile_ModEquiv:
    forall ty1 ty2, ModEquiv ty1 ty2 (regFile name init).
  Proof.
    kequiv.
  Qed.

  Lemma regFile_ValidRegs:
    forall ty, ValidRegsModules ty (regFile name init).
  Proof.
    kvr.
  Qed.

  Variable n: nat.
  Hypothesis (Hgood: index 0 indexSymbol name = None).
  
  Lemma regFileS_ModEquiv:
    forall ty1 ty2, MetaModEquiv ty1 ty2 (getMetaFromSinNat n (regFileS name init Hgood)).
  Proof.
    kequiv.
  Qed.

  Lemma regFileM_ModEquiv:
    forall ty1 ty2, MetaModEquiv ty1 ty2 (regFileM name init Hgood).
  Proof.
    kequiv.
  Qed.

  Lemma regFileS_ValidRegs:
    forall ty, ValidRegsMetaModule ty (getMetaFromSinNat n (regFileS name init Hgood)).
  Proof.
    kvr.
  Qed.

  Lemma regFileM_ValidRegs:
    forall ty, ValidRegsMetaModule ty (regFileM name init Hgood).
  Proof.
    kvr.
  Qed.

End Facts.

Hint Resolve regFile_ModEquiv regFileS_ModEquiv regFileM_ModEquiv.
Hint Resolve regFile_ValidRegs regFileS_ValidRegs regFileM_ValidRegs.

