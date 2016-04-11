Require Import Ascii Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word Lib.Struct Lib.StringBound.
Require Import Lts.Syntax Lts.Semantics Lts.Specialize Lts.Equiv.

Set Implicit Arguments.

(* The Coherent Memory module, which contains a directory for every address
 *)
Definition Msi := Bit 2.
Definition Mod := 3.
Definition Sh := 1.
Definition Inv := 0.

Section CoherentMemory.
  Variables AddrBits LgDataBytes LgNumDatas LgNumChildren: nat.
  Variable Id: Kind.
  Definition Addr := Bit AddrBits.
  Definition Data := Bit (LgDataBytes * 8).
  Definition Line := Vector Data LgNumDatas.
  Definition IdxBits := AddrBits - (LgNumDatas + LgDataBytes + 3).
  Definition Child := Bit LgNumChildren.
  
  Definition RqFromC := STRUCT {
                            "child" :: Child;
                            "addr" :: Addr;
                            "from" :: Msi;
                            "to" :: Msi;
                            "id" :: Id
                          }.

  Definition ToC := STRUCT {
                        "isRq" :: Bool;
                        "child" :: Child;
                        "addr" :: Addr;
                        "to" :: Msi;
                        "data" :: Data
                      }.

  Definition RsFromC := STRUCT {
                            "child" :: Child;
                            "addr" :: Addr;
                            "to" :: Msi;
                            "data" :: Data
                          }.

  Variable LgCRqSz: nat.
  Definition CRqState := Bit 2.
  Definition Empty := 0.
  Definition Init := 1.
  Definition WaitSt := 2.

  Definition CRqEntry := STRUCT {
                             "state" :: CRqState;
                             "rq" :: RqFromC
                           }.
  
  Definition CRqArray := Vector CRqEntry LgCRqSz.

  Definition DataArray := Vector Line IdxBits.

  Definition Dir := Vector Msi LgNumChildren.
  
  Definition Dirw := Vector Bool LgNumChildren.
  
  Definition DirArray := Vector Dir IdxBits.

  Section WithVar.
    Variable var: Kind -> Type.

  Definition toCompat (x: var Msi): (Msi @ var)%kami :=
    (IF (#x == $ Mod)
     then $ Inv
     else (IF (#x == $ Sh)
           then $ Sh
           else $ Mod))%kami.

    Variable searchAddr: var CRqArray -> var Addr -> (Bool @ var)%kami.

    Variable findIncompat: var Child -> var Dir -> var Dirw -> var Msi -> ((Maybe Child) @ var)%kami.

    Definition isCompat (x y: var Msi) := (#x <= toCompat y)%kami.
  End WithVar.

  Definition dirInit: ConstT Dir := ConstVector (replicate (ConstBit (natToWord _ Inv)) _).
  Definition dirArrayInit: ConstT DirArray := ConstVector (replicate dirInit _).

  Definition DirDirw := STRUCT {
                            "dir" :: Dir;
                            "dirw" :: Dirw
                          }.
  Definition rqFromCPop := MethodSig "reqFromC.pop" (DirDirw): RqFromC.
  Definition cRqsIns := MethodSig "cRqs.ins" (RqFromC): Void.
  
  Definition Mem: Modules.
    refine (MODULE {
        Register "dir": DirArray <- dirArrayInit
        with Register "data" : DataArray <- Default

        with Rule "cTransfer" :=
          (* Call rq <- rqFromCPop();
          Call cRqsIns(rq); *)
          LET x: SyntaxKind RqFromC <- $$ Default;
        _
          Retv
              }).
    apply Retv.
    
  Print Mem.
End CoherentMemory.