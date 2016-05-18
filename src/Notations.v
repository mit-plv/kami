Require Import Bool List String.
Require Import Lib.Struct.
Require Import Lts.Syntax Lts.MetaSyntax.

Set Implicit Arguments.

(** * Notation for meta-modules *)

Inductive MetaModuleElt :=
| MMERegister (_ : MetaReg)
| MMERule (_ : MetaRule)
| MMEMeth (_ : MetaMeth).

Inductive InMetaModule :=
| NilInMetaModule
| ConsInMetaModule (_ : MetaModuleElt) (_ : InMetaModule).

Fixpoint makeMetaModule (im : InMetaModule) :=
  match im with
  | NilInMetaModule => {| metaRegs:= nil;
                          metaRules:= nil;
                          metaMeths:= nil |}
  | ConsInMetaModule e i =>
    let '(Build_MetaModule iregs irules imeths) := makeMetaModule i in
    match e with
    | MMERegister mreg => Build_MetaModule (mreg :: iregs) irules imeths
    | MMERule mrule => Build_MetaModule iregs (mrule :: irules) imeths
    | MMEMeth mmeth => Build_MetaModule iregs irules (mmeth :: imeths)
    end
  end.

Definition makeConst k (c: ConstT k): ConstFullT (SyntaxKind k) := SyntaxConst c.
Notation DefaultFull := (makeConst Default).

Notation "'Register' name : type <- init" :=
  (MMERegister (One (Build_Attribute name (existT ConstFullT (SyntaxKind type) (makeConst init)))))
  (at level 0, name at level 0, type at level 0, init at level 0) : kami_action_scope.

Notation "'Repeat' 'Register' 'as' i 'till' n 'by' name : type <- init" :=
  (MMERegister (Rep name (fun i => (makeConst (k:= type) init)) n))
    (at level 0, name at level 0, type at level 0, init at level 0) : kami_action_scope.

Notation "'RegisterN' name : type <- init" :=
  (MMERegister (One (Build_Attribute name (existT ConstFullT (type) (init)))))
  (at level 0, name at level 0, type at level 0, init at level 0) : kami_action_scope.

Notation "'Method' name () : retT := c" :=
  (MMEMeth (One (Build_Attribute name (existT MethodT {| arg := Void; ret := retT |}
                                              (fun ty => fun _ : ty Void => (c)%kami : ActionT ty retT)))))
    (at level 0, name at level 0) : kami_action_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (MMEMeth (One (Build_Attribute name (existT MethodT {| arg := dom; ret := retT |}
                                              (fun ty => fun param : ty dom => (c)%kami : ActionT ty retT)))))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_action_scope.

Notation "'Repeat' 'Method' 'as' i 'till' n 'by' name () : retT := c" :=
  (MMEMeth (Rep name (fun i => (existT MethodT {| arg:= Void; ret:= retT |}
                                       (fun ty (_: ty Void) => c%kami))) n))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_action_scope.

Notation "'Repeat' 'Method' 'as' i 'till' n 'by' name ( param : dom ) : retT := c" :=
  (MMEMeth (Rep name (fun i => (existT MethodT {| arg:= dom; ret:= retT |}
                                       (fun ty (param: ty dom) => c%kami))) n))
    (at level 0, name at level 0, param at level 0, dom at level 0) : kami_action_scope.

Notation "'Rule' name := c" :=
  (MMERule (One (Build_Attribute name (fun ty => c%kami : ActionT ty Void))))
    (at level 0, name at level 0) : kami_action_scope.

Notation "'Repeat' 'Rule' 'as' i 'till' n 'by' name := c" :=
  (MMERule (Rep name (fun i => fun ty => c%kami : ActionT ty Void) n))
    (at level 0, name at level 0) : kami_action_scope.

Delimit Scope kami_action_scope with action.

Notation "'MODULE' { m1 'with' .. 'with' mN }" :=
  (makeModule (makeMetaModule (ConsInMetaModule m1%action .. (ConsInMetaModule mN%action NilInMetaModule) ..))) (at level 0, only parsing).

Notation "'META' { m1 'with' .. 'with' mN }" :=
  (makeMetaModule (ConsInMetaModule m1%action .. (ConsInMetaModule mN%action NilInMetaModule) ..)) (at level 0, only parsing).

