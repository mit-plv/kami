Require Import Bool List String Omega.
Require Import Lib.FMap Lib.Struct.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.ModularFacts Kami.Wf.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Checklist
 * 0) Is below the best design for proving contextual trace refinement?
 * 1) Is the relation between amortization and context correct?
 * 2) Is it possible to apply this concept to real processor proofs?
 *)

Section AboutCertainCall.
  Variable f: string.

  Definition EquivalentLabelWithout l1 l2 :=
    defs l1 = defs l2 /\
    M.complement (calls l1) [f] = M.complement (calls l2) [f] /\
    match annot l1, annot l2 with
    | Some _, Some _ => True
    | None, None => True
    | _, _ => False
    end.

  Fixpoint EquivalentLabelSeqWithout ll1 ll2 :=
    match ll1, ll2 with
    | nil, nil => True
    | l1 :: ll1', l2 :: ll2' =>
      EquivalentLabelWithout l1 l2 /\
      EquivalentLabelSeqWithout ll1' ll2'
    | _, _ => False
    end.

  Definition Amortization := list {x : SignatureT & SignT x}.

  Definition amortize (l1 l2: LabelT) (am: Amortization): option Amortization :=
    match M.find f (calls l1), M.find f (calls l2) with
    | Some av1, Some av2 => if signIsEq av1 av2 then Some am else None
    | Some av1, None => Some (av1 :: am)
    | None, Some av2 =>
      match am with
      | nil => None
      | a :: am' => if signIsEq av2 a then Some am' else None
      end
    | None, None => Some am
    end.
    
  Inductive AmortizedLabelSeqWith: LabelSeqT -> LabelSeqT -> Amortization -> Prop :=
  | AmortizedNil: forall am, AmortizedLabelSeqWith nil nil am
  | AmortizedCons:
      forall l1 l2 ll1 ll2 am,
        AmortizedLabelSeqWith ll1 ll2 am ->
        forall am',
          Some am' = amortize l1 l2 am ->
          AmortizedLabelSeqWith (l1 :: ll1) (l2 :: ll2) am'.

End AboutCertainCall.

Fixpoint IntactAction {retT} (a: ActionT typeUT retT): Prop :=
  match a with
  | MCall _ _ _ _ => False
  | Let_ fk _ cont => IntactAction (cont match fk as fk' return fullType typeUT fk' with
                                         | SyntaxKind _ => tt
                                         | NativeKind _ c' => c'
                                         end)
  | ReadReg _ fk cont => IntactAction (cont match fk as fk' return fullType typeUT fk' with
                                            | SyntaxKind _ => tt
                                            | NativeKind _ c' => c'
                                            end)
  | WriteReg _ _ _ cont => IntactAction cont
  | IfElse _ _ _ _ cont => IntactAction (cont tt)
  | Assert_ _ cont => IntactAction cont
  | Return _ => True
  end.

Section TwoModules.
  Variables (m1 m2: Modules).

  Hypotheses (Hwf1: ModEquiv type typeUT m1)
             (Hwf2: ModEquiv type typeUT m2)
             (Hvr1: ValidRegsModules type m1)
             (Hvr2: ValidRegsModules type m2).

  (* Hypothesis (Hdefs: SubList (getDefs m2) (getDefs m1)) *)
  (*            (Hcalls: SubList (getCalls m2) (getCalls m1)). *)

  Definition traceRefinesAmortized f :=
    forall s1 sig1,
      Behavior m1 s1 sig1 ->
      exists s2 sig2, Behavior m2 s2 sig2 /\
                      EquivalentLabelSeqWithout f sig1 sig2 /\
                      exists am, AmortizedLabelSeqWith f sig1 sig2 am.

  Section Contextual.
    Variable f: string.

    Definition Absorber m :=
      exists dm, getDefsBodies m = [dm] /\
                 attrName dm = f /\
                 IntactAction (projT2 (attrType dm) typeUT tt).

    Definition traceRefinesContextual :=
      forall m,
        Absorber m ->
        (m1 ++ m)%kami <<== (m2 ++ m)%kami.

  End Contextual.
  
  Theorem amortized_implies_contextual:
    forall f, traceRefinesAmortized f -> traceRefinesContextual f.
  Proof.
  Admitted.

End TwoModules.

