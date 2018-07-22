Require Import Omega NatLib Kami Kami.Ex.ExpressionsTutorial.
Import Phoas.

(* Your job in this exercise is to implement and verify a static analysis that
 * computes a bound on how large of a result a program may generate.
 * This basic fact about word addition may come in handy. *)
Lemma wplus_bound : forall n (w1 w2 : word n),
    (#(w1 ^+ w2) <= #w1 + #w2)%nat.
Proof.
  intros.
  rewrite wplus_alt.
  unfold wplusN, wordBinN.
  apply wordToNat_natToWord_le.
Qed.

(* Let's consider expressions with two free variables each.
 * Here is a type formalizing that concept for the standalone PHOAS expression
 * type that we developed in lecture. *)
Definition Expr2 n := forall var, var n -> var n -> expr var n.

(* This predicate captures well-formedness of such expressions. *)
Definition Expr2Wf {n} (E : Expr2 n) :=
  forall var1 var2 x1 x2 y1 y2,
    equiv [{| val1 := x1; val2 := x2 |};
             {| val1 := y1; val2 := y2 |}]%list
          (E var1 x1 y1) (E var2 x2 y2).

(* Given word values for the two free variables, it is easy to compute an
 * expression's denotation. *)
Definition Interp2 {n} (E : Expr2 n) (w1 w2 : word n) : word n :=
  interp (E word w1 w2).

(* Your first job is to implement this function, which, given a [nat] upper
 * bound for each of the two free variables, computes an upper bound for the
 * whole expression.  You could, of course, always return [2^n-1], but where
 * would the fun be in that?  We are interested in more precise bounds. *)
Parameter UpperBound2 : forall {n}, Expr2 n -> nat -> nat -> nat.

(* The following theorem should be provable. *)
Theorem UpperBound2_ok : forall n (E : Expr2 n) (w1 w2 : word n) (bound1 bound2 : nat),
    Expr2Wf E
    -> (wordToNat w1 <= bound1)%nat
    -> (wordToNat w2 <= bound2)%nat
    -> (wordToNat (Interp2 E w1 w2) <= UpperBound2 E bound1 bound2)%nat.
Proof.
Admitted.


(** * Hints *)

(* Note how we enclose expressions in parentheses with [%nat] afterward, to
 * trigger resolution of operators like [<=] for [nat] instead of [word]. *)

(* You may find it helpful to use the division operator [/] in your bounds
 * function. *)

(* Some of the tightest bounds require pulling constructor implicit arguments
 * out of patterns.  Put [@]s in front of constructors to let you bind names for
 * any of their arguments, even implicit ones. *)

(* A good number of library theorems will be helpful.  Use this two-step recipe
 * to find them.
 * 1) Decide which identifiers and operators are likely to appear in the ideal
 *    theorem for your circumstance.
 * 2) Use commands like [Locate ".".] to find which identifiers operators expand
 *    into.  Some operators are overloaded, so check for the expansion that goes
 *    with the appropriate notation scope.
 * 3) Now you have a list of just identifiers that are relevant.  Use commands
 *    like [SearchAbout wplus wordToNat.] to find library theorems that mention
 *    all of those identifiers. *)

(* Our solution uses the [etransitivity] tactic a few times. *)

(* We also use [pose proof (pow2_zero n)] to remind Coq that [2^n > 0], after
 * which the trusty [omega] tactic can discharge some goals.  However, [omega]
 * only does linear arithmetic, and most likely some of the arithmetic will be
 * nonlinear, calling for a more manual approach appealing to library
 * theorems. *)
