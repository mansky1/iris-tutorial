From iris.base_logic Require Import iprop.
From iris.proofmode Require Import proofmode.

(* ################################################################# *)
(** * Basics of Iris *)

(* ================================================================= *)
(** ** Introduction *)

(** In this chapter, we introduce basic separation logic in Iris. *)

(* ================================================================= *)
(** ** Iris in Rocq *)

(**
  The type of propositions in Iris is [iProp Σ]. All proofs in Iris are
  performed in a context with a [Σ: gFunctors], used to specify
  available resources. The details of [Σ] will come later when we
  introduce resource algebras. For now, just remember to work inside a
  section with a [Σ] in its context. Keep in mind that [Σ] has type
  [gFunctors] plural, not [gFunctor] singular. There is a coercion from
  gFunctor to gFunctors, so if you accidentally use [gFunctor] everything
  will seem to work until [Σ] becomes relevant.
*)
Section proofs.
Context {Σ: gFunctors}.

(**
  The theorems we can prove in Iris have the form [P ⊢ Q] (type \vdash), saying that
  the separation logic assertion [P] implies the assertion [Q].

  Iris is built on top of Rocq, and has a custom interface called the
  Iris Proof Mode (IPM). IPM has its own versions of basic Rocq tactics,
  which maintain a new context, called the spatial context, in
  addition to the usual context, now called the non-spatial context.
  Hypotheses from both contexts can be used to prove the goal.

  The regular Rocq tactics can still be used when we work within the
  non-spatial context, but, in general, we shall use the new tactics that
  work natively with the spatial context. These new tactics start with
  'i', and since many of them simply 'lift' the regular tactics to also
  work with the spatial context, they borrow the regular names but with
  the 'i' prefixed. For instance, instead of [intros H] we use
  [iIntros "H"], and instead of [apply H] we use [iApply "H"]. Note that
  identifiers for hypotheses in the spatial context are strings, instead
  of the usual Rocq identifiers.

  To see this in action we will prove the statement [P ⊢ P], for all
  [P].
*)

Lemma asm (P : iProp Σ) : P ⊢ P.
Proof. 
  (**
    We can begin by introducing [P].
  *)
  iIntros "H".
  (**
    This adds [P] to the spatial context with the identifier ["H"]. To
    finish the proof in Rocq, one would use either [exact] or [apply].
    So in Iris, we use either [iExact] or [iApply].
  *)
  iApply "H".
Qed.

(**
  Iris propositions include many of the usual logical connectives such
  as conjunction [P ∧ Q] (type \and). As such, Iris uses a notation scope to
  overload the usual logical notation in Rocq. This scope is delimited by
  [I] and bound to [iProp Σ]. Hence, you may need to wrap your
  propositions in [(_)%I] to use the notations.
*)
Fail Definition and_fail (P Q : iProp Σ) := P ∧ Q.
Definition and_success (P Q : iProp Σ) := (P ∧ Q)%I.

(**
  Iris uses ssreflect, but we will not assume knowledge of ssreflect
  tactics. As such we will limit the use of ssreflect tactics whenever
  possible. However, ssreflect overrides the definition of [rewrite]
  changing its syntax and behaviour slightly. Notably:
  - No commas between arguments, meaning you have to write
    [rewrite H1 H2] instead of [rewrite H1, H2].
  - [rewrite -H] instead of [rewrite <-H]
  - Occurrences are written in front of the argument
    [rewrite {1 2 3}H] instead of [rewrite H at 1 2 3]
  - Rewrite can unfold definitions as [rewrite /def] which does the
    same as [unfold def]
*)

(* ================================================================= *)
(** ** Basic Separation Logic *)

(**
  The core connective in separation logic is the `separating
  conjunction', written [P ∗ Q] (type \sep or \star), for propositions
  [P] and [Q]. Separating conjunction differs from regular conjunction,
  particularly in its introduction rule:

  [[
        P1 ⊢ Q1⠀⠀⠀⠀⠀⠀P2 ⊢ Q2
        ----------------------
          P1 ∗ P2 ⊢ Q1 ∗ Q2
  ]]

  That is, if we want to prove [Q1 ∗ Q2], we must decide which of our
  owned resources we use to prove [Q1] and which we use to prove [Q2].
  To see this in action, let us prove that separating conjunction is
  commutative.
*)
Lemma sep_comm (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  (**
    To eliminate a separating conjunction we can use the tactic
    [iDestruct] with the usual introduction pattern. However, like
    with [intros], we can use [iIntros] to eliminate directly.
  *)
  iIntros "[HP HQ]".
  (**
    Unlike [∧], [∗] is not idempotent. Specifically, there are Iris
    propositions for which [¬(P ⊢ P ∗ P)]. Because of this, it is
    generally not possible to use [iSplit] to introduce [∗]. The
    [iSplit] tactic would duplicate the spatial context and is therefore
    not available when the context is non-empty.
  *)
  Fail iSplit.
  (**
    Instead, Iris introduces the tactics [iSplitL] and [iSplitR]. These
    allow you to specify how you want to separate your resources to
    prove each subgoal. The hypotheses mentioned by [iSplitL] are given
    to the left subgoal, and the remaining to the right. Conversely for
    [iSplitR].
  *)
  iSplitL "HQ".
  - iApply "HQ".
  - iApply "HP".
Qed.

(**
  Separating conjunction has an analogue to implication which, instead
  of introducing the antecedent to the assumptions with conjunction,
  introduces it with separating conjunction. This connective is written
  as [P -∗ Q] and pronounced `magic wand' or simply `wand'. Separation
  is so widely used that [P -∗ Q] is treated specially; instead of
  writing [P ⊢ Q], we can write [P -∗ Q], with the [⊢] being implicit.
  That is, [⊢ P -∗ Q] is notationally equivalent to [P -∗ Q].

  Writing a wand instead of entailment makes currying more natural. Here
  is the Iris version of modus ponens. It is provable using only
  [iIntros] and [iApply].
*)
Lemma modus_ponens (P Q : iProp Σ) : P -∗ (P -∗ Q) -∗ Q.
Proof.
  (* exercise *)
Admitted.

(**
  Just as with Rocq tactics, Iris allows nesting of introduction
  patterns. In fact, like Rocq, Iris supports patterns of the form
  [(H1 & .. & H2 & H3)] as a shorthand for [[H1 .. [H2 H3] ..]].

  Exercise: try to use an introduction with a pattern of parentheses to
  prove associativity for [∗]. Note that [∗] is right-associative, so
  [P ∗ Q ∗ R] is parsed as [P ∗ (Q ∗ R)].
*)
Lemma sep_assoc_1 (P Q R : iProp Σ) : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R.
Proof.
  (* exercise *)
Admitted.

(**
  Manually splitting a separation can become tedious. To alleviate this,
  we can use the [iFrame] tactic. This tactic pairs up hypotheses with
  pieces of a separation sequence. Its full use is described in

  <<https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md?ref_type=heads#separation-logic-specific-tactics>>

*)
Lemma sep_comm_v2 (P Q : iProp Σ) : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "H".
  iDestruct "H" as "[HP HQ]".
  iFrame.
Qed.

(**
  Bi-entailment of Iris propositions is denoted [P ⊣⊢ Q]. It is an
  equivalence relation, and most connectives preserve this relation. It
  is encoded using the setoid library with the typeclass [Proper]. It is
  therefore possible to use the [rewrite] tactic inside the Iris Proof
  Mode. Bi-entailment is defined as [(P -∗ Q) ∧ (Q -∗ P)], so it can be
  decomposed using the [iSplit] tactic.

  For hypotheses with multiple curried wands, it is necessary to specify
  how to split the Iris context during application. This can be done as
  [iApply ("H" with "[H1 H2 H3] [H4 H5]")]. Each set of square brackets
  specifies the part of the context going to that argument. Let us
  consider a specific example.
*)

Lemma wand_adj_1 (P Q R : iProp Σ) : (P -∗ Q -∗ R) ∗ P ∗ Q ⊢ R.
Proof.
  iIntros "H".
  iDestruct "H" as "(H & HP & HQ)".
  (**
    When applying ["H"], we get the subgoals [P] and [Q]. To specify that
    we want to use ["HP"] to prove the first subgoal, and ["HQ"] the second,
    we add ["HP"] in the first square bracket, and ["HQ"] in the second.
  *)
  iApply ("H" with "[HP] [HQ]").
  - iApply "HP".
  - iApply "HQ".
Qed.

(**
  Hypotheses that fit arguments exactly can be supplied directly without
  a square bracket to avoid trivial subgoals, as in the above. Try this
  in the following exercise.
*)
Lemma wand_adj (P Q R : iProp Σ) : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  iSplit.
  (* exercise *)
Admitted.

(**
  Disjunctions [∨] are treated just like disjunctions in Rocq. The
  introduction pattern [[ _ | _ ]] allows us to eliminate a disjunction,
  while the tactics [iLeft] and [iRight] let us introduce them.

  Prove that disjunction commutes.
*)
Lemma or_comm (P Q : iProp Σ) : Q ∨ P ⊢ P ∨ Q.
Proof.
  (* exercise *)
Admitted.

(**
  We can even prove the usual elimination rule for or-elimination
  written with separation. This version is, however, not very useful, as
  it does not allow the two cases to share resources.
*)
Lemma or_elim (P Q R : iProp Σ) : (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R.
Proof.
  (* exercise *)
Admitted.

(**
  Separating conjunction distributes over disjunction (for the same
  reason as ordinary conjunction).
*)
Lemma sep_or_distr (P Q R : iProp Σ) : P ∗ (Q ∨ R) ⊣⊢ P ∗ Q ∨ P ∗ R.
Proof.
  (* exercise *)
Admitted.

(**
  Iris has existential and universal quantifiers over any Rocq type.
  Existential quantifiers are proved using the [iExists] tactic, using
  the same syntax as for [exists]. Elimination of existentials is done
  through the pattern ["[%_ _]"] or as part of a ["(_&..&_)"] with a [%]
  in front of the existential variable. (type \exists)
*)
Lemma sep_ex_distr {A} (P : iProp Σ) (Φ : A → iProp Σ) :
  (P ∗ ∃ x, Φ x) ⊣⊢ ∃ x, P ∗ Φ x.
Proof.
  iSplit.
  - iIntros "H".
    iDestruct "H" as "(HP & %x & HΦ)".
    iExists x.
    iFrame.
  - (* exercise *)
Admitted.

(**
  Likewise, forall quantification works almost as in Rocq. To introduce
  universally quantified variables, you can either use [iIntros (x y z)]
  or [iIntros "%x %y %z"]. These patterns are interchangeable. To
  specify the parameters of hypotheses, we write
  [iApply ("H" $! x y z)]. (type \forall)
*)
Lemma sep_all_distr {A} (P Q : A → iProp Σ) :
  (∀ x, P x) ∗ (∀ x, Q x) -∗ (∀ x, P x ∗ Q x).
Proof.
  (* exercise *)
Admitted.

End proofs.

(* For documentation of the various Iris tactics and their arguments, see
   https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md. *)