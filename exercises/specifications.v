From iris.heap_lang Require Import lang proofmode notation par.

(* ################################################################# *)
(** * Specifications *)

(* ================================================================= *)
(** ** Introduction *)

(**
  Now that we have seen basic separation logic in Iris and introduced a
  suitable language, HeapLang, we are finally ready to start reasoning
  about programs. HeapLang ships with a program logic defined using
  Iris. We can access the logic through the [proofmode] package, which
  also defines tactics to alleviate working with the logic. The logic
  provides constructs that allow us to specify the behaviour of HeapLang
  programs. These specifications can then be proven by using rules
  associated with the constructs. The tactics provided by the
  [proofmode] package essentially just apply these rules.

  The program logic for HeapLang relies on a basic notion of a resource
  – the resource of heaps. Recall that [Σ] specifies the available
  resources. To make the resource of heaps available, we have to specify
  that [Σ] should contain it. The typeclass [heapGS] does exactly this.
  Using [heapGS] and the [Context] command, we can assume that [Σ]
  contains the resource of heaps throughout the [specifications]
  section.
*)

Section specifications.
Context `{!heapGS Σ}.

(* ================================================================= *)
(** ** Hoare Triples and Weakest Preconditions *)

(**
  How do we state the correctness of a program? One common way is with a pre-
  and postcondition, e.g., with a Hoare triple [{ P } e { Q }], which says
  that if we start with resources [P], we can run [e] and end in a state with
  resources [Q]. In Iris, this is a derived form built out of several pieces:
  "we can run [e] and end in a state with resources [Q]" is an assertion
  [WP e {{ Q }}], and the Hoare triple is defined as [P ⊢ WP e {{ Q }}].
  (WP stands for "weakest precondition", i.e., "we have enough resources to run
  [e] and prove [Q] but no more.") To make triples easier to apply as lemmas,
  Iris also quantifies over all possible postconditions implied by [Q] (we will
  see this concretely in the coming examples).

  The full syntax for Hoare triples is as follows:
    [{{{ P }}} e {{{ r0 .. rn, RET v; Q v }}}]
  - [P]: the precondition that is assumed to hold before the program runs.
  - [e]: the program to run.
  - [r0 .. rn]: optional, forall quantified variables used for abstract
    return values.
  - [v]: the return value.
  - [Q]: the postcondition which holds after the program terminates.

  Formally, this syntax is defined as

    [□( ∀ Φ, P -∗ ▷ (∀ r0 .. rn, Q -∗ Φ v) -∗ WP e {{v, Φ v }})]

  For any desired postcondition [Φ], if we have the precondition [P], and
  [Φ] follows from the postcondition [Q], then we have enough resources to
  run [e] and conclude [Φ] at the end. The modalities [□] and [▷] can be
  ignored for now.
*)

Example arith : expr :=
  #1 + #2 * #3 + #4 + #5.

(**
  What specifications does this program meet? There are several:
  * it runs without crashing
  * it returns a number
  * it returns specifically the number 16
  We can express each of these in separation logic as Hoare triples:
  {{{ True }}} arith {{{ RET v; True }}}
  {{{ True }}} arith {{{ z : Z, RET #z; True }}}
  {{{ True }}} arith {{{ RET #16; True }}}
    (or equivalently, {{{ True }}} arith {{{ v, RET v; ⌜v = #16⌝ }}})
  All of these are provable; the last one is the *strongest*, since it gives
  the most information about [arith].
*)

Lemma arith_spec : {{{ True }}} arith {{{ RET #16; True }}}.
Proof.
  (** Because of the structure of the Hoare triple definition, we will always
    begin by introducing three pieces: the arbitrary postcondition [Φ] (a pure
    variable), the precondition, and the "postcondition implication" saying
    that we can prove [Φ] by proving the function's postcondition. *)
  iIntros "%Φ H HΦ".
  (** Now our goal is a WP assertion. *)
  rewrite /arith.
  (**
    To prove this weakest precondition, we can use the tactics provided
    by [proofmode]. The initial step of the program is to multiply [#2]
    by [#3]. The tactic [wp_op] symbolically executes this expression
    using the underlying rules of the logic.
  *)
  wp_op.
  (**
    Note that the expression [#2 * #3] turned into [#(2 * 3)] – the Rocq
    expression [2 * 3] is treated as a value in HeapLang.

    Under the hood, [wp_op] pulled out the next sub-expression to be
    evaluated (in this case #2 * #3), evaluated it, and put the resulting
    value in its place.
    
    The next step of the program is
    to add [#1] to [#(2 * 3)]. We could again use [wp_op] to
    symbolically execute this, but instead, we shall use the [wp_pure]
    tactic. This tactic can symbolically execute any pure expression.
  *)
  wp_pure.
  (**
    If there are several pure steps in a row, we can use the [wp_pures]
    tactic, which repeatedly applies [wp_pure].
  *)
  wp_pures.
  (**
    When the expression in a weakest precondition turns into a value,
    the goal becomes proving the postcondition with said value
    (essentially applying wp-val). Technically, the goal is to prove the
    postcondition behind a `fancy update modality'. This functionality
    is related to resources and invariants, so we skip it for now. We
    can always remove a fancy update modality in the goal with
    [iModIntro].
  *)
  iModIntro.
  (** Now we must prove the arbitrary postcondition [Φ]; the only way to
    do this is by using the implication [HΦ], i.e., proving the postcondition
    we wrote in the specification. *)
  iApply "HΦ".
  done.
Qed.

(** Let's try another example. *)
Definition arith2 : expr :=
  let: "x" := #1 + #2 * #3 in
  let: "y" := #4 * #5 in
  "y" - "x".

Lemma arith2_spec : {{{ True }}} arith2 {{{ RET #13; True }}}.
Proof.
  (* exercise *)
Admitted.

(* ================================================================= *)
(** ** Resources *)

(**
  In this section, we introduce our first notion of a resource: the
  resource of heaps. As mentioned in basics.v, propositions in Iris
  describe/assert ownership of resources. To describe resources in the
  resource of heaps, we use the `points-to' predicate, written [l ↦ v]
  (type \mapsto). Intuitively, this describes all heap fragments that have
  value [v] stored at location [l]. The proposition [l1 ↦ #1 ∗ l2 ↦ #2]
  then describes all heap fragments that map [l1] to [#1] and [l2] to [#2].

  To see this in action, let us consider a simple program.
*)
Definition prog : expr :=
  (** Allocate the number [1] on the heap *)
  let: "x" := ref #1 in
  (** Increment [x] by [2] *)
  "x" <- !"x" + #2;;
  (** Read the value of [x] *)
  !"x".

(**
  This program should evaluate to [3]. We express this with a Hoare triple.
*)
Lemma prog_spec : {{{ True }}} prog {{{ RET #3; True }}}.
Proof.
  iIntros "%Φ H HΦ".
  rewrite /prog.
  (**
    The initial step of [prog] is to allocate a reference containing the
    value [1]. We can symbolically execute this step of [prog] using the
    [wp_alloc] tactic. As a result of the allocation, we get the
    existence of some location [l] which points-to [1], [l ↦ #1]. The
    [wp_alloc] tactic requires that we give names to the location and the
    proposition.
  *)
  wp_alloc l as "Hl".
  (**
    The next step of [prog] is a let expression which we symbolically
    execute with [wp_let].
  *)
  wp_let.
  (**
    Next, we load from location [l]. Loading from a location requires
    the associated points-to predicate in the context. The predicate
    then governs the result of the load. Since we have [Hl], we can
    perform the load using the [wp_load] tactic.
  *)
  wp_load.
  (** Then we evaluate the addition. *)
  wp_op.
  (**
    Storing is handled by [wp_store]. As with loading, we must have the
    associated points-to predicate in the context. [wp_store] updates
    the points-to predicate to reflect the store.
  *)
  wp_store.
  (** Finally, we use [wp_load] again. *)
  wp_load.
  (** Now we are left with a trivial proof that [1 + 2 = 3]. *)
  iModIntro.
  iApply "HΦ".
  done.
Qed.

(**
  We finish this section with a final remark about the points-to
  predicate. One of its essential properties is that it is not
  duplicable. That is, for every location [l], there can only exist one
  points-to predicate associated with it [l ↦ v]. This is captured by
  the following lemma.
*)
Lemma pt_not_dupl (l : loc) (v v' : val) : l ↦ v ∗ l ↦ v' ⊢ False.
Proof.
  (**
    The proof of this lemma is not important here. It relies on details
    of the underlying implementation of the resource of heaps. We will
    return to this when we treat resources in general later in the
    tutorial.
  *)
  iIntros "[Hlv Hlv']".
  iCombine "Hlv Hlv'" gives "[%H _]".
  contradiction.
Qed.

(* ================================================================= *)
(** ** Composing Programs and Proofs *)

(**
  Let us use the specification we proved for [prog] in the previous
  section to prove a specification for a larger program.
*)
Lemma prog_add_2_spec : {{{ True }}} prog + #2 {{{ RET #5; True }}}.
Proof.
  iIntros "%Φ H HΦ".
  (**
    The first part of this program is to evaluate [prog]. We already
    have a specification that tells us how this sub-expression behaves:
    [prog_spec]. We can apply a previously proved specification with the
    [wp_apply] tactic. Note that we apply the *specification* lemma, not
    the program itself; [wp_apply prog] will cause Rocq to hang or crash.
  *)
  wp_apply prog_spec.
  (** This does two things: asks us to prove the precondition of [prog],
    and replaces [prog] with its postcondition from [prog_spec]. *)
  { done. }
  (** Now [prog] has been replaced with its return value #3, and we have
    its postcondition resources [True]. *)
  iIntros "Hpost".
  (** And now we can evaluate the rest of the program. *)
  wp_pure.
  iApply "HΦ".
  done.
Qed.

(* ================================================================= *)
(** ** Working with Preconditions *)

(**
  Consider a function that swaps two values.
*)

Definition swap : val :=
  λ: "x" "y",
  let: "v" := !"x" in
  "x" <- !"y";;
  "y" <- "v".

(** We will use a Hoare triple to specify this program's behaviour. *)
Lemma swap_spec (l1 l2 : loc) (v1 v2 : val) :
  {{{ l1 ↦ v1 ∗ l2 ↦ v2 }}}
    swap #l1 #l2
  {{{ RET #(); l1 ↦ v2 ∗ l2 ↦ v1 }}}.
(** Note that [()] is a "nothing" value for functions that don't return
  a value. *)
Proof.
  iIntros "%Φ H HΦ".
  iDestruct "H" as "[H1 H2]".
  (** We can now prove the specification as we have done previously. *)
  rewrite /swap.
  wp_pures.
  wp_load.
  wp_load.
  wp_store.
  wp_store.
  iApply "HΦ".
  by iFrame.
Qed.

(**
  Since Hoare triples are generic in the postcondition `under the hood',
  specifications written using Hoare triples can be easily used by
  clients, as demonstrated in the previous section. We demonstrate it
  here again with a client of [swap].
*)
Lemma swap_swap_spec (l1 l2 : loc) (v1 v2 : val) :
  {{{ l1 ↦ v1 ∗ l2 ↦ v2 }}}
    swap #l1 #l2;; swap #l1 #l2
  {{{ RET #(); l1 ↦ v1 ∗ l2 ↦ v2 }}}.
Proof.
  iIntros "%Φ H HΦ".
  wp_apply (swap_spec with "H").
  iIntros "H".
  wp_seq.
  wp_apply (swap_spec with "H").
  done.
Qed.

(** More practice: Here is a program that adds 3 to a memory location.
*)

Definition add3 : val :=
  λ: "x",
  let: "v" := !"x" in
  "x" <- "v" + #3.

(** Exercise: Write a specification (i.e., a Hoare triple) that add3 satisfies,
  and prove it. *)

(* ================================================================= *)
(** ** Concurrency *)

(**
  We finish this chapter with a final example that utilises the theory
  presented in the previous sections. The example gives a specification
  for a concurrent program, which illustrates how ownership of resources
  (in particular points-to predicates) can be transferred between
  threads. The program is as follows.
*)

Example par_client : expr :=
  let: "l1" := ref #0 in
  let: "l2" := ref #0 in
  (("l1" <- #21) ||| ("l2" <- #2)) ;;
  let: "life" := !"l1" * !"l2" in
  ("l1", "l2", "life").

(**
  The program uses parallel composition (e1 ||| e2) from the [par]
  package. Note that the two threads operate on separate locations;
  there is no possibility for a data race.

  The [par] package provides a specification for parallel composition
  called [wp_par]. The specification is as follows.

  [[
  ∀ (Ψ1 Ψ2 : val → iProp Σ) (e1 e2 : expr) (Φ : val → iProp Σ),
    WP e1 {{ Ψ1 }} -∗
    WP e2 {{ Ψ2 }} -∗
    (∀ v1 v2, (Ψ1 v1) ∗ (Ψ2 v2) -∗ ▷ Φ (v1, v2)) -∗
    WP (e1 ||| e2) {{ Φ }}
  ]]

  Essentially, to prove a weakest precondition of parallel composition
  [WP (e1 ||| e2) {{ Φ }}], one must prove a weakest precondition for
  each of the threads, [WP e1 {{ Ψ1 }}] and [WP e2 {{ Ψ2 }}], and show
  that all pairs of values that satisfy the postconditions [Ψ1] and [Ψ2]
  respectively, also satisfy the postcondition of the weakest
  precondition we wish to prove [Φ]. Note that the specification uses
  the `later' modality [▷]. This is not needed for our current purposes,
  so it can safely be ignored. We cover the later modality later.
*)

(**
  The [wp_par] specification relies on a notion of resources different
  from the resource of heaps. The details of the resources are
  irrelevant for our example, but we must still assume that [Σ] contains
  the resources.
*)

Context `{!spawnG Σ}.

(**
  Let us now return to our [par_client] example. We specify the
  behaviour of [par_client] with a Hoare triple.
*)

Lemma par_client_spec :
  {{{ True }}}
    par_client
  {{{ l1 l2 life, RET (#l1, #l2, #life); l1 ↦ #21 ∗ l2 ↦ #2 ∗ ⌜life = 42⌝ }}}.
Proof.
  iIntros (Φ _) "HΦ".
  rewrite /par_client.
  (**
    The program starts by creating two fresh locations, [l1] and [l2].
  *)
  wp_alloc l1 as "Hl1".
  wp_let.
  wp_alloc l2 as "Hl2".
  wp_let.
  wp_pures.
  (**
    The specification for [par] requires us to specify the
    postconditions for the two threads. Since the threads return unit,
    the postconditions will just describe the points-to predicates,
    reflecting the writes.
  *)
  set t1_post := (λ v : val, (l1 ↦ #21)%I).
  set t2_post := (λ v : val, (l2 ↦ #2)%I).
  (**
    We can now apply the [wp_par] specification. Note how we transfer
    ownership of [l1 ↦ #0] to the first thread, and [l2 ↦ #0] to the
    second. This allows each thread to perform its store operation.
  *)
  wp_apply (wp_par t1_post t2_post with "[Hl1] [Hl2]").
  (**
    We must now prove WP specifications for each thread, with the
    postconditions we specified above.
  *)
  { wp_store. by iFrame. }
  { wp_store. by iFrame. }
  (**
    Finally, we return to the main thread, and we are allowed to assume
    the postconditions of both threads. Since the postconditions
    mentioned the points-to predicates, these are essentially
    transferred back to the main thread.
  *)
  iIntros (r1 r2) "[Hl1 Hl2]".
  rewrite /t1_post /t2_post.
  (**
    Note: the [wp_par] specification adds a later modality [▷] to the
    goal. This actually strengthens [wp_par], but we do not need that
    strength in this example, so we can simply ignore it. The [▷] can be
    introduced with [iNext].
  *)
  iNext.
  wp_seq.
  wp_load.
  wp_load.
  wp_pures.
  iApply ("HΦ" $! l1 l2 (21 * 2)).
  by iFrame.
Qed.

(**
  Food for thought: Imagine a program that has threads operating on the
  _same_ location in parallel, akin to the following.
*)
Example race (l : loc) : expr := ((#l <- #1) ||| (#l <- #2)).

(**
  Even though the program is non-deterministic, we can still give it a
  meaningful specification.
*)
Definition race_spec (l : loc) (v : val) :=
  {{{ l ↦ v }}} race l {{{ w, RET w; (l ↦ #1) ∨ (l ↦ #2) }}}.

(**
  Could we prove this specification similarly to how we proved
  [par_client]?
*)

End specifications.
