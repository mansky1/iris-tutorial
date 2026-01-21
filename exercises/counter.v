From iris.algebra Require Export auth excl frac numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.

(* ################################################################# *)
(** * Case Study: Counter *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us define a simple counter module. Our counter consists of three
  functions:
  - a constructor, [mk_counter], which creates a new counter starting at
    [0].
  - an increment function, [incr], which increments the counter and
    returns the old value of the counter.
  - a read function, [read], which reads the current value of the
    counter.
  Furthermore, we want the counter to be shareable across multiple
  threads, so we will implement [incr] with [CAS] as the synchronisation
  mechanism.
*)

Definition mk_counter : val :=
  λ: <>, ref #0.

Definition incr : val :=
  rec: "incr" "c" :=
  let: "n" := !"c" in
  let: "m" := "n" + #1 in
  if: CAS "c" "n" "m" then "n" else "incr" "c".

Definition read : val :=
  λ: "c", !"c".

(* ================================================================= *)
(** ** Defining a Representation Predicate for the Counter *)

Module spec1.
Section spec1.
Context `{heapGS Σ}.

(**
  We are going to keep the fact that our counter is built on a pointer
  as an implementation detail. Instead, we will define a predicate
  describing when a value is a counter.

  Note that [#n] uses an implicit coercion from [nat] to [Z] called
  [Z.of_nat]. So if you have trouble applying lemmas that should work,
  it is likely because there is a hidden coercion in the way.
*)

Definition is_counter1 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ #n.

(**
  This predicate is, however, not persistent, so our value would not be
  shareable across threads. To fix this, we can put the knowledge into
  an invariant.
*)

Let N := nroot .@ "counter".

Definition is_counter2 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (l ↦ #n).

(**
  However, with this definition, we have locked the value of the pointer
  to always be [n]. We need to answer a fundamental question: what can
  one thread know about the value of the counter, given that other threads
  may concurrently increment it?
  One answer is: a thread can know a *lower bound* on the counter's value.
*)

Definition is_counter3 (v : val) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ inv N (∃ m : nat, l ↦ #m ∗ ⌜n ≤ m⌝).

(**
  We can now change what the pointer maps to, but we still cannot refine
  the lower bound.

  The final step is to use ghost state. The idea is to link [n] and [m]
  to pieces of ghost state in such a way that the validity of their
  composite is [n ≤ m].

  To achieve this, we will use the _authoritative_ resource algebra,
  [auth]. This gives us two types of ghost state we can own:
  - [● x] called an authoritative element
  - [◯ y] called a fragment
  The authoritative element represents the current value of the resource,
  while the fragments act as pieces of that value.

  In our case, we will use the authoritative RA over the [max_nat]
  resource algebra. The carrier of [max_nat] is the natural numbers, and
  the operation is the maximum: that is, if we combine two fragments [◯ a]
  and [◯ b], we will obtain the fragment [◯ (max a b)].
*)
Context `{!inG Σ (authR max_natUR)}.

(**
  As such, [● (MaxNat m)] will represent the _true_ value of the counter
  [m], and [◯ (MaxNat n)] will represent a _fragment_ of the counter – a
  lower bound [n] observed by one thread.
*)

Definition is_counter (v : val) (γ : gname) (n : nat) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ MaxNat n) ∗
    inv N (∃ m : nat, l ↦ #m ∗ own γ (● MaxNat m)).

Global Instance is_counter_persistent v γ n :
  Persistent (is_counter v γ n) := _.

(* ================================================================= *)
(** ** Properties of the Authoritative RA with MaxNat *)

(**
  Before we start proving the specification, let us prove some useful
  lemmas about our ghost state. The statements of these lemmas are
  important, but their proofs are not: if you want to understand them
  in detail anyway, you'll need to read resource_algebras.v first.
*)
Lemma alloc_initial_state :
  ⊢ |==> ∃ γ, own γ (● MaxNat 0) ∗ own γ (◯ MaxNat 0).
Proof.
  setoid_rewrite <- own_op.
  apply own_alloc.
  apply auth_both_valid_discrete.
  split.
  - apply max_nat_included; simpl.
    reflexivity.
  - cbv.
    done.
Qed.

Lemma state_valid γ n m :
  own γ (● MaxNat n) -∗
  own γ (◯ MaxNat m) -∗
  ⌜m ≤ n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply max_nat_included in H; cbn in H.
  done.
Qed.

Lemma update_state γ n :
  own γ (● MaxNat n) ==∗
  own γ (● MaxNat (S n)) ∗ own γ (◯ MaxNat (S n)).
Proof.
  iIntros "H".
  rewrite <- own_op.
  iApply (own_update with "H").
  apply auth_update_alloc.
  apply max_nat_local_update; cbn.
  by apply le_S.
Qed.

(* ================================================================= *)
(** ** Proving the Counter Specification *)

(**
  We are finally ready to give and prove specifications for the three
  counter functions. We begin with [mk_counter].
*)

Lemma mk_counter_spec :
  {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0}}}.
Proof.
  (* exercise *)
Admitted.

Lemma read_spec c γ n :
  {{{ is_counter c γ n }}} read c {{{ (u : nat), RET #u; ⌜n ≤ u⌝ }}}.
Proof.
  (* exercise *)
Admitted.

Lemma incr_spec c γ n :
  {{{ is_counter c γ n }}}
    incr c
  {{{ (u : nat), RET #u; ⌜n ≤ u⌝ ∗ is_counter c γ (S n) }}}.
Proof.
  iIntros "%Φ (%l & -> & #Hγ' & #HI) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "HI" as "(%m & Hl & Hγ)".
  wp_load.
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "HI" as "(%m' & Hl & Hγ)".
  destruct (decide (#m = #m')) as [e | ne].
  - wp_cmpxchg_suc.
    injection e as e.
    apply (inj Z.of_nat) in e.
    subst m'.
    (* exercise *)
Admitted.

(* ================================================================= *)
(** ** A Simple Counter Client *)

(**
  To illustrate how this counter specification works, let us consider a
  simple concurrent client of our counter module, which increments a
  counter twice in parallel. Our specification will simply be that the
  value of the counter will be at least [1] afterwards.
*)

Context `{!spawnG Σ}.

Lemma par_incr :
  {{{ True }}}
    let: "c" := mk_counter #() in
    (incr "c" ||| incr "c");;
    read "c"
  {{{ n, RET #(S n); True }}}.
Proof.
  (* exercise *)
Admitted.

End spec1.
End spec1.

(* ================================================================= *)
(** ** A Stronger Counter Specification *)

Module spec2.
Section spec2.

(**
  Our first specification only allowed us to find a lower bound for the
  value in [par_incr]. To do better, we need to go beyond persistent
  ghost state, as we need to aggregate the knowledge to conclude the
  total value.

  So we will try another answer to "what can each thread know": each
  thread can know the number of times *that thread* incremented the
  counter. Then the total counter value is the sum of every thread's
  contribution. To this end, we will use fractions. The resource
  algebra [authR (optionUR (prodR fracR natR))] associates each
  fragment with a fraction; if we collect all the fractions, we know
  that the total fragment value is the same as the authoritative value.
*)

Context `{!heapGS Σ, !inG Σ (authR (optionUR (prodR fracR natR)))}.

Let N := nroot .@ "counter".

Definition is_counter (v : val) (γ : gname) (n : nat) (q : Qp) : iProp Σ :=
  ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ Some (q, n)) ∗
    inv N (∃ m : nat, l ↦ #m ∗ own γ (● Some (1%Qp, m))).

(**
  With this definition, we can now decompose access to the counter by
  splitting the fraction, as well as splitting the knowledge of how much
  the counter has been incremented.
*)
Lemma is_counter_add (c : val) (γ : gname) (n m : nat) (p q : Qp) :
  is_counter c γ (n + m) (p + q) ⊣⊢ is_counter c γ n p ∗ is_counter c γ m q.
Proof.
  iSplit.
  - iIntros "(%l & -> & [Hγ1 Hγ2] & #I)".
    iSplitL "Hγ1".
    + iExists l.
      iSplitR; first done.
      by iFrame.
    + iExists l.
      iSplitR; first done.
      by iFrame.
  - iIntros "[(%l & -> & Hγ1 & I) (%l' & %H & Hγ2 & _)]".
    injection H as <-.
    iExists l.
    iSplitR; first done.
    iCombine "Hγ1 Hγ2" as "Hγ".
    iFrame.
Qed.

(**
  When allocating a new state, there will be _one_ fragment, which
  contains the entire fraction. Using the above lemma, we can then split
  up the fragment and supply these fragments to participating threads.
*)
Lemma alloc_initial_state :
  ⊢ |==> ∃ γ, own γ (● Some (1%Qp, 0)) ∗ own γ (◯ Some (1%Qp, 0)).
Proof.
  setoid_rewrite <-own_op.
  iApply own_alloc.
  apply auth_both_valid_discrete.
  split.
  - reflexivity.
  - apply Some_valid.
    apply pair_valid.
    split.
    + apply frac_valid.
      reflexivity.
    + cbv.
      done.
Qed.

(**
  The fragments of natural numbers add up to the full value, meaning
  that, in particular, they must all be less than or equal to the
  authoritative element.
*)
Lemma state_valid γ (n m : nat) (q : Qp) :
  own γ (● Some (1%Qp, n)) -∗
  own γ (◯ Some (q, m)) -∗
  ⌜m ≤ n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_pair_included in H.
  destruct H as [_ H].
  rewrite Some_included_total in H.
  apply nat_included in H.
  done.
Qed.

(**
  However, when a fragment has the entire fraction, there can't be any
  other fragments – intuitively, we have collected all contributions
  from all threads. So the count stored in the fragment must be equal to
  the one in the authoritative element.
*)
Lemma state_valid_full γ (n m : nat) :
  own γ (● Some (1%Qp, n)) -∗
  own γ (◯ Some (1%Qp, m)) -∗
  ⌜m = n⌝.
Proof.
  iIntros "Hγ Hγ'".
  iPoseProof (own_valid_2 with "Hγ Hγ'") as "%H".
  iPureIntro.
  apply auth_both_valid_discrete in H.
  destruct H as [H _].
  apply Some_included_exclusive in H.
  - destruct H as [_ H]; cbn in H.
    apply leibniz_equiv in H.
    done.
  - apply _.
  - done.
Qed.

(**
  Finally, when we have both the authoritative element and a fragment,
  we can increment both.
*)
Lemma update_state γ n m (q : Qp) :
  own γ (● Some (1%Qp, n)) ∗ own γ (◯ Some (q, m)) ==∗
  own γ (● Some (1%Qp, S n)) ∗ own γ (◯ Some (q, S m)).
Proof.
  iIntros "H".
  rewrite -!own_op.
  iApply (own_update with "H").
  apply auth_update.
  apply option_local_update.
  apply prod_local_update_2.
  apply (op_local_update_discrete _ _ 1).
  done.
Qed.

(**
  Let us prove the specifications for the counter functions again. This
  time, however, we will have two specifications for [read] – one with
  an arbitrary fraction and one with the whole fraction.
*)

Lemma mk_counter_spec :
  {{{ True }}} mk_counter #() {{{ c γ, RET c; is_counter c γ 0 1}}}.
Proof.
  (* exercise *)
Admitted.

Lemma read_spec (c : val) (γ : gname) (n : nat) (q : Qp) :
  {{{ is_counter c γ n q }}}
    read c
  {{{ (u : nat), RET #u; is_counter c γ n q ∗ ⌜n ≤ u⌝ }}}.
Proof.
  (* exercise *)
Admitted.

Lemma read_spec_full (c : val) (γ : gname) (n : nat) :
  {{{ is_counter c γ n 1 }}} read c {{{ RET #n; is_counter c γ n 1 }}}.
Proof.
  (* exercise *)
Admitted.

Lemma incr_spec (c : val) (γ : gname) (n : nat) (q : Qp) :
  {{{ is_counter c γ n q }}}
    incr c
  {{{ (u : nat), RET #u; ⌜n ≤ u⌝ ∗ is_counter c γ (S n) q }}}.
Proof.
  iIntros "%Φ (%l & -> & Hγ' & #I) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_bind (! _)%E.
  iInv "I" as "(%m & Hl & Hγ)".
  wp_load.
  iModIntro.
  iSplitL "Hl Hγ".
  { iExists m. iFrame. }
  wp_pures.
  wp_bind (CmpXchg _ _ _).
  iInv "I" as "(%m' & Hl & Hγ)".
  destruct (decide (# m = # m')).
  - injection e as e.
    apply (inj Z.of_nat) in e.
    subst m'.
    wp_cmpxchg_suc.
    (* exercise *)
Admitted.

End spec2.
End spec2.
