From iris.base_logic Require Import upred iprop.
From iris.proofmode Require Import proofmode.

Section proofs.
Context {Σ : gFunctors}.

(*
  When stating lemmas that do not depend on generic Iris propositions
  (which mention [Σ]), we have to manually specify the [Σ]. We do this
  locally using notation.
*)
Local Notation "⊢ P" := (⊢@{iPropI Σ} P).
Local Notation "Q ⊢ P" := (Q ⊢@{iPropI Σ} P).

(* ################################################################# *)
(** * Pure Propositions *)

(**
  Any Rocq proposition [φ : Prop] can be turned into an Iris proposition through
  the pure embedding [⌜φ⌝ : iProp Σ] (type \lc and \rc). We call these
  "pure assertions".
*)

(**
  Pure propositions can be introduced using [iPureIntro]. This exits the
  Iris Proof Mode, throwing away the spatial context and turns the
  proposition into a Rocq proposition.
*)
Lemma eq_5_5 : ⊢ ⌜5 = 5⌝.
Proof.
  iPureIntro.
  reflexivity.
Qed.

(**
  To eliminate a pure proposition, we can use the specialization pattern
  ["%_"]. This adds the proposition to the non-spatial context as a Rocq
  proposition.
*)
Lemma eq_elm {A} (P : A → iProp Σ) (x y : A) : ⌜x = y⌝ -∗ P x -∗ P y.
Proof.
  iIntros "%Heq HP".
  rewrite -Heq.
  iApply "HP".
Qed.

(** [True] is pure. *)
Lemma true_intro : ⊢ True.
Proof.
  iPureIntro.
  constructor.
Qed.

(** Conjunction preserves pureness. *)
Lemma and_pure : ⊢ ⌜5 = 5⌝ ∧ ⌜8 = 8⌝.
Proof.
  iPureIntro.
  split; reflexivity.
Qed.

(** Separating conjunction preserves pureness. *)
Lemma sep_pure : ⊢ ⌜5 = 5⌝ ∗ ⌜8 = 8⌝.
Proof.
  iPureIntro.
  split; reflexivity.
Qed.

(** Wand preserves pureness. *)
Lemma wand_pure {A} (x y : A) : ⊢ ⌜x = y⌝ -∗ ⌜y = x⌝.
Proof.
  iPureIntro.
  intros Heq.
  symmetry.
  assumption.
Qed.

(** Arbitrary Iris propositions are not pure. *)
Lemma abstr_not_pure (P : iProp Σ) : ⊢ P -∗ ⌜8 = 8⌝.
Proof.
  Fail iPureIntro. (* [P] is not pure *)
  iIntros "HP".
  iPureIntro. (* [⌜8 = 8⌝] is pure *)
  reflexivity.
Qed.

(**
  The pure embedding allows us to state an important property, namely
  soundness. Soundness is proved in the [uPred_primitive.pure_soundness]
  lemma stating: [∀ φ, (True ⊢ ⌜φ⌝) → φ]. This means that anything
  proved inside the Iris logic is as true as anything proved in Rocq.
*)

End proofs.
