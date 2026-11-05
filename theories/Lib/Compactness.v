(** * RUG.Analysis.Lib.Compactness

  The plan is to move this to the Waterproof library eventually.
*)

Require Import RUG.Analysis.Lib.StdlibReals.
(** This file wraps the Stdlib compactness results, so it imports [Rtopology]
    explicitly. The import is not re-exported to the files that use this one. *)
From Stdlib Require Import Reals.Rtopology.
From Stdlib Require Import Lists.List.

From Waterproof Require Import Tactics.
From Waterproof Require Import Automation.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Chains.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
From Waterproof Require Import Libs.Analysis.LimsupLiminfBolzano.
From Waterproof Require Import Libs.Analysis.Subsequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

(** Temporary axiom of countable choice.

    For any relation [P], if [∀ n : ℕ, ∃ y : ℝ, P n y], then there is a
    sequence [f] that picks a specific choice of [y] for each [n]:
    [∃ f : ℕ → ℝ, ∀ n : ℕ, P n (f n)]. *)
Axiom countable_choice : ∀ (P : ℕ → ℝ → Prop),
  (∀ n : ℕ, ∃ y : ℝ, P n y) → ∃ f : ℕ → ℝ, ∀ n : ℕ, P n (f n).

(** * Compactness

We rely on rocq Stdlib's notion of compactness: every open cover has a finite subcover.
See [Reals.Rtopology] in the Stdlib for the full definition and available theorems.

Key facts available from the Stdlib and usable in proofs are:
  - [compact_P3]: the closed interval [a,b] is compact.
  - [compact_P5]: closed + bounded implies compact.
  - [compact_P2]: compact implies closed.
  - [compact_P1]: compact implies bounded.
*)

(* NOTE: maybe better to move this whole file into Reals,
   but I had some circular dependency issues when I tried. *)

Notation "A 'is' '_bounded_'" := (bounded A) (at level 69).
Notation "A 'is' 'bounded'" := (bounded A) (at level 69, only parsing).

Definition is_compact (A : subset ℝ) : Prop := compact A.

Notation "A 'is' '_compact_'" := (is_compact A) (at level 69).
Notation "A 'is' 'compact'" := (is_compact A) (at level 69, only parsing).

(** The maximum of a finite list of natural numbers bounds every element
    of the list. *)
Lemma fold_right_max_geq (l : list ℕ) (d x : ℕ) :
    In x l → (x ≤ fold_right Nat.max d l)%nat.
Proof.
  induction l as [| a l IH]; simpl.
  - intros [].                      (* In x [] is False *)
  - intros [-> | Hin].
    + apply Nat.le_max_l.           (* x <= max x (fold_right ...) *)
    + etransitivity.
      * apply IH, Hin.              (* x <= fold_right Nat.max d l *)
      * apply Nat.le_max_r.         (* ... <= max a (fold_right ...) *)
Qed.

(** Any real-valued function on a finite nonempty list attains its minimum
    on the list. *)
Lemma list_has_min (A : Type) (f : A -> R) (xs : list A) :
    xs <> nil ->
    exists a, In a xs /\ forall b, In b xs -> f a <= f b.
Proof.
  induction xs as [| x tail IH]; simpl.
  - exact (fun H => False_rect _ (H eq_refl)).
  - destruct tail as [| y ys].
    + exists x. split.
      * simpl. left. reflexivity.
      * intros b Hb.
        simpl in Hb.
        destruct Hb as [Hb | Hfalse].
        -- subst b. apply Rle_refl.
        -- Contradiction.
    + destruct (IH ltac:(discriminate)) as [m [Hm Hmin]].
      (* Use Ltac1 to split the real-order sumbool. *)
      ltac1:(destruct (Rle_dec (f x) (f m)) as [Hxm | Hxm]).
      * exists x. split.
        -- simpl. left. reflexivity.
        -- intros b Hb.
           simpl in Hb.
           destruct Hb as [Hb | Hb].
           ++ subst b. apply Rle_refl.
           ++ eapply Rle_trans.
              ** exact Hxm.
              ** apply Hmin. exact Hb.
      * ltac1:(assert (Hmx : f m <= f x) by
          (apply Rlt_le; apply Rnot_le_lt; exact Hxm)).
        exists m. split.
        -- simpl. right. exact Hm.
        -- intros b Hb.
           simpl in Hb.
           destruct Hb as [Hb | Hb].
           ++ subst b. exact Hmx.
           ++ apply Hmin. exact Hb.
Qed.

(** [a, b] is compact. *)
Lemma closed_interval_is_compact (a b : ℝ) :
    [a, b] is compact.
Proof.
  apply compact_P3.
Qed.

(** Stdlib's [open_set] (via [neighbourhood] and [disc]) agrees with
    Waterproof's [is_open] (via [is_interior_point] and [open_ball]). *)
Lemma open_iff_is_open (A : subset ℝ) :
    open_set A <-> A is open.
Proof.
  We show both directions.
  - We need to show that (open_set A) -> (A is open).
    Assume that open_set A as (openA).
    We need to show that A is open.
    We need to show that ∀ a ∈ A, is_interior_point a A.
    We need to show that ∀ a ∈ A, ∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ A.
    Take a ∈ A.
    By openA it holds that (a ∈ A) -> (neighbourhood A a) as (aNeigh).
    It holds that neighbourhood A a as (aNeigh').
    By aNeigh' it holds that
      ∃ r : posreal, included (disc a r) A as (DiscA).
    Obtain r according to (DiscA).
    It holds that included (disc a r) A as (DiscA').
    We need to show that ∃ r0 > 0, ∀ x ∈ (open_ball a r0), x ∈ A.
    Choose r0 := pos r.
    {
      We need to verify that r0 > 0.
      By cond_pos it holds that 0 < pos r as (Hrpos).
      We conclude that r0 > 0.
    }
    We need to show that ∀ x ∈ (open_ball a r0), x ∈ A.
    Take x ∈ (open_ball a r0).
    We need to show that x ∈ A.
    By DiscA' it holds that x ∈ A.
    We conclude that x ∈ A.

  - We need to show that (A is open) -> (open_set A).
    Assume that A is open as (Aopen).
    We need to show that open_set A.
    We need to show that ∀ a ∈ A, neighbourhood A a.
    Take a ∈ A.
    By Aopen it holds that is_interior_point a A as (aInt).
    It holds that ∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ A as (aInt').
    Obtain r according to (aInt').
    It holds that r > 0 as (cond_posr).
    It holds that ∀ x ∈ (open_ball a r), x ∈ A as (aInt'').
    We need to show that neighbourhood A a.
    We need to show that ∃ r0 : posreal, included (disc a r0) A.
    Choose r0 := mkposreal r cond_posr.
    We need to show that included (disc a r0) A.
    We need to show that ∀ x ∈ (disc a r0), x ∈ A.
    Take x ∈ disc a r0.
    We need to show that x ∈ A.
    By aInt'' it holds that x ∈ A.
    We conclude that x ∈ A.
Qed.

(** Consequently, Stdlib's [closed_set] agrees with Waterproof's
    [is_closed]. *)
Lemma closed_iff_is_closed (A : subset ℝ) :
    closed_set A <-> A is closed.
Proof.
  We show both directions.
  - We need to show that (closed_set A) -> (A is closed).
    Assume that closed_set A as (closedA).
    We need to show that A is closed.
    By closedA it holds that open_set (complementary A) as (openComplA).
    We need to show that (complementary A) is open.
    By open_iff_is_open it holds that
      open_set (complementary A) <-> complementary A is open
      as (openComplA_iff).
    We conclude that (complementary A) is open.

  - We need to show that (A is closed) -> (closed_set A).
    Assume that A is closed as (Aopen).
    We need to show that closed_set A.
    By Aopen it holds that (complementary A) is open as (ComplAopen).
    By open_iff_is_open it holds that
      open_set (complementary A) <-> complementary A is open
      as (openComplA_iff).
    We conclude that closed_set A.
Qed.

(** Closed and bounded subsets of [ℝ] are compact. *)
Lemma closed_and_bounded_is_compact (A : subset ℝ) :
    A is closed ->
    A is bounded ->
    A is compact.
Proof.
  We need to show that (A is closed) -> (A is bounded) -> (A is compact).
  Assume that A is closed as (Aclosed).
  Assume that A is bounded as (Abounded).
  We need to show that A is compact.
  By closed_iff_is_closed it holds that
    closed_set A <-> A is closed as (Aclosed_).
  By Aclosed_ it holds that closed_set A as (Aclosed').
  apply compact_P5.
  - exact Aclosed'.
  - exact Abounded.
Qed.

(** Compact subsets of [ℝ] are closed. *)
Lemma compact_is_closed (A : subset ℝ) :
    A is compact ->
    A is closed.
Proof.
  We need to show that (A is compact) -> (A is closed).
  Assume that A is compact as (Acompact).
  By compact_P2 it holds that closed_set A as (Aclosed).
  We need to show that A is closed.
  By closed_iff_is_closed it holds that
    closed_set A <-> A is closed as (Aclosed_).
  By Aclosed_ it holds that A is closed.
  We conclude that A is closed.
Qed.

(** Compact subsets of [ℝ] are bounded. *)
Lemma compact_is_bounded (A : subset ℝ) :
    A is compact ->
    A is bounded.
Proof.
  apply compact_P1.
Qed.

(** * Bounded injective sequences

Helpers for [inj_bounded_seq_has_limit_point] in [RUG.Analysis.Compactness]:
every bounded infinite set has a limit point (Bolzano-Weierstrass route).
*)

(** A sequence [(aₙ)] gives infinitely many distinct points in [A] if it is
    injective and contained in [A]. *)
Definition inj_seq_in (A : subset ℝ) (a : ℕ → ℝ) : Prop :=
  (forall n : ℕ, a n ∈ A) ∧
  (forall n m : ℕ, (n ≠ m)%nat -> a n ≠ a m).

(* TODO: This is a convenience for the next theorem,
   we should probably move this into Waterproof.Analysis.Reals *)
Lemma neq_implies_abs_pos : forall a b : R, a ≠ b ⇒ 0 < | b - a |.
Proof.
  intros a b Hneq.
  apply Rminus_eq_contra in Hneq.
  rewrite Rabs_minus_sym.
  apply Rabs_pos_lt.
  assumption.
Qed.


Close Scope subset_scope.
Close Scope R_scope.

