(** * RUG.Analysis.Lib.Compactness

  The plan is to move this to the Waterproof library eventually.
*)

From Stdlib Require Import Classical_Pred_Type.
From Stdlib Require Import Lra.

From Stdlib Require Import Reals.Reals.

From Waterproof Require Import Tactics.
From Waterproof Require Import Automation.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Notations.Sets.
From Waterproof Require Import Chains.
From Waterproof Require Import Libs.Analysis.SupAndInf.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
From Waterproof Require Import Libs.Analysis.LimsupLiminfBolzano.
From Waterproof Require Import Libs.Analysis.Subsequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.


(** * Limit points of sets

A point [x] is a limit point (or accumulation point) of [A] if every open interval
around [x] contains a point of [A] different from [x].
*)

Definition is_limit_point_of (x : ℝ) (A : subset ℝ) : Prop :=
  ∀ ε > 0, ∃ y ∈ A, 0 < | y - x | < ε.

Notation "x 'is' 'a' '_limit' 'point_' 'of' A" :=
  (is_limit_point_of x A) (at level 69).

Notation "x 'is' 'a' 'limit' 'point' 'of' A" :=
  (is_limit_point_of x A) (at level 69, only parsing).

Waterproof Register Expand "limit" "point";
  for is_limit_point_of;
  as "Definition limit point".

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

(** [a, b] is compact. *)
Lemma closed_interval_is_compact (a b : ℝ) :
    [a, b] is compact.
Proof.
  apply compact_P3.
Qed.

(* TODO: I need to replace "close_set" by "is closed" in the
   next two lemmas, but it breaks in a weird way if I do. *)

(** Closed and bounded subsets of [ℝ] are compact. *)

Lemma open_iff_is_open (A : subset ℝ) :
    open_set A <-> A is open.
Proof.
 We show both directions.
  - We need to show that (open_set A) -> (A is open).
    Assume that open_set A as (openA).
    We need to show that A is open.
    We need to show that 
    ( ∀ a ∈ A, is_interior_point a A). 
    We need to show that 
    (∀ a ∈ A, ∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ A).  
    Take a ∈ A.
    By (openA) it holds that (a ∈ A) -> (neighbourhood A a) as (aNeigh).
    It holds that (neighbourhood A a) as (aNeigh').
    By (aNeigh') it holds that (∃ r : posreal, included (disc a r) A) as (DiscA).
    Obtain r according to (DiscA).
    It holds that (included (disc a r) A) as (DiscA').
    We need to show that ∃ r0 > 0, ∀ x ∈ (open_ball a r0), x ∈ A.
    Choose r0 := pos r. { We need to verify that r0 > 0.  
     By cond_pos it holds that 0 < pos r as (Hrpos). 
     We conclude that r0 > 0. } 
    We need to show that ∀ x ∈ (open_ball a r0), x ∈ A. 
    Take x ∈ (open_ball a r0).
    We need to show that x ∈ A.
    By (DiscA') it holds that x ∈ A.
    We conclude that x ∈ A.


  - We need to show that (A is open) -> (open_set A).
    Assume that A is open as (Aopen).
    We need to show that open_set A.
    We need to show that ∀ a ∈ A, neighbourhood A a.
    Take a ∈ A.
    By (Aopen) it holds that is_interior_point a A as (aInt).
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
    By (aInt'') it holds that x ∈ A.
    We conclude that x ∈ A.
Qed.

Lemma closed_iff_is_closed (A : subset ℝ) :
    closed_set A <-> A is closed.
Proof.
  We show both directions.
  - We need to show that (closed_set A) -> (A is closed).
    Assume that closed_set A as (closedA).
    We need to show that A is closed.
    By (closedA) it holds that (open_set (complementary A)) as (openComplA).
    We need to show that (complementary A) is open.
    By (open_iff_is_open) it holds that 
    (open_set (complementary A) <-> complementary A is open) as (openComplA_iff).
    We conclude that (complementary A) is open.

  - We need to show that (A is closed) -> (closed_set A).
    Assume that A is closed as (Aopen).
    We need to show that closed_set A.
    By (Aopen) it holds that (complementary A) is open as (ComplAopen).
    By (open_iff_is_open) it holds that
    (open_set (complementary A) <-> complementary A is open) as (openComplA_iff).
    We conclude that closed_set A.
Qed.

Lemma closed_and_bounded_is_compact (A : subset ℝ) :
    closed_set A ->
    A is bounded ->
    A is compact.
Proof.
  apply compact_P5.
Qed.

(** Compact subsets of [ℝ] are closed. *)
Lemma compact_is_closed (A : subset ℝ) :
    A is compact ->
    closed_set A.
Proof.
  apply compact_P2.
Qed.

(** Compact subsets of [ℝ] are bounded. *)
Lemma compact_is_bounded (A : subset ℝ) :
    A is compact ->
    A is bounded.
Proof.
  apply compact_P1.
Qed.

(** * Bounded injective sequences and limit points

Every bounded infinite set has a limit point (Bolzano-Weierstrass route).
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

(** If [(aₙ)] is a bounded injective sequence in [A], then [A] has a limit point.

    Proof: Bolzano-Weierstrass gives a convergent subsequence [a_{φ(k)} → x].
    Then [x] is a limit point of [A]: every ball around [x] contains infinitely many
    terms [a_{φ(k)}], all distinct from each other, and all in [A].
*)
Theorem inj_bounded_seq_has_limit_point
    (A : subset ℝ) (a : ℕ → ℝ) :
  inj_seq_in A a →
  (* We cannot write a is bounded since it conflicts with bounded sets here *)
  has_ub a →
  has_lb a →
  ∃ x ∈ ℝ, x is a _limit point_ of A.
Proof.
  (* Let's introduce and name the necessary hypotheses,
     what in Rocq can be done as intros [Ha_A Ha_inj] Hub Hlb. *)
  Assume that (forall n : ℕ, a n ∈ A) ∧ (forall n m : ℕ, (n ≠ m)%nat -> a n ≠ a m).
  It holds that forall n : ℕ, a n ∈ A as (Ha_A).
  It holds that forall n m : ℕ, (n ≠ m)%nat -> a n ≠ a m as (Ha_inj).
  Assume that has_ub a as (Hub).
  Assume that has_lb a as (Hlb).

  By Bolzano_Weierstrass it holds that
    ∃ (phi : ℕ → ℕ), ∃ (x : ℝ), is_index_seq phi ∧
      converges_to (fun k ↦ a (phi k)) x as (HBW).
 
  Obtain phi according to (HBW).
  It holds that ∃ (x0 : ℝ), is_index_seq phi ∧ converges_to (fun k ↦ a (phi k)) x0 as (Hphi).
  Obtain such a x0.

  It holds that is_index_seq phi as (Hphi_is).
  It holds that (fun k ↦ a (phi k)) ⟶ x0 as (Hphi_cv).

  Choose x := x0. { Indeed, x ∈ ℝ. }

  (* We need to show that x is a _limit point_ of A. *)
  We need to show that ∀ ε > 0, ∃ y ∈ A, 0 < | y - x | < ε.
  Take ε > 0.

  By (Hphi_cv) it holds that
    ∃ M ∈ ℕ, ∀ n ≥ M, | a (phi n) - x | < ε / 2 as (Hphi_cv').
  Obtain M according to (Hphi_cv').

  Either (a (phi M) = x) or (a (phi M) ≠ x).
  - Case (a (phi M) = x).
    Choose y := a (phi (S M)). {
      We need to verify that y ∈ A.
      By (Ha_A) it holds that a (phi (S M)) ∈ A.
      We conclude that y ∈ A.
    }
    We need to show that 0 < | y - x | < ε.
    
    By (Hphi_cv') it holds that (&
      | y - x |
      = | a (phi (S M)) - x |
      < ε / 2 < ε
    ).

    (* Mixing ≠ and < makes it hard for Rocq, we need to
       give it a little help. *)
    By (Hphi_is) it holds that phi M < phi (S M).
    By Nat.lt_neq it holds that phi M ≠ phi (S M).
    By (Ha_inj) it holds that a (phi M) ≠ a (phi (S M)).
    By neq_implies_abs_pos it holds that 0 < | y - x |.

    We conclude that 0 < | y - x | < ε.

  - Case (a (phi M) ≠ x).
    Choose y := a (phi M). {
      We need to verify that y ∈ A.
      By (Ha_A) it holds that a (phi M) ∈ A.
      We conclude that y ∈ A.
    }
    We need to show that 0 < | y - x | < ε.

    By (Hphi_cv') it holds that (&
      | y - x |
      = | a (phi M) - x |
      < ε / 2 < ε
    ).

    By neq_implies_abs_pos it holds that 0 < | y - x |.

    We conclude that 0 < | y - x | < ε.
Qed.

Close Scope subset_scope.
Close Scope R_scope.

