(** * RUG.Analysis.CauchySequences — Cauchy sequences and completeness of ℝ.

  #<a href="../../index.html##lecture05">Lecture 5</a>#, first part.

  Formalizes Abbott §2.6 (Cauchy criterion for sequences): a real sequence
  converges iff it is Cauchy. The forward direction is elementary; the converse
  is completeness of ℝ, proved via Bolzano–Weierstrass.

  Cauchy sequences ([is_cauchy] / [_Cauchy_]) and [cauchy_is_bounded] are
  developed in [Analysis.Subsequences] (lecture 4) and reused here. These results
  are in turn used by [Analysis.Series] for the Cauchy criterion of series. *)

From Stdlib Require Import Reals.Reals.
From Waterproof Require Import Libs.Analysis.Subsequences.
From Waterproof Require Import Libs.Analysis.LimsupLiminfBolzano.
Require Export RUG.Analysis.Subsequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Convergent sequences are Cauchy *)

(** Every convergent sequence is Cauchy.

    Given [ε > 0], pick [N] so that [|aₙ - L| < ε/2] for [n ≥ N]; then for
    [m, n ≥ N] the triangle inequality gives [|aₘ - aₙ| < ε]. *)
Lemma convergent_is_cauchy (a : ℕ → ℝ) (L : ℝ) :
    a ⟶ L → a is _Cauchy_.
Proof.
  Assume that ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, | a n - L | < ε as (Hac).
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε.
  Take ε > 0.
  By Hac it holds that ∃ N12 ∈ ℕ, ∀ n ≥ N12, |a n - L| < ε/2 as (HN).
  Obtain such an N12.
  It holds that ∀ n ≥ N12, |a n - L| < ε/2 as (Hconv).
  Choose N1 := N12. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε.
  Take n ≥ N1. It holds that |a n - L| < ε/2.
  Take m ≥ N1. It holds that |a m - L| < ε/2.
  It holds that |a n - a m| = | a n - L + L - a m |.
  By Rabs_triang it holds that | a n - L + L - a m | ≤ | a n - L | + | a m - L |.
  We conclude that (&
    |a n - a m|
    ≤ | a n - L | + | a m - L |
    < ε/2 + ε/2 = ε
  ).
Qed.

(** ** Cauchy sequences converge (completeness of ℝ) *)

(** Every Cauchy sequence of reals converges.

    A Cauchy sequence is bounded ([cauchy_is_bounded]), so by
    Bolzano–Weierstrass it has a convergent subsequence; the Cauchy property then
    forces the whole sequence to converge to the same limit. *)
Lemma cauchy_is_convergent (a : ℕ → ℝ) :
  a is _Cauchy_ → ∃ L ∈ ℝ, a ⟶ L.
Proof.
  Assume that a is _Cauchy_.
  It holds that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε as (HC).
  By cauchy_is_bounded it holds that a is bounded.
  By is_bounded_equivalence it holds that (a is bounded ⇔ is_bounded_equivalent a) as (Hequiv).
  By Hequiv it holds that ∃ M > 0, ∀ n ∈ ℕ, | a n | ≤ M as (HB).
  Obtain such a M.

  We claim that has_ub a.
  {
    We need to show ∃ m, ∀ x : ℝ, (∃ i, x = a i) → x ≤ m.
    Choose m := M.
    Take x : ℝ.
    Assume that ∃ i, x = a i. Obtain such a i.
    It holds that (&
      x = a i ≤ | a i | ≤ M
    ).
    Indeed, x ≤ m.
  }

  We claim that has_lb a.
  {
    We need to show ∃ m, ∀ x, (∃ i, x = - a(i)) ⇨ x ≤ m.
    Choose m := M.
    Take x : ℝ.
    Assume that ∃ i, x = - a i. Obtain such a i.
    It holds that (&
      x = - a i ≤ | a i | ≤ M
    ).
    Indeed, x ≤ m.
  }

  By Bolzano_Weierstrass it holds that ∃ phi : ℕ → ℕ, ∃ l : ℝ,
      is_index_seq phi ∧ (fun k ↦ a (phi k)) ⟶ l.
  Obtain such a phi.
  It holds that ∃ l : ℝ, is_index_seq phi ∧ (fun k ↦ a (phi k)) ⟶ l.
  Obtain such a l.
  Choose L := l. { Indeed, L ∈ ℝ. }

  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | a n - L | < ε.

  Take ε > 0. It holds that ε/2 > 0.
  By HC it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε/2 as (Hcauchy).
  Obtain such an N1.

  Since (fun k ↦ a (phi k)) ⟶ l it holds that ∀ ε > 0, ∃ K ∈ ℕ, ∀ k ≥ K, |a (phi k) - l| < ε as (Hsubconv).

  It holds that ∃ K ∈ ℕ, ∀ k ≥ K, |a (phi k) - l| < ε/2.
  Obtain such a K.

  We claim that ∀ n : ℕ, (n ≤ phi n)%nat.
  {
    We use induction on n.
    + We first show the base case (0 ≤ phi(0))%nat.
      We conclude that (0 ≤ phi 0)%nat.
    + We now show the induction step.
      Take n : ℕ.
      Assume that (n ≤ phi(n))%nat as (IH).
      Since is_index_seq phi it holds that ∀ n ∈ ℕ, (phi n < phi (S n))%nat as (Hmono).

      By Hmono it holds that phi n < phi (S n) as (Hlt).
      It holds that (& n ≤ phi n < phi (S n)).
      It holds that (S n ≤ phi (S n))%nat.
      It holds that S n = (n + 1)%nat.
      We conclude that (n + 1 ≤ phi(n + 1))%nat.
  }

  Choose N2 := (Nat.max K N1)%nat. { Indeed, N2 ∈ ℕ. }
  We need to show that ∀ n ≥ N2, |a(n) - L| < ε.

  It holds that (K ≤ N2)%nat.
  It holds that (K ≤ Nat.max K N1)%nat.
  It holds that (N1 ≤ N2)%nat as (HleN1N2).
  (** These extra two lines help to speed up the proof substantially *)
  By HleN1N2 it holds that (N1 ≤ Nat.max K N1)%nat.
  By index_seq_grows_0 it holds that (phi N2 ≥ N2)%nat.
  It holds that (phi N2 ≥ N1)%nat.

  Take n ≥ N2.

  We claim that |a n - a (phi N2)| < ε/2.
  {
    By Hcauchy it holds that ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε/2.
    It holds that n ≥ N1.
    We conclude that |a n - a (phi N2)| < ε/2.
  }

  It holds that |a (phi N2) - L| < ε/2.

  We conclude that (&
    |a n - L|
    ≤ |a n - a (phi N2)| + |a (phi N2) - L|
    < ε/2 + ε/2 = ε
  ).
Qed.

(** This is a convenient helper to be able to use the
    Cauchy criterion also from Rocq standard library. *)
Lemma Cauchy_iff_CauchyCrit (a : ℕ → ℝ) :
    a is _Cauchy_ ↔ Cauchy_crit a.
Proof.
  split.
  - Assume that a is _Cauchy_ as (Hc).
    It holds that ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| < ε.
    We need to show that forall eps:R,
      eps > 0 ->
      exists N1 : nat,
        (forall n m:nat,
          (n >= N1)%nat -> (m >= N1)%nat 
          -> Rdist (a n) (a m) < eps).
    Take eps > 0.
    By Hc it holds that ∃ N1 ∈ ℕ,
      ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < eps.
    Obtain such an N1. Choose (N1).
    We need to show that 
        forall n m:nat,
          (n >= N1)%nat -> (m >= N1)%nat -> Rdist (a n) (a m) < eps.
    Take n : nat. Take m : nat.
    Assume that (n >= N1)%nat and (m >= N1)%nat.
    By Hc we conclude that Rdist (a n) (a m) < eps.
    
  - Assume that Cauchy_crit a as (Hcc).
    It holds that forall eps:R,
      eps > 0 ->
      exists N1 : nat,
        (forall n m:nat,
          (n >= N1)%nat -> (m >= N1)%nat 
          -> Rdist (a n) (a m) < eps).
    We need to show that a is _Cauchy_.
    We need to show that
      ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| < ε.
    Take ε > 0.
    By Hcc it holds that exists N1 : nat,
        (forall n m:nat,
          (n >= N1)%nat -> (m >= N1)%nat 
          -> Rdist (a n) (a m) < ε).
    Obtain such an N1. Choose (N1). { Indeed, N1 ∈ ℕ. }
    We need to show that ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε.
    Take n ≥ N1. Take m ≥ N1.
    By Hcc we conclude that |a n - a m| < ε.
Qed.