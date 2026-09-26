(** * RUG.Analysis.CauchySequences — Cauchy sequences and completeness of ℝ.

  #<a href="../../index.html##lecture05">Lecture 5</a>#, first part.

  Formalizes Abbott §2.6 (Cauchy criterion for sequences): a real sequence
  converges iff it is Cauchy. The forward direction is elementary; the converse
  is completeness of ℝ, proved via Bolzano–Weierstrass.

  These results are used by [Analysis.Series] for the Cauchy criterion of series. *)

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

(** ** Cauchy sequences *)

(** A sequence is Cauchy if its terms eventually cluster arbitrarily close.
    We are going to add some extra syntax to that [is_cauchy a] can
    also be written as [a is _Cauchy_]. *)
Definition is_cauchy (a : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
    |a n - a m| < ε.

(* begin hide *)
Notation "a 'is' '_Cauchy_'" := (is_cauchy a) (at level 69).

Waterproof Register Expand "Cauchy";
  for is_cauchy;
  as "Definition Cauchy".

(* end hide *)

(** [is_cauchy] is equivalent to Stdlib's [Cauchy_crit]. *)
Lemma cauchy_crit_equiv (a : ℕ → ℝ) :
    (a is _Cauchy_) ⇔ Cauchy_crit a.
Proof.
  We show both directions.

  - We need to show that a is _Cauchy_
        ⇨ ∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m, (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps.
    Assume that a is _Cauchy_ as (HC).
    Take eps > 0. It holds that eps > 0.
    It holds that
      ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a(n) - a(m)| < eps as (H').
    Obtain such a N1. Choose (N1).
    Take n : ℕ. Take m : ℕ. 
    Assume that (n ≥ N1)%nat as (Hn) and (m ≥ N1)%nat as (Hm).
    By H' we conclude that ｜a(n) - a(m)｜ < eps.

  - We need to show that (∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m,
          (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps)
        ⇨ a is _Cauchy_.
    Assume that ∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m,
          (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps as (HC).
    We need to show that
      ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε.
    Take ε > 0.
    By HC it holds that
      ∃ N1, ∀ n, ∀ m, (n ≥ N1)%nat ⇨ (m ≥ N1)%nat ⇨ ｜a(n) - a(m)｜ < ε.
    Obtain such a N1.
    Choose N2 := N1%nat. { Indeed, N2 ∈ ℕ. }
    We need to show that
      ∀ n ≥ N2, ∀ m ≥ N2, |a(n) - a(m)| < ε.
    Take n ≥ N2. Take m ≥ N2.
    By HC we conclude that |a(n) - a(m)| < ε.
Qed.

(** Every Cauchy sequence is bounded. *)
Theorem cauchy_is_bounded (a : ℕ → ℝ) : a is _Cauchy_ → a is _bounded_.
Proof.
  Assume that a is _Cauchy_ as (HC).
  It holds that
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε as (HC').
  We need to show that a is _bounded_.
  By is_bounded_equivalence it holds that
    (is_bounded a ⇔ is_bounded_equivalent a) as (Hequiv).
  By Hequiv it suffices to show that is_bounded_equivalent a.
  We need to show that
    ∃ M > 0, ∀ n ∈ ℕ, | a n | ≤ M.
  By HC it holds that
    ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, | a n - a m | < 1.
  Obtain such a N1.

  We claim that Cauchy_crit a as (HCr).
  { 
    By cauchy_crit_equiv it holds that a is _Cauchy_ ⇔ Cauchy_crit a.
    It suffices to show that a is _Cauchy_.
    By HC we conclude that a is _Cauchy_.
  }
  
  (** This EUn(a) is the Rocq Stdlib way of denoting the set
      of all elements of the sequence a. *)
  We claim that ∃ UB : ℝ, is_upper_bound (EUn a) UB.
  {
    (** From the StdLib
        [cauchy_maj: ∀ Un, Cauchy_crit(Un) ⇨ has_ub(Un)]
        
        Which means that every Cauchy sequence has an upper bound.
    *)
    By cauchy_maj it holds that has_ub a.
    It holds that ∃ m, m is an _upper bound_ for EUn(a).
    Obtain such an m. Choose (m).
    We conclude that m is an _upper bound_ for EUn(a).
  }
  
  Obtain such a UB.
  It holds that (is_upper_bound (EUn a) UB) as (HUB).
  We claim that ∀ n ∈ ℕ, a n ≤ UB.
  {
    Take n ∈ ℕ.
    We claim that EUn a (a n) as (Heun).
    {
      We need to show that ∃ k : ℕ, a n = a k.
      Choose k := n. We conclude that a n = a k.
    }
    By HUB we conclude that a n ≤ UB.
  }

  We claim that ∃ LB : ℝ, is_upper_bound (EUn (opp_seq a)) LB.
  { 
    By cauchy_min it holds that has_lb a.
    (** By definition of [has_lb a]: -a has an upper bound *)
    It holds that ∃ l, l is an _upper bound_ for EUn (opp_seq a).
    Obtain such an l. Choose (l). 
    We conclude that l is an _upper bound_ for EUn (opp_seq a).
  }

  Obtain such a LB.
  It holds that
    (is_upper_bound (EUn (opp_seq a)) LB) as (HLB).
  
  We claim that ∀ n ∈ ℕ, -LB ≤ a n.
  {
    Take n ∈ ℕ.
    We claim that EUn (opp_seq a) (- a n).
    { 
      We need to show that
        ∃ k : ℕ, - a n = opp_seq a k.
      Choose k := n.
      We conclude that - a n = opp_seq a k.
    }
    By HLB it holds that - a n ≤ LB.
    We conclude that -LB ≤ a n.
  }

  Choose M := (Rabs UB + Rabs LB + 1). { Indeed, M > 0. }
  
  We need to show that ∀ n ∈ ℕ,
    | a n | ≤ Rabs UB + Rabs LB + 1.
  Take n ∈ ℕ.
  It holds that (a n ≤ UB).
  It holds that (-LB ≤ a n).
  By Rle_abs it holds that UB ≤ Rabs UB.
  By Rle_abs it holds that LB ≤ Rabs LB.
  By Rle_abs it holds that -LB ≤ Rabs (-LB).
  By Rabs_Ropp it holds that (Rabs (-LB) = Rabs LB).

  We conclude that | a n | ≤ Rabs UB + Rabs LB + 1.
Qed.


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