(** * RUG.Analysis.Taylor — Taylor's theorem and Taylor series.

  #<a href="../../index.html##lecture12">Lecture 12</a>#.

  Formalizes Abbott §6.6 and §8.6: Taylor polynomials, the Lagrange
  remainder formula, and Taylor series for exp, sin, cos. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Arith.Factorial.
Require Export RUG.Analysis.Derivatives.
Require Export RUG.Analysis.PowerSeries.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Taylor polynomials for exp *)

(** The Taylor polynomial of degree [n] for [f] around [0] is
    [sₙ(x) = ∑_{k=0}^n f^{(k)}(0)/k! · xᵏ]; the Lagrange remainder is
    [Eₙ(x) = f(x) - sₙ(x)]. For [f(x) = eˣ] all derivatives at [0] equal [1],
    so [sₙ(x) = ∑_{k=0}^n xᵏ/k!]. *)

(** The [n]-th Taylor polynomial of exp at [0], [Tₙ(x) = ∑_{k=0}^n xᵏ/k!]. *)
Fixpoint T_exp (n : nat) (x : R) : R :=
    match n with
    | O    => 1
    | S n' => T_exp n' x + x ^ n / INR (fact n)
    end.

(** [T₀(x) = 1]. *)
Lemma T_exp_0 (x : R) : T_exp 0%nat x = 1.
Proof.
  We conclude that T_exp 0%nat x = 1.
Qed.

(** [T₁(x) = 1 + x]. *)
Lemma T_exp_1 (x : R) : T_exp 1%nat x = 1 + x.
Proof.
  It holds that
    T_exp 1%nat x = T_exp 0%nat x + x ^ 1 / INR (fact 1) as (Hrec).
  By T_exp_0 it holds that T_exp 0%nat x = 1 as (H0).
  It holds that INR (fact 1) = 1 as (Hf1).
  rewrite Hrec. rewrite H0. rewrite Hf1.
  We conclude that 1 + x ^ 1 / 1 = 1 + x.
Qed.

(** [T₂(x) = 1 + x + x²/2]. *)
Lemma T_exp_2 (x : R) : T_exp 2%nat x = 1 + x + x ^ 2 / 2.
Proof.
  It holds that
    T_exp 2%nat x = T_exp 1%nat x + x ^ 2 / INR (fact 2) as (Hrec).
  By T_exp_1 it holds that T_exp 1%nat x = 1 + x as (H1).
  It holds that INR (fact 2) = 2 as (Hf2).
  rewrite Hrec. rewrite H1. rewrite Hf2.
  We conclude that 1 + x + x ^ 2 / 2 = 1 + x + x ^ 2 / 2.
Qed.

(** ** Taylor series and Lagrange remainder *)

(** Given the derivative values [d k = f^{(k)}(a)], the [n]-th Taylor polynomial
    of [f] about [a] is [∑_{k=0}^n d(k)/k! · (x - a)ᵏ]. The Taylor series about
    [0] is the special case [a = 0]. *)
Definition taylor_poly (d : ℕ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
    sum_f_R0 (fun k => d k / INR (fact k) * (x - a) ^ k) n.

(** The *Lagrange remainder* [Eₙ(x) = f(x) - Tₙ(x)] is the error of the [n]-th
    Taylor polynomial. *)
Definition lagrange_remainder (f : ℝ → ℝ) (d : ℕ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ)
    : ℝ :=
    f x - taylor_poly d a n x.

(** _Generalized (repeated) Rolle_: if [g] has [n + 1] distinct zeros and its
    successive derivatives [g, g', …, g⁽ⁿ⁾] exist, then [g⁽ⁿ⁾] has a zero in the
    spanning interval.

    Here [df k] denotes [g⁽ᵏ⁾], with [df (S k)] the derivative of [df k].

    Proof idea: between consecutive zeros of [df k], Rolle's theorem produces a
    zero of [df (S k)]; iterating [n] times leaves a single zero of [df n]. *)
Lemma generalized_rolle (df : ℕ → ℝ → ℝ) (n : ℕ) (pts : ℕ → ℝ)
    (Hstep : ∀ k ∈ ℕ, ∀ y ∈ ℝ,
        ∃ Hd : derivable_pt (df k) y, derive_pt (df k) y Hd = df (S k) y)
    (Hincr : ∀ k : ℕ, (k < n)%nat → pts k < pts (S k))
    (Hzero : ∀ k : ℕ, (k ≤ n)%nat → df 0%nat (pts k) = 0) :
    ∃ c : ℝ, pts 0%nat < c ∧ c < pts n ∧ df n c = 0.
Proof.
  Admitted.

(** _Taylor's theorem with Lagrange remainder_ (Abbott Theorem 6.6.3): if [f] is
    [(n+1)]-times differentiable, with [df k = f⁽ᵏ⁾] and [df (S k)] the
    derivative of [df k] (and [df 0 = f]), then for every [x] there is a [c]
    strictly between [a] and [x] with
    [f(x) = ∑_{k=0}^n f⁽ᵏ⁾(a)/k!·(x - a)ᵏ + f⁽ⁿ⁺¹⁾(c)/(n+1)!·(x - a)ⁿ⁺¹].

    Proof idea: apply generalized Rolle to an auxiliary function that agrees with
    [f] and its Taylor polynomial to order [n] and is adjusted by a multiple of
    [(t - a)ⁿ⁺¹] to also vanish at [x]. *)
Theorem taylor_theorem_lagrange
    (f : ℝ → ℝ) (df : ℕ → ℝ → ℝ) (a x : ℝ) (n : ℕ)
    (H0 : df 0%nat = f)
    (Hstep : ∀ k ∈ ℕ, ∀ y ∈ ℝ,
        ∃ Hd : derivable_pt (df k) y, derive_pt (df k) y Hd = df (S k) y) :
    ∃ c : ℝ, Rmin a x < c ∧ c < Rmax a x ∧
      f x = sum_f_R0 (fun k => df k a / INR (fact k) * (x - a) ^ k) n
            + df (S n) c / INR (fact (S n)) * (x - a) ^ (S n).
Proof.
  Admitted.

(** ** Sinusoidal bounds *)

(** The first-order Taylor polynomial of [sin] at [0]. *)
Definition T_sin1 (x : R) : R := x.

(** _Taylor series for sin(x)_ (upper bound): [sin x < x] for [x > 0]. The degree-1 Taylor
    polynomial of [sin] at [0] is [s₁(x) = x], and this is the Stdlib lemma
    [sin_lt_x]. *)
Lemma sin_lt_x (x : R) (Hx : 0 < x) : sin x < x.
Proof.
  Admitted.

(** _Taylor series for sin(x)_ (lower bound): [x - x³/6 ≤ sin x] for [0 ≤ x ≤ π/2].

    Proof idea: this follows from the alternating series estimate for
    [sin x = x - x³/3! + x⁵/5! - ⋯]; truncating after the cubic term gives a
    lower bound on [[0, π/2]]. *)
Lemma sin_ge_taylor (x : R) (Hx0 : 0 ≤ x) (HxPI : x ≤ PI / 2) :
    x - x ^ 3 / 6 ≤ sin x.
Proof.
  Admitted.

(** ** Error bound for the linear approximation of sin *)

(** _Taylor series for sin(x)_ (cf. Abbott Example 6.6.4): [|sin x - x| ≤ x³/6] for [0 < x ≤ π/2], so the linear
    approximation [sin x ≈ x] has error at most [x³/6].

    Proof idea: the upper bound [sin x < x] gives [sin x - x < 0], so
    [|sin x - x| = x - sin x]; the lower bound [sin x ≥ x - x³/6] then gives
    [x - sin x ≤ x³/6]. *)
Lemma sin_approx_error (x : R) (Hx0 : 0 < x) (HxPI : x ≤ PI / 2) :
    Rabs (sin x - x) ≤ x ^ 3 / 6.
Proof.
  Admitted.
