(** * RUG.Analysis.PowerSeries — Power series and radius of convergence.

  #<a href="../../index.html##lecture11">Lecture 11</a># and #<a href="../../index.html##lecture12">Lecture 12</a>#.

  Formalizes Abbott §6.5: radius of convergence, Abel's theorem,
  term-by-term differentiation and integration of power series. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.PSeries_reg.
From Stdlib Require Import micromega.Lra.
From Waterproof Require Import Libs.Analysis.Series.
From Waterproof Require Import Libs.Analysis.Subsequences.
Require Export RUG.Analysis.FunctionSequences.
Require Export RUG.Analysis.Series.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

Notation "∑" := partial_sums (at level 50) : R_scope.

(** ** Radius of convergence *)

(** The radius of convergence of [∑ aₙ xⁿ] is the supremum of all [r ≥ 0]
    for which the series converges. *)

(** _Convergence at [x₀] implies absolute convergence inside_: a power series
    converging at [x₀] converges absolutely on [(-|x₀|, |x₀|)].

    Proof idea: from convergence at [x₀] the terms [aₙ x₀ⁿ] are bounded, say
    [|aₙ x₀ⁿ| ≤ M]. Then [|aₙ xⁿ| = |aₙ x₀ⁿ| · |x/x₀|ⁿ ≤ M · |x/x₀|ⁿ], and
    [|x/x₀| < 1] gives a convergent geometric bound. *)
Lemma power_series_converges_absolutely_inside (a : ℕ → ℝ) (x0 : ℝ)
    (H : ∃ L : ℝ, ∑ (fun n => a n * x0 ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < Rabs x0) :
    ∃ L : ℝ, ∑ (fun n => Rabs (a n * x ^ n)) ⟶ L.
Proof.
  Admitted.

(** ** Uniform convergence on compact sub-intervals *)

(** _Uniform convergence_ of power series (Abbott Theorem 6.5.2): if the radius of convergence is [R > 0], then [∑ aₙ xⁿ]
    converges uniformly on every [[−r, r]] with [r < R].

    Proof idea: pick [r'] with [r < r' < R]. The series converges absolutely at
    [r'], so [∑ |aₙ| (r')ⁿ < ∞]. For [x ∈ [−r, r]],
    [|aₙ xⁿ| ≤ |aₙ| rⁿ ≤ |aₙ| (r')ⁿ], so the Weierstrass M-test gives uniform
    convergence. *)
Lemma power_series_uniform_on_compact (a : ℕ → ℝ) (R r : ℝ)
    (HR : R > 0) (Hr0 : 0 < r) (HrR : r < R)
    (Hconv : ∀ x : ℝ, Rabs x < R →
      ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L) :
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun N x => sum_f_R0 (fun n => a n * x ^ n) N)
        g
        (fun x => Rabs x ≤ r).
Proof.
  Admitted.

(** The predicate "[g] is the sum of the power series [∑ aₙ xⁿ] on the disc of
    radius [R]": for every [x] with [|x| < R], the partial sums converge to
    [g(x)]. This lets us talk about the limit function without constructing it
    explicitly. *)
Definition is_series_sum (a : ℕ → ℝ) (g : ℝ → ℝ) (R : ℝ) : Prop :=
    ∀ x : ℝ, Rabs x < R → ∑ (fun n => a n * x ^ n) ⟶ g x.

(** ** Radius of convergence *)

(** _Existence of the radius of convergence_: for every coefficient sequence
    with a finite radius there is [R ≥ 0] such that the series converges for
    [|x| < R] and diverges for [|x| > R].

    Proof idea (Cauchy–Hadamard / root test): [R = 1 / limsup |aₙ|^{1/n}]. Below
    [R] the root test gives convergence; above [R] the terms do not tend to [0].
    (When the radius is infinite the "diverges" clause is vacuous.) *)
Lemma radius_of_convergence (a : ℕ → ℝ) :
    ∃ R : ℝ, R ≥ 0 ∧
      (∀ x : ℝ, Rabs x < R → ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L) ∧
      (∀ x : ℝ, Rabs x > R → ¬ (∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L)).
Proof.
  Admitted.

(** ** Absolute convergence strictly inside the radius *)

(** _Pointwise convergence_ of power series (Abbott Theorem 6.5.1): if the series converges at every [r] with [0 < r < R], then it
    converges absolutely at every [x] with [|x| < R].

    Proof idea: pick [r] with [|x| < r < R] (e.g. [r = (|x| + R)/2]); the series
    converges at [r], so [power_series_converges_absolutely_inside] with
    [x₀ = r] gives absolute convergence at [x]. *)
Lemma power_series_abs_convergent (a : ℕ → ℝ) (R : ℝ) (HR : R > 0)
    (Hcv_inside : ∀ r : ℝ, 0 < r → r < R →
      ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < R) :
    ∃ L : ℝ, ∑ (fun n => Rabs (a n * x ^ n)) ⟶ L.
Proof.
  Admitted.

(** ** Continuity of a power series *)

(** A power series is continuous on its open interval of convergence.

    Proof idea: on each [[−r, r]] with [r < R] the series converges uniformly
    ([power_series_uniform_on_compact]), and each partial sum is a (continuous) polynomial; the
    uniform limit of continuous functions is continuous. *)
Lemma power_series_continuous (a : ℕ → ℝ) (g : ℝ → ℝ) (R : ℝ) (HR : R > 0)
    (Hsum : is_series_sum a g R)
    (x : ℝ) (Hx : Rabs x < R) :
    continuity_pt g x.
Proof.
  Admitted.

(** ** Abel's summation by parts *)

(** _Abel's summation by parts_: with partial sums [Bₖ = ∑_{j=0}^k bⱼ],
    [∑_{k=0}^{n+1} aₖ bₖ = a_{n+1} B_{n+1} - ∑_{k=0}^n (a_{k+1} - aₖ) Bₖ].

    Proof idea: substitute [bₖ = Bₖ - B_{k-1}] and reindex the sum. *)
Lemma abel_summation_by_parts (a b : ℕ → ℝ) (n : ℕ) :
    sum_f_R0 (fun k => a k * b k) (S n) =
    a (S n) * sum_f_R0 b (S n)
    - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) n.
Proof.
  Admitted.

(** _Abel's lemma_ (bounded partial sums): if [(aₖ)] is nonnegative and
    decreasing and the partial sums of [(bₖ)] are bounded by [M], then
    [|∑_{k=0}^n aₖ bₖ| ≤ a₀·M].

    Proof idea: apply summation by parts; the decreasing nonnegative weights
    make the estimate telescope to [a₀·M]. *)
Lemma abel_lemma_bounded_partial_sums (a b : ℕ → ℝ) (n : ℕ) (M : ℝ)
    (Hdec : ∀ k : ℕ, 0 ≤ a (S k) ∧ a (S k) ≤ a k)
    (Hbound : ∀ k : ℕ, Rabs (sum_f_R0 b k) ≤ M) :
    Rabs (sum_f_R0 (fun k => a k * b k) n) ≤ a 0%nat * M.
Proof.
  Admitted.

(** ** Abel's theorem *)

(** _Abel's theorem_: if [∑ aₙ Rⁿ] converges at the endpoint [R > 0], then the
    power series converges uniformly on [[0, R]] (so its sum is continuous up to
    the endpoint).

    Proof idea: apply Abel's lemma to the tails, writing [aₙ xⁿ = (aₙ Rⁿ)(x/R)ⁿ]
    with decreasing weights [(x/R)ⁿ] and bounded partial sums of [(aₙ Rⁿ)]. *)
Theorem abel_theorem (a : ℕ → ℝ) (R : ℝ) (HR : R > 0)
    (Hend : ∃ L : ℝ, ∑ (fun n => a n * R ^ n) ⟶ L) :
    ∃ g : ℝ → ℝ,
      converges_uniformly (fun N x => sum_f_R0 (fun n => a n * x ^ n) N) g
        (fun x => 0 ≤ x ∧ x ≤ R).
Proof.
  Admitted.

(** ** Term-by-term differentiation *)

(** _Differentiation can be done term-by-term_ (Abbott Theorem 6.5.7): the sum [g] of [∑ aₙ xⁿ] is
    differentiable on [(−R, R)], and its derivative is the sum [h] of the derived
    series [∑ (n+1) a_{n+1} xⁿ] — which has the same radius [R].

    Proof idea: (1) the derived series has the same radius [R]; (2) it converges
    uniformly on [[−r, r]] for [r < R]; (3) apply the term-wise differentiability
    theorem ([uniform_differentiability_theorem]) to the partial sums. *)
Lemma power_series_termwise_derivative (a : ℕ → ℝ) (g h : ℝ → ℝ) (R : ℝ)
    (HR : R > 0) (Hsum : is_series_sum a g R)
    (Hder : is_series_sum (fun n => INR (S n) * a (S n)) h R)
    (x : ℝ) (Hx : Rabs x < R) :
    ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x.
Proof.
  Admitted.

(** ** Infinite differentiability and Taylor coefficients *)

(** A power series is infinitely differentiable on [(−R, R)], and its
    coefficients are its Taylor coefficients: [aₙ = g^{(n)}(0) / n!]. In
    particular [a₀ = g(0)].

    Proof idea: iterate term-by-term differentiation; each derived series again
    has radius [R], so [g] has derivatives of all orders, and evaluating the
    [n]-th derived series at [0] isolates [n!·aₙ]. *)
Theorem power_series_infinitely_differentiable
    (a : ℕ → ℝ) (g : ℝ → ℝ) (R : ℝ) (HR : R > 0) (Hsum : is_series_sum a g R) :
    (∀ x : ℝ, Rabs x < R → ∃ l : ℝ, derivable_pt_lim g x l) ∧ a 0%nat = g 0.
Proof.
  Admitted.