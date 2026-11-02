(** * RUG.Analysis.FunctionSequences — Sequences of functions.

  #<a href="../../index.html##lecture10">Lecture 10</a># and #<a href="../../index.html##lecture11">Lecture 11</a>#.

  Formalizes Abbott §6.2–6.4: pointwise and uniform convergence,
  the Weierstrass M-test, and the interchange of limits with
  continuity and integration for uniformly convergent sequences. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.RiemannInt.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Continuity.
Require Export RUG.Analysis.Lib.UniformConvergence.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Pointwise convergence *)

(** The sequence of functions [fₙ(x) = x/n]. *)
Definition fx_over_n : ℕ → ℝ → ℝ := fun n x => x / INR n.

(** The constant zero function. *)
Definition zero_fn : ℝ → ℝ := fun _ => 0.

(** [(fₙ)] converges pointwise to [g] on [A] iff for each [x ∈ A], [fₙ(x) → g(x)]. *)
(** This is [converges_pointwise fn g A] from [Analysis.Lib.UniformConvergence]. *)

(** The sequence [fₙ(x) = x/n] converges pointwise to [0].

    Proof idea: for each fixed [x] and [ε > 0], the Archimedean property gives
    [N > |x|/ε]; then for [n ≥ N ≥ 1], [|fₙ(x)| = |x|/n ≤ |x|/N < ε]. Here the
    threshold [N] depends on [x]. *)
Lemma x_over_n_pointwise :
    converges_pointwise (fun n x => x / INR n) (fun _ => 0) (fun _ => True).
Proof.
  We need to show that ∀ x ∈ (fun _ : ℝ => True), (fun n => x / INR n) ⟶ 0.
  Take x ∈ (fun _ : ℝ => True).
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | x / n - 0 | < ε.
  Take ε > 0.
  By the Archimedean property it holds that ∃ n1 ∈ ℕ, n1 > | x | / ε.
  Obtain such an n1. Choose N1 := S n1. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, | x / n - 0 | < ε.
  Take n ≥ N1.
  It holds that (n > n1)%nat.
  It holds that INR n > INR n1.
  It holds that INR n > 0.
  (** First we turn the choice of [n1] into [|x| < n·ε]. *)
  It holds that | x | / ε < n.
  It holds that | x | = (| x | / ε) * ε.
  By Rmult_lt_compat_r it holds that (| x | / ε) * ε < n * ε.
  It holds that | x | < n * ε.
  (** Then we divide by [n > 0]. *)
  It holds that | n | = n.
  By Rabs_mult it holds that | x * / n | = | x | * | / n |.
  By Rabs_inv it holds that | / n | = / | n |.
  It holds that | x / n | = | x | / n.
  It holds that / n > 0.
  By Rmult_lt_compat_r it holds that | x | * / n < (n * ε) * / n.
  We conclude that (& | x / n - 0 | = | x | * / n < (n * ε) * / n = ε).
Qed.

(** Pointwise limit of continuous functions need not be continuous. *)
(** (illustrated by fₙ(x) = xⁿ on [0,1]; limit is the step function) *)

(** ** Uniform convergence *)

(** Uniform convergence on a set implies pointwise convergence.

    Proof idea: for a fixed [x ∈ A], the uniform threshold [N] (which works for
    all points simultaneously) works in particular for the single point [x]. *)
Lemma uniform_implies_pointwise (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ)
    (H : converges_uniformly fn g A) :
    converges_pointwise fn g A.
Proof.
  (** This is proved in [Analysis.Lib.UniformConvergence]. *)
  By RUG.Analysis.Lib.UniformConvergence.uniform_implies_pointwise
    we conclude that converges_pointwise fn g A.
Qed.

(** ** Cauchy criterion for uniform convergence *)

(** Theorem 12.4: [(fₙ)] converges uniformly on [A] iff it is uniformly Cauchy:
    for every ε > 0 there exists N such that for all [n, m ≥ N] and all [x ∈ A],
    [|fₙ(x) - fₘ(x)| < ε].

    Proof idea (⇒): by the triangle inequality
    [|fₙ(x) - fₘ(x)| ≤ |fₙ(x) - g(x)| + |g(x) - fₘ(x)| < ε/2 + ε/2 = ε]. *)
Lemma uniform_cauchy_criterion (fn : ℕ → ℝ → ℝ) (A : subset ℝ) :
    (∃ g : ℝ → ℝ, converges_uniformly fn g A) ⇔
    (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      Rabs (fn n x - fn m x) < ε).
Proof.
  Admitted.

(** ** Uniform limit of continuous functions is continuous *)

(** Theorem 12.1: if each [fₙ] is continuous at [a] and [(fₙ) ⇉ g] uniformly on
    a neighborhood of [a], then [g] is continuous at [a].

    Proof idea (3ε argument): given [ε > 0], (1) uniform convergence gives [N]
    with [|f_N(x) - g(x)| < ε/3] for all [x]; (2) continuity of [f_N] at [a]
    gives [δ] with [|f_N(x) - f_N(a)| < ε/3] for [|x - a| < δ]; (3) then
    [|g(x) - g(a)| ≤ |g(x) - f_N(x)| + |f_N(x) - f_N(a)| + |f_N(a) - g(a)| < ε]. *)
Theorem uniform_limit_continuous (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a : ℝ)
    (Hfn : ∀ n ∈ ℕ, continuity_pt (fn n) a)
    (Hunif : ∃ A : subset ℝ, A a ∧ converges_uniformly fn g A) :
    continuity_pt g a.
Proof.
  Admitted.

(** ** Weierstrass M-test *)

(** Theorem 12.2 (Weierstrass M-test): if [|fₙ(x)| ≤ Mₙ] for all [x ∈ A] and
    [∑ Mₙ] converges, then [∑ fₙ] converges uniformly on [A].

    Proof idea: use the Cauchy criterion. Since [∑ Mₙ] converges, for [ε > 0]
    there is an [N] such that for [m > n ≥ N],
    [|∑_{k=n+1}^m fₖ(x)| ≤ ∑_{k=n+1}^m |fₖ(x)| ≤ ∑_{k=n+1}^m Mₖ < ε],
    uniformly in [x]. *)
Theorem weierstrass_M_test (fn : ℕ → ℝ → ℝ) (M : ℕ → ℝ) (A : subset ℝ)
    (Hbound : ∀ n ∈ ℕ, ∀ x ∈ A, Rabs (fn n x) ≤ M n)
    (HM : ∃ L ∈ ℝ, (fun n => sum_f_R0 M n) ⟶ L) :
    ∃ g : ℝ → ℝ, converges_uniformly (fun n x => sum_f_R0 (fun k => fn k x) n) g A.
Proof.
  Admitted.

(** ** Term-by-term integration *)

(** _Interchange of limit and integral_ (Abbott 6.4.1): if [(fₙ) ⇉ g] uniformly
    on [[a, b]] and each [fₙ] is integrable, then [g] is integrable and
    [∫_a^b fₙ → ∫_a^b g].

    Here [I n = ∫_a^b fₙ] and [Ig = ∫_a^b g] are the recorded integral values.

    Proof idea: uniform convergence lets the error [∫|fₙ - g| ≤ (b - a)·‖fₙ - g‖∞]
    be made arbitrarily small, so the integrals converge. *)
Theorem uniform_limit_integral (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hunif : converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b))
    (I : ℕ → ℝ) (Ig : ℝ)
    (HI : ∀ n : ℕ, ∀ pr : Riemann_integrable (fn n) a b, I n = RiemannInt pr)
    (HIg : ∀ pr : Riemann_integrable g a b, Ig = RiemannInt pr) :
    I ⟶ Ig.
Proof.
  Admitted.

(** ** Uniform convergence of [x/n] on a bounded interval *)

(** [fₙ(x) = x/n] converges uniformly to [0] on [[−R, R]].

    Proof idea: for [x ∈ [−R, R]] and [n ≥ 1], [|fₙ(x)| = |x|/n ≤ R/n]. The
    bound [R/n] is independent of [x] and tends to [0], giving a uniform
    threshold. *)
Lemma x_over_n_uniform (bR : ℝ) (HR : bR > 0) :
    converges_uniformly fx_over_n zero_fn (fun x => -bR ≤ x ∧ x ≤ bR).
Proof.
  Admitted.

(** ** A pointwise-only example *)

(** [fₙ(0) = 0ⁿ → 0] (pointwise value at the origin).

    For [fₙ(x) = xⁿ] on [[0,1]] and the point [x = 0], [fₙ(0) = 0ⁿ = 0] for all
    [n ≥ 1], so the sequence is eventually the constant [0]. (More generally
    [xⁿ → 0] for [0 ≤ x < 1] and [1ⁿ → 1], so the pointwise limit is the
    indicator of [{1}], which is not continuous.) *)
Lemma zero_pow_to_zero : (fun n : ℕ => (0 : ℝ) ^ n) ⟶ 0.
Proof.
  Admitted.

(** ** Uniform convergence of the geometric series on [[−r, r]] *)

(** Theorem 12.3: for [0 ≤ r < 1], the partial sums [∑ xᵏ] converge uniformly on
    [[−r, r]].

    Proof idea: apply the Weierstrass M-test with [Mₙ = rⁿ]. For [x ∈ [−r, r]],
    [|xⁿ| = |x|ⁿ ≤ rⁿ], and [∑ rⁿ = 1/(1 - r) < ∞]. The uniform limit is
    [g(x) = 1/(1 - x)]. *)
Lemma geometric_series_uniform (r : ℝ) (Hr0 : 0 ≤ r) (Hr1 : r < 1) :
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun n x => sum_f_R0 (fun k => x ^ k) n) g (fun x => -r ≤ x ∧ x ≤ r).
Proof.
  Admitted.

(** ** The supremum characterization of uniform convergence *)

(** _Mₙ-test_: [(fₙ) ⇉ g] uniformly on [A] iff there is a sequence [Mₙ → 0]
    dominating the pointwise errors, [|fₙ(x) - g(x)| ≤ Mₙ] for all [x ∈ A].
    (One may take [Mₙ = sup_{x ∈ A} |fₙ(x) - g(x)|].)

    Proof idea: (⇒) the uniform threshold provides such a bounding [Mₙ].
    (⇐) [Mₙ → 0] gives a single [N] making all errors [< ε] simultaneously. *)
Lemma uniform_convergence_sup_characterization
    (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) :
    converges_uniformly fn g A ⇔
    (∃ M : ℕ → ℝ,
      (∀ n ∈ ℕ, ∀ x ∈ ℝ, A x → Rabs (fn n x - g x) ≤ M n) ∧ M ⟶ 0).
Proof.
  Admitted.

(** ** The example [fₙ(x) = xⁿ] *)

(** [fₙ(x) = xⁿ] converges pointwise to [0] on [[0, 1)].

    Proof idea: for fixed [0 ≤ x < 1], [xⁿ → 0] (geometric decay); the rate
    depends on how close [x] is to [1]. *)
Lemma x_pow_n_pointwise :
    converges_pointwise (fun n x => x ^ n) (fun _ => 0)
      (fun x => 0 ≤ x ∧ x < 1).
Proof.
  Admitted.

(** The convergence [xⁿ → 0] on [[0, 1)] is *not* uniform.

    Proof idea: for any [n], points [x] near [1] have [xⁿ] near [1], so
    [sup_{x ∈ [0,1)} |xⁿ - 0| = 1] does not tend to [0]; equivalently the
    [Mₙ]-test fails. *)
Lemma x_pow_n_not_uniform :
    ¬ (∃ g : ℝ → ℝ,
        converges_uniformly (fun n x => x ^ n) g (fun x => 0 ≤ x ∧ x < 1)).
Proof.
  Admitted.

(** ** The triangle (tent) sequence *)

(** The *triangle sequence* [Tₙ] is the tent of height [n] and base
    [(0, 2/n)] centred at [1/n]:
    [Tₙ(x) = max(0, n - n²·|x - 1/n|)]. *)
Definition triangle_sequence : ℕ → ℝ → ℝ :=
    fun n x => Rmax 0 (INR n - (INR n) ^ 2 * Rabs (x - / INR n)).

(** The triangle sequence converges pointwise to [0] on [[0, 1]], even though
    each [Tₙ] has a spike of height [n].

    Proof idea: [Tₙ(0) = 0] for all [n]; for a fixed [x > 0], once [2/n < x] the
    support of [Tₙ] no longer contains [x], so [Tₙ(x) = 0] eventually. (This is
    the standard example where [lim ∫ Tₙ ≠ ∫ lim Tₙ].) *)
Lemma triangle_sequence_pointwise :
    converges_pointwise triangle_sequence (fun _ => 0)
      (fun x => 0 ≤ x ∧ x ≤ 1).
Proof.
  Admitted.

(** ** Uniform convergence of [√(x² + 1/n)] *)

(** Exercise: [fₙ(x) = √(x² + 1/n)] converges uniformly to [|x|] on all of [ℝ].

    Proof idea: [0 ≤ √(x² + 1/n) - |x| = (1/n)/(√(x² + 1/n) + |x|) ≤ √(1/n)],
    a bound independent of [x] tending to [0]. *)
Lemma sqrt_x_sq_plus_1_over_n_uniform :
    converges_uniformly (fun n x => sqrt (x ^ 2 + / INR n)) Rabs
      (fun _ => True).
Proof.
  Admitted.

(** ** Uniform convergence and differentiation *)

(** _Differentiability transfer lemma_ (Abbott 6.3.1): if each [fₙ] is
    differentiable on [[a, b]] with derivative [dfnₙ], and the derivatives
    [(dfnₙ)] are uniformly Cauchy, then the differences [fₙ - fₘ] are uniformly
    Lipschitz, with constant controlled by the derivative gap.

    Proof idea: apply the mean value theorem to [fₙ - fₘ] on [[x, y]]:
    [(fₙ - fₘ)(x) - (fₙ - fₘ)(y) = ((dfnₙ - dfnₘ)(ξ))·(x - y)] for some [ξ]. *)
Lemma differentiability_transfer_lemma
    (fn : ℕ → ℝ → ℝ) (dfn : ℕ → ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hderiv : ∀ n ∈ ℕ, ∀ x ∈ ℝ, a ≤ x → x ≤ b →
        ∃ Hd : derivable_pt (fn n) x, derive_pt (fn n) x Hd = dfn n x)
    (Hdcauchy : ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x : ℝ,
        a ≤ x → x ≤ b → Rabs (dfn n x - dfn m x) < ε) :
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      a ≤ x → x ≤ b → a ≤ y → y ≤ b →
      Rabs ((fn n x - fn m x) - (fn n y - fn m y)) ≤ ε * Rabs (x - y).
Proof.
  Admitted.

(** _Differentiability theorem_ (Abbott 6.3.3): if each [fₙ] is differentiable
    on [[a, b]] with derivative [dfnₙ], the derivatives converge uniformly to
    [h], and [(fₙ)] converges at one point, then [(fₙ)] converges uniformly to a
    limit [g] with [g' = h].

    Proof idea: the transfer lemma makes [(fₙ)] uniformly Cauchy (hence
    uniformly convergent to some [g]); a difference-quotient estimate shows [g]
    is differentiable with [g' = h = lim dfnₙ]. *)
Theorem uniform_differentiability_theorem
    (fn : ℕ → ℝ → ℝ) (dfn : ℕ → ℝ → ℝ) (g h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hderiv : ∀ n ∈ ℕ, ∀ x ∈ ℝ, a ≤ x → x ≤ b →
        ∃ Hd : derivable_pt (fn n) x, derive_pt (fn n) x Hd = dfn n x)
    (Hpt : ∃ x0 : ℝ, a ≤ x0 ∧ x0 ≤ b ∧ (fun n => fn n x0) ⟶ g x0)
    (Hdunif : converges_uniformly dfn h (fun x => a ≤ x ∧ x ≤ b)) :
    converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b) ∧
    (∀ x : ℝ, a < x → x < b →
        ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x).
Proof.
  Admitted.

(** ** Series of functions *)

(** The partial sums [Sₙ(x) = ∑_{k=0}^n fₖ(x)] of a series of functions. *)
Definition series_partial_sums (fn : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
    fun n x => sum_f_R0 (fun k => fn k x) n.

(** The series [∑ fₙ] *converges uniformly* to [g] on [A] when its partial sums
    do. *)
Definition series_converges_uniformly
    (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) : Prop :=
    converges_uniformly (series_partial_sums fn) g A.

(** _Cauchy criterion for series of functions_: [∑ fₙ] converges uniformly on
    [A] iff its partial sums are uniformly Cauchy — equivalently the tails
    [∑_{k=n+1}^m fₖ] are uniformly small.

    Proof idea: apply the Cauchy criterion for uniform convergence
    ([uniform_cauchy_criterion]) to the sequence of partial sums. *)
Lemma series_cauchy_criterion_functions (fn : ℕ → ℝ → ℝ) (A : subset ℝ) :
    (∃ g : ℝ → ℝ, series_converges_uniformly fn g A) ⇔
    (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      Rabs (series_partial_sums fn n x - series_partial_sums fn m x) < ε).
Proof.
  Admitted.

(** _Term-wise continuity of a series_: if each [fₙ] is continuous at [a] and
    [∑ fₙ] converges uniformly on a neighbourhood of [a], then the sum is
    continuous at [a].

    Proof idea: each partial sum is continuous (finite sum of continuous
    functions); apply [uniform_limit_continuous] to the partial sums. *)
Theorem termwise_continuity_series
    (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a : ℝ)
    (Hcont : ∀ n ∈ ℕ, continuity_pt (fn n) a)
    (Hunif : ∃ A : subset ℝ, A a ∧ series_converges_uniformly fn g A) :
    continuity_pt g a.
Proof.
  Admitted.

(** _Term-wise differentiability of a series_ (Abbott 6.4.3): if each [fₙ] is
    differentiable on [[a, b]] with derivative [dfnₙ], the series of derivatives
    [∑ dfnₙ] converges uniformly to [h], and [∑ fₙ] converges at one point, then
    [∑ fₙ] converges uniformly to a differentiable [g] with [g' = h].

    Proof idea: apply [uniform_differentiability_theorem] to the partial sums,
    whose derivatives are the partial sums of the derivative series. Compact
    intervals are essential. *)
Theorem termwise_differentiability_series
    (fn : ℕ → ℝ → ℝ) (dfn : ℕ → ℝ → ℝ) (g h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hderiv : ∀ n ∈ ℕ, ∀ x ∈ ℝ, a ≤ x → x ≤ b →
        ∃ Hd : derivable_pt (fn n) x, derive_pt (fn n) x Hd = dfn n x)
    (Hpt : ∃ x0 : ℝ, a ≤ x0 ∧ x0 ≤ b ∧
        (fun n => series_partial_sums fn n x0) ⟶ g x0)
    (Hdunif : series_converges_uniformly dfn h (fun x => a ≤ x ∧ x ≤ b)) :
    series_converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b) ∧
    (∀ x : ℝ, a < x → x < b →
        ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x).
Proof.
  Admitted.
