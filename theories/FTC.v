(** * RUG.Analysis.FTC — The fundamental theorem of calculus.

  #<a href="../../index.html##lecture14">Lecture 14</a>#.

  Formalizes Abbott §7.4–7.5: further properties of the integral (bound by the
  supremum, order property, [|∫f| ≤ ∫|f|]), the oriented integral, the two
  parts of the fundamental theorem, and integration by parts. *)

Require Import RUG.Analysis.Lib.StdlibReals.
Require Export RUG.Analysis.Integration.
Require Export RUG.Analysis.Derivatives.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Bound by the supremum *)

(** _Integral bound_: if [f ≤ M] on [[a, b]] (with [a ≤ b]), then
    [∫_a^b f ≤ (b - a)·M].

    Proof idea: on every partition each cell's supremum is at most [M], so every
    upper sum is at most [(b - a)·M]; the integral is the infimum of the upper
    sums. *)
Lemma integral_bound_sup (f : ℝ → ℝ) (a b M : ℝ) (Hab : a ≤ b)
    (prf : Riemann_integrable f a b)
    (HM : ∀ x : ℝ, a ≤ x ∧ x ≤ b → f x ≤ M) :
    RiemannInt prf ≤ (b - a) * M.
Proof.
  (** Compare with the constant function [M] and evaluate its integral. The
      comparison is an inequality of [RiemannInt] terms, on which Waterproof
      automation does not finish within minutes (even with the lemma fully
      applied), so it is done with [apply]/[exact]. *)
  Define prc := (RiemannInt_P14 a b M).
  apply (Rle_trans (RiemannInt prf) (RiemannInt prc) ((b - a) * M)).
  - exact (integral_monotone f (fct_cte M) a b Hab prf prc HM).
  - rewrite (RiemannInt_P15 prc).
    We conclude that M * (b - a) ≤ (b - a) * M.
Qed.

(** ** Order property and absolute value *)

(** _Order property_: if [f ≤ g] on [[a, b]] then [∫_a^b f ≤ ∫_a^b g]. (This is
    [integral_monotone] from [Analysis.Integration], restated as the order form
    of Lecture 15.) *)
Lemma integral_order (f g : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (prf : Riemann_integrable f a b)
    (prg : Riemann_integrable g a b)
    (Hle : ∀ x : ℝ, a ≤ x ∧ x ≤ b → f x ≤ g x) :
    RiemannInt prf ≤ RiemannInt prg.
Proof.
  (** [By integral_monotone we conclude that …] does not finish within
      minutes on this [RiemannInt] goal, so we give the proof term directly. *)
  exact (integral_monotone f g a b Hab prf prg Hle).
Qed.

(** _Triangle inequality for integrals_: [|f|] is integrable and
    [|∫_a^b f| ≤ ∫_a^b |f|] (for [a ≤ b]).

    Proof idea: [-|f| ≤ f ≤ |f|]; integrating and using the order property gives
    [-∫|f| ≤ ∫f ≤ ∫|f|], i.e. [|∫f| ≤ ∫|f|]. *)
Lemma integral_abs_le (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (prf : Riemann_integrable f a b) :
    ∃ prabs : Riemann_integrable (fun x => Rabs (f x)) a b,
      Rabs (RiemannInt prf) ≤ RiemannInt prabs.
Proof.
  (** [RiemannInt_P16] gives integrability of [|f|], [RiemannInt_P17] the
      bound. The bound is a [RiemannInt] inequality, on which Waterproof
      automation does not finish within minutes, so we give the proof term
      directly. *)
  Choose prabs := (RiemannInt_P16 prf).
  exact (RiemannInt_P17 prf (RiemannInt_P16 prf) Hab).
Qed.

(** ** The oriented integral *)

(** The *oriented* (signed) integral sets [∫_a^b f = -∫_b^a f] when [a > b], so
    that additivity holds for any ordering of the endpoints. It is defined from
    the ordinary integral over the sorted interval [[min a b, max a b]]. *)
Definition RiemannInt_oriented (f : ℝ → ℝ) (a b : ℝ)
    (pr : Riemann_integrable f (Rmin a b) (Rmax a b)) : ℝ :=
    if Rle_dec a b then RiemannInt pr else - RiemannInt pr.

(** ** Additivity (Chasles property) *)

(** _Chasles / additivity_: if [f] is integrable on [[a,b]], [[b,c]] and
    [[a,c]], then [∫_a^b f + ∫_b^c f = ∫_a^c f], regardless of the ordering of
    [a], [b], [c]. *)
Lemma integral_additive (f : ℝ → ℝ) (a b c : ℝ)
    (pr1 : Riemann_integrable f a b)
    (pr2 : Riemann_integrable f b c)
    (pr3 : Riemann_integrable f a c) :
    RiemannInt pr3 = RiemannInt pr1 + RiemannInt pr2.
Proof.
  (** Stdlib's Chasles relation. Waterproof automation does not finish within
      minutes on this [RiemannInt] equality, so we use [symmetry] and the
      proof term. *)
  symmetry.
  exact (RiemannInt_P26 pr1 pr2 pr3).
Qed.

(** _Additivity for the oriented integral_: with the sign convention above,
    [∫_a^b f + ∫_b^c f = ∫_a^c f] holds for *every* arrangement of [a], [b],
    [c]. *)
Lemma integral_additive_any_order (f : ℝ → ℝ) (a b c : ℝ)
    (pr1 : Riemann_integrable f (Rmin a b) (Rmax a b))
    (pr2 : Riemann_integrable f (Rmin b c) (Rmax b c))
    (pr3 : Riemann_integrable f (Rmin a c) (Rmax a c)) :
    RiemannInt_oriented f a c pr3 =
      RiemannInt_oriented f a b pr1 + RiemannInt_oriented f b c pr2.
Proof.
  Admitted.

(** ** Fundamental theorem of calculus, Part 1 (antiderivative formula) *)

(** _FTC, Part 1_: if [f] is continuous on [[a,b]] and [g] is an antiderivative
    of [f] (so [g' = f] on [[a,b]]), then [∫_a^b f = g(b) - g(a)].

    Proof idea: the canonical integral function [G(x) = ∫_a^x f] is an
    antiderivative of [f] (Part 2), and [∫_a^b f = G(b) - G(a)]. Since [G] and
    [g] are both antiderivatives of the continuous [f], they differ by a
    constant, so [G(b) - G(a) = g(b) - g(a)]. *)
Theorem ftc_part1 (f g : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (prf : Riemann_integrable f a b)
    (Hg  : derivable g)
    (Hant : ∀ x : ℝ, a ≤ x ∧ x ≤ b → derive_pt g x (Hg x) = f x) :
    RiemannInt prf = g b - g a.
Proof.
  Admitted.

(** ** Fundamental theorem of calculus, Part 2 (derivative of the integral) *)

(** [F] is *the integral function* of [f] based at [a] if [F x = ∫_a^x f] for
    every [x] (for whatever integrability witness). *)
Definition is_integral_function (f F : ℝ → ℝ) (a : ℝ) : Prop :=
    ∀ x : ℝ, ∀ pr : Riemann_integrable f a x, F x = RiemannInt pr.

(** _FTC, Part 2_: if [f] is continuous on [[a,b]], then the integral function
    [F(x) = ∫_a^x f] is continuous on [[a,b]] and differentiable on [(a,b)] with
    [F'(x) = f(x)].

    Proof idea: for [x ≠ c],
    [(F(x) - F(c))/(x - c) - f(c) = 1/(x - c)·∫_c^x (f(t) - f(c)) dt]. Given
    [ε > 0], continuity of [f] at [c] gives [δ] with [|f(t) - f(c)| < ε] for
    [|t - c| < δ]; then for [|x - c| < δ] the difference quotient is within [ε]
    of [f(c)]. *)
Theorem ftc_part2 (f F : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x : ℝ, a ≤ x ∧ x ≤ b → continuity_pt f x)
    (HF : is_integral_function f F a) :
    (∀ x : ℝ, a ≤ x ∧ x ≤ b → continuity_pt F x) ∧
    (∀ c : ℝ, a < c ∧ c < b →
        ∃ Hd : derivable_pt F c, derive_pt F c Hd = f c).
Proof.
  Admitted.

(** ** Integration by parts *)

(** _Integration by parts_: if [f] and [g] are continuously differentiable on
    [[a, b]], then [∫_a^b f g' = f(b)g(b) - f(a)g(a) - ∫_a^b f' g].

    Proof idea: apply Part 1 to the product [f·g], whose derivative is
    [f'·g + f·g'] by the product rule; splitting the integral by linearity and
    rearranging gives the formula. *)
Theorem integration_by_parts (f g : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : derivable f) (Hg : derivable g)
    (Hfcont : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt (fun x => derive_pt f x (Hf x)) x)
    (Hgcont : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt (fun x => derive_pt g x (Hg x)) x) :
    ∃ (pr1 : Riemann_integrable (fun x => f x * derive_pt g x (Hg x)) a b),
    ∃ (pr2 : Riemann_integrable (fun x => derive_pt f x (Hf x) * g x) a b),
      RiemannInt pr1 = f b * g b - f a * g a - RiemannInt pr2.
Proof.
  Admitted.

(** ** Application: ∫₀¹ x dx = 1/2

    [∫₀¹ x dx = 1/2], by Part 1 with antiderivative [F(x) = x²/2]:
    [F(1) - F(0) = 1/2 - 0 = 1/2]. *)
Lemma integral_id_unit (pr : Riemann_integrable id 0 1) :
    RiemannInt pr = 1 / 2.
Proof.
  Admitted.
