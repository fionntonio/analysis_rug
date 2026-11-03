(** * RUG.Analysis.Derivatives — Differentiability and the mean value theorem.

  #<a href="../../index.html##lecture09">Lecture 9</a>#.

  Formalizes Abbott §5.2–5.3: differentiability at a point,
  differentiable implies continuous, Fermat's theorem on local extrema,
  the mean value theorem, and Darboux's intermediate value theorem for
  derivatives. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.Ranalysis1.
From Stdlib Require Import Reals.Ranalysis5.
From Stdlib Require Import Reals.MVT.
From Stdlib Require Import micromega.Lra.
Require Export RUG.Analysis.Continuity.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Differentiable implies continuous *)

(** _Differentiability versus continuity_ (Abbott Theorem 5.2.3): if [g] is differentiable at [x₀] then [g] is continuous at
    [x₀]. *)
Lemma differentiable_implies_continuous (g : ℝ → ℝ) (x0 : ℝ)
    (Hd : derivable_pt g x0) :
    continuity_pt g x0.
Proof.
  By derivable_continuous_pt we conclude that continuity_pt g x0.
Qed.

(** ** Fermat's theorem *)

(** If [h] is differentiable on [(a,b)] and has a local extremum at [c ∈ (a,b)],
    then [h'(c) = 0]. *)
Lemma fermat (h : ℝ → ℝ) (a b c : ℝ)
    (Hab : a < b) (Hac : a < c) (HcB : c < b)
    (Hd : ∀ x, a < x < b → derivable_pt h x)
    (Hloc : (∃ δ > 0, ∀ x, Rabs (x - c) < δ → h x ≤ h c) ∨
            (∃ δ > 0, ∀ x, Rabs (x - c) < δ → h c ≤ h x)) :
    derive_pt h c (Hd c (conj Hac HcB)) = 0.
Proof.
  Admitted.

(** ** Mean value theorem *)

(** _Mean value theorem_ (Abbott Theorem 5.3.2): if [h] is continuous on [[a,b]] and
    differentiable on [(a,b)], then there exists [c ∈ (a,b)] with
    [h'(c) = (h(b) - h(a))/(b - a)].

    Proof idea: subtract the secant line from [h] to obtain a function with equal
    values at [a] and [b], then apply Rolle's theorem. *)
Theorem mean_value_theorem (h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hcont : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt h x)
    (Hdiff : ∀ x, a < x ∧ x < b → derivable_pt h x) :
    ∃ c, a < c ∧ c < b ∧
      ∃ Hc : derivable_pt h c,
        derive_pt h c Hc = (h b - h a) / (b - a).
Proof.
  (* Stdlib's [MVT] is the Cauchy form; take the second function to be the
     identity, whose derivative is [1]. *)
  We claim that
    ∀ x : ℝ, a < x ∧ x < b → derivable_pt (fun y => y) x as (Hid).
  {
    Take x : ℝ. Assume that a < x ∧ x < b as (Hx).
    exact (derivable_pt_id x).
  }
  We claim that
    ∀ x : ℝ, a ≤ x ∧ x ≤ b → continuity_pt (fun y => y) x as (Hcid).
  {
    Take x : ℝ. Assume that a ≤ x ∧ x ≤ b as (Hx).
    exact (derivable_continuous_pt (fun y => y) x (derivable_pt_id x)).
  }
  destruct (MVT h (fun y => y) a b Hdiff Hid Hab Hcont Hcid) as [c Hc].
  destruct Hc as [P Heq].
  (* The derivative of the identity is 1, independently of the proof term. *)
  By (pr_nu (fun y => y) c (Hid c P) (derivable_pt_id c)) it holds that
    derive_pt (fun y => y) c (Hid c P)
      = derive_pt (fun y => y) c (derivable_pt_id c) as (Hpr).
  By derive_pt_id it holds that
    derive_pt (fun y => y) c (derivable_pt_id c) = 1 as (Hd1).
  It holds that
    (b - a) * derive_pt h c (Hdiff c P) = h b - h a as (Heq2).
  (* Divide by [b - a]. *)
  It holds that b - a ≠ 0 as (Hne).
  By Rinv_r it holds that (b - a) * / (b - a) = 1 as (Ei).
  It holds that (b - a) * ((h b - h a) / (b - a)) = h b - h a as (Hr).
  It holds that (b - a) * derive_pt h c (Hdiff c P)
    = (b - a) * ((h b - h a) / (b - a)) as (Hmul).
  By Rmult_eq_reg_l it holds that
    derive_pt h c (Hdiff c P) = (h b - h a) / (b - a) as (Hfin).
  Choose c1 := c.
  We claim that
    ∃ Hc : derivable_pt h c,
      derive_pt h c Hc = (h b - h a) / (b - a) as (Hex).
  { Choose Hc := (Hdiff c P). exact Hfin. }
  It holds that a < c as (H1).
  It holds that c < b as (H2).
  We conclude that
    (a < c ∧ c < b ∧
     ∃ Hc : derivable_pt h c, derive_pt h c Hc = (h b - h a) / (b - a)).
Qed.

(** ** Consequence: zero derivative implies constant *)

(** If [φ] is differentiable with [φ'(x) = 0] everywhere, then [φ] is constant. *)
Lemma zero_derivative_constant (phi : ℝ → ℝ) (Hd : derivable phi)
    (Hz : ∀ x ∈ ℝ, derive_pt phi x (Hd x) = 0) :
    ∀ x ∈ ℝ, ∀ y ∈ ℝ, phi x = phi y.
Proof.
  (* Stdlib's [null_derivative_1] gives [constant phi]. *)
  We claim that ∀ x : ℝ, derive_pt phi x (Hd x) = 0 as (Hz').
  {
    Take x : ℝ.
    By Hz we conclude that derive_pt phi x (Hd x) = 0.
  }
  By (null_derivative_1 phi Hd Hz') it holds that constant phi as (Hconst).
  Take x ∈ ℝ. Take y ∈ ℝ.
  By Hconst we conclude that phi x = phi y.
Qed.

(** ** MVT consequence: bound on function growth *)

(** If [|φ'| ≤ M] on an interval, then [|φ(b) - φ(a)| ≤ M · |b - a|]. *)
Lemma mvt_bound (psi : ℝ → ℝ) (Hd : derivable psi) (a v : ℝ)
    (M : ℝ) (HM : ∀ x : ℝ, Rabs (derive_pt psi x (Hd x)) ≤ M) :
    Rabs (psi v - psi a) ≤ M * Rabs (v - a).
Proof.
  (* [MVT_cor1] on the relevant orientation of [[a, v]]. *)
  By HM it holds that Rabs (derive_pt psi a (Hd a)) ≤ M as (Hma).
  By Rabs_pos it holds that 0 ≤ Rabs (derive_pt psi a (Hd a)) as (Hpa).
  It holds that 0 ≤ M as (HM0).
  Either (a < v) or (¬ (a < v)).
  - Case (a < v).
    It holds that a < v as (Hav).
    destruct (MVT_cor1 psi a v Hd Hav) as [c Hc].
    destruct Hc as [Heq Hcin].
    By HM it holds that Rabs (derive_pt psi c (Hd c)) ≤ M as (Hb).
    By Rabs_pos it holds that 0 ≤ Rabs (v - a) as (Hp).
    rewrite Heq.
    By Rabs_mult it holds that
      Rabs (derive_pt psi c (Hd c) * (v - a))
        = Rabs (derive_pt psi c (Hd c)) * Rabs (v - a) as (Hm).
    rewrite Hm.
    We conclude that
      Rabs (derive_pt psi c (Hd c)) * Rabs (v - a) ≤ M * Rabs (v - a).
  - Case (¬ (a < v)).
    Either (v < a) or (¬ (v < a)).
    + Case (v < a).
      It holds that v < a as (Hva).
      destruct (MVT_cor1 psi v a Hd Hva) as [c Hc].
      destruct Hc as [Heq Hcin].
      By HM it holds that Rabs (derive_pt psi c (Hd c)) ≤ M as (Hb).
      By Rabs_minus_sym it holds that
        Rabs (psi v - psi a) = Rabs (psi a - psi v) as (Hsym).
      By Rabs_minus_sym it holds that
        Rabs (a - v) = Rabs (v - a) as (Hsym2).
      By Rabs_pos it holds that 0 ≤ Rabs (v - a) as (Hp).
      rewrite Hsym. rewrite Heq.
      By Rabs_mult it holds that
        Rabs (derive_pt psi c (Hd c) * (a - v))
          = Rabs (derive_pt psi c (Hd c)) * Rabs (a - v) as (Hm).
      rewrite Hm. rewrite Hsym2.
      We conclude that
        Rabs (derive_pt psi c (Hd c)) * Rabs (v - a) ≤ M * Rabs (v - a).
    + Case (¬ (v < a)).
      It holds that a = v as (Heqav).
      rewrite Heqav.
      We conclude that Rabs (psi v - psi v) ≤ M * Rabs (v - v).
Qed.

(** ** Derivative of the squaring function *)

(** Example (Abbott Example 5.2.2(i) with [n = 2]): the derivative of [x ↦ x²] at [x₀] is [2·x₀].

    Proof idea: apply the power rule [d/dx xⁿ = n·xⁿ⁻¹] with [n = 2]. *)
Lemma sq_derivative (x0 : ℝ) :
    derive_pt (fun y => y ^ 2) x0 (derivable_pt_pow 2 x0) = 2 * x0.
Proof.
  (* Power rule with [n = 2]. *)
  rewrite derive_pt_pow.
  We conclude that INR 2 * x0 ^ (2 - 1) = 2 * x0.
Qed.

(** ** Rolle's theorem *)

(** _Rolle's theorem_ (Abbott Theorem 5.3.1): if [h] is continuous on [[a,b]],
    differentiable on [(a,b)] and [h a = h b], then [h'(c) = 0] for some
    [c ∈ (a,b)].

    Proof idea: by the extreme value theorem [h] attains a maximum and a minimum
    on [[a,b]]. If both occur at the endpoints then [h] is constant and any
    interior point works; otherwise an interior extremum has, by Fermat's
    theorem, a vanishing derivative. *)
Lemma rolle_theorem (h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hcont : ∀ c : ℝ, a ≤ c ∧ c ≤ b → continuity_pt h c)
    (Hd : ∀ c : ℝ, a < c ∧ c < b → derivable_pt h c)
    (Heq : h a = h b) :
    ∃ c : ℝ, a < c ∧ c < b ∧ ∃ Hc : a < c ∧ c < b, derive_pt h c (Hd c Hc) = 0.
Proof.
  (* This is Stdlib's [Rolle], repackaged. *)
  destruct (Rolle h a b Hd Hcont Hab Heq) as [c Hc].
  destruct Hc as [P Hderiv].
  Choose c1 := c.
  We claim that
    ∃ Hc : a < c ∧ c < b, derive_pt h c (Hd c Hc) = 0 as (Hex).
  { Choose Hc := P. exact Hderiv. }
  It holds that a < c as (H1).
  It holds that c < b as (H2).
  We conclude that
    (a < c ∧ c < b ∧ ∃ Hc : a < c ∧ c < b, derive_pt h c (Hd c Hc) = 0).
Qed.

(** ** Darboux's theorem *)

(** _Darboux's theorem_ (Abbott Theorem 5.2.7): derivatives have the intermediate value property.
    If [h] is differentiable on [[a,b]] and [v] lies strictly between [h'(a)]
    and [h'(b)], then [h'(c) = v] for some [c ∈ (a,b)] — even though [h'] need
    not be continuous.

    Proof idea: consider [g(x) = h(x) - v·x], which is differentiable with
    [g'(a)] and [g'(b)] of opposite sign. By the extreme value theorem [g]
    attains an interior extremum at some [c ∈ (a,b)], and Fermat's theorem gives
    [g'(c) = 0], i.e. [h'(c) = v]. *)
Theorem darboux_theorem (h : ℝ → ℝ) (a b v : ℝ) (Hab : a < b)
    (Hd : derivable h)
    (Hva : derive_pt h a (Hd a) < v)
    (Hvb : v < derive_pt h b (Hd b)) :
    ∃ c, a < c ∧ c < b ∧ derive_pt h c (Hd c) = v.
Proof.
  Admitted.

(** ** A differentiability example *)

(** Exercise: the function [g(x) = x²·sin(1/x)] for [x ≠ 0] and [g(0) = 0] is
    differentiable at [0] with [g'(0) = 0], yet [g'] is not continuous at [0].

    Proof idea: the difference quotient [g(x)/x = x·sin(1/x) → 0] as [x → 0] by
    the squeeze theorem, so [g'(0) = 0]. For [x ≠ 0],
    [g'(x) = 2x·sin(1/x) - cos(1/x)] has no limit as [x → 0]. *)
Lemma differentiable_example
    (g : ℝ → ℝ)
    (Hg : ∀ x : ℝ, x ≠ 0 → g x = x ^ 2 * sin (1 / x)) (Hg0 : g 0 = 0) :
    ∃ Hd : derivable_pt g 0, derive_pt g 0 Hd = 0.
Proof.
  Admitted.

(** ** A continuous nowhere-differentiable function *)

(** Pathology: there exists a function [f : ℝ → ℝ] that is continuous at every
    point yet differentiable at no point.

    Proof idea (Weierstrass / Abbott's construction): let [w(x)] be the
    distance from [x] to the nearest integer, and set
    [f(x) = ∑ (1/2)ⁿ · w(2ⁿ x)]. The series converges uniformly (Weierstrass
    M-test) so [f] is continuous; a careful estimate of difference quotients
    along dyadic points shows [f] is differentiable nowhere. *)
Theorem nowhere_differentiable_function :
    ∃ f : ℝ → ℝ,
      (∀ x : ℝ, continuity_pt f x) ∧
      (∀ x : ℝ, ¬ (∃ l : ℝ, derivable_pt_lim f x l)).
Proof.
  Admitted.

(** ** Positive derivative implies strictly increasing *)

(** A consequence of the _mean value theorem_: if [ψ' > 0] on [(a,v)] then [ψ] is strictly increasing on
    [[a,v]].

    Proof idea: for [a ≤ x < y ≤ v], the mean value theorem gives a point
    [c ∈ (x,y) ⊂ (a,v)] with [ψ(y) - ψ(x) = ψ'(c)·(y - x)]. Since [ψ'(c) > 0]
    and [y - x > 0], we get [ψ(y) > ψ(x)]. *)
Lemma positive_derivative_strictly_increasing (psi : ℝ → ℝ) (Hd : derivable psi)
    (a v : ℝ)
    (Hderiv_pos : ∀ x : ℝ, a < x ∧ x < v → 0 < derive_pt psi x (Hd x)) :
    ∀ x ∈ ℝ, ∀ y ∈ ℝ, a ≤ x → x < y → y ≤ v → psi x < psi y.
Proof.
  (* Exactly Stdlib's [derive_increasing_interv]. *)
  Take x ∈ ℝ. Take y ∈ ℝ.
  Assume that a ≤ x as (H1).
  Assume that x < y as (H2).
  Assume that y ≤ v as (H3).
  It holds that a < v as (Hav).
  It holds that a ≤ x ∧ x ≤ v as (Hx).
  It holds that a ≤ y ∧ y ≤ v as (Hy).
  exact (derive_increasing_interv a v psi Hd Hav Hderiv_pos x y Hx Hy H2).
Qed.
