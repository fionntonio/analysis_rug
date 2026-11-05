(** * RUG.Analysis.Derivatives — Differentiability and the mean value theorem.

  #<a href="../../index.html##lecture09">Lecture 9</a>#.

  Formalizes Abbott §5.2–5.3: differentiability at a point,
  differentiable implies continuous, Fermat's theorem on local extrema,
  the mean value theorem, and Darboux's intermediate value theorem for
  derivatives. *)

Require Import RUG.Analysis.Lib.StdlibReals.
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
  Because (Hloc) either (∃ δ > 0, ∀ x, |x - c| < δ → h x ≤ h c)
    or (∃ δ > 0, ∀ x, |x - c| < δ → h c ≤ h x).
  - Case (∃ δ > 0, ∀ x, |x - c| < δ → h x ≤ h c).
    Obtain such a δ.
    It holds that ∀ x, |x - c| < δ → h x ≤ h c as (Hmax).
    We claim that ∀ x : ℝ, c - δ < x → x < c + δ → h x ≤ h c as (Hmax').
    {
      Take x : ℝ. Assume that c - δ < x. Assume that x < c + δ.
      It holds that x - c < δ ∧ - δ < x - c.
      By (Rabs_def1 (x - c) δ) it holds that |x - c| < δ as (H4).
      By (Hmax x H4) we conclude that h x ≤ h c.
    }
    It holds that c - δ < c as (Hl).
    It holds that c < c + δ as (Hr).
    By (deriv_maximum h (c - δ) (c + δ) c (Hd c (conj Hac HcB)) Hl Hr Hmax')
      we conclude that derive_pt h c (Hd c (conj Hac HcB)) = 0.
  - Case (∃ δ > 0, ∀ x, |x - c| < δ → h c ≤ h x).
    Obtain such a δ.
    It holds that ∀ x, |x - c| < δ → h c ≤ h x as (Hmin).
    We claim that ∀ x : ℝ, c - δ < x → x < c + δ → h c ≤ h x as (Hmin').
    {
      Take x : ℝ. Assume that c - δ < x. Assume that x < c + δ.
      It holds that x - c < δ ∧ - δ < x - c.
      By (Rabs_def1 (x - c) δ) it holds that |x - c| < δ as (H4).
      By (Hmin x H4) we conclude that h c ≤ h x.
    }
    It holds that c - δ < c as (Hl).
    It holds that c < c + δ as (Hr).
    By (deriv_minimum h (c - δ) (c + δ) c (Hd c (conj Hac HcB)) Hl Hr Hmin')
      we conclude that derive_pt h c (Hd c (conj Hac HcB)) = 0.
Qed.


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
    Take x : ℝ. Assume that a < x ∧ x < b.
    By derivable_pt_id we conclude that derivable_pt (fun y => y) x.
  }
  We claim that
    ∀ x : ℝ, a ≤ x ∧ x ≤ b → continuity_pt (fun y => y) x as (Hcid).
  {
    Take x : ℝ. Assume that a ≤ x ∧ x ≤ b.
    By (derivable_continuous_pt (fun y => y) x (derivable_pt_id x))
      we conclude that continuity_pt (fun y => y) x.
  }
  By (MVT h (fun y => y) a b Hdiff Hid Hab Hcont Hcid) it holds that
    ∃ c : ℝ, ∃ P : a < c ∧ c < b,
      (b - a) * derive_pt h c (Hdiff c P)
        = (h b - h a) * derive_pt (fun y => y) c (Hid c P) as (Hmvt).
  Obtain c according to (Hmvt).
  It holds that
    ∃ P : a < c ∧ c < b,
      (b - a) * derive_pt h c (Hdiff c P)
        = (h b - h a) * derive_pt (fun y => y) c (Hid c P) as (HP).
  Obtain P according to (HP).
  (* The derivative of the identity is 1, independently of the proof term. *)
  By (pr_nu (fun y => y) c (Hid c P) (derivable_pt_id c)) it holds that
    derive_pt (fun y => y) c (Hid c P)
      = derive_pt (fun y => y) c (derivable_pt_id c).
  By derive_pt_id it holds that
    derive_pt (fun y => y) c (derivable_pt_id c) = 1.
  It holds that
    (b - a) * derive_pt h c (Hdiff c P) = h b - h a.
  (* Divide by [b - a]. *)
  It holds that b - a ≠ 0.
  By Rinv_r it holds that (b - a) * / (b - a) = 1.
  It holds that (b - a) * ((h b - h a) / (b - a)) = h b - h a.
  It holds that (b - a) * derive_pt h c (Hdiff c P)
    = (b - a) * ((h b - h a) / (b - a)).
  By Rmult_eq_reg_l it holds that
    derive_pt h c (Hdiff c P) = (h b - h a) / (b - a) as (Hfin).
  Choose c1 := c.
  We claim that
    ∃ Hc : derivable_pt h c,
      derive_pt h c Hc = (h b - h a) / (b - a).
  {
    Choose Hc := (Hdiff c P).
    We conclude that derive_pt h c (Hdiff c P) = (h b - h a) / (b - a).
  }
  It holds that a < c.
  It holds that c < b.
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
  By HM it holds that Rabs (derive_pt psi a (Hd a)) ≤ M.
  By Rabs_pos it holds that 0 ≤ Rabs (derive_pt psi a (Hd a)).
  It holds that 0 ≤ M.
  Either (a < v) or (¬ (a < v)).
  - Case (a < v).
    It holds that a < v as (Hav).
    By (MVT_cor1 psi a v Hd Hav) it holds that
      ∃ c : ℝ, psi v - psi a = derive_pt psi c (Hd c) * (v - a) ∧
        (a < c ∧ c < v) as (Hmvt).
    Obtain c according to (Hmvt).
    It holds that psi v - psi a = derive_pt psi c (Hd c) * (v - a) as (Heq).
    By HM it holds that Rabs (derive_pt psi c (Hd c)) ≤ M.
    By Rabs_pos it holds that 0 ≤ Rabs (v - a).
    By Rabs_mult it holds that
      Rabs (derive_pt psi c (Hd c) * (v - a))
        = Rabs (derive_pt psi c (Hd c)) * Rabs (v - a).
    It holds that
      Rabs (psi v - psi a) = Rabs (derive_pt psi c (Hd c)) * Rabs (v - a).
    By Rmult_le_compat_r it holds that
      Rabs (derive_pt psi c (Hd c)) * Rabs (v - a) ≤ M * Rabs (v - a).
    We conclude that Rabs (psi v - psi a) ≤ M * Rabs (v - a).
  - Case (¬ (a < v)).
    Either (v < a) or (¬ (v < a)).
    + Case (v < a).
      It holds that v < a as (Hva).
      By (MVT_cor1 psi v a Hd Hva) it holds that
        ∃ c : ℝ, psi a - psi v = derive_pt psi c (Hd c) * (a - v) ∧
          (v < c ∧ c < a) as (Hmvt).
      Obtain c according to (Hmvt).
      It holds that psi a - psi v = derive_pt psi c (Hd c) * (a - v) as (Heq).
      By HM it holds that Rabs (derive_pt psi c (Hd c)) ≤ M.
      By Rabs_minus_sym it holds that Rabs (psi v - psi a) = Rabs (psi a - psi v).
      By Rabs_minus_sym it holds that Rabs (a - v) = Rabs (v - a).
      By Rabs_pos it holds that 0 ≤ Rabs (v - a).
      By Rabs_mult it holds that
        Rabs (derive_pt psi c (Hd c) * (a - v))
          = Rabs (derive_pt psi c (Hd c)) * Rabs (a - v).
      It holds that
        Rabs (psi v - psi a) = Rabs (derive_pt psi c (Hd c)) * Rabs (v - a).
      By Rmult_le_compat_r it holds that
        Rabs (derive_pt psi c (Hd c)) * Rabs (v - a) ≤ M * Rabs (v - a).
      We conclude that Rabs (psi v - psi a) ≤ M * Rabs (v - a).
    + Case (¬ (v < a)).
      It holds that a = v as (Heqav).
      It holds that psi a = psi v.
      It holds that psi v - psi a = 0.
      It holds that v - a = 0.
      By Rabs_R0 it holds that Rabs 0 = 0.
      We conclude that Rabs (psi v - psi a) ≤ M * Rabs (v - a).
Qed.

(** ** Derivative of the squaring function *)

(** Example (Abbott Example 5.2.2(i) with [n = 2]): the derivative of [x ↦ x²] at [x₀] is [2·x₀].

    Proof idea: apply the power rule [d/dx xⁿ = n·xⁿ⁻¹] with [n = 2]. *)
Lemma sq_derivative (x0 : ℝ) :
    derive_pt (fun y => y ^ 2) x0 (derivable_pt_pow 2 x0) = 2 * x0.
Proof.
  (* Power rule with [n = 2]. *)
  By derive_pt_pow it holds that
    derive_pt (fun y => y ^ 2) x0 (derivable_pt_pow 2 x0) = INR 2 * x0 ^ (2 - 1).
  We conclude that
    derive_pt (fun y => y ^ 2) x0 (derivable_pt_pow 2 x0) = 2 * x0.
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
  By (Rolle h a b Hd Hcont Hab Heq) it holds that
    ∃ c : ℝ, ∃ P : a < c ∧ c < b, derive_pt h c (Hd c P) = 0 as (Hrolle).
  Obtain c according to (Hrolle).
  It holds that ∃ P : a < c ∧ c < b, derive_pt h c (Hd c P) = 0 as (HP).
  Obtain P according to (HP).
  Choose c1 := c.
  We claim that
    ∃ Hc : a < c ∧ c < b, derive_pt h c (Hd c Hc) = 0.
  {
    Choose Hc := P.
    We conclude that derive_pt h c (Hd c P) = 0.
  }
  It holds that a < c.
  It holds that c < b.
  We conclude that
    (a < c ∧ c < b ∧ ∃ Hc : a < c ∧ c < b, derive_pt h c (Hd c Hc) = 0).
Qed.

(** ** Darboux's theorem *)

(** A negative derivative at [x₀] gives smaller values just to the right of [x₀]. *)
Lemma deriv_neg_right (phi : ℝ → ℝ) (x0 l d0 : ℝ)
    (Hl : derivable_pt_lim phi x0 l) (Hneg : l < 0) (Hd0 : d0 > 0) :
    ∃ k : ℝ, 0 < k ∧ k < d0 ∧ phi (x0 + k) < phi x0.
Proof.
  It holds that - l > 0 as (Hnl).
  By (Hl (- l) Hnl) it holds that ∃ δ : posreal, ∀ k : ℝ, k ≠ 0 → |k| < δ →
    |(phi (x0 + k) - phi x0) / k - l| < - l as (Hδ).
  Obtain δ according to (Hδ).
  It holds that ∀ k : ℝ, k ≠ 0 → |k| < δ →
    |(phi (x0 + k) - phi x0) / k - l| < - l as (Hδ').
  By (cond_pos δ) it holds that δ > 0 as (Hδpos).
  Define k := Rmin (δ / 2) (d0 / 2).
  By (Rmin_l (δ / 2) (d0 / 2)) it holds that k ≤ δ / 2.
  By (Rmin_r (δ / 2) (d0 / 2)) it holds that k ≤ d0 / 2.
  By (Rmin_pos (δ / 2) (d0 / 2)) it holds that 0 < k.
  It holds that k ≠ 0 as (Hkn).
  By (Rabs_pos_eq k) it holds that |k| = k.
  It holds that |k| < δ as (Hkd).
  By (Hδ' k Hkn Hkd) it holds that |(phi (x0 + k) - phi x0) / k - l| < - l as (Hq).
  By (Rabs_def2 ((phi (x0 + k) - phi x0) / k - l) (- l) Hq) it holds that
    (phi (x0 + k) - phi x0) / k - l < - l ∧ - - l < (phi (x0 + k) - phi x0) / k - l.
  It holds that (phi (x0 + k) - phi x0) / k < 0.
  By (Rinv_l k Hkn) it holds that / k * k = 1.
  It holds that (phi (x0 + k) - phi x0) / k * k = phi (x0 + k) - phi x0.
  It holds that (phi (x0 + k) - phi x0) / k * k < 0.
  It holds that phi (x0 + k) < phi x0.
  It holds that k < d0.
  Choose k0 := k.
  We conclude that 0 < k0 ∧ k0 < d0 ∧ phi (x0 + k0) < phi x0.
Qed.

(** Dually, a positive derivative at [x₀] gives smaller values just to the left. *)
Lemma deriv_pos_left (phi : ℝ → ℝ) (x0 l d0 : ℝ)
    (Hl : derivable_pt_lim phi x0 l) (Hpos : l > 0) (Hd0 : d0 > 0) :
    ∃ k : ℝ, 0 < k ∧ k < d0 ∧ phi (x0 - k) < phi x0.
Proof.
  By (Hl l Hpos) it holds that ∃ δ : posreal, ∀ k : ℝ, k ≠ 0 → |k| < δ →
    |(phi (x0 + k) - phi x0) / k - l| < l as (Hδ).
  Obtain δ according to (Hδ).
  It holds that ∀ k : ℝ, k ≠ 0 → |k| < δ →
    |(phi (x0 + k) - phi x0) / k - l| < l as (Hδ').
  By (cond_pos δ) it holds that δ > 0 as (Hδpos).
  Define k := Rmin (δ / 2) (d0 / 2).
  By (Rmin_l (δ / 2) (d0 / 2)) it holds that k ≤ δ / 2.
  By (Rmin_r (δ / 2) (d0 / 2)) it holds that k ≤ d0 / 2.
  By (Rmin_pos (δ / 2) (d0 / 2)) it holds that 0 < k.
  It holds that - k ≠ 0 as (Hkn).
  By (Rabs_Ropp k) it holds that |- k| = |k|.
  By (Rabs_pos_eq k) it holds that |k| = k.
  It holds that |- k| < δ as (Hkd).
  By (Hδ' (- k) Hkn Hkd) it holds that
    |(phi (x0 + - k) - phi x0) / (- k) - l| < l as (Hq).
  By (Rabs_def2 ((phi (x0 + - k) - phi x0) / (- k) - l) l Hq) it holds that
    (phi (x0 + - k) - phi x0) / (- k) - l < l ∧ - l < (phi (x0 + - k) - phi x0) / (- k) - l.
  It holds that 0 < (phi (x0 + - k) - phi x0) / (- k).
  By (Rinv_l (- k) Hkn) it holds that / (- k) * (- k) = 1.
  It holds that (phi (x0 + - k) - phi x0) / (- k) * (- k) = phi (x0 + - k) - phi x0.
  It holds that (phi (x0 + - k) - phi x0) / (- k) * (- k) < 0.
  It holds that x0 + - k = x0 - k as (Ex).
  It holds that phi (x0 + - k) < phi x0.
  By Ex it holds that phi (x0 - k) < phi x0.
  It holds that k < d0.
  Choose k0 := k.
  We conclude that 0 < k0 ∧ k0 < d0 ∧ phi (x0 - k0) < phi x0.
Qed.

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
  (** The auxiliary function [φ(x) = h(x) - v·x] has [φ' = h' - v]. *)
  We claim that ∀ y : ℝ, derivable_pt_lim (fun x => h x - v * x) y (derive_pt h y (Hd y) - v)
    as (Hphi).
  {
    Take y : ℝ.
    It holds that derive_pt h y (Hd y) = derive_pt h y (Hd y) as (Er).
    By (derive_pt_eq_1 h y (derive_pt h y (Hd y)) (Hd y) Er) it holds that
      derivable_pt_lim h y (derive_pt h y (Hd y)) as (H1).
    By (derivable_pt_lim_scal id v y 1 (derivable_pt_lim_id y)) it holds that
      derivable_pt_lim (fun x => v * x) y (v * 1) as (H2).
    By (derivable_pt_lim_minus h (fun x => v * x) y _ _ H1 H2) it holds that
      derivable_pt_lim (fun x => h x - v * x) y (derive_pt h y (Hd y) - v * 1) as (H3).
    It holds that derive_pt h y (Hd y) - v = derive_pt h y (Hd y) - v * 1 as (E1).
    By E1 we conclude that
      derivable_pt_lim (fun x => h x - v * x) y (derive_pt h y (Hd y) - v).
  }
  (** [φ] is continuous, so it attains a minimum on [[a, b]]. *)
  We claim that ∀ x, a ≤ x ∧ x ≤ b → continuity_pt (fun x => h x - v * x) x as (Hcont).
  {
    Take x : ℝ. Assume that a ≤ x ∧ x ≤ b.
    Define Hdx := @exist ℝ (fun l : ℝ => derivable_pt_abs (fun x => h x - v * x) x l)
      (derive_pt h x (Hd x) - v) (Hphi x).
    By (derivable_continuous_pt (fun x => h x - v * x) x Hdx) we conclude that
      continuity_pt (fun x => h x - v * x) x.
  }
  It holds that a ≤ b as (Hab').
  By (extreme_value_theorem_min (fun x => h x - v * x) a b Hab' Hcont) it holds that
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → h c - v * c ≤ h x - v * x as (Hmin).
  Obtain c according to (Hmin).
  It holds that a ≤ c.
  It holds that c ≤ b.
  It holds that ∀ x, a ≤ x ∧ x ≤ b → h c - v * c ≤ h x - v * x as (Hminc).
  It holds that b - a > 0 as (Hba).
  (** The minimum is not at [a], because [φ'(a) < 0]. *)
  We claim that a < c as (Hac').
  {
    We argue by contradiction.
    Assume that ¬ (a < c).
    It holds that c = a as (Eca).
    It holds that derive_pt h a (Hd a) - v < 0 as (Hneg).
    By (deriv_neg_right (fun x => h x - v * x) a (derive_pt h a (Hd a) - v) (b - a)
          (Hphi a) Hneg Hba) it holds that
      ∃ k : ℝ, 0 < k ∧ k < b - a ∧ h (a + k) - v * (a + k) < h a - v * a as (Hk).
    Obtain k according to (Hk).
    It holds that h (a + k) - v * (a + k) < h a - v * a.
    It holds that a ≤ a + k ∧ a + k ≤ b as (Hk2).
    By (Hminc (a + k) Hk2) it holds that h c - v * c ≤ h (a + k) - v * (a + k).
    By Eca it holds that h a - v * a ≤ h (a + k) - v * (a + k).
    Contradiction.
  }
  (** The minimum is not at [b], because [φ'(b) > 0]. *)
  We claim that c < b as (Hcb').
  {
    We argue by contradiction.
    Assume that ¬ (c < b).
    It holds that c = b as (Ecb).
    It holds that derive_pt h b (Hd b) - v > 0 as (Hpos).
    By (deriv_pos_left (fun x => h x - v * x) b (derive_pt h b (Hd b) - v) (b - a)
          (Hphi b) Hpos Hba) it holds that
      ∃ k : ℝ, 0 < k ∧ k < b - a ∧ h (b - k) - v * (b - k) < h b - v * b as (Hk).
    Obtain k according to (Hk).
    It holds that h (b - k) - v * (b - k) < h b - v * b.
    It holds that a ≤ b - k ∧ b - k ≤ b as (Hk2).
    By (Hminc (b - k) Hk2) it holds that h c - v * c ≤ h (b - k) - v * (b - k).
    By Ecb it holds that h b - v * b ≤ h (b - k) - v * (b - k).
    Contradiction.
  }
  (** At the interior minimum, [φ'(c) = 0] (Fermat). *)
  Define Hdc := @exist ℝ (fun l : ℝ => derivable_pt_abs (fun x => h x - v * x) c l)
    (derive_pt h c (Hd c) - v) (Hphi c).
  We claim that ∀ x : ℝ, a < x → x < b → h c - v * c ≤ h x - v * x as (Hmin').
  {
    Take x : ℝ. Assume that a < x. Assume that x < b.
    It holds that a ≤ x ∧ x ≤ b as (H3).
    By (Hminc x H3) we conclude that h c - v * c ≤ h x - v * x.
  }
  By (deriv_minimum (fun x => h x - v * x) a b c Hdc Hac' Hcb' Hmin') it holds that
    derive_pt (fun x => h x - v * x) c Hdc = 0.
  By (derive_pt_eq_0 (fun x => h x - v * x) c (derive_pt h c (Hd c) - v) Hdc (Hphi c))
    it holds that derive_pt (fun x => h x - v * x) c Hdc = derive_pt h c (Hd c) - v.
  It holds that derive_pt h c (Hd c) = v.
  Choose c0 := c.
  We conclude that a < c0 ∧ c0 < b ∧ derive_pt h c0 (Hd c0) = v.
Qed.


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
  We claim that derivable_pt_lim g 0 0 as (Hlim).
  {
    We need to show that ∀ eps : ℝ, 0 < eps → ∃ δ : posreal, ∀ k : ℝ, k ≠ 0 → |k| < δ →
      |(g (0 + k) - g 0) / k - 0| < eps.
    Take eps : ℝ. Assume that 0 < eps as (Heps).
    Choose δ := mkposreal eps Heps.
    Take k : ℝ. Assume that k ≠ 0 as (Hk). Assume that |k| < δ.
    It holds that |k| < eps.
    It holds that 0 + k = k as (E0).
    By (Hg k Hk) it holds that g k = k ^ 2 * sin (1 / k).
    By (Rinv_r k Hk) it holds that k * / k = 1.
    It holds that k ^ 2 * sin (1 / k) / k = k * sin (1 / k).
    It holds that (g k - g 0) / k - 0 = k * sin (1 / k).
    By (Rabs_mult k (sin (1 / k))) it holds that
      |k * sin (1 / k)| = |k| * |sin (1 / k)|.
    By (SIN_bound (1 / k)) it holds that -1 ≤ sin (1 / k) ∧ sin (1 / k) ≤ 1 as (Hs).
    By (Rabs_le (sin (1 / k)) 1 Hs) it holds that |sin (1 / k)| ≤ 1.
    By (Rabs_pos (sin (1 / k))) it holds that 0 ≤ |sin (1 / k)|.
    By (Rabs_pos k) it holds that 0 ≤ |k|.
    It holds that |k| * |sin (1 / k)| ≤ |k|.
    It holds that |(g k - g 0) / k - 0| < eps.
    By E0 we conclude that |(g (0 + k) - g 0) / k - 0| < eps.
  }
  Define Hd := @exist ℝ (fun l : ℝ => derivable_pt_abs g 0 l) 0 Hlim.
  Choose Hd0 := Hd.
  By (derive_pt_eq_0 g 0 0 Hd0 Hlim) we conclude that derive_pt g 0 Hd0 = 0.
Qed.


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
  (** Proving this in Wateproof remains challenging and time-consuming,
      so we decided to postpone it to a future update. *)
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
  (** This is Stdlib's [derive_increasing_interv]. *)
  Take x ∈ ℝ. Take y ∈ ℝ.
  Assume that a ≤ x.
  Assume that x < y as (Hxy).
  Assume that y ≤ v.
  It holds that a < v as (Hav).
  It holds that a ≤ x ∧ x ≤ v as (Hx).
  It holds that a ≤ y ∧ y ≤ v as (Hy).
  By derive_increasing_interv we conclude that psi x < psi y.
Qed.
