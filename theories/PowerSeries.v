(** * RUG.Analysis.PowerSeries — Power series and radius of convergence.

  #<a href="../../index.html##lecture11">Lecture 11</a># and #<a href="../../index.html##lecture12">Lecture 12</a>#.

  Formalizes Abbott §6.5: radius of convergence, Abel's theorem,
  term-by-term differentiation and integration of power series. *)

Require Import RUG.Analysis.Lib.StdlibReals.
From Waterproof Require Import Libs.Analysis.Series.
From Stdlib Require Import Logic.ClassicalUniqueChoice.
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

(** Helper: if [|x| = q·|x₀|] with [q ≥ 0] and [|c·x₀ⁿ| ≤ M], then
    [|c·xⁿ| ≤ M·qⁿ]. *)
Lemma abs_term_geometric_bound (c x x0 q M : ℝ) (n : ℕ)
    (Hq : |x| = q * |x0|) (Hq0 : 0 ≤ q) (HM : |c * x0 ^ n| ≤ M) :
    |c * x ^ n| ≤ M * q ^ n.
Proof.
  By (Rabs_mult c (x ^ n)) it holds that |c * x ^ n| = |c| * |x ^ n|.
  By (RPow_abs x n) it holds that |x ^ n| = |x| ^ n.
  By (Rpow_mult_distr q (|x0|) n) it holds that (q * |x0|) ^ n = q ^ n * |x0| ^ n.
  By (Rabs_mult c (x0 ^ n)) it holds that |c * x0 ^ n| = |c| * |x0 ^ n|.
  By (RPow_abs x0 n) it holds that |x0 ^ n| = |x0| ^ n.
  By (pow_le q n Hq0) it holds that 0 ≤ q ^ n.
  By Hq it holds that |x| ^ n = (q * |x0|) ^ n.
  It holds that |c * x ^ n| = |c * x0 ^ n| * q ^ n.
  We conclude that |c * x ^ n| ≤ M * q ^ n.
Qed.

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
  Obtain L according to (H).
  It holds that ∑ (fun n => a n * x0 ^ n) ⟶ L as (HL).
  By (series_convergent_terms_zero (fun n => a n * x0 ^ n) L HL) it holds that
    (fun n => a n * x0 ^ n) ⟶ 0 as (Hterm).
  By (convergent_sequence_is_bounded (fun n => a n * x0 ^ n) 0 Hterm) it holds that
    bounded_sequence (fun n => a n * x0 ^ n).
  It holds that (∃ M ∈ ℝ, M > 0 ∧ ∀ n ∈ ℕ, | a n * x0 ^ n | ≤ M).
  Obtain such an M.
  It holds that ∀ n ∈ ℕ, |a n * x0 ^ n| ≤ M as (HMb).
  It holds that |x0| > 0.
  Define q := |x| / |x0|.
  By (Rinv_r (|x0|)) it holds that |x0| * / |x0| = 1.
  It holds that |x| = q * |x0| as (Hq).
  It holds that 0 ≤ q as (Hq0).
  It holds that q < 1.
  It holds that |q| < 1 as (Hqa).
  By (geometric_series q Hqa) it holds that
    ∃ G : ℝ, G = 1 / (1 - q) ∧ partial_sums (fun n ↦ q ^ n) ⟶ G.
  Obtain such a G.
  It holds that partial_sums (fun n ↦ q ^ n) ⟶ G as (HG).
  By (series_algebraic_limit (fun n ↦ q ^ n) (fun n ↦ q ^ n) G G HG HG) it holds that
    ∀ c ∈ ℝ, partial_sums (sprod (fun n ↦ q ^ n) c) ⟶ (c * G) as (Hsc).
  By (Hsc M) it holds that partial_sums (sprod (fun n ↦ q ^ n) M) ⟶ (M * G).
  We claim that ∀ n ∈ ℕ, |a n * x ^ n| ≤ sprod (fun n ↦ q ^ n) M n as (Hle).
  {
    Take n ∈ ℕ.
    By (HMb n) it holds that |a n * x0 ^ n| ≤ M as (E7).
    By (abs_term_geometric_bound (a n) x x0 q M n Hq Hq0 E7) it holds that
      |a n * x ^ n| ≤ M * q ^ n.
    We conclude that |a n * x ^ n| ≤ sprod (fun n ↦ q ^ n) M n.
  }
  We claim that ∀ n ∈ ℕ, 0 ≤ |a n * x ^ n| as (Hpos).
  {
    Take n ∈ ℕ.
    By (Rabs_pos (a n * x ^ n)) we conclude that 0 ≤ |a n * x ^ n|.
  }
  We claim that ∃ l ∈ ℝ, partial_sums (sprod (fun n ↦ q ^ n) M) ⟶ l as (Hb).
  {
    Choose l := M * G. { Indeed, l ∈ ℝ. }
    We conclude that partial_sums (sprod (fun n ↦ q ^ n) M) ⟶ l.
  }
  By (series_comparison_test (fun n => |a n * x ^ n|) (sprod (fun n ↦ q ^ n) M) Hpos Hle Hb)
    it holds that ∃ l ∈ ℝ, partial_sums (fun n => |a n * x ^ n|) ⟶ l as (Hcmp).
  Obtain l according to (Hcmp).
  Choose L0 := l.
  We conclude that ∑ (fun n => |a n * x ^ n|) ⟶ L0.
Qed.


(** ** Absolute convergence strictly inside the radius *)

(** _Pointwise convergence_ of power series (Abbott Theorem 6.5.1): if the series converges at every [r] with [0 < r < R], then it
    converges absolutely at every [x] with [|x| < R].

    Proof idea: pick [r] with [|x| < r < R] (e.g. [r = (|x| + R)/2]); the series
    converges at [r], so [power_series_converges_absolutely_inside] with
    [x₀ = r] gives absolute convergence at [x]. *)
Lemma power_series_abs_convergent (a : ℕ → ℝ) (Rad : ℝ) (HR : Rad > 0)
    (Hcv_inside : ∀ r : ℝ, 0 < r → r < Rad →
      ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < Rad) :
    ∃ L : ℝ, ∑ (fun n => Rabs (a n * x ^ n)) ⟶ L.
Proof.
  Define r := (|x| + Rad) / 2.
  By (Rabs_pos x) it holds that 0 ≤ |x|.
  It holds that 0 < r as (Hr0).
  It holds that r < Rad as (HrR).
  It holds that |x| < r.
  By (Rabs_pos_eq r) it holds that |r| = r.
  It holds that |x| < |r| as (Hxr').
  By (Hcv_inside r Hr0 HrR) it holds that
    ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L as (Hcv).
  By (power_series_converges_absolutely_inside a r Hcv x Hxr')
    we conclude that ∃ L : ℝ, ∑ (fun n => Rabs (a n * x ^ n)) ⟶ L.
Qed.


(** ** Uniform convergence on compact sub-intervals *)

(** Helper: for [|x| ≤ r], [|c·xⁿ| ≤ |c·rⁿ|]. *)
Lemma abs_term_mono (c x r : ℝ) (n : ℕ) (Hx : |x| ≤ r) :
    |c * x ^ n| ≤ |c * r ^ n|.
Proof.
  By (Rabs_pos x) it holds that 0 ≤ |x| as (H0).
  By (Rabs_mult c (x ^ n)) it holds that |c * x ^ n| = |c| * |x ^ n|.
  By (RPow_abs x n) it holds that |x ^ n| = |x| ^ n.
  By (Rabs_mult c (r ^ n)) it holds that |c * r ^ n| = |c| * |r ^ n|.
  By (RPow_abs r n) it holds that |r ^ n| = |r| ^ n.
  It holds that 0 ≤ r as (Hr).
  By (Rabs_pos_eq r Hr) it holds that |r| = r.
  By (pow_incr (|x|) r n (conj H0 Hx)) it holds that |x| ^ n ≤ r ^ n.
  By (Rabs_pos c) it holds that 0 ≤ |c|.
  It holds that |c| * |x| ^ n ≤ |c| * r ^ n.
  We conclude that |c * x ^ n| ≤ |c * r ^ n|.
Qed.

(** _Uniform convergence_ of power series (Abbott Theorem 6.5.2): if the radius of convergence is [R > 0], then [∑ aₙ xⁿ]
    converges uniformly on every [[−r, r]] with [r < R].

    Proof idea: pick [r'] with [r < r' < R]. The series converges absolutely at
    [r'], so [∑ |aₙ| (r')ⁿ < ∞]. For [x ∈ [−r, r]],
    [|aₙ xⁿ| ≤ |aₙ| rⁿ ≤ |aₙ| (r')ⁿ], so the Weierstrass M-test gives uniform
    convergence. *)
Lemma power_series_uniform_on_compact (a : ℕ → ℝ) (Rad r : ℝ)
    (HR : Rad > 0) (Hr0 : 0 < r) (HrR : r < Rad)
    (Hconv : ∀ x : ℝ, Rabs x < Rad →
      ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L) :
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun N x => sum_f_R0 (fun n => a n * x ^ n) N)
        g
        (fun x => Rabs x ≤ r).
Proof.
  We claim that ∀ s : ℝ, 0 < s → s < Rad →
      ∃ L : ℝ, ∑ (fun n => a n * s ^ n) ⟶ L as (Hin).
  {
    Take s : ℝ. Assume that 0 < s. Assume that s < Rad.
    By (Rabs_pos_eq s) it holds that |s| = s.
    It holds that |s| < Rad as (Hs).
    By (Hconv s Hs) we conclude that ∃ L : ℝ, ∑ (fun n => a n * s ^ n) ⟶ L.
  }
  By (Rabs_pos_eq r) it holds that |r| = r.
  It holds that |r| < Rad as (Hr).
  By (power_series_abs_convergent a Rad HR Hin r Hr) it holds that
    ∃ L : ℝ, ∑ (fun n => |a n * r ^ n|) ⟶ L as (Habs).
  Obtain L according to (Habs).
  We claim that ∃ L0 ∈ ℝ, (fun n => sum_f_R0 (fun n => |a n * r ^ n|) n) ⟶ L0 as (HM).
  {
    Choose L0 := L. { Indeed, L0 ∈ ℝ. }
    We conclude that
      (fun n => sum_f_R0 (fun n => |a n * r ^ n|) n) ⟶ L0.
  }
  We claim that ∀ n ∈ ℕ, ∀ x ∈ (fun x => |x| ≤ r),
      |(fun k x => a k * x ^ k) n x| ≤ (fun n => |a n * r ^ n|) n as (Hbound).
  {
    Take n ∈ ℕ. Take x ∈ (fun x => |x| ≤ r).
    It holds that |x| ≤ r as (Hx).
    By (abs_term_mono (a n) x r n Hx) we conclude that
      |(fun k x => a k * x ^ k) n x| ≤ (fun n => |a n * r ^ n|) n.
  }
  By (weierstrass_M_test (fun k x => a k * x ^ k) (fun n => |a n * r ^ n|)
        (fun x => |x| ≤ r) Hbound HM) we conclude that
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun N x => sum_f_R0 (fun n => a n * x ^ n) N)
        g
        (fun x => Rabs x ≤ r).
Qed.


(** The predicate "[g] is the sum of the power series [∑ aₙ xⁿ] on the disc of
    radius [R]": for every [x] with [|x| < R], the partial sums converge to
    [g(x)]. This lets us talk about the limit function without constructing it
    explicitly. *)
Definition is_series_sum (a : ℕ → ℝ) (g : ℝ → ℝ) (R : ℝ) : Prop :=
    ∀ x : ℝ, Rabs x < R → ∑ (fun n => a n * x ^ n) ⟶ g x.

(** ** Radius of convergence *)

(** At [x = 0] the power series reduces to its constant term [a₀]. *)
Lemma power_series_at_zero (a : ℕ → ℝ) :
    ∑ (fun n => a n * 0 ^ n) ⟶ a 0%nat.
Proof.
  We claim that ∀ m : ℕ, sum_f_R0 (fun n => a n * 0 ^ n) m = a 0%nat as (Hall).
  {
    We use induction on m.
    - We first show the base case (sum_f_R0 (fun n => a n * 0 ^ n) 0 = a 0%nat).
      It holds that sum_f_R0 (fun n => a n * 0 ^ n) 0 = a 0%nat * 0 ^ 0.
      It holds that 0 ^ 0 = 1.
      We conclude that sum_f_R0 (fun n => a n * 0 ^ n) 0 = a 0%nat.
    - We now show the induction step.
      Take m : ℕ.
      Assume that sum_f_R0 (fun n => a n * 0 ^ n) m = a 0%nat.
      It holds that (m + 1 = S m)%nat as (En).
      It holds that 0 ^ (S m) = 0 * 0 ^ m.
      It holds that 0 ^ (S m) = 0.
      It holds that sum_f_R0 (fun n => a n * 0 ^ n) (S m)
        = sum_f_R0 (fun n => a n * 0 ^ n) m + a (S m) * 0 ^ (S m).
      It holds that sum_f_R0 (fun n => a n * 0 ^ n) (S m) = a 0%nat.
      By En we conclude that sum_f_R0 (fun n => a n * 0 ^ n) (Nat.add m 1) = a 0%nat.
  }
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1,
    | sum_f_R0 (fun n => a n * 0 ^ n) n - a 0%nat | < ε.
  Take ε > 0.
  Choose N1 := 0%nat. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1,
    | sum_f_R0 (fun n => a n * 0 ^ n) n - a 0%nat | < ε.
  Take n ≥ N1.
  By (Hall n) it holds that
    sum_f_R0 (fun n => a n * 0 ^ n) n = a 0%nat.
  We conclude that
    | sum_f_R0 (fun n => a n * 0 ^ n) n - a 0%nat | < ε.
Qed.

(** Convergence at [x₀] implies convergence at every [x] with [|x| < |x₀|]. *)
Lemma power_series_converges_inside (a : ℕ → ℝ) (x0 : ℝ)
    (H : ∃ L : ℝ, ∑ (fun n => a n * x0 ^ n) ⟶ L)
    (x : ℝ) (Hx : Rabs x < Rabs x0) :
    ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L.
Proof.
  By (power_series_converges_absolutely_inside a x0 H x Hx) it holds that
    ∃ L : ℝ, ∑ (fun n => |a n * x ^ n|) ⟶ L as (Habs).
  Obtain labs according to (Habs).
  It holds that ∑ (fun n => |a n * x ^ n|) ⟶ labs as (Hl).
  By (absolute_convergence_implies_convergence (fun n => a n * x ^ n) labs Hl)
    it holds that ∃ l ∈ ℝ, ∑ (fun n => a n * x ^ n) ⟶ l as (Hc).
  Obtain l according to (Hc).
  Choose L := l.
  We conclude that ∑ (fun n => a n * x ^ n) ⟶ L.
Qed.

(** _Existence of the radius of convergence_: for every coefficient sequence
    with a finite radius — i.e. whose series diverges at some point [x₀] — there
    is [R ≥ 0] such that the series converges for [|x| < R] and diverges for
    [|x| > R]. (Without the hypothesis [Hfin] the statement fails, e.g. for
    [aₙ = 1/n!] the series converges everywhere and no real [R] works.)

    Proof idea: let [S = {r ≥ 0 | ∑ aₙ rⁿ converges}]. It contains [0], and it
    is bounded above by [|x₀|]: convergence at [r > |x₀|] would force
    convergence at [x₀]. Take [R = sup S]. For [|x| < R] some [r ∈ S] exceeds
    [|x|], so the series converges at [x]; for [|x| > R], convergence at [x]
    would put [(|x| + R)/2 ∈ S], contradicting [R = sup S]. (Cauchy–Hadamard
    Theorem gives the explicit formula [R = 1 / limsup |aₙ|^{1/n}].) *)
Lemma radius_of_convergence (a : ℕ → ℝ)
    (Hfin : ∃ x0 : ℝ, ¬ (∃ L : ℝ, ∑ (fun n => a n * x0 ^ n) ⟶ L)) :
    ∃ Rad : ℝ, Rad ≥ 0 ∧
      (∀ x : ℝ, Rabs x < Rad → ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L) ∧
      (∀ x : ℝ, Rabs x > Rad → ¬ (∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L)).
Proof.
  Obtain x0 according to (Hfin).
  It holds that ¬ (∃ L : ℝ, ∑ (fun n => a n * x0 ^ n) ⟶ L).
  Define Conv := (fun r : ℝ => 0 ≤ r ∧ ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L).
  (** [0 ∈ Conv]: at [0] the series reduces to [a₀]. *)
  We claim that 0 ∈ Conv as (H0S).
  {
    By (power_series_at_zero a) it holds that ∑ (fun n => a n * 0 ^ n) ⟶ a 0%nat.
    We claim that ∃ L : ℝ, ∑ (fun n => a n * 0 ^ n) ⟶ L.
    { Choose L := a 0%nat. We conclude that ∑ (fun n => a n * 0 ^ n) ⟶ L. }
    We need to show that 0 ≤ 0 ∧ ∃ L : ℝ, ∑ (fun n => a n * 0 ^ n) ⟶ L.
    We conclude that 0 ≤ 0 ∧ ∃ L : ℝ, ∑ (fun n => a n * 0 ^ n) ⟶ L.
  }
  (** [|x₀|] is an upper bound for [Conv]. *)
  We claim that |x0| is an _upper bound_ for Conv.
  {
    We need to show that ∀ r ∈ Conv, r ≤ |x0|.
    Take r ∈ Conv.
    It holds that 0 ≤ r ∧ ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L.
    It holds that ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L as (Hrc).
    It holds that 0 ≤ r as (Hr0).
    We argue by contradiction.
    Assume that ¬ (r ≤ |x0|).
    It holds that |x0| < r as (Hlt).
    By (Rabs_pos_eq r Hr0) it holds that |r| = r.
    It holds that |x0| < |r| as (Hlt').
    By (power_series_converges_inside a r Hrc x0 Hlt') it holds that
      ∃ L : ℝ, ∑ (fun n => a n * x0 ^ n) ⟶ L as (Hc).
    Contradiction.
  }
  We claim that Conv is _bounded from above_ as (Hbdd).
  {
    We need to show that ∃ M ∈ ℝ, M is an _upper bound_ for Conv.
    Choose M := |x0|. { Indeed, M ∈ ℝ. }
    We conclude that M is an _upper bound_ for Conv.
  }
  By (R_complete Conv 0 H0S Hbdd) it holds that ∃ Rad ∈ ℝ,
    Rad is the _supremum_ of Conv as (Hsup).
  Obtain Rad according to (Hsup).
  It holds that Rad is the _supremum_ of Conv.
  It holds that Rad is an _upper bound_ for Conv ∧
    (∀ L ∈ ℝ, L is an _upper bound_ for Conv ⇨ Rad ≤ L).
  It holds that Rad is an _upper bound_ for Conv.
  It holds that ∀ L ∈ ℝ,
    L is an _upper bound_ for Conv ⇨ Rad ≤ L as (HRleast).
  It holds that ∀ r ∈ Conv, r ≤ Rad as (HRub').
  By (HRub' 0 H0S) it holds that 0 ≤ Rad.
  Choose Rad0 := Rad.
  We need to show that Rad0 ≥ 0 ∧
      (∀ x : ℝ, |x| < Rad0 → ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L) ∧
      (∀ x : ℝ, |x| > Rad0 → ¬ (∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L)).
  We show both statements.
  - We need to show that Rad0 ≥ 0.
    We conclude that Rad0 ≥ 0.
  - We need to show that
      (∀ x : ℝ, |x| < Rad0 → ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L) ∧
      (∀ x : ℝ, |x| > Rad0 → ¬ (∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L)).
    We show both statements.
    + We need to show that ∀ x : ℝ,
        |x| < Rad0 → ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L.
      Take x : ℝ. Assume that |x| < Rad0.
      We argue by contradiction.
      Assume that ¬ (∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L).
      (** Then [|x|] would be an upper bound for [Conv], below [Rad]. *)
      We claim that |x| is an _upper bound_ for Conv.
      {
        We need to show that ∀ r ∈ Conv, r ≤ |x|.
        Take r ∈ Conv.
        It holds that 0 ≤ r ∧ ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L.
        It holds that ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L as (Hrc).
        It holds that 0 ≤ r as (Hr0).
        We argue by contradiction.
        Assume that ¬ (r ≤ |x|).
        It holds that |x| < r as (Hlt).
        By (Rabs_pos_eq r Hr0) it holds that |r| = r.
        It holds that |x| < |r| as (Hlt').
        By (power_series_converges_inside a r Hrc x Hlt') it holds that
          ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L as (Hc).
        Contradiction.
      }
      By (HRleast (|x|)) it holds that Rad ≤ |x|.
      Contradiction.
    + We need to show that ∀ x : ℝ,
        |x| > Rad0 → ¬ (∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L).
      Take x : ℝ. Assume that |x| > Rad0.
      Assume that ∃ L : ℝ, ∑ (fun n => a n * x ^ n) ⟶ L as (Hc).
      (** A point strictly between [Rad] and [|x|] would lie in [Conv]. *)
      Define r := (|x| + Rad) / 2.
      It holds that 0 ≤ r as (Hr0).
      By (Rabs_pos_eq r Hr0) it holds that |r| = r.
      It holds that |r| < |x| as (Hlt).
      By (power_series_converges_inside a x Hc r Hlt) it holds that
        ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L.
      We claim that r ∈ Conv as (HrS).
      {
        We need to show that 0 ≤ r ∧ ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L.
        We conclude that 0 ≤ r ∧ ∃ L : ℝ, ∑ (fun n => a n * r ^ n) ⟶ L.
      }
      By (HRub' r HrS) it holds that r ≤ Rad.
      Contradiction.
Qed.


(** ** Continuity of a power series *)

(** Helper: every partial sum [∑_{n=0}^N aₙ zⁿ] is a polynomial, hence continuous. *)
Lemma partial_sum_continuous (a : ℕ → ℝ) (Nn : ℕ) (y : ℝ) :
    continuity_pt (fun z => sum_f_R0 (fun n => a n * z ^ n) Nn) y.
Proof.
  We claim that ∀ n : ℕ, (n ≤ Nn)%nat → continuity_pt (fun z => a n * z ^ n) y as (Hm).
  {
    Take n : ℕ. Assume that (n ≤ Nn)%nat.
    By (derivable_continuous_pt (fun z => z ^ n) y (derivable_pt_pow n y)) it holds that
      continuity_pt (fun z => z ^ n) y as (Hp).
    By (continuity_pt_scal (fun z => z ^ n) (a n) y Hp) we conclude that
      continuity_pt (fun z => a n * z ^ n) y.
  }
  By (continuity_pt_finite_SF (fun n z => a n * z ^ n) Nn y Hm) we conclude that
    continuity_pt (fun z => sum_f_R0 (fun n => a n * z ^ n) Nn) y.
Qed.

(** A power series is continuous on its open interval of convergence.

    Proof idea: on each [[−r, r]] with [r < R] the series converges uniformly
    ([power_series_uniform_on_compact]), and each partial sum is a (continuous) polynomial; the
    uniform limit of continuous functions is continuous. *)
Lemma power_series_continuous (a : ℕ → ℝ) (g : ℝ → ℝ) (Rad : ℝ) (HR : Rad > 0)
    (Hsum : is_series_sum a g Rad)
    (x : ℝ) (Hx : Rabs x < Rad) :
    continuity_pt g x.
Proof.
  By (Rabs_pos x) it holds that 0 ≤ |x|.
  Define r := (|x| + Rad) / 2.
  It holds that 0 < r as (Hr0).
  It holds that r < Rad as (HrR).
  We claim that ∀ y : ℝ, |y| < Rad → ∃ L : ℝ, ∑ (fun n => a n * y ^ n) ⟶ L as (Hconv).
  {
    Take y : ℝ. Assume that |y| < Rad as (Hy).
    By (Hsum y Hy) it holds that ∑ (fun n => a n * y ^ n) ⟶ g y as (Hgy).
    Choose L := g y.
    We conclude that ∑ (fun n => a n * y ^ n) ⟶ L.
  }
  By (power_series_uniform_on_compact a Rad r HR Hr0 HrR Hconv) it holds that
    ∃ g' : ℝ → ℝ, converges_uniformly
      (fun N x => sum_f_R0 (fun n => a n * x ^ n) N) g' (fun x => |x| ≤ r) as (Hu).
  Obtain g' according to (Hu).
  It holds that converges_uniformly
      (fun N x => sum_f_R0 (fun n => a n * x ^ n) N) g' (fun x => |x| ≤ r) as (Hunif).
  Define rp := mkposreal r Hr0.
  We claim that CVU (fun N x => sum_f_R0 (fun n => a n * x ^ n) N) g 0 rp as (Hcvu).
  {
    We need to show that ∀ eps : ℝ, 0 < eps → ∃ Nc : ℕ, ∀ n : ℕ, ∀ y : ℝ,
      (Nc ≤ n)%nat → Boule 0 rp y →
      |g y - sum_f_R0 (fun k => a k * y ^ k) n| < eps.
    Take eps : ℝ. Assume that 0 < eps as (Heps).
    By (Hunif eps Heps) it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ y ∈ (fun x => |x| ≤ r), |sum_f_R0 (fun k => a k * y ^ k) n - g' y| < eps as (HN).
    Obtain N1 according to (HN).
    It holds that ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ y ∈ (fun x => |x| ≤ r), |sum_f_R0 (fun k => a k * y ^ k) n - g' y| < eps as (HN1).
    Choose Nc := N1.
    Take n : ℕ. Take y : ℝ.
    Assume that (Nc ≤ n)%nat.
    Assume that Boule 0 rp y.
    It holds that |y - 0| < r.
    It holds that |y| < r.
    It holds that |y| ≤ r as (Hyle).
    It holds that |y| < Rad as (HyR).
    It holds that (n ≥ N1)%nat as (Hn1).
    By (HN1 n Hn1 y Hyle) it holds that
      |sum_f_R0 (fun k => a k * y ^ k) n - g' y| < eps.
    By (Hsum y HyR) it holds that ∑ (fun k => a k * y ^ k) ⟶ g y as (Hgy).
    By (uniform_implies_pointwise _ _ _ Hunif y Hyle) it holds that
      ∑ (fun k => a k * y ^ k) ⟶ g' y as (Hg'y).
    By (limit_unique _ (g y) (g' y) Hgy Hg'y) it holds that g y = g' y as (Heq).
    By Heq it holds that |g y - sum_f_R0 (fun k => a k * y ^ k) n|
      = |g' y - sum_f_R0 (fun k => a k * y ^ k) n|.
    By (Rabs_minus_sym (g' y) (sum_f_R0 (fun k => a k * y ^ k) n)) it holds that
      |g' y - sum_f_R0 (fun k => a k * y ^ k) n|
      = |sum_f_R0 (fun k => a k * y ^ k) n - g' y|.
    We conclude that |g y - sum_f_R0 (fun k => a k * y ^ k) n| < eps.
  }
  We claim that ∀ n : ℕ, ∀ y : ℝ, Boule 0 rp y →
    continuity_pt ((fun N x => sum_f_R0 (fun n => a n * x ^ n) N) n) y as (Hcn).
  {
    Take n : ℕ. Take y : ℝ. Assume that Boule 0 rp y.
    By (partial_sum_continuous a n y) we conclude that
      continuity_pt ((fun N x => sum_f_R0 (fun n => a n * x ^ n) N) n) y.
  }
  It holds that |x - 0| < r.
  It holds that Boule 0 rp x as (Hxb).
  By (CVU_continuity _ g 0 rp Hcvu Hcn x Hxb)
    we conclude that continuity_pt g x.
Qed.


(** ** Abel's summation by parts *)

(** _Abel's summation by parts_: with partial sums [Bₖ = ∑_{j=0}^k bⱼ],
    [∑_{k=0}^{n+1} aₖ bₖ = a_{n+1} B_{n+1} - ∑_{k=0}^n (a_{k+1} - aₖ) Bₖ].

    Proof idea: substitute [bₖ = Bₖ - B_{k-1}] and reindex the sum. *)
Lemma abel_summation_by_parts (a b : ℕ → ℝ) (n : ℕ) :
    sum_f_R0 (fun k => a k * b k) (S n) =
    a (S n) * sum_f_R0 b (S n)
    - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) n.
Proof.
  We claim that ∀ m : ℕ, sum_f_R0 (fun k => a k * b k) (S m) =
      a (S m) * sum_f_R0 b (S m)
      - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m as (Hall).
  {
    We use induction on m.
    - We first show the base case
        (sum_f_R0 (fun k => a k * b k) 1 =
         a 1%nat * sum_f_R0 b 1 - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) 0).
      It holds that
        sum_f_R0 (fun k => a k * b k) 1
        = a 0%nat * b 0%nat + a 1%nat * b 1%nat.
      It holds that sum_f_R0 b 1 = b 0%nat + b 1%nat.
      It holds that
        sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) 0
        = (a 1%nat - a 0%nat) * b 0%nat.
      We conclude that
         sum_f_R0 (fun k => a k * b k) 1
         = a 1%nat * sum_f_R0 b 1
           - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) 0.
    - We now show the induction step.
      Take m : ℕ.
      Assume that
        sum_f_R0 (fun k => a k * b k) (S m)
        = a (S m) * sum_f_R0 b (S m)
          - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m.
      We claim that
        sum_f_R0 (fun k => a k * b k) (S (S m))
        = a (S (S m)) * sum_f_R0 b (S (S m))
          - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (S m).
      {
        It holds that
          sum_f_R0 (fun k => a k * b k) (S (S m))
          = sum_f_R0 (fun k => a k * b k) (S m) + a (S (S m)) * b (S (S m)).
        It holds that
          sum_f_R0 b (S (S m)) = sum_f_R0 b (S m) + b (S (S m)).
        It holds that
          sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (S m)
          = sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m
            + (a (S (S m)) - a (S m)) * sum_f_R0 b (S m).
        We conclude that
          sum_f_R0 (fun k => a k * b k) (S (S m))
          = a (S (S m)) * sum_f_R0 b (S (S m))
            - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (S m).
      }
      It holds that (S m + 1 = S (S m))%nat as (En2).
      By En2 we conclude that sum_f_R0 (fun k => a k * b k) (Nat.add (S m) 1) =
        a (Nat.add (S m) 1) * sum_f_R0 b (Nat.add (S m) 1)
        - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (S m).
  }
  By (Hall n) we conclude that sum_f_R0 (fun k => a k * b k) (S n) =
      a (S n) * sum_f_R0 b (S n)
      - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) n.
Qed.


(** Helper: if [u ≤ v] and [|B| ≤ M] then [|(u - v)·B| ≤ (v - u)·M]. *)
Lemma abs_decr_term (u v B M : ℝ) (Huv : u ≤ v) (HB : |B| ≤ M) :
    |(u - v) * B| ≤ (v - u) * M.
Proof.
  By (Rabs_mult (u - v) B) it holds that |(u - v) * B| = |u - v| * |B|.
  By (Rabs_minus_sym u v) it holds that |u - v| = |v - u|.
  It holds that 0 ≤ v - u as (Hvu).
  By (Rabs_pos_eq (v - u) Hvu) it holds that |v - u| = v - u.
  It holds that (v - u) * |B| ≤ (v - u) * M.
  We conclude that |(u - v) * B| ≤ (v - u) * M.
Qed.

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
  (** The weighted sum of the partial sums telescopes. *)
  We claim that ∀ m : ℕ,
    |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m| ≤ (a 0%nat - a (S m)) * M
    as (Htel).
  {
    We use induction on m.
    - We first show the base case
        (|sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) 0| ≤ (a 0%nat - a 1%nat) * M).
      By (Hdec 0%nat) it holds that 0 ≤ a 1%nat ∧ a 1%nat ≤ a 0%nat.
      It holds that a 1%nat ≤ a 0%nat as (H1).
      By (abs_decr_term (a 1%nat) (a 0%nat) (sum_f_R0 b 0) M H1 (Hbound 0%nat))
        it holds that |(a 1%nat - a 0%nat) * sum_f_R0 b 0| ≤ (a 0%nat - a 1%nat) * M.
      We conclude that
        |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) 0| ≤ (a 0%nat - a 1%nat) * M.
    - We now show the induction step.
      Take m : ℕ.
      Assume that |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m|
        ≤ (a 0%nat - a (S m)) * M.
      By (Hdec (S m)) it holds that 0 ≤ a (S (S m)) ∧ a (S (S m)) ≤ a (S m).
      It holds that a (S (S m)) ≤ a (S m) as (H1).
      By (abs_decr_term (a (S (S m))) (a (S m)) (sum_f_R0 b (S m)) M H1 (Hbound (S m)))
        it holds that |(a (S (S m)) - a (S m)) * sum_f_R0 b (S m)|
          ≤ (a (S m) - a (S (S m))) * M.
      It holds that sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (S m)
        = sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m
          + (a (S (S m)) - a (S m)) * sum_f_R0 b (S m).
      By (Rabs_triang (sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m)
          ((a (S (S m)) - a (S m)) * sum_f_R0 b (S m))) it holds that
        |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m
          + (a (S (S m)) - a (S m)) * sum_f_R0 b (S m)|
        ≤ |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m|
          + |(a (S (S m)) - a (S m)) * sum_f_R0 b (S m)|.
      It holds that |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (S m)|
        ≤ (a 0%nat - a (S (S m))) * M.
      It holds that (m + 1 = S m)%nat as (En).
      It holds that (S m + 1 = S (S m))%nat as (En2).
      By En it holds that
        |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (Nat.add m 1)|
          ≤ (a 0%nat - a (S (S m))) * M.
      By En2 we conclude that
        |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) (Nat.add m 1)|
          ≤ (a 0%nat - a (Nat.add (S m) 1)) * M.
  }
  We claim that ∀ m : ℕ, |sum_f_R0 (fun k => a k * b k) m| ≤ a 0%nat * M as (Hall).
  {
    We use induction on m.
    - We first show the base case (|sum_f_R0 (fun k => a k * b k) 0| ≤ a 0%nat * M).
      By (Hdec 0%nat) it holds that 0 ≤ a 1%nat ∧ a 1%nat ≤ a 0%nat.
      It holds that 0 ≤ a 0%nat as (Ha0).
      By (Rabs_mult (a 0%nat) (b 0%nat)) it holds that
        |a 0%nat * b 0%nat| = |a 0%nat| * |b 0%nat|.
      By (Rabs_pos_eq (a 0%nat) Ha0) it holds that |a 0%nat| = a 0%nat.
      By (Hbound 0%nat) it holds that |sum_f_R0 b 0| ≤ M.
      It holds that sum_f_R0 b 0 = b 0%nat as (E3b).
      By E3b it holds that |b 0%nat| ≤ M.
      It holds that a 0%nat * |b 0%nat| ≤ a 0%nat * M.
      It holds that |a 0%nat * b 0%nat| ≤ a 0%nat * M.
      It holds that sum_f_R0 (fun k => a k * b k) 0 = a 0%nat * b 0%nat as (E0).
      By E0 we conclude that |sum_f_R0 (fun k => a k * b k) 0| ≤ a 0%nat * M.
    - We now show the induction step.
      Take m : ℕ.
      Assume that |sum_f_R0 (fun k => a k * b k) m| ≤ a 0%nat * M.
      By (abel_summation_by_parts a b m) it holds that
        sum_f_R0 (fun k => a k * b k) (S m) =
        a (S m) * sum_f_R0 b (S m)
        - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m.
      By (Rabs_triang (a (S m) * sum_f_R0 b (S m))
          (- sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m)) it holds that
        |a (S m) * sum_f_R0 b (S m) + - sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m|
        ≤ |a (S m) * sum_f_R0 b (S m)|
          + |- sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m|.
      By (Rabs_Ropp (sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m)) it holds that
        |- sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m|
        = |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m|.
      By (Hdec m) it holds that 0 ≤ a (S m) ∧ a (S m) ≤ a m.
      It holds that 0 ≤ a (S m) as (H3').
      By (Rabs_mult (a (S m)) (sum_f_R0 b (S m))) it holds that
        |a (S m) * sum_f_R0 b (S m)| = |a (S m)| * |sum_f_R0 b (S m)|.
      By (Rabs_pos_eq (a (S m)) H3') it holds that |a (S m)| = a (S m).
      By (Hbound (S m)) it holds that |sum_f_R0 b (S m)| ≤ M.
      It holds that |a (S m) * sum_f_R0 b (S m)| ≤ a (S m) * M.
      By (Htel m) it holds that
        |sum_f_R0 (fun k => (a (S k) - a k) * sum_f_R0 b k) m| ≤ (a 0%nat - a (S m)) * M.
      It holds that |sum_f_R0 (fun k => a k * b k) (S m)| ≤ a 0%nat * M.
      It holds that (m + 1 = S m)%nat as (En).
      By En we conclude that |sum_f_R0 (fun k => a k * b k) (Nat.add m 1)| ≤ a 0%nat * M.
  }
  By (Hall n) we conclude that Rabs (sum_f_R0 (fun k => a k * b k) n) ≤ a 0%nat * M.
Qed.


(** ** Abel's theorem *)

(** Index shift: [∑_{k=0}^{m+1+p} F k = ∑_{k=0}^m F k + ∑_{i=0}^p F (m+1+i)]. *)
Lemma sum_shift (F : ℕ → ℝ) (m p : ℕ) :
    sum_f_R0 F (Nat.add m (S p)) = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) p.
Proof.
  We claim that ∀ q : ℕ,
    sum_f_R0 F (Nat.add m (S q)) = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) q as (Hall).
  {
    We use induction on q.
    - We first show the base case
        (sum_f_R0 F (Nat.add m 1) = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) 0).
      It holds that (m + 1 = S m)%nat as (E0).
      It holds that sum_f_R0 F (S m) = sum_f_R0 F m + F (S m).
      It holds that sum_f_R0 (fun i => F (Nat.add m (S i))) 0 = F (Nat.add m 1).
      By E0 it holds that sum_f_R0 (fun i => F (Nat.add m (S i))) 0 = F (S m).
      By E0 we conclude that
        sum_f_R0 F (Nat.add m 1) = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) 0.
    - We now show the induction step.
      Take q : ℕ.
      Assume that sum_f_R0 F (Nat.add m (S q))
        = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) q.
      It holds that sum_f_R0 F (S (Nat.add m (S q)))
        = sum_f_R0 F (Nat.add m (S q)) + F (S (Nat.add m (S q))).
      It holds that sum_f_R0 (fun i => F (Nat.add m (S i))) (S q)
        = sum_f_R0 (fun i => F (Nat.add m (S i))) q + F (Nat.add m (S (S q))).
      It holds that (m + S (S q) = S (m + S q))%nat as (E4).
      By E4 it holds that sum_f_R0 (fun i => F (Nat.add m (S i))) (S q)
        = sum_f_R0 (fun i => F (Nat.add m (S i))) q + F (S (Nat.add m (S q))).
      It holds that sum_f_R0 F (S (Nat.add m (S q)))
        = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) (S q).
      It holds that (m + (S q + 1) = S (m + S q))%nat as (E7).
      By E7 we conclude that sum_f_R0 F (Nat.add m (Nat.add (S q) 1))
        = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) (S q).
  }
  By (Hall p) we conclude that
    sum_f_R0 F (Nat.add m (S p)) = sum_f_R0 F m + sum_f_R0 (fun i => F (Nat.add m (S i))) p.
Qed.

(** Abel's lemma applied to a tail: if all tails [∑_{k=m+1}^{m+1+j} cₖ] are
    bounded by [M] and [0 ≤ t ≤ 1], then so are the tails of [∑ cₖ tᵏ]. *)
Lemma abel_tail (c : ℕ → ℝ) (t M : ℝ) (m p : ℕ) (Ht0 : 0 ≤ t) (Ht1 : t ≤ 1)
    (HM : ∀ k : ℕ, |sum_f_R0 c (Nat.add m (S k)) - sum_f_R0 c m| ≤ M) :
    |sum_f_R0 (fun j => c j * t ^ j) (Nat.add m (S p))
      - sum_f_R0 (fun j => c j * t ^ j) m| ≤ M.
Proof.
  By (sum_shift (fun j => c j * t ^ j) m p) it holds that
    sum_f_R0 (fun j => c j * t ^ j) (Nat.add m (S p))
    = sum_f_R0 (fun j => c j * t ^ j) m
      + sum_f_R0 (fun i => c (Nat.add m (S i)) * t ^ (Nat.add m (S i))) p.
  We claim that ∀ i : ℕ, (i ≤ p)%nat →
    c (Nat.add m (S i)) * t ^ (Nat.add m (S i))
    = t ^ (Nat.add m (S i)) * c (Nat.add m (S i)) as (Hcomm).
  {
    Take i : ℕ. Assume that (i ≤ p)%nat.
    We conclude that c (Nat.add m (S i)) * t ^ (Nat.add m (S i))
      = t ^ (Nat.add m (S i)) * c (Nat.add m (S i)).
  }
  By (sum_eq _ _ p Hcomm) it holds that
    sum_f_R0 (fun i => c (Nat.add m (S i)) * t ^ (Nat.add m (S i))) p
    = sum_f_R0 (fun i => t ^ (Nat.add m (S i)) * c (Nat.add m (S i))) p.
  (** The weights [t^{m+1+k}] are nonnegative and decreasing. *)
  We claim that ∀ k : ℕ, 0 ≤ t ^ (Nat.add m (S (S k)))
      ∧ t ^ (Nat.add m (S (S k))) ≤ t ^ (Nat.add m (S k)) as (Hdec).
  {
    Take k : ℕ.
    It holds that (Nat.add m (S (S k)) = S (Nat.add m (S k)))%nat as (Ek).
    By Ek it holds that t ^ (Nat.add m (S (S k))) = t ^ (S (Nat.add m (S k))) as (Ek2).
    It holds that t ^ (S (Nat.add m (S k))) = t * t ^ (Nat.add m (S k)).
    By (pow_le t (Nat.add m (S k)) Ht0) it holds that 0 ≤ t ^ (Nat.add m (S k)).
    It holds that t * t ^ (Nat.add m (S k)) ≤ t ^ (Nat.add m (S k)).
    It holds that 0 ≤ t * t ^ (Nat.add m (S k)).
    We conclude that 0 ≤ t ^ (Nat.add m (S (S k)))
      ∧ t ^ (Nat.add m (S (S k))) ≤ t ^ (Nat.add m (S k)).
  }
  (** The partial sums of the shifted coefficients are bounded by [M]. *)
  We claim that ∀ k : ℕ, |sum_f_R0 (fun i => c (Nat.add m (S i))) k| ≤ M as (Hbound).
  {
    Take k : ℕ.
    By (sum_shift c m k) it holds that sum_f_R0 c (Nat.add m (S k))
      = sum_f_R0 c m + sum_f_R0 (fun i => c (Nat.add m (S i))) k.
    By (HM k) it holds that |sum_f_R0 c (Nat.add m (S k)) - sum_f_R0 c m| ≤ M.
    It holds that sum_f_R0 c (Nat.add m (S k)) - sum_f_R0 c m
      = sum_f_R0 (fun i => c (Nat.add m (S i))) k as (Ek2).
    By Ek2 we conclude that |sum_f_R0 (fun i => c (Nat.add m (S i))) k| ≤ M.
  }
  By (abel_lemma_bounded_partial_sums (fun i => t ^ (Nat.add m (S i)))
        (fun i => c (Nat.add m (S i))) p M Hdec Hbound) it holds that
    |sum_f_R0 (fun i => t ^ (Nat.add m (S i)) * c (Nat.add m (S i))) p|
      ≤ t ^ (Nat.add m 1) * M.
  (** Finally [t^{m+1} ≤ 1] and [M ≥ 0]. *)
  By (pow_le t (Nat.add m 1) Ht0) it holds that 0 ≤ t ^ (Nat.add m 1).
  By (pow_incr t 1 (Nat.add m 1) (conj Ht0 Ht1)) it holds that
    t ^ (Nat.add m 1) ≤ 1 ^ (Nat.add m 1).
  By (pow1 (Nat.add m 1)) it holds that 1 ^ (Nat.add m 1) = 1.
  By (HM 0%nat) it holds that |sum_f_R0 c (Nat.add m 1) - sum_f_R0 c m| ≤ M.
  By (Rabs_pos (sum_f_R0 c (Nat.add m 1) - sum_f_R0 c m)) it holds that
    0 ≤ |sum_f_R0 c (Nat.add m 1) - sum_f_R0 c m|.
  It holds that 0 ≤ M.
  It holds that t ^ (Nat.add m 1) * M ≤ M.
  It holds that sum_f_R0 (fun j => c j * t ^ j) (Nat.add m (S p))
    - sum_f_R0 (fun j => c j * t ^ j) m
    = sum_f_R0 (fun i => t ^ (Nat.add m (S i)) * c (Nat.add m (S i))) p as (E3).
  By E3 we conclude that |sum_f_R0 (fun j => c j * t ^ j) (Nat.add m (S p))
      - sum_f_R0 (fun j => c j * t ^ j) m| ≤ M.
Qed.

(** Rescaling: [aⱼ xʲ = (aⱼ Rʲ)(x/R)ʲ]. *)
Lemma abel_rescale (a : ℕ → ℝ) (Rad x : ℝ) (HR : Rad > 0) (Nn : ℕ) :
    sum_f_R0 (fun j => a j * x ^ j) Nn
    = sum_f_R0 (fun j => (a j * Rad ^ j) * (x / Rad) ^ j) Nn.
Proof.
  By (Rinv_r Rad) it holds that Rad * / Rad = 1.
  It holds that x / Rad * Rad = x as (Ex).
  We claim that ∀ j : ℕ, (j ≤ Nn)%nat →
    a j * x ^ j = (a j * Rad ^ j) * (x / Rad) ^ j as (Hpt).
  {
    Take j : ℕ. Assume that (j ≤ Nn)%nat.
    By (Rpow_mult_distr (x / Rad) Rad j) it holds that
      (x / Rad * Rad) ^ j = (x / Rad) ^ j * Rad ^ j.
    By Ex it holds that x ^ j = (x / Rad) ^ j * Rad ^ j.
    We conclude that a j * x ^ j = (a j * Rad ^ j) * (x / Rad) ^ j.
  }
  By (sum_eq _ _ Nn Hpt) we conclude that
    sum_f_R0 (fun j => a j * x ^ j) Nn
    = sum_f_R0 (fun j => (a j * Rad ^ j) * (x / Rad) ^ j) Nn.
Qed.

(** Tails of [∑ aⱼ xʲ] on [[0, R]] are controlled by the tails of [∑ aⱼ Rʲ]. *)
Lemma abel_tail_rescaled (a : ℕ → ℝ) (Rad x M : ℝ) (HR : Rad > 0)
    (Hx0 : 0 ≤ x) (HxR : x ≤ Rad) (m p : ℕ)
    (HM : ∀ k : ℕ, |sum_f_R0 (fun j => a j * Rad ^ j) (Nat.add m (S k))
                    - sum_f_R0 (fun j => a j * Rad ^ j) m| ≤ M) :
    |sum_f_R0 (fun j => a j * x ^ j) (Nat.add m (S p))
      - sum_f_R0 (fun j => a j * x ^ j) m| ≤ M.
Proof.
  By (Rinv_r Rad) it holds that Rad * / Rad = 1.
  By (Rinv_0_lt_compat Rad HR) it holds that 0 < / Rad.
  It holds that 0 ≤ x / Rad as (Ht0).
  It holds that x / Rad ≤ 1 as (Ht1).
  By (abel_tail (fun j => a j * Rad ^ j) (x / Rad) M m p Ht0 Ht1 HM) it holds that
    |sum_f_R0 (fun j => (a j * Rad ^ j) * (x / Rad) ^ j) (Nat.add m (S p))
      - sum_f_R0 (fun j => (a j * Rad ^ j) * (x / Rad) ^ j) m| ≤ M.
  By (abel_rescale a Rad x HR (Nat.add m (S p))) it holds that
    sum_f_R0 (fun j => a j * x ^ j) (Nat.add m (S p))
    = sum_f_R0 (fun j => (a j * Rad ^ j) * (x / Rad) ^ j) (Nat.add m (S p)) as (E1).
  By (abel_rescale a Rad x HR m) it holds that
    sum_f_R0 (fun j => a j * x ^ j) m
    = sum_f_R0 (fun j => (a j * Rad ^ j) * (x / Rad) ^ j) m as (E2).
  By E1 it holds that |sum_f_R0 (fun j => a j * x ^ j) (Nat.add m (S p))
      - sum_f_R0 (fun j => (a j * Rad ^ j) * (x / Rad) ^ j) m| ≤ M.
  By E2 we conclude that |sum_f_R0 (fun j => a j * x ^ j) (Nat.add m (S p))
      - sum_f_R0 (fun j => a j * x ^ j) m| ≤ M.
Qed.

(** _Abel's theorem_: if [∑ aₙ Rⁿ] converges at the endpoint [R > 0], then the
    power series converges uniformly on [[0, R]] (so its sum is continuous up to
    the endpoint).

    Proof idea: apply Abel's lemma to the tails, writing [aₙ xⁿ = (aₙ Rⁿ)(x/R)ⁿ]
    with decreasing weights [(x/R)ⁿ] and bounded partial sums of [(aₙ Rⁿ)]. *)
Theorem abel_theorem (a : ℕ → ℝ) (Rad : ℝ) (HR : Rad > 0)
    (Hend : ∃ L : ℝ, ∑ (fun n => a n * Rad ^ n) ⟶ L) :
    ∃ g : ℝ → ℝ,
      converges_uniformly (fun N x => sum_f_R0 (fun n => a n * x ^ n) N) g
        (fun x => 0 ≤ x ∧ x ≤ Rad).
Proof.
  (** The series at the endpoint is Cauchy. *)
  Obtain L according to (Hend).
  We claim that ∃ L0 ∈ ℝ, partial_sums (fun n => a n * Rad ^ n) ⟶ L0.
  { Choose L0 := L. { Indeed, L0 ∈ ℝ. }
    We conclude that partial_sums (fun n => a n * Rad ^ n) ⟶ L0. }
  By (series_cauchy_criterion (fun n => a n * Rad ^ n)) it holds that
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
      |partial_sums (fun n => a n * Rad ^ n) n - partial_sums (fun n => a n * Rad ^ n) m| < ε
    as (Hcauchy).
  (** It suffices to show that the partial sums are uniformly Cauchy. *)
  By (uniform_cauchy_criterion (fun N x => sum_f_R0 (fun n => a n * x ^ n) N)
        (fun x => 0 ≤ x ∧ x ≤ Rad)) it suffices to show that
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ (fun x => 0 ≤ x ∧ x ≤ Rad),
      |(fun N x => sum_f_R0 (fun n => a n * x ^ n) N) n x
        - (fun N x => sum_f_R0 (fun n => a n * x ^ n) N) m x| < ε.
  Take ε > 0.
  It holds that ε / 2 > 0.
  By Hcauchy it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
      |partial_sums (fun n => a n * Rad ^ n) n - partial_sums (fun n => a n * Rad ^ n) m|
        < ε / 2 as (HN).
  Obtain N1 according to (HN).
  It holds that ∀ n ≥ N1, ∀ m ≥ N1,
      |partial_sums (fun n => a n * Rad ^ n) n - partial_sums (fun n => a n * Rad ^ n) m|
        < ε / 2 as (HN1).
  (** Abel's lemma bounds every tail starting beyond [N1] by [ε/2]. *)
  We claim that ∀ m : ℕ, (m ≥ N1)%nat → ∀ p : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ Rad →
    |sum_f_R0 (fun j => a j * x ^ j) (Nat.add m (S p))
      - sum_f_R0 (fun j => a j * x ^ j) m| ≤ ε / 2 as (Htail).
  {
    Take m : ℕ. Assume that (m ≥ N1)%nat as (Hm).
    Take p : ℕ. Take x : ℝ. Assume that 0 ≤ x as (Hx0). Assume that x ≤ Rad as (HxR).
    We claim that ∀ k : ℕ, |sum_f_R0 (fun j => a j * Rad ^ j) (Nat.add m (S k))
        - sum_f_R0 (fun j => a j * Rad ^ j) m| ≤ ε / 2 as (HM).
    {
      Take k : ℕ.
      It holds that (Nat.add m (S k) ≥ N1)%nat as (Hk).
      By (HN1 (Nat.add m (S k)) Hk m Hm) it holds that
        |partial_sums (fun n => a n * Rad ^ n) (Nat.add m (S k))
          - partial_sums (fun n => a n * Rad ^ n) m| < ε / 2.
      We conclude that |sum_f_R0 (fun j => a j * Rad ^ j) (Nat.add m (S k))
        - sum_f_R0 (fun j => a j * Rad ^ j) m| ≤ ε / 2.
    }
    By (abel_tail_rescaled a Rad x (ε / 2) HR Hx0 HxR m p HM) we conclude that
      |sum_f_R0 (fun j => a j * x ^ j) (Nat.add m (S p))
        - sum_f_R0 (fun j => a j * x ^ j) m| ≤ ε / 2.
  }
  Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
  We need to show that ∀ n ≥ N2, ∀ m ≥ N2, ∀ x ∈ (fun x => 0 ≤ x ∧ x ≤ Rad),
      |(fun N x => sum_f_R0 (fun n => a n * x ^ n) N) n x
        - (fun N x => sum_f_R0 (fun n => a n * x ^ n) N) m x| < ε.
  Take n ≥ N2. Take m ≥ N2. Take x ∈ (fun x => 0 ≤ x ∧ x ≤ Rad).
  It holds that 0 ≤ x ∧ x ≤ Rad.
  It holds that 0 ≤ x as (Hx0).
  It holds that x ≤ Rad as (HxR).
  We need to show that
    |sum_f_R0 (fun j => a j * x ^ j) n - sum_f_R0 (fun j => a j * x ^ j) m| < ε.
  Either (n < m)%nat or (m ≤ n)%nat.
  - Case (n < m)%nat.
    It holds that (Nat.add n (S (Nat.sub m (S n))) = m)%nat as (Em).
    It holds that (n ≥ N1)%nat as (Hn).
    By (Htail n Hn (Nat.sub m (S n)) x Hx0 HxR) it holds that
      |sum_f_R0 (fun j => a j * x ^ j) (Nat.add n (S (Nat.sub m (S n))))
        - sum_f_R0 (fun j => a j * x ^ j) n| ≤ ε / 2.
    By Em it holds that
      |sum_f_R0 (fun j => a j * x ^ j) m - sum_f_R0 (fun j => a j * x ^ j) n| ≤ ε / 2.
    By (Rabs_minus_sym (sum_f_R0 (fun j => a j * x ^ j) m) (sum_f_R0 (fun j => a j * x ^ j) n))
      it holds that |sum_f_R0 (fun j => a j * x ^ j) m - sum_f_R0 (fun j => a j * x ^ j) n|
        = |sum_f_R0 (fun j => a j * x ^ j) n - sum_f_R0 (fun j => a j * x ^ j) m|.
    We conclude that
      |sum_f_R0 (fun j => a j * x ^ j) n - sum_f_R0 (fun j => a j * x ^ j) m| < ε.
  - Case (m ≤ n)%nat.
    Either (m = n)%nat or (m < n)%nat.
    + Case (m = n)%nat.
      It holds that m = n as (Emn).
      By Emn it holds that
        sum_f_R0 (fun j => a j * x ^ j) n - sum_f_R0 (fun j => a j * x ^ j) m = 0 as (Hzero).
      By Hzero we conclude that
        |sum_f_R0 (fun j => a j * x ^ j) n - sum_f_R0 (fun j => a j * x ^ j) m| < ε.
    + Case (m < n)%nat.
      It holds that (Nat.add m (S (Nat.sub n (S m))) = n)%nat as (En).
      It holds that (m ≥ N1)%nat as (Hm).
      By (Htail m Hm (Nat.sub n (S m)) x Hx0 HxR) it holds that
        |sum_f_R0 (fun j => a j * x ^ j) (Nat.add m (S (Nat.sub n (S m))))
          - sum_f_R0 (fun j => a j * x ^ j) m| ≤ ε / 2.
      By En it holds that
        |sum_f_R0 (fun j => a j * x ^ j) n - sum_f_R0 (fun j => a j * x ^ j) m| ≤ ε / 2.
      We conclude that
        |sum_f_R0 (fun j => a j * x ^ j) n - sum_f_R0 (fun j => a j * x ^ j) m| < ε.
Qed.


(** ** Term-by-term differentiation *)

(** Shifting a convergent sequence by one index does not change its limit. *)
Lemma shift_converges (u : ℕ → ℝ) (L : ℝ) (Hu : u ⟶ L) :
    (fun n => u (S n)) ⟶ L.
Proof.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, |u (S n) - L| < ε.
  Take ε > 0.
  By Hu it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, |u n - L| < ε as (HN).
  Obtain N1 according to (HN).
  It holds that ∀ n ≥ N1, |u n - L| < ε as (HN1).
  Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
  We need to show that ∀ n ≥ N2, |u (S n) - L| < ε.
  Take n ≥ N2.
  It holds that (S n ≥ N1)%nat as (Hn).
  By (HN1 (S n) Hn) we conclude that |u (S n) - L| < ε.
Qed.

(** The partial sum [∑_{n=0}^{M+1} aₙ zⁿ] has derivative [∑_{n=0}^M (n+1) a_{n+1} yⁿ]. *)
Lemma partial_sum_derivative (a : ℕ → ℝ) (M : ℕ) (y : ℝ) :
    ∃ Hd : derivable_pt (fun z => sum_f_R0 (fun n => a n * z ^ n) (S M)) y,
      derive_pt (fun z => sum_f_R0 (fun n => a n * z ^ n) (S M)) y Hd
      = sum_f_R0 (fun n => INR (S n) * a (S n) * y ^ n) M.
Proof.
  It holds that (0 < S M)%nat as (HM).
  By (derivable_pt_lim_fs a y (S M) HM) it holds that
    derivable_pt_lim (fun z => sum_f_R0 (fun n => a n * z ^ n) (S M)) y
      (sum_f_R0 (fun n => INR (S n) * a (S n) * y ^ n) M) as (Hlim).
  Define Hd := @exist ℝ
    (fun l : ℝ => derivable_pt_abs (fun z => sum_f_R0 (fun n => a n * z ^ n) (S M)) y l)
    (sum_f_R0 (fun n => INR (S n) * a (S n) * y ^ n) M) Hlim.
  Choose Hd0 := Hd.
  By (derive_pt_eq_0 _ y _ Hd0 Hlim) we conclude that
    derive_pt (fun z => sum_f_R0 (fun n => a n * z ^ n) (S M)) y Hd0
      = sum_f_R0 (fun n => INR (S n) * a (S n) * y ^ n) M.
Qed.

(** _Differentiation can be done term-by-term_ (Abbott Theorem 6.5.7): the sum [g] of [∑ aₙ xⁿ] is
    differentiable on [(−R, R)], and its derivative is the sum [h] of the derived
    series [∑ (n+1) a_{n+1} xⁿ] — which has the same radius [R].

    Proof idea: (1) the derived series has the same radius [R]; (2) it converges
    uniformly on [[−r, r]] for [r < R]; (3) apply the term-wise differentiability
    theorem ([uniform_differentiability_theorem]) to the partial sums. *)
Lemma power_series_termwise_derivative (a : ℕ → ℝ) (g h : ℝ → ℝ) (Rad : ℝ)
    (HR : Rad > 0) (Hsum : is_series_sum a g Rad)
    (Hder : is_series_sum (fun n => INR (S n) * a (S n)) h Rad)
    (x : ℝ) (Hx : Rabs x < Rad) :
    ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x.
Proof.
  By (Rabs_pos x) it holds that 0 ≤ |x|.
  Define r := (|x| + Rad) / 2.
  It holds that 0 < r as (Hr0).
  It holds that r < Rad as (HrR).
  It holds that |x| < r as (Hxr).
  It holds that - r < r as (Hab).
  (** The derived series converges uniformly on [[-r, r]] to [h]. *)
  We claim that ∀ y : ℝ, |y| < Rad →
    ∃ L : ℝ, ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L as (Hconv').
  {
    Take y : ℝ. Assume that |y| < Rad as (Hy).
    By (Hder y Hy) it holds that ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y as (Hhy).
    Choose L := h y.
    We conclude that ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L.
  }
  By (power_series_uniform_on_compact (fun n => INR (S n) * a (S n)) Rad r HR Hr0 HrR Hconv')
    it holds that ∃ h' : ℝ → ℝ, converges_uniformly
      (fun N z => sum_f_R0 (fun n => INR (S n) * a (S n) * z ^ n) N) h' (fun z => |z| ≤ r)
    as (Hu).
  Obtain h' according to (Hu).
  It holds that converges_uniformly
      (fun N z => sum_f_R0 (fun n => INR (S n) * a (S n) * z ^ n) N) h' (fun z => |z| ≤ r)
    as (Hunif).
  We claim that converges_uniformly
      (fun N z => sum_f_R0 (fun n => INR (S n) * a (S n) * z ^ n) N) h
      (fun z => - r ≤ z ∧ z ≤ r) as (Hdunif).
  {
    We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ y ∈ (fun z => - r ≤ z ∧ z ≤ r),
      |sum_f_R0 (fun k => INR (S k) * a (S k) * y ^ k) n - h y| < ε.
    Take ε > 0.
    By Hunif it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ y ∈ (fun z => |z| ≤ r),
      |sum_f_R0 (fun k => INR (S k) * a (S k) * y ^ k) n - h' y| < ε as (HN).
    Obtain N1 according to (HN).
    It holds that ∀ n : ℕ, (n ≥ N1)%nat → ∀ y ∈ (fun z => |z| ≤ r),
      |sum_f_R0 (fun k => INR (S k) * a (S k) * y ^ k) n - h' y| < ε as (HN1).
    Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
    We need to show that ∀ n : ℕ, (n ≥ N2)%nat → ∀ y ∈ (fun z => - r ≤ z ∧ z ≤ r),
      |sum_f_R0 (fun k => INR (S k) * a (S k) * y ^ k) n - h y| < ε.
    Take n : ℕ. Assume that (n ≥ N2)%nat.
    Take y ∈ (fun z => - r ≤ z ∧ z ≤ r).
    It holds that - r ≤ y ∧ y ≤ r as (Hy).
    By (Rabs_le y r Hy) it holds that |y| ≤ r as (Hyr).
    It holds that |y| < Rad as (HyR).
    It holds that (n ≥ N1)%nat as (Hn1).
    By (HN1 n Hn1 y Hyr) it holds that
      |sum_f_R0 (fun k => INR (S k) * a (S k) * y ^ k) n - h' y| < ε.
    By (Hder y HyR) it holds that
      ∑ (fun k => INR (S k) * a (S k) * y ^ k) ⟶ h y as (Hhy).
    By (uniform_implies_pointwise _ _ _ Hunif y Hyr) it holds that
      ∑ (fun k => INR (S k) * a (S k) * y ^ k) ⟶ h' y as (Hh'y).
    By (limit_unique _ (h y) (h' y) Hhy Hh'y) it holds that h y = h' y as (Heq).
    By Heq we conclude that
      |sum_f_R0 (fun k => INR (S k) * a (S k) * y ^ k) n - h y| < ε.
  }
  (** The shifted partial sums [S_{N+1}] have the derived partial sums as derivatives. *)
  We claim that ∀ n ∈ ℕ, ∀ y ∈ ℝ, - r ≤ y → y ≤ r →
    ∃ Hd : derivable_pt ((fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n) y,
      derive_pt ((fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n) y Hd
      = (fun N z => sum_f_R0 (fun k => INR (S k) * a (S k) * z ^ k) N) n y as (Hderiv).
  {
    Take n ∈ ℕ. Take y ∈ ℝ. Assume that - r ≤ y. Assume that y ≤ r.
    By (partial_sum_derivative a n y) we conclude that
      ∃ Hd : derivable_pt ((fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n) y,
        derive_pt ((fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n) y Hd
        = (fun N z => sum_f_R0 (fun k => INR (S k) * a (S k) * z ^ k) N) n y.
  }
  (** The shifted partial sums converge at [0]. *)
  It holds that |0| < Rad as (H0R).
  By (Hsum 0 H0R) it holds that ∑ (fun k => a k * 0 ^ k) ⟶ g 0 as (Hg0).
  By (shift_converges _ (g 0) Hg0) it holds that
    (fun n => sum_f_R0 (fun k => a k * 0 ^ k) (S n)) ⟶ g 0.
  We claim that ∃ x0 : ℝ, - r ≤ x0 ∧ x0 ≤ r ∧
    ∃ L : ℝ, (fun n => (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n x0) ⟶ L as (Hpt).
  {
    Choose x0 := 0.
    We need to show that - r ≤ 0 ∧ 0 ≤ r ∧
      ∃ L : ℝ, (fun n => (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n 0) ⟶ L.
    We claim that ∃ L : ℝ,
      (fun n => (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n 0) ⟶ L.
    { Choose L := g 0.
      We conclude that
        (fun n => (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n 0) ⟶ L. }
    We conclude that - r ≤ 0 ∧ 0 ≤ r ∧
      ∃ L : ℝ, (fun n => (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) n 0) ⟶ L.
  }
  (** Apply the differentiability theorem. *)
  By (uniform_differentiability_theorem
        (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N))
        (fun N z => sum_f_R0 (fun k => INR (S k) * a (S k) * z ^ k) N)
        h (- r) r Hab Hderiv Hpt Hdunif) it holds that
    ∃ G : ℝ → ℝ,
      converges_uniformly (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) G
        (fun z => - r ≤ z ∧ z ≤ r) ∧
      (∀ z : ℝ, - r < z → z < r → ∃ Hd : derivable_pt G z, derive_pt G z Hd = h z)
    as (HG).
  Obtain G according to (HG).
  It holds that converges_uniformly (fun N z => sum_f_R0 (fun k => a k * z ^ k) (S N)) G
      (fun z => - r ≤ z ∧ z ≤ r) as (HGu).
  It holds that ∀ z : ℝ, - r < z → z < r →
      ∃ Hd : derivable_pt G z, derive_pt G z Hd = h z as (HGd).
  (** The limit [G] agrees with [g] on [(-r, r)]. *)
  We claim that ∀ z : ℝ, - r < z < r → G z = g z as (Hagree).
  {
    Take z : ℝ. Assume that - r < z < r.
    It holds that - r ≤ z ∧ z ≤ r as (Hz').
    By (Rabs_le z r Hz') it holds that |z| ≤ r.
    It holds that |z| < Rad as (HzR).
    By (Hsum z HzR) it holds that ∑ (fun k => a k * z ^ k) ⟶ g z as (Hgz).
    By (shift_converges _ (g z) Hgz) it holds that
      (fun n => sum_f_R0 (fun k => a k * z ^ k) (S n)) ⟶ g z as (Hgz').
    By (uniform_implies_pointwise _ _ _ HGu z Hz') it holds that
      (fun n => sum_f_R0 (fun k => a k * z ^ k) (S n)) ⟶ G z as (HGz).
    By (limit_unique _ (G z) (g z) HGz Hgz') we conclude that G z = g z.
  }
  (** Transfer the derivative from [G] to [g]. *)
  By (Rabs_def2 x r Hxr) it holds that x < r ∧ - r < x.
  It holds that - r < x as (Hx1).
  It holds that x < r as (Hx2).
  By (HGd x Hx1 Hx2) it holds that
    ∃ Hd : derivable_pt G x, derive_pt G x Hd = h x as (HGx).
  Obtain HdG according to (HGx).
  It holds that derive_pt G x HdG = h x as (HdGx).
  By (derive_pt_eq_1 G x (h x) HdG HdGx) it holds that
    derivable_pt_lim G x (h x) as (HlimG).
  It holds that - r < x < r as (Hxin).
  By (derivable_pt_lim_locally_ext G g x (- r) r (h x) Hxin Hagree HlimG) it holds that
    derivable_pt_lim g x (h x) as (Hlim).
  Define Hd := @exist ℝ (fun l : ℝ => derivable_pt_abs g x l) (h x) Hlim.
  Choose Hd0 := Hd.
  By (derive_pt_eq_0 g x (h x) Hd0 Hlim) we conclude that derive_pt g x Hd0 = h x.
Qed.


(** For [0 < u < 1] the sequence [(n+1)·uⁿ] is bounded (via Bernoulli's inequality). *)
Lemma linear_times_geometric_bounded (u : ℝ) (Hu0 : 0 < u) (Hu1 : u < 1) :
    ∃ Cb : ℝ, ∀ n : ℕ, INR (S n) * u ^ n ≤ Cb.
Proof.
  Define hh := / u - 1.
  By (Rinv_r u) it holds that u * / u = 1 as (Ei).
  By (Rinv_lt_contravar u 1) it holds that / 1 < / u.
  It holds that / 1 = 1.
  It holds that 0 < hh as (Hh).
  By (Rinv_r hh) it holds that hh * / hh = 1.
  By (Rinv_0_lt_compat hh Hh) it holds that 0 < / hh.
  Choose Cb := 1 + / hh.
  Take n : ℕ.
  By (poly n hh Hh) it holds that 1 + INR n * hh ≤ (1 + hh) ^ n.
  It holds that 1 + hh = / u as (E1).
  By (Rpow_mult_distr u (/ u) n) it holds that (u * / u) ^ n = u ^ n * (/ u) ^ n.
  By (pow1 n) it holds that 1 ^ n = 1.
  By Ei it holds that (u * / u) ^ n = 1 ^ n.
  It holds that u ^ n * (/ u) ^ n = 1.
  By E1 it holds that u ^ n * (1 + hh) ^ n = 1.
  By (S_INR n) it holds that INR (S n) = INR n + 1.
  By (pos_INR n) it holds that 0 ≤ INR n.
  By (pow_le u n) it holds that 0 ≤ u ^ n.
  (** [(n+1) ≤ C·(1 + n h) ≤ C·(1+h)ⁿ]. *)
  It holds that INR n * hh * / hh = INR n.
  It holds that INR (S n) ≤ Cb * (1 + INR n * hh).
  It holds that 0 ≤ Cb.
  It holds that Cb * (1 + INR n * hh) ≤ Cb * (1 + hh) ^ n.
  It holds that INR (S n) * u ^ n ≤ Cb * (1 + hh) ^ n * u ^ n.
  It holds that Cb * (1 + hh) ^ n * u ^ n = Cb.
  We conclude that INR (S n) * u ^ n ≤ Cb.
Qed.

(** From [|c·t^{n+1}| ≤ M] and [t > 0] we get [|c|·tⁿ ≤ M/t]. *)
Lemma coeff_bound_from_term (c t M : ℝ) (n : ℕ) (Ht0 : 0 < t)
    (HM : |c * t ^ (S n)| ≤ M) :
    |c| * t ^ n ≤ M * / t.
Proof.
  By (Rabs_mult c (t ^ (S n))) it holds that |c * t ^ (S n)| = |c| * |t ^ (S n)|.
  By (RPow_abs t (S n)) it holds that |t ^ (S n)| = |t| ^ (S n).
  It holds that 0 ≤ t as (Ht0').
  By (Rabs_pos_eq t Ht0') it holds that |t| = t.
  It holds that t ^ (S n) = t * t ^ n.
  It holds that t * (|c| * t ^ n) ≤ M.
  By (Rinv_0_lt_compat t Ht0) it holds that 0 < / t.
  It holds that t * (|c| * t ^ n) * / t ≤ M * / t.
  By (Rinv_r t) it holds that t * / t = 1.
  It holds that t * (|c| * t ^ n) * / t = (|c| * t ^ n) * (t * / t).
  We conclude that |c| * t ^ n ≤ M * / t.
Qed.

(** Rewriting [|(n+1)·c·xⁿ|] when [|x| = q·s] and [s = u·t]. *)
Lemma abs_derived_term (c x s t q u : ℝ) (n : ℕ)
    (Hs : |x| = q * s) (Ht : s = u * t) (Ht0 : 0 < t) :
    |INR (S n) * c * x ^ n| = (INR (S n) * u ^ n) * (q ^ n * (|c| * t ^ n)).
Proof.
  By (pos_INR (S n)) it holds that 0 ≤ INR (S n) as (Hn).
  By (Rabs_pos_eq (INR (S n)) Hn) it holds that |INR (S n)| = INR (S n).
  By (Rabs_mult (INR (S n) * c) (x ^ n)) it holds that
    |INR (S n) * c * x ^ n| = |INR (S n) * c| * |x ^ n|.
  By (Rabs_mult (INR (S n)) c) it holds that |INR (S n) * c| = |INR (S n)| * |c|.
  By (RPow_abs x n) it holds that |x ^ n| = |x| ^ n.
  By Hs it holds that |x| ^ n = (q * s) ^ n.
  By (Rpow_mult_distr q s n) it holds that (q * s) ^ n = q ^ n * s ^ n.
  By Ht it holds that s ^ n = (u * t) ^ n.
  By (Rpow_mult_distr u t n) it holds that (u * t) ^ n = u ^ n * t ^ n.
  It holds that |x ^ n| = q ^ n * (u ^ n * t ^ n).
  We conclude that
    |INR (S n) * c * x ^ n| = (INR (S n) * u ^ n) * (q ^ n * (|c| * t ^ n)).
Qed.

(** The terms of the derived series are dominated by a geometric sequence. *)
Lemma derived_term_bound (c x s t q u M Cb : ℝ) (n : ℕ)
    (Hs : |x| = q * s) (Ht : s = u * t) (Hq : 0 ≤ q) (Hu : 0 ≤ u) (Ht0 : 0 < t)
    (HM : |c * t ^ (S n)| ≤ M) (HC : INR (S n) * u ^ n ≤ Cb) :
    |INR (S n) * c * x ^ n| ≤ Cb * M / t * q ^ n.
Proof.
  By (abs_derived_term c x s t q u n Hs Ht Ht0) it holds that
    |INR (S n) * c * x ^ n| = (INR (S n) * u ^ n) * (q ^ n * (|c| * t ^ n)).
  By (coeff_bound_from_term c t M n Ht0 HM) it holds that |c| * t ^ n ≤ M * / t as (H1).
  By (pow_le q n Hq) it holds that 0 ≤ q ^ n as (Hqn).
  By (Rabs_pos c) it holds that 0 ≤ |c| as (Hc).
  It holds that 0 ≤ t as (Ht0').
  By (pow_le t n Ht0') it holds that 0 ≤ t ^ n as (Htn).
  By (pos_INR (S n)) it holds that 0 ≤ INR (S n) as (Hn).
  By (pow_le u n Hu) it holds that 0 ≤ u ^ n as (Hun).
  By (Rmult_le_pos (|c|) (t ^ n) Hc Htn) it holds that 0 ≤ |c| * t ^ n as (H2a).
  By (Rmult_le_pos (q ^ n) (|c| * t ^ n) Hqn H2a) it holds that
    0 ≤ q ^ n * (|c| * t ^ n) as (H2).
  By (Rmult_le_pos (INR (S n)) (u ^ n) Hn Hun) it holds that 0 ≤ INR (S n) * u ^ n.
  It holds that 0 ≤ Cb as (H3).
  By (Rmult_le_compat_r (q ^ n * (|c| * t ^ n)) (INR (S n) * u ^ n) Cb H2 HC) it holds that
    (INR (S n) * u ^ n) * (q ^ n * (|c| * t ^ n))
    ≤ Cb * (q ^ n * (|c| * t ^ n)).
  By (Rmult_le_compat_l (q ^ n) (|c| * t ^ n) (M * / t) Hqn H1) it holds that
    q ^ n * (|c| * t ^ n) ≤ q ^ n * (M * / t) as (H5a).
  By (Rmult_le_compat_l Cb (q ^ n * (|c| * t ^ n)) (q ^ n * (M * / t)) H3 H5a) it holds that
    Cb * (q ^ n * (|c| * t ^ n)) ≤ Cb * (q ^ n * (M * / t)).
  It holds that Cb * (q ^ n * (M * / t)) = Cb * M / t * q ^ n.
  We conclude that |INR (S n) * c * x ^ n| ≤ Cb * M / t * q ^ n.
Qed.

(** The derived series [∑ (n+1) a_{n+1} xⁿ] converges wherever [|x| < R].

    Proof idea: pick [|x| < s < t < R]. The terms [aₙ tⁿ] are bounded by [M], and
    [(n+1)(s/t)ⁿ ≤ C], so [|(n+1) a_{n+1} xⁿ| ≤ (C M / t)(|x|/s)ⁿ]: compare with
    a geometric series. *)
Lemma derived_series_converges (a : ℕ → ℝ) (g : ℝ → ℝ) (Rad : ℝ) (HR : Rad > 0)
    (Hsum : is_series_sum a g Rad) (x : ℝ) (Hx : |x| < Rad) :
    ∃ L : ℝ, ∑ (fun n => INR (S n) * a (S n) * x ^ n) ⟶ L.
Proof.
  By (Rabs_pos x) it holds that 0 ≤ |x|.
  Define t := (|x| + Rad) / 2.
  Define s := (|x| + t) / 2.
  It holds that 0 < s.
  It holds that s < t.
  It holds that t < Rad.
  It holds that 0 < t as (Ht0).
  It holds that |x| < s.
  (** The terms [aₙ tⁿ] are bounded, since the series converges at [t]. *)
  By (Rabs_pos_eq t) it holds that |t| = t.
  It holds that |t| < Rad as (HtR').
  By (Hsum t HtR') it holds that ∑ (fun n => a n * t ^ n) ⟶ g t as (Hgt).
  By (series_convergent_terms_zero (fun n => a n * t ^ n) (g t) Hgt) it holds that
    (fun n => a n * t ^ n) ⟶ 0 as (Hterm).
  By (convergent_sequence_is_bounded (fun n => a n * t ^ n) 0 Hterm) it holds that
    bounded_sequence (fun n => a n * t ^ n).
  It holds that (∃ M ∈ ℝ, M > 0 ∧ ∀ n ∈ ℕ, | a n * t ^ n | ≤ M).
  Obtain such an M.
  It holds that ∀ n ∈ ℕ, |a n * t ^ n| ≤ M as (HMb).
  (** The ratios [u = s/t] and [q = |x|/s] are in [[0, 1)]. *)
  Define u := s / t.
  By (Rinv_r t) it holds that t * / t = 1.
  It holds that s = u * t as (Hsu).
  It holds that 0 < u as (Hu0).
  It holds that u < 1 as (Hu1).
  Define q := |x| / s.
  By (Rinv_r s) it holds that s * / s = 1.
  It holds that |x| = q * s as (Hxq).
  It holds that 0 ≤ q as (Hq0).
  It holds that q < 1.
  It holds that |q| < 1 as (Hqa).
  By (linear_times_geometric_bounded u Hu0 Hu1) it holds that
    ∃ Cb : ℝ, ∀ n : ℕ, INR (S n) * u ^ n ≤ Cb as (HCb).
  Obtain Cb according to (HCb).
  It holds that ∀ n : ℕ, INR (S n) * u ^ n ≤ Cb as (HC).
  It holds that 0 ≤ u as (Hu0').
  (** Termwise comparison with a geometric series. *)
  We claim that ∀ n ∈ ℕ, |INR (S n) * a (S n) * x ^ n|
      ≤ sprod (fun n ↦ q ^ n) (Cb * M / t) n as (Hle).
  {
    Take n ∈ ℕ.
    By (HMb (S n)) it holds that |a (S n) * t ^ (S n)| ≤ M as (HMn).
    By (derived_term_bound (a (S n)) x s t q u M Cb n Hxq Hsu Hq0 Hu0' Ht0 HMn (HC n))
      we conclude that |INR (S n) * a (S n) * x ^ n| ≤ sprod (fun n ↦ q ^ n) (Cb * M / t) n.
  }
  We claim that ∀ n ∈ ℕ, 0 ≤ |INR (S n) * a (S n) * x ^ n| as (Hpos).
  { Take n ∈ ℕ. By (Rabs_pos (INR (S n) * a (S n) * x ^ n)) we conclude that
      0 ≤ |INR (S n) * a (S n) * x ^ n|. }
  By (geometric_series q Hqa) it holds that
    ∃ G : ℝ, G = 1 / (1 - q) ∧ partial_sums (fun n ↦ q ^ n) ⟶ G as (Hgeo).
  Obtain G according to (Hgeo).
  It holds that partial_sums (fun n ↦ q ^ n) ⟶ G as (HG).
  By (series_algebraic_limit (fun n ↦ q ^ n) (fun n ↦ q ^ n) G G HG HG) it holds that
    ∀ c ∈ ℝ, partial_sums (sprod (fun n ↦ q ^ n) c) ⟶ (c * G) as (Hsc).
  By (Hsc (Cb * M / t)) it holds that
    partial_sums (sprod (fun n ↦ q ^ n) (Cb * M / t)) ⟶ (Cb * M / t * G).
  We claim that ∃ l ∈ ℝ, partial_sums (sprod (fun n ↦ q ^ n) (Cb * M / t)) ⟶ l as (Hb).
  { Choose l := Cb * M / t * G. { Indeed, l ∈ ℝ. }
    We conclude that partial_sums (sprod (fun n ↦ q ^ n) (Cb * M / t)) ⟶ l. }
  By (series_comparison_test (fun n => |INR (S n) * a (S n) * x ^ n|)
        (sprod (fun n ↦ q ^ n) (Cb * M / t)) Hpos Hle Hb)
    it holds that ∃ l ∈ ℝ, partial_sums (fun n => |INR (S n) * a (S n) * x ^ n|) ⟶ l
    as (Hcmp).
  Obtain labs according to (Hcmp).
  It holds that partial_sums (fun n => |INR (S n) * a (S n) * x ^ n|) ⟶ labs as (Habs).
  By (absolute_convergence_implies_convergence
        (fun n => INR (S n) * a (S n) * x ^ n) labs Habs)
    it holds that ∃ l ∈ ℝ, ∑ (fun n => INR (S n) * a (S n) * x ^ n) ⟶ l as (Hc).
  Obtain l according to (Hc).
  Choose L := l.
  We conclude that ∑ (fun n => INR (S n) * a (S n) * x ^ n) ⟶ L.
Qed.

(** ** Infinite differentiability and Taylor coefficients *)

(** A power series is infinitely differentiable on [(−R, R)], and its
    coefficients are its Taylor coefficients: [aₙ = g^{(n)}(0) / n!]. In
    particular [a₀ = g(0)].

    Proof idea: iterate term-by-term differentiation; each derived series again
    has radius [R], so [g] has derivatives of all orders, and evaluating the
    [n]-th derived series at [0] isolates [n!·aₙ]. *)
Theorem power_series_infinitely_differentiable
    (a : ℕ → ℝ) (g : ℝ → ℝ) (Rad : ℝ) (HR : Rad > 0) (Hsum : is_series_sum a g Rad) :
    (∀ x : ℝ, Rabs x < Rad → ∃ l : ℝ, derivable_pt_lim g x l) ∧ a 0%nat = g 0.
Proof.
  (** Name the sum [h] of the derived series: by uniqueness of limits there
      is exactly one candidate value at each point (we put [0] outside the disc). *)
  We claim that ∀ y : ℝ, exists! L : ℝ,
    (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L) ∨ (¬ (|y| < Rad) ∧ L = 0)
    as (Huniq).
  {
    Take y : ℝ.
    Either (|y| < Rad) or (¬ (|y| < Rad)).
    - Case (|y| < Rad).
      By (derived_series_converges a g Rad HR Hsum y) it holds that
        ∃ L : ℝ, ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L as (Hc).
      Obtain L according to (Hc).
      It holds that ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L as (HL).
      Choose L0 := L.
      We need to show that
        ((|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L0) ∨ (¬ (|y| < Rad) ∧ L0 = 0))
        ∧ ∀ L1 : ℝ, ((|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
                     ∨ (¬ (|y| < Rad) ∧ L1 = 0)) → L0 = L1.
      We show both statements.
      + We need to show that
          (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L0) ∨ (¬ (|y| < Rad) ∧ L0 = 0).
        We conclude that
          (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L0) ∨ (¬ (|y| < Rad) ∧ L0 = 0).
      + We need to show that ∀ L1 : ℝ, ((|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
                     ∨ (¬ (|y| < Rad) ∧ L1 = 0)) → L0 = L1.
        Take L1 : ℝ.
        Assume that (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
                     ∨ (¬ (|y| < Rad) ∧ L1 = 0) as (HL1).
        Because (HL1) either (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
          or (¬ (|y| < Rad) ∧ L1 = 0).
        * Case (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1).
          It holds that ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1 as (HL1').
          By (limit_unique _ L L1 HL HL1') we conclude that L0 = L1.
        * Case (¬ (|y| < Rad) ∧ L1 = 0).
          Contradiction.
    - Case (¬ (|y| < Rad)).
      Choose L0 := 0.
      We need to show that
        ((|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L0) ∨ (¬ (|y| < Rad) ∧ L0 = 0))
        ∧ ∀ L1 : ℝ, ((|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
                     ∨ (¬ (|y| < Rad) ∧ L1 = 0)) → L0 = L1.
      We show both statements.
      + We need to show that
          (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L0) ∨ (¬ (|y| < Rad) ∧ L0 = 0).
        We conclude that
          (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L0) ∨ (¬ (|y| < Rad) ∧ L0 = 0).
      + We need to show that ∀ L1 : ℝ, ((|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
                     ∨ (¬ (|y| < Rad) ∧ L1 = 0)) → L0 = L1.
        Take L1 : ℝ.
        Assume that (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
                     ∨ (¬ (|y| < Rad) ∧ L1 = 0) as (HL1).
        Because (HL1) either (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1)
          or (¬ (|y| < Rad) ∧ L1 = 0).
        * Case (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ L1).
          Contradiction.
        * Case (¬ (|y| < Rad) ∧ L1 = 0).
          We conclude that L0 = L1.
  }
  By (unique_choice ℝ ℝ _ Huniq) it holds that ∃ h : ℝ → ℝ, ∀ y : ℝ,
    (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y) ∨ (¬ (|y| < Rad) ∧ h y = 0)
    as (Hh).
  Obtain h according to (Hh).
  It holds that ∀ y : ℝ,
    (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y) ∨ (¬ (|y| < Rad) ∧ h y = 0)
    as (Hhy).
  We claim that is_series_sum (fun n => INR (S n) * a (S n)) h Rad as (Hder).
  {
    We need to show that ∀ y : ℝ, |y| < Rad →
      ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y.
    Take y : ℝ. Assume that |y| < Rad.
    By (Hhy y) it holds that
      (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y) ∨ (¬ (|y| < Rad) ∧ h y = 0)
      as (Hy').
    Because (Hy') either (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y)
      or (¬ (|y| < Rad) ∧ h y = 0).
    - Case (|y| < Rad ∧ ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y).
      We conclude that ∑ (fun n => INR (S n) * a (S n) * y ^ n) ⟶ h y.
    - Case (¬ (|y| < Rad) ∧ h y = 0).
      Contradiction.
  }
  We show both statements.
  - We need to show that ∀ x : ℝ, |x| < Rad → ∃ l : ℝ, derivable_pt_lim g x l.
    (** This is term-by-term differentiation. *)
    Take x : ℝ. Assume that |x| < Rad as (Hx).
    By (power_series_termwise_derivative a g h Rad HR Hsum Hder x Hx) it holds that
      ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x as (Hd).
    Obtain Hd0 according to (Hd).
    It holds that derive_pt g x Hd0 = h x as (Hd1).
    By (derive_pt_eq_1 g x (h x) Hd0 Hd1) it holds that derivable_pt_lim g x (h x).
    Choose l := h x.
    We conclude that derivable_pt_lim g x l.
  - We need to show that a 0%nat = g 0.
    (** At [0] the series reduces to [a₀]. *)
    It holds that |0| < Rad as (H0).
    By (Hsum 0 H0) it holds that ∑ (fun n => a n * 0 ^ n) ⟶ g 0 as (Hg0).
    By (power_series_at_zero a) it holds that ∑ (fun n => a n * 0 ^ n) ⟶ a 0%nat as (Ha0).
    By (limit_unique _ (a 0%nat) (g 0) Ha0 Hg0) we conclude that a 0%nat = g 0.
Qed.
