(** * RUG.Analysis.Taylor — Taylor's theorem and Taylor series.

  #<a href="../../index.html##lecture12">Lecture 12</a>#.

  Formalizes Abbott §6.6 and §8.6: Taylor polynomials, the Lagrange
  remainder formula, and Taylor series for exp, sin, cos. *)

Require Import RUG.Analysis.Lib.StdlibReals.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Logic.ClassicalChoice.
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
  We conclude that (&
    T_exp 1%nat x = T_exp 0%nat x + x ^ 1 / INR (fact 1)
    = 1 + x ^ 1 / 1 = 1 + x).
Qed.

(** [T₂(x) = 1 + x + x²/2]. *)
Lemma T_exp_2 (x : R) : T_exp 2%nat x = 1 + x + x ^ 2 / 2.
Proof.
  It holds that
    T_exp 2%nat x = T_exp 1%nat x + x ^ 2 / INR (fact 2) as (Hrec).
  By T_exp_1 it holds that T_exp 1%nat x = 1 + x as (H1).
  It holds that INR (fact 2) = 2 as (Hf2).
  We conclude that (&
    T_exp 2%nat x = T_exp 1%nat x + x ^ 2 / INR (fact 2)
    = 1 + x + x ^ 2 / 2).
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

(** Rolle's theorem in the form used below: if [F' = G] everywhere and [F]
    vanishes at [a < b], then [G] vanishes somewhere in [(a, b)]. *)
Lemma rolle_zero (F G : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hlim : ∀ y : ℝ, derivable_pt_lim F y (G y)) (Ha : F a = 0) (Hb : F b = 0) :
    ∃ c : ℝ, a < c ∧ c < b ∧ G c = 0.
Proof.
  Define pr := fun (y : ℝ) (_ : a < y < b) =>
    @exist ℝ (fun l : ℝ => derivable_pt_abs F y l) (G y) (Hlim y).
  We claim that ∀ y : ℝ, a <= y <= b → continuity_pt F y as (Hcont).
  {
    Take y : ℝ. Assume that (a <= y <= b).
    Define Hdy := @exist ℝ (fun l : ℝ => derivable_pt_abs F y l) (G y) (Hlim y).
    By (derivable_continuous_pt F y Hdy) we conclude that continuity_pt F y.
  }
  It holds that F a = F b as (Heq).
  By (Rolle F a b pr Hcont Hab Heq) it holds that
    ∃ c : ℝ, ∃ P : a < c < b, derive_pt F c (pr c P) = 0 as (HR).
  Obtain c according to (HR).
  It holds that ∃ P : a < c < b, derive_pt F c (pr c P) = 0 as (HP).
  Obtain P according to (HP).
  It holds that derive_pt F c (pr c P) = 0.
  By (derive_pt_eq_0 F c (G c) (pr c P) (Hlim c)) it holds that
    derive_pt F c (pr c P) = G c.
  It holds that a < c < b.
  Choose c0 := c.
  We conclude that a < c0 ∧ c0 < b ∧ G c0 = 0.
Qed.

(** _Generalized (repeated) Rolle_: if [g] has [n + 1] distinct zeros and its
    successive derivatives [g, g', …, g⁽ⁿ⁾] exist, then [g⁽ⁿ⁾] has a zero in the
    spanning interval.

    Here [df k] denotes [g⁽ᵏ⁾], with [df (S k)] the derivative of [df k].

    We need [n ≥ 1]: for [n = 0] there is no point strictly inside the
    degenerate interval [[pts 0, pts 0]].

    Proof idea: between consecutive zeros of [df k], Rolle's theorem produces a
    zero of [df (S k)]; iterating [n] times leaves a single zero of [df n].
    Choosing one Rolle point in every gap at once uses the axiom of choice
    ([choice]); finitely many choices would suffice, but this keeps the proof
    short. *)
Lemma generalized_rolle (df : ℕ → ℝ → ℝ) (n : ℕ) (pts : ℕ → ℝ)
    (Hn : (1 ≤ n)%nat)
    (Hstep : ∀ k ∈ ℕ, ∀ y ∈ ℝ,
        ∃ Hd : derivable_pt (df k) y, derive_pt (df k) y Hd = df (S k) y)
    (Hincr : ∀ k : ℕ, (k < n)%nat → pts k < pts (S k))
    (Hzero : ∀ k : ℕ, (k ≤ n)%nat → df 0%nat (pts k) = 0) :
    ∃ c : ℝ, pts 0%nat < c ∧ c < pts n ∧ df n c = 0.
Proof.
  We claim that ∀ k : ℕ, ∀ y : ℝ, derivable_pt_lim (df k) y (df (S k) y) as (Hlim).
  {
    Take k : ℕ. Take y : ℝ.
    By Hstep it holds that
      ∃ Hd : derivable_pt (df k) y, derive_pt (df k) y Hd = df (S k) y as (Hk).
    Obtain Hd according to (Hk).
    It holds that derive_pt (df k) y Hd = df (S k) y as (Hk').
    By (derive_pt_eq_1 (df k) y (df (S k) y) Hd Hk') we conclude that
      derivable_pt_lim (df k) y (df (S k) y).
  }
  We claim that ∀ j : ℕ, ∀ m : ℕ, (j + m = n)%nat → ∃ q : ℕ → ℝ,
    (∀ i : ℕ, (i < m)%nat → q i < q (S i)) ∧
    (∀ i : ℕ, (i ≤ m)%nat → df j (q i) = 0) ∧
    pts 0%nat ≤ q 0%nat ∧ q m ≤ pts n ∧
    ((1 ≤ j)%nat → pts 0%nat < q 0%nat ∧ q m < pts n) as (Hind).
  {
    We use induction on j.
    - We first show the base case (∀ m : ℕ, (0 + m = n)%nat → ∃ q : ℕ → ℝ,
        (∀ i : ℕ, (i < m)%nat → q i < q (S i)) ∧
        (∀ i : ℕ, (i ≤ m)%nat → df 0%nat (q i) = 0) ∧
        pts 0%nat ≤ q 0%nat ∧ q m ≤ pts n ∧
        ((1 ≤ 0)%nat → pts 0%nat < q 0%nat ∧ q m < pts n)).
      Take m : ℕ. Assume that (0 + m = n)%nat.
      It holds that m = n as (Emn).
      Choose q := pts.
      We need to show that
        (∀ i : ℕ, (i < m)%nat → pts i < pts (S i)) ∧
        (∀ i : ℕ, (i ≤ m)%nat → df 0%nat (pts i) = 0) ∧
        pts 0%nat ≤ pts 0%nat ∧ pts m ≤ pts n ∧
        ((1 ≤ 0)%nat → pts 0%nat < pts 0%nat ∧ pts m < pts n).
      We claim that ∀ i : ℕ, (i < m)%nat → pts i < pts (S i).
      { Take i : ℕ. Assume that (i < m)%nat. It holds that (i < n)%nat as (Hi).
        By (Hincr i Hi) we conclude that pts i < pts (S i). }
      We claim that ∀ i : ℕ, (i ≤ m)%nat → df 0%nat (pts i) = 0.
      { Take i : ℕ. Assume that (i ≤ m)%nat. It holds that (i ≤ n)%nat as (Hi).
        By (Hzero i Hi) we conclude that df 0%nat (pts i) = 0. }
      By Emn it holds that pts m ≤ pts n.
      We claim that (1 ≤ 0)%nat → pts 0%nat < pts 0%nat ∧ pts m < pts n.
      { Assume that (1 ≤ 0)%nat. Contradiction. }
      We conclude that
        (∀ i : ℕ, (i < m)%nat → pts i < pts (S i)) ∧
        (∀ i : ℕ, (i ≤ m)%nat → df 0%nat (pts i) = 0) ∧
        pts 0%nat ≤ pts 0%nat ∧ pts m ≤ pts n ∧
        ((1 ≤ 0)%nat → pts 0%nat < pts 0%nat ∧ pts m < pts n).
    - We now show the induction step.
      Take j : ℕ.
      Assume that ∀ m : ℕ, (j + m = n)%nat → ∃ q : ℕ → ℝ,
        (∀ i : ℕ, (i < m)%nat → q i < q (S i)) ∧
        (∀ i : ℕ, (i ≤ m)%nat → df j (q i) = 0) ∧
        pts 0%nat ≤ q 0%nat ∧ q m ≤ pts n ∧
        ((1 ≤ j)%nat → pts 0%nat < q 0%nat ∧ q m < pts n) as (IH).
      Take m : ℕ. Assume that (j + 1 + m = n)%nat.
      It holds that (j + S m = n)%nat as (Hm').
      By (IH (S m) Hm') it holds that ∃ q : ℕ → ℝ,
        (∀ i : ℕ, (i < S m)%nat → q i < q (S i)) ∧
        (∀ i : ℕ, (i ≤ S m)%nat → df j (q i) = 0) ∧
        pts 0%nat ≤ q 0%nat ∧ q (S m) ≤ pts n ∧
        ((1 ≤ j)%nat → pts 0%nat < q 0%nat ∧ q (S m) < pts n) as (Hq).
      Obtain q according to (Hq).
      It holds that ∀ i : ℕ, (i < S m)%nat → q i < q (S i) as (Hq1).
      It holds that ∀ i : ℕ, (i ≤ S m)%nat → df j (q i) = 0 as (Hq2).
      It holds that pts 0%nat ≤ q 0%nat.
      It holds that q (S m) ≤ pts n.
      (** Rolle's theorem in each gap [(qᵢ, qᵢ₊₁)] gives a zero of the next derivative. *)
      We claim that ∀ i : ℕ, ∃ c : ℝ,
        (i < S m)%nat → q i < c ∧ c < q (S i) ∧ df (S j) c = 0 as (Hgap).
      {
        Take i : ℕ.
        Either (i < S m)%nat or (¬ (i < S m)%nat).
        - Case (i < S m)%nat.
          It holds that (i < S m)%nat as (Hi).
          By (Hq1 i Hi) it holds that q i < q (S i) as (Hlt).
          It holds that (i ≤ S m)%nat as (Hi1).
          It holds that (S i ≤ S m)%nat as (Hi2).
          By (Hq2 i Hi1) it holds that df j (q i) = 0 as (Hz1).
          By (Hq2 (S i) Hi2) it holds that df j (q (S i)) = 0 as (Hz2).
          By (rolle_zero (df j) (df (S j)) (q i) (q (S i)) Hlt (Hlim j) Hz1 Hz2) it holds that
            ∃ c : ℝ, q i < c ∧ c < q (S i) ∧ df (S j) c = 0 as (Hc).
          Obtain c according to (Hc).
          Choose c0 := c.
          Assume that (i < S m)%nat.
          We conclude that q i < c0 ∧ c0 < q (S i) ∧ df (S j) c0 = 0.
        - Case (¬ (i < S m)%nat).
          Choose c0 := 0.
          Assume that (i < S m)%nat.
          Contradiction.
      }
      By (choice _ Hgap) it holds that ∃ r : ℕ → ℝ, ∀ i : ℕ,
        (i < S m)%nat → q i < r i ∧ r i < q (S i) ∧ df (S j) (r i) = 0 as (Hr).
      Obtain r according to (Hr).
      It holds that ∀ i : ℕ,
        (i < S m)%nat → q i < r i ∧ r i < q (S i) ∧ df (S j) (r i) = 0 as (Hr').
      It holds that (0 < S m)%nat as (H0m).
      It holds that (m < S m)%nat as (Hmm).
      By (Hr' 0%nat H0m) it holds that
        q 0%nat < r 0%nat ∧ r 0%nat < q 1%nat ∧ df (S j) (r 0%nat) = 0.
      By (Hr' m Hmm) it holds that
        q m < r m ∧ r m < q (S m) ∧ df (S j) (r m) = 0.
      It holds that pts 0%nat < r 0%nat.
      It holds that r m < pts n.
      We claim that ∀ i : ℕ, (i < m)%nat → r i < r (S i).
      {
        Take i : ℕ. Assume that (i < m)%nat.
        It holds that (i < S m)%nat as (Hi1).
        It holds that (S i < S m)%nat as (Hi2).
        By (Hr' i Hi1) it holds that
          q i < r i ∧ r i < q (S i) ∧ df (S j) (r i) = 0.
        By (Hr' (S i) Hi2) it holds that
          q (S i) < r (S i) ∧ r (S i) < q (S (S i)) ∧ df (S j) (r (S i)) = 0.
        It holds that r i < q (S i).
        It holds that q (S i) < r (S i).
        We conclude that r i < r (S i).
      }
      It holds that (j + 1 = S j)%nat as (Ej).
      We claim that ∀ i : ℕ, (i ≤ m)%nat → df (Nat.add j 1) (r i) = 0.
      {
        Take i : ℕ. Assume that (i ≤ m)%nat.
        It holds that (i < S m)%nat as (Hi1).
        By (Hr' i Hi1) it holds that
          q i < r i ∧ r i < q (S i) ∧ df (S j) (r i) = 0.
        It holds that df (S j) (r i) = 0.
        By Ej we conclude that df (Nat.add j 1) (r i) = 0.
      }
      Choose q0 := r.
      We need to show that
        (∀ i : ℕ, (i < m)%nat → r i < r (S i)) ∧
        (∀ i : ℕ, (i ≤ m)%nat → df (Nat.add j 1) (r i) = 0) ∧
        pts 0%nat ≤ r 0%nat ∧ r m ≤ pts n ∧
        ((1 ≤ j + 1)%nat → pts 0%nat < r 0%nat ∧ r m < pts n).
      We claim that (1 ≤ j + 1)%nat → pts 0%nat < r 0%nat ∧ r m < pts n as (Hs).
      { Assume that (1 ≤ j + 1)%nat. We conclude that pts 0%nat < r 0%nat ∧ r m < pts n. }
      It holds that pts 0%nat ≤ r 0%nat.
      It holds that r m ≤ pts n.
      We conclude that
        (∀ i : ℕ, (i < m)%nat → r i < r (S i)) ∧
        (∀ i : ℕ, (i ≤ m)%nat → df (Nat.add j 1) (r i) = 0) ∧
        pts 0%nat ≤ r 0%nat ∧ r m ≤ pts n ∧
        ((1 ≤ j + 1)%nat → pts 0%nat < r 0%nat ∧ r m < pts n).
  }
  (** For [j = n] only one point is left, strictly inside [(pts 0, pts n)]. *)
  It holds that (n + 0 = n)%nat as (En).
  By (Hind n 0%nat En) it holds that ∃ q : ℕ → ℝ,
    (∀ i : ℕ, (i < 0)%nat → q i < q (S i)) ∧
    (∀ i : ℕ, (i ≤ 0)%nat → df n (q i) = 0) ∧
    pts 0%nat ≤ q 0%nat ∧ q 0%nat ≤ pts n ∧
    ((1 ≤ n)%nat → pts 0%nat < q 0%nat ∧ q 0%nat < pts n) as (Hfin).
  Obtain q according to (Hfin).
  It holds that ∀ i : ℕ, (i ≤ 0)%nat → df n (q i) = 0 as (Hz).
  It holds that (1 ≤ n)%nat → pts 0%nat < q 0%nat ∧ q 0%nat < pts n as (Hs).
  By (Hs Hn) it holds that pts 0%nat < q 0%nat ∧ q 0%nat < pts n.
  It holds that (0 ≤ 0)%nat as (H00).
  By (Hz 0%nat H00) it holds that df n (q 0%nat) = 0.
  Choose c := q 0%nat.
  We conclude that pts 0%nat < c ∧ c < pts n ∧ df n c = 0.
Qed.


(** Derivative of [s ↦ (x - s)ᵏ]. *)
Lemma reflected_pow_derivative (x t : ℝ) (k : ℕ) :
    derivable_pt_lim (fun s => (x - s) ^ k) t (- (INR k * (x - t) ^ (pred k))).
Proof.
  By (derivable_pt_lim_minus (fct_cte x) id t 0 1
        (derivable_pt_lim_const x t) (derivable_pt_lim_id t)) it holds that
    derivable_pt_lim (fun s => x - s) t (0 - 1) as (H1).
  By (derivable_pt_lim_pow (x - t) k) it holds that
    derivable_pt_lim (fun y => y ^ k) (x - t) (INR k * (x - t) ^ (pred k)) as (H2).
  By (derivable_pt_lim_comp (fun s => x - s) (fun y => y ^ k) t _ _ H1 H2) it holds that
    derivable_pt_lim (fun s => (x - s) ^ k) t (INR k * (x - t) ^ (pred k) * (0 - 1)).
  It holds that - (INR k * (x - t) ^ (pred k)) = INR k * (x - t) ^ (pred k) * (0 - 1) as (E).
  By E we conclude that
    derivable_pt_lim (fun s => (x - s) ^ k) t (- (INR k * (x - t) ^ (pred k))).
Qed.

(** Product rule for one Taylor term [c·u(s)·(x - s)ᵏ]. *)
Lemma taylor_term_derivative (u0 u1 : ℝ → ℝ) (Hd : ∀ y : ℝ, derivable_pt_lim u0 y (u1 y))
    (cst x t : ℝ) (k : ℕ) :
    derivable_pt_lim (fun s => cst * u0 s * (x - s) ^ k) t
      (cst * u1 t * (x - t) ^ k - cst * u0 t * (INR k * (x - t) ^ (pred k))).
Proof.
  By (derivable_pt_lim_scal u0 cst t (u1 t) (Hd t)) it holds that
    derivable_pt_lim (fun s => cst * u0 s) t (cst * u1 t) as (H1).
  By (derivable_pt_lim_mult (fun s => cst * u0 s) (fun s => (x - s) ^ k) t _ _
        H1 (reflected_pow_derivative x t k)) it holds that
    derivable_pt_lim (fun s => cst * u0 s * (x - s) ^ k) t
      (cst * u1 t * (x - t) ^ k + cst * u0 t * (- (INR k * (x - t) ^ (pred k)))).
  It holds that cst * u1 t * (x - t) ^ k - cst * u0 t * (INR k * (x - t) ^ (pred k))
    = cst * u1 t * (x - t) ^ k + cst * u0 t * (- (INR k * (x - t) ^ (pred k))) as (E).
  By E we conclude that derivable_pt_lim (fun s => cst * u0 s * (x - s) ^ k) t
      (cst * u1 t * (x - t) ^ k - cst * u0 t * (INR k * (x - t) ^ (pred k))).
Qed.

(** [(n+1)/(n+1)! = 1/n!]. *)
Lemma inv_fact_succ (m : ℕ) :
    / INR (fact (S m)) * INR (S m) = / INR (fact m).
Proof.
  It holds that (fact (S m) = S m * fact m)%nat as (E1).
  By E1 it holds that INR (fact (S m)) = INR (Nat.mul (S m) (fact m)).
  By (mult_INR (S m) (fact m)) it holds that INR (Nat.mul (S m) (fact m)) = INR (S m) * INR (fact m).
  By (lt_0_INR (S m)) it holds that 0 < INR (S m).
  By (INR_fact_lt_0 m) it holds that 0 < INR (fact m).
  It holds that INR (S m) ≠ 0 as (HB').
  It holds that INR (fact m) ≠ 0.
  By (Rinv_mult (INR (S m)) (INR (fact m))) it holds that
    / (INR (S m) * INR (fact m)) = / INR (S m) * / INR (fact m).
  By (Rinv_r (INR (S m)) HB') it holds that INR (S m) * / INR (S m) = 1 as (E5).
  It holds that / INR (fact (S m)) = / INR (S m) * / INR (fact m) as (E6).
  By E6 it holds that / INR (fact (S m)) * INR (S m)
    = / INR (S m) * / INR (fact m) * INR (S m).
  It holds that / INR (S m) * / INR (fact m) * INR (S m)
    = / INR (fact m) * (INR (S m) * / INR (S m)).
  By E5 it holds that / INR (fact m) * (INR (S m) * / INR (S m)) = / INR (fact m).
  We conclude that / INR (fact (S m)) * INR (S m) = / INR (fact m).
Qed.

(** The derivative (in the base point [s]) of [∑_{k≤m} f⁽ᵏ⁾(s)/k!·(x - s)ᵏ]
    telescopes to [f⁽ᵐ⁺¹⁾(s)/m!·(x - s)ᵐ]. *)
Lemma taylor_sum_derivative (df : ℕ → ℝ → ℝ)
    (Hlim : ∀ k : ℕ, ∀ y : ℝ, derivable_pt_lim (df k) y (df (S k) y)) (x t : ℝ) (m : ℕ) :
    derivable_pt_lim (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) m) t
      (/ INR (fact m) * df (S m) t * (x - t) ^ m).
Proof.
  We claim that ∀ p : ℕ,
    derivable_pt_lim (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) p) t
      (/ INR (fact p) * df (S p) t * (x - t) ^ p) as (Hall).
  {
    We use induction on p.
    - We first show the base case
        (derivable_pt_lim (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) 0) t
          (/ INR (fact 0) * df 1%nat t * (x - t) ^ 0)).
      By (taylor_term_derivative (df 0%nat) (df 1%nat) (Hlim 0%nat) (/ INR (fact 0)) x t 0)
        it holds that derivable_pt_lim (fun s => / INR (fact 0) * df 0%nat s * (x - s) ^ 0) t
          (/ INR (fact 0) * df 1%nat t * (x - t) ^ 0
            - / INR (fact 0) * df 0%nat t * (INR 0 * (x - t) ^ (pred 0))) as (H1).
      It holds that / INR (fact 0) * df 1%nat t * (x - t) ^ 0
        = / INR (fact 0) * df 1%nat t * (x - t) ^ 0
            - / INR (fact 0) * df 0%nat t * (INR 0 * (x - t) ^ (pred 0)) as (E).
      By E we conclude that
        derivable_pt_lim (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) 0) t
          (/ INR (fact 0) * df 1%nat t * (x - t) ^ 0).
    - We now show the induction step.
      Take p : ℕ.
      Assume that
        derivable_pt_lim (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) p) t
          (/ INR (fact p) * df (S p) t * (x - t) ^ p) as (IH).
      By (taylor_term_derivative (df (S p)) (df (S (S p))) (Hlim (S p))
            (/ INR (fact (S p))) x t (S p)) it holds that
        derivable_pt_lim (fun s => / INR (fact (S p)) * df (S p) s * (x - s) ^ (S p)) t
          (/ INR (fact (S p)) * df (S (S p)) t * (x - t) ^ (S p)
            - / INR (fact (S p)) * df (S p) t * (INR (S p) * (x - t) ^ p)) as (H1).
      By (derivable_pt_lim_plus _ _ t _ _ IH H1) it holds that
        derivable_pt_lim
          (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) (S p)) t
          (/ INR (fact p) * df (S p) t * (x - t) ^ p
            + (/ INR (fact (S p)) * df (S (S p)) t * (x - t) ^ (S p)
               - / INR (fact (S p)) * df (S p) t * (INR (S p) * (x - t) ^ p))).
      By (inv_fact_succ p) it holds that / INR (fact (S p)) * INR (S p) = / INR (fact p).
      It holds that / INR (fact (S p)) * df (S (S p)) t * (x - t) ^ (S p)
        = / INR (fact p) * df (S p) t * (x - t) ^ p
            + (/ INR (fact (S p)) * df (S (S p)) t * (x - t) ^ (S p)
               - / INR (fact (S p)) * df (S p) t * (INR (S p) * (x - t) ^ p)) as (E).
      By E it holds that
        derivable_pt_lim
          (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) (S p)) t
          (/ INR (fact (S p)) * df (S (S p)) t * (x - t) ^ (S p)).
      It holds that (p + 1 = S p)%nat as (Ep).
      By Ep we conclude that
        derivable_pt_lim
          (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) (Nat.add p 1)) t
          (/ INR (fact (Nat.add p 1)) * df (S (Nat.add p 1)) t * (x - t) ^ (Nat.add p 1)).
  }
  By (Hall m) we conclude that
    derivable_pt_lim (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) m) t
      (/ INR (fact m) * df (S m) t * (x - t) ^ m).
Qed.

(** At [s = x] only the constant term of the Taylor sum survives. *)
Lemma taylor_sum_at_center (df : ℕ → ℝ → ℝ) (x : ℝ) (m : ℕ) :
    sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) m = df 0%nat x.
Proof.
  We claim that ∀ p : ℕ,
    sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) p = df 0%nat x as (Hall).
  {
    We use induction on p.
    - We first show the base case
        (sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) 0 = df 0%nat x).
      It holds that sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) 0
        = / INR (fact 0) * df 0%nat x * (x - x) ^ 0.
      It holds that INR (fact 0) = 1.
      It holds that (x - x) ^ 0 = 1.
      We conclude that sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) 0 = df 0%nat x.
    - We now show the induction step.
      Take p : ℕ.
      Assume that sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) p = df 0%nat x.
      It holds that (x - x) ^ (S p) = (x - x) * (x - x) ^ p.
      It holds that (x - x) ^ (S p) = 0.
      It holds that sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) (S p)
        = sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) p
          + / INR (fact (S p)) * df (S p) x * (x - x) ^ (S p).
      It holds that sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) (S p)
        = df 0%nat x.
      It holds that (p + 1 = S p)%nat as (Ep).
      By Ep we conclude that
        sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) (Nat.add p 1) = df 0%nat x.
  }
  By (Hall m) we conclude that
    sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) m = df 0%nat x.
Qed.

(** [u/e·e = u] for [e ≠ 0]. *)
Lemma div_mul_cancel (u e : ℝ) (He : e ≠ 0) : u / e * e = u.
Proof.
  By (Rinv_l e He) it holds that / e * e = 1.
  It holds that u / e * e = u * (/ e * e).
  We conclude that u / e * e = u.
Qed.

(** _Taylor's theorem with Lagrange remainder_ (Abbott Theorem 6.6.3): if [f] is
    [(n+1)]-times differentiable, with [df k = f⁽ᵏ⁾] and [df (S k)] the
    derivative of [df k] (and [df 0 = f]), then for every [x ≠ a] there is a [c]
    strictly between [a] and [x] with
    [f(x) = ∑_{k=0}^n f⁽ᵏ⁾(a)/k!·(x - a)ᵏ + f⁽ⁿ⁺¹⁾(c)/(n+1)!·(x - a)ⁿ⁺¹].
    (For [x = a] there is no point strictly between, hence [x ≠ a].)

    Proof idea: fix [x] and vary the base point: the function
    [G(s) = f(x) - ∑_{k≤n} f⁽ᵏ⁾(s)/k!·(x - s)ᵏ - K·(x - s)ⁿ⁺¹], with [K] chosen
    so that [G(a) = 0], also satisfies [G(x) = 0]. Its derivative telescopes to
    [G'(s) = (K·(n+1) - f⁽ⁿ⁺¹⁾(s)/n!)·(x - s)ⁿ], so Rolle's theorem gives a [c]
    with [K = f⁽ⁿ⁺¹⁾(c)/(n+1)!]. *)
Theorem taylor_theorem_lagrange
    (f : ℝ → ℝ) (df : ℕ → ℝ → ℝ) (a x : ℝ) (n : ℕ)
    (Hxa : x ≠ a)
    (H0 : df 0%nat = f)
    (Hstep : ∀ k ∈ ℕ, ∀ y ∈ ℝ,
        ∃ Hd : derivable_pt (df k) y, derive_pt (df k) y Hd = df (S k) y) :
    ∃ c : ℝ, Rmin a x < c ∧ c < Rmax a x ∧
      f x = sum_f_R0 (fun k => df k a / INR (fact k) * (x - a) ^ k) n
            + df (S n) c / INR (fact (S n)) * (x - a) ^ (S n).
Proof.
  We claim that ∀ k : ℕ, ∀ y : ℝ, derivable_pt_lim (df k) y (df (S k) y) as (Hlim).
  {
    Take k : ℕ. Take y : ℝ.
    By Hstep it holds that
      ∃ Hd : derivable_pt (df k) y, derive_pt (df k) y Hd = df (S k) y as (Hk).
    Obtain Hd according to (Hk).
    It holds that derive_pt (df k) y Hd = df (S k) y as (Hk').
    By (derive_pt_eq_1 (df k) y (df (S k) y) Hd Hk') we conclude that
      derivable_pt_lim (df k) y (df (S k) y).
  }
  (** The Taylor polynomial at [a], and the constant [K] making [G(a) = 0]. *)
  Define P := sum_f_R0 (fun k => / INR (fact k) * df k a * (x - a) ^ k) n.
  It holds that x - a ≠ 0 as (Hxa').
  By (pow_nonzero (x - a) (S n) Hxa') it holds that (x - a) ^ (S n) ≠ 0 as (He).
  Define K := (df 0%nat x - P) / (x - a) ^ (S n).
  By (div_mul_cancel (df 0%nat x - P) ((x - a) ^ (S n)) He) it holds that
    K * (x - a) ^ (S n) = df 0%nat x - P.
  (** The auxiliary function
      [G(s) = f(x) - ∑_{k≤n} f⁽ᵏ⁾(s)/k!·(x - s)ᵏ - K·(x - s)ⁿ⁺¹]. *)
  Define G := fun s => df 0%nat x
    - sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) n - K * (x - s) ^ (S n).
  Define Gd := fun s => 0 - / INR (fact n) * df (S n) s * (x - s) ^ n
    - K * (- (INR (S n) * (x - s) ^ (pred (S n)))).
  We claim that ∀ y : ℝ, derivable_pt_lim G y (Gd y) as (HG).
  {
    Take y : ℝ.
    By (derivable_pt_lim_minus (fct_cte (df 0%nat x))
          (fun s => sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) n) y _ _
          (derivable_pt_lim_const (df 0%nat x) y) (taylor_sum_derivative df Hlim x y n))
      it holds that derivable_pt_lim
        (fun s => df 0%nat x - sum_f_R0 (fun k => / INR (fact k) * df k s * (x - s) ^ k) n) y
        (0 - / INR (fact n) * df (S n) y * (x - y) ^ n) as (H1).
    By (derivable_pt_lim_scal (fun s => (x - s) ^ (S n)) K y _
          (reflected_pow_derivative x y (S n))) it holds that
      derivable_pt_lim (fun s => K * (x - s) ^ (S n)) y
        (K * (- (INR (S n) * (x - y) ^ (pred (S n))))) as (H2).
    By (derivable_pt_lim_minus _ _ y _ _ H1 H2) we conclude that
      derivable_pt_lim G y (Gd y).
  }
  (** [G] vanishes at both [a] and [x]. *)
  It holds that G a = df 0%nat x - P - K * (x - a) ^ (S n).
  It holds that G a = 0 as (HGa).
  By (taylor_sum_at_center df x n) it holds that
    sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) n = df 0%nat x.
  It holds that (x - x) ^ (S n) = (x - x) * (x - x) ^ n.
  It holds that (x - x) ^ (S n) = 0.
  It holds that G x = df 0%nat x
    - sum_f_R0 (fun k => / INR (fact k) * df k x * (x - x) ^ k) n - K * (x - x) ^ (S n).
  It holds that G x = 0 as (HGx).
  (** Rolle's theorem between [a] and [x]. *)
  We claim that ∃ c : ℝ, Rmin a x < c ∧ c < Rmax a x ∧ c ≠ x ∧ Gd c = 0 as (Hc).
  {
    Either (a < x) or (¬ (a < x)).
    - Case (a < x).
      It holds that a < x as (Hax).
      By (rolle_zero G Gd a x Hax HG HGa HGx) it holds that
        ∃ c : ℝ, a < c ∧ c < x ∧ Gd c = 0 as (Hr).
      Obtain c according to (Hr).
      It holds that a ≤ x as (Hax').
      By (Rmin_left a x Hax') it holds that Rmin a x = a.
      By (Rmax_right a x Hax') it holds that Rmax a x = x.
      Choose c0 := c.
      We conclude that Rmin a x < c0 ∧ c0 < Rmax a x ∧ c0 ≠ x ∧ Gd c0 = 0.
    - Case (¬ (a < x)).
      It holds that x < a as (Hxa2).
      By (rolle_zero G Gd x a Hxa2 HG HGx HGa) it holds that
        ∃ c : ℝ, x < c ∧ c < a ∧ Gd c = 0 as (Hr).
      Obtain c according to (Hr).
      It holds that x ≤ a as (Hxa3).
      By (Rmin_right a x Hxa3) it holds that Rmin a x = x.
      By (Rmax_left a x Hxa3) it holds that Rmax a x = a.
      Choose c0 := c.
      We conclude that Rmin a x < c0 ∧ c0 < Rmax a x ∧ c0 ≠ x ∧ Gd c0 = 0.
  }
  Obtain c according to (Hc).
  It holds that Rmin a x < c ∧ c < Rmax a x.
  It holds that c ≠ x.
  It holds that Gd c = 0.
  (** Solve [G'(c) = 0] for [K]. *)
  It holds that x - c ≠ 0 as (Hxc).
  By (pow_nonzero (x - c) n Hxc) it holds that (x - c) ^ n ≠ 0.
  It holds that Gd c = 0 - / INR (fact n) * df (S n) c * (x - c) ^ n
    - K * (- (INR (S n) * (x - c) ^ n)).
  It holds that (K * INR (S n) - / INR (fact n) * df (S n) c) * (x - c) ^ n = 0 as (H1).
  By (Rmult_integral (K * INR (S n) - / INR (fact n) * df (S n) c) ((x - c) ^ n) H1)
    it holds that K * INR (S n) - / INR (fact n) * df (S n) c = 0 ∨ (x - c) ^ n = 0.
  It holds that K * INR (S n) = / INR (fact n) * df (S n) c.
  By (inv_fact_succ n) it holds that / INR (fact (S n)) * INR (S n) = / INR (fact n).
  By (lt_0_INR (S n)) it holds that 0 < INR (S n).
  It holds that INR (S n) ≠ 0.
  It holds that (K - df (S n) c / INR (fact (S n))) * INR (S n) = 0 as (H4).
  By (Rmult_integral (K - df (S n) c / INR (fact (S n))) (INR (S n)) H4)
    it holds that K - df (S n) c / INR (fact (S n)) = 0 ∨ INR (S n) = 0.
  It holds that K = df (S n) c / INR (fact (S n)) as (HKc).
  (** Conclude. *)
  We claim that ∀ k : ℕ, (k ≤ n)%nat →
    df k a / INR (fact k) * (x - a) ^ k = / INR (fact k) * df k a * (x - a) ^ k as (Hterm).
  { Take k : ℕ. Assume that (k ≤ n)%nat.
    We conclude that df k a / INR (fact k) * (x - a) ^ k = / INR (fact k) * df k a * (x - a) ^ k. }
  By (sum_eq _ _ n Hterm) it holds that
    sum_f_R0 (fun k => df k a / INR (fact k) * (x - a) ^ k) n = P as (HP).
  By H0 it holds that f x = df 0%nat x as (Hf).
  It holds that df 0%nat x = P + K * (x - a) ^ (S n).
  By HKc it holds that
    df 0%nat x = P + df (S n) c / INR (fact (S n)) * (x - a) ^ (S n).
  By HP it holds that
    df 0%nat x = sum_f_R0 (fun k => df k a / INR (fact k) * (x - a) ^ k) n
      + df (S n) c / INR (fact (S n)) * (x - a) ^ (S n).
  By Hf it holds that
    f x = sum_f_R0 (fun k => df k a / INR (fact k) * (x - a) ^ k) n
      + df (S n) c / INR (fact (S n)) * (x - a) ^ (S n).
  It holds that Rmin a x < c.
  It holds that c < Rmax a x.
  Choose c0 := c.
  We conclude that Rmin a x < c0 ∧ c0 < Rmax a x ∧
      f x = sum_f_R0 (fun k => df k a / INR (fact k) * (x - a) ^ k) n
            + df (S n) c0 / INR (fact (S n)) * (x - a) ^ (S n).
Qed.


(** ** Sinusoidal bounds *)

(** The first-order Taylor polynomial of [sin] at [0]. *)
Definition T_sin1 (x : R) : R := x.

(** _Taylor series for sin(x)_ (upper bound): [sin x < x] for [x > 0]. The degree-1 Taylor
    polynomial of [sin] at [0] is [s₁(x) = x], and this is the Stdlib lemma
    [sin_lt_x]. *)
Lemma sin_lt_x (x : R) (Hx : 0 < x) : sin x < x.
Proof.
  By (Stdlib.Reals.Ratan.sin_lt_x x Hx) we conclude that sin x < x.
Qed.


(** _Taylor series for sin(x)_ (lower bound): [x - x³/6 ≤ sin x] for [0 ≤ x ≤ π/2].

    Proof idea: this follows from the alternating series estimate for
    [sin x = x - x³/3! + x⁵/5! - ⋯]; truncating after the cubic term gives a
    lower bound on [[0, π/2]]. *)
Lemma sin_ge_taylor (x : R) (Hx0 : 0 ≤ x) (HxPI : x ≤ PI / 2) :
    x - x ^ 3 / 6 ≤ sin x.
Proof.
  By PI_RGT_0 it holds that PI > 0.
  It holds that x ≤ PI as (HxP).
  By (sin_bound x 0 Hx0 HxP) it holds that
    sin_approx x (2 * 0 + 1) ≤ sin x ∧ sin x ≤ sin_approx x (2 * (0 + 1)).
  It holds that sin_approx x (2 * 0 + 1) ≤ sin x.
  It holds that sin_approx x (2 * 0 + 1) = sin_term x 0 + sin_term x 1.
  It holds that sin_term x 0 = (-1) ^ 0 * (x ^ 1 / INR (fact 1)).
  It holds that sin_term x 1 = (-1) ^ 1 * (x ^ 3 / INR (fact 3)).
  It holds that INR (fact 1) = 1 as (F1).
  It holds that (fact 3 = 6)%nat as (F3n).
  By F3n it holds that INR (fact 3) = INR 6.
  By (INR_IZR_INZ 6) it holds that INR 6 = 6.
  It holds that INR (fact 3) = 6 as (F3).
  By F1 it holds that sin_term x 0 = (-1) ^ 0 * (x ^ 1 / 1).
  It holds that (-1) ^ 0 * (x ^ 1 / 1) = x.
  By F3 it holds that sin_term x 1 = (-1) ^ 1 * (x ^ 3 / 6).
  It holds that (-1) ^ 1 * (x ^ 3 / 6) = - (x ^ 3 / 6).
  It holds that sin_term x 0 = x.
  It holds that sin_term x 1 = - (x ^ 3 / 6).
  We conclude that x - x ^ 3 / 6 ≤ sin x.
Qed.


(** ** Error bound for the linear approximation of sin *)

(** _Taylor series for sin(x)_ (cf. Abbott Example 6.6.4): [|sin x - x| ≤ x³/6] for [0 < x ≤ π/2], so the linear
    approximation [sin x ≈ x] has error at most [x³/6].

    Proof idea: the upper bound [sin x < x] gives [sin x - x < 0], so
    [|sin x - x| = x - sin x]; the lower bound [sin x ≥ x - x³/6] then gives
    [x - sin x ≤ x³/6]. *)
Lemma sin_approx_error (x : R) (Hx0 : 0 < x) (HxPI : x ≤ PI / 2) :
    Rabs (sin x - x) ≤ x ^ 3 / 6.
Proof.
  By (sin_lt_x x Hx0) it holds that sin x < x.
  It holds that 0 ≤ x as (Hx0').
  By (sin_ge_taylor x Hx0' HxPI) it holds that x - x ^ 3 / 6 ≤ sin x.
  It holds that sin x - x < 0 as (Hneg).
  By (Rabs_left (sin x - x) Hneg) it holds that |sin x - x| = - (sin x - x).
  We conclude that Rabs (sin x - x) ≤ x ^ 3 / 6.
Qed.

