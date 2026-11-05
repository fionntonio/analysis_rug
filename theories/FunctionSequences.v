(** * RUG.Analysis.FunctionSequences — Sequences of functions.

  #<a href="../../index.html##lecture10">Lecture 10</a># and #<a href="../../index.html##lecture11">Lecture 11</a>#.

  Formalizes Abbott §6.2–6.4: pointwise and uniform convergence,
  the Weierstrass M-test, and the interchange of limits with
  continuity and differentiation for uniformly convergent sequences.
  Term-by-term integration is in [Analysis.Integration]. *)

Require Import RUG.Analysis.Lib.StdlibReals.
From Stdlib Require Import Logic.ClassicalDescription.
Require Export RUG.Analysis.Continuity.
Require Import RUG.Analysis.CauchySequences.
Require Import RUG.Analysis.Series.
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

(** _Cauchy criterion_ for uniform convergence (Abbott Theorem 6.2.5): [(fₙ)] converges uniformly on [A] iff it is uniformly Cauchy:
    for every ε > 0 there exists N such that for all [n, m ≥ N] and all [x ∈ A],
    [|fₙ(x) - fₘ(x)| < ε].

    Proof idea (⇒): by the triangle inequality
    [|fₙ(x) - fₘ(x)| ≤ |fₙ(x) - g(x)| + |g(x) - fₘ(x)| < ε/2 + ε/2 = ε]. *)
Lemma uniform_cauchy_criterion (fn : ℕ → ℝ → ℝ) (A : subset ℝ) :
    (∃ g : ℝ → ℝ, converges_uniformly fn g A) ⇔
    (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      Rabs (fn n x - fn m x) < ε).
Proof.
  We show both directions.
  - We need to show that (∃ g : ℝ → ℝ, converges_uniformly fn g A) ⇨
      (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
        | fn n x - fn m x | < ε).
    Assume that ∃ g : ℝ → ℝ, converges_uniformly fn g A.
    Obtain such a g.
    By unif_conv_is_cauchy it holds that
      ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, ∀ m : ℕ, (n ≥ N1)%nat → (m ≥ N1)%nat →
        ∀ x ∈ A, | fn n x - fn m x | < ε as (Hcauchy).
    Take ε > 0.
    By Hcauchy it holds that
      ∃ N1 ∈ ℕ, ∀ n : ℕ, ∀ m : ℕ, (n ≥ N1)%nat → (m ≥ N1)%nat →
        ∀ x ∈ A, | fn n x - fn m x | < ε as (HN).
    Obtain such an N1.
    Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
    We need to show that ∀ n ≥ N2, ∀ m ≥ N2, ∀ x ∈ A, | fn n x - fn m x | < ε.
    Take n ≥ N2. Take m ≥ N2. Take x ∈ A.
    By HN we conclude that | fn n x - fn m x | < ε.
  - We need to show that
      (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
        | fn n x - fn m x | < ε) ⇨ ∃ g : ℝ → ℝ, converges_uniformly fn g A.
    Assume that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      | fn n x - fn m x | < ε as (Hcauchy).
    (** For each [x ∈ A] the sequence [fₙ(x)] is Cauchy, hence convergent. *)
    We claim that ∀ x ∈ A, ∃ L ∈ ℝ, (fun n => fn n x) ⟶ L as (Hpt).
    {
      Take x ∈ A.
      We claim that is_cauchy (fun n => fn n x).
      {
        We need to show that
          ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, | fn n x - fn m x | < ε.
        Take ε > 0.
        By Hcauchy it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ y ∈ A,
          | fn n y - fn m y | < ε as (HN).
        Obtain such an N1.
        Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
        We need to show that ∀ n ≥ N2, ∀ m ≥ N2, | fn n x - fn m x | < ε.
        Take n ≥ N2. Take m ≥ N2.
        By HN we conclude that | fn n x - fn m x | < ε.
      }
      By cauchy_is_convergent we conclude that
        ∃ L ∈ ℝ, (fun n => fn n x) ⟶ L.
    }
    (** We choose [g(x)] as the limit of [fₙ(x)] for [x ∈ A], and [0] elsewhere. *)
    (** Remark: here we need to deal with [x ∉ A] due to the way we conveniently
        defined [g], as a total function [ℝ → ℝ]: [unique_choice] needs exactly
        one value at every [x]. We can probably circumvent this by using
        [choice] (from [Logic.ClassicalChoice]), shifting the complexity to the
        axiom. We are paying this price due to the way we defined
        [converges_uniformly], which simplifies the functions at the expense of
        the proofs. Changing the definition (e.g. taking [g] defined only on
        [A]) would make many results on integrability and differentiation,
        which need functions [ℝ → ℝ], unnecessarily harder to use. *)
    Define Rlim := fun (x : ℝ) (L : ℝ) =>
      (x ∈ A ∧ (fun n => fn n x) ⟶ L) ∨ (¬ x ∈ A ∧ L = 0).
    We claim that ∀ x : ℝ, ∃ L : ℝ, Rlim x L ∧ ∀ L1 : ℝ, Rlim x L1 → L = L1.
    {
      Take x : ℝ.
      Either x ∈ A or ¬ x ∈ A.
      - Case x ∈ A.
        By Hpt it holds that ∃ L ∈ ℝ, (fun n => fn n x) ⟶ L.
        Obtain such an L.
        Choose L0 := L.
        We show both statements.
        + We need to show that
            (x ∈ A ∧ (fun n => fn n x) ⟶ L0) ∨ (¬ x ∈ A ∧ L0 = 0).
          It holds that x ∈ A ∧ (fun n => fn n x) ⟶ L0.
          We conclude that
            (x ∈ A ∧ (fun n => fn n x) ⟶ L0) ∨ (¬ x ∈ A ∧ L0 = 0).
        + We need to show that ∀ L1 : ℝ, Rlim x L1 → L0 = L1.
          Take L1 : ℝ.
          Assume that
            (x ∈ A ∧ (fun n => fn n x) ⟶ L1) ∨ (¬ x ∈ A ∧ L1 = 0) as (HL1).
          Because (HL1) either (x ∈ A ∧ (fun n => fn n x) ⟶ L1)
            or (¬ x ∈ A ∧ L1 = 0) holds.
          * Case (x ∈ A ∧ (fun n => fn n x) ⟶ L1).
            It holds that (fun n => fn n x) ⟶ L1.
            By (limit_unique (fun n => fn n x) L L1) we conclude that L0 = L1.
          * Case (¬ x ∈ A ∧ L1 = 0).
            It holds that ¬ x ∈ A.
            Contradiction.
      - Case ¬ x ∈ A.
        Choose L := 0.
        We show both statements.
        + We need to show that
            (x ∈ A ∧ (fun n => fn n x) ⟶ L) ∨ (¬ x ∈ A ∧ L = 0).
          It holds that ¬ x ∈ A ∧ L = 0.
          We conclude that
            (x ∈ A ∧ (fun n => fn n x) ⟶ L) ∨ (¬ x ∈ A ∧ L = 0).
        + We need to show that ∀ L1 : ℝ, Rlim x L1 → L = L1.
          Take L1 : ℝ.
          Assume that
            (x ∈ A ∧ (fun n => fn n x) ⟶ L1) ∨ (¬ x ∈ A ∧ L1 = 0) as (HL1).
          Because (HL1) either (x ∈ A ∧ (fun n => fn n x) ⟶ L1)
            or (¬ x ∈ A ∧ L1 = 0) holds.
          * Case (x ∈ A ∧ (fun n => fn n x) ⟶ L1).
            It holds that x ∈ A.
            Contradiction.
          * Case (¬ x ∈ A ∧ L1 = 0).
            We conclude that L = L1.
    }
    By unique_choice it holds that ∃ g : ℝ → ℝ, ∀ x : ℝ, Rlim x (g x) as (Hchoice).
    Obtain such a g.
    Choose g0 := g.
    We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ x ∈ A, | fn n x - g0 x | < ε.
    Take ε > 0.
    It holds that ε / 2 > 0.
    By Hcauchy it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      | fn n x - fn m x | < ε / 2 as (HN).
    Obtain such an N1.
    Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
    We need to show that ∀ n : ℕ, (n ≥ N2)%nat → ∀ x ∈ A, | fn n x - g0 x | < ε.
    Take n : ℕ. Assume that (n ≥ N2)%nat.
    Take x ∈ A.
    By Hchoice it holds that Rlim x (g x).
    It holds that
      (x ∈ A ∧ (fun m => fn m x) ⟶ g x) ∨ (¬ x ∈ A ∧ g x = 0) as (Hgx).
    Because (Hgx) either (x ∈ A ∧ (fun m => fn m x) ⟶ g x)
      or (¬ x ∈ A ∧ g x = 0) holds.
    - Case (x ∈ A ∧ (fun m => fn m x) ⟶ g x).
      (** We compare [fₙ(x)] with [fₘ(x)] for some large [m]. *)
      It holds that ∃ M ∈ ℕ, ∀ m ≥ M, | fn m x - g x | < ε / 2 as (HM).
      Obtain such an M.
      Define m := Nat.max N1 M.
      It holds that (m ≥ N1)%nat. It holds that (m ≥ M)%nat.
      By HN it holds that | fn n x - fn m x | < ε / 2.
      By HM it holds that | fn m x - g x | < ε / 2.
      It holds that | fn n x - g x | = | (fn n x - fn m x) + (fn m x - g x) |.
      By Rabs_triang it holds that
        | (fn n x - fn m x) + (fn m x - g x) |
          ≤ | fn n x - fn m x | + | fn m x - g x |.
      It holds that | fn n x - g x | < ε.
      We conclude that | fn n x - g0 x | < ε.
    - Case (¬ x ∈ A ∧ g x = 0).
      It holds that ¬ x ∈ A.
      Contradiction.
Qed.

(** ** Uniform limit of continuous functions is continuous *)

(** _Preservation of continuity_ (Abbott Theorem 6.2.6): if [(fₙ) ⇉ g] uniformly on [A] and each [fₙ]
    is continuous at [a ∈ A], then [g] is continuous at [a]. As in Abbott, the
    functions live on [A], so continuity at [a] is relative to [A]: for every
    [ε > 0] there is [δ > 0] with [|h(x) - h(a)| < ε] for all [x ∈ A] with
    [|x - a| < δ].

    Proof idea (3ε argument): given [ε > 0], (1) uniform convergence gives [N]
    with [|f_N(x) - g(x)| < ε/3] for all [x ∈ A]; (2) continuity of [f_N] at [a]
    gives [δ] with [|f_N(x) - f_N(a)| < ε/3] for [x ∈ A], [|x - a| < δ]; (3) then
    [|g(x) - g(a)| ≤ |g(x) - f_N(x)| + |f_N(x) - f_N(a)| + |f_N(a) - g(a)| < ε]. *)
Theorem uniform_limit_continuous (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) (a : ℝ)
    (Ha : a ∈ A)
    (Hfn : ∀ n ∈ ℕ, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A,
      | x - a | < δ → | fn n x - fn n a | < ε)
    (Hunif : converges_uniformly fn g A) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, | x - a | < δ → | g x - g a | < ε.
Proof.
  Take ε > 0.
  It holds that ε / 3 > 0.
  (** Step 1: one [f_N] is uniformly [ε/3]-close to [g] on [A]. *)
  By Hunif it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ A, | fn n x - g x | < ε / 3 as (HN).
  Obtain such an N1.
  It holds that (N1 ≥ N1)%nat.
  By HN it holds that ∀ x ∈ A, | fn N1 x - g x | < ε / 3 as (HN1).
  (** Step 2: continuity of [f_N] at [a]. *)
  By Hfn it holds that ∃ δ > 0, ∀ x ∈ A, | x - a | < δ →
    | fn N1 x - fn N1 a | < ε / 3 as (Hδ).
  Obtain such a δ.
  Choose δ0 := δ. { Indeed, δ0 > 0. }
  We need to show that ∀ x ∈ A, | x - a | < δ0 → | g x - g a | < ε.
  Take x ∈ A.
  Assume that | x - a | < δ0.
  By Hδ it holds that | fn N1 x - fn N1 a | < ε / 3.
  By HN1 it holds that | fn N1 x - g x | < ε / 3.
  By HN1 it holds that | fn N1 a - g a | < ε / 3.
  (** Step 3: the [ε/3]-argument. *)
  It holds that | g x - fn N1 x | = | fn N1 x - g x |.
  It holds that
    | g x - g a | = | (g x - fn N1 x) + ((fn N1 x - fn N1 a) + (fn N1 a - g a)) |.
  By Rabs_triang it holds that
    | (g x - fn N1 x) + ((fn N1 x - fn N1 a) + (fn N1 a - g a)) |
      ≤ | g x - fn N1 x | + | (fn N1 x - fn N1 a) + (fn N1 a - g a) |.
  By Rabs_triang it holds that
    | (fn N1 x - fn N1 a) + (fn N1 a - g a) |
      ≤ | fn N1 x - fn N1 a | + | fn N1 a - g a |.
  We conclude that | g x - g a | < ε.
Qed.

(** ** Weierstrass M-test *)

(** _Weierstrass M-test_ (Abbott Corollary 6.4.5): if [|fₙ(x)| ≤ Mₙ] for all [x ∈ A] and
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
  (** The tails of [∑ fₖ(x)] are dominated by the tails of [∑ Mₖ]. *)
  We claim that ∀ x : ℝ, x ∈ A → ∀ m : ℕ, ∀ k : ℕ,
    | sum_f_R0 (fun j => fn j x) (m + k)%nat - sum_f_R0 (fun j => fn j x) m |
      ≤ sum_f_R0 M (m + k)%nat - sum_f_R0 M m as (Htail).
  {
    Take x : ℝ. Assume that x ∈ A. Take m : ℕ.
    We use induction on k.
    + We first show the base case
        | sum_f_R0 (fun j => fn j x) (m + 0)%nat - sum_f_R0 (fun j => fn j x) m |
          ≤ sum_f_R0 M (m + 0)%nat - sum_f_R0 M m.
      It holds that (m + 0)%nat = m.
      It holds that
        sum_f_R0 (fun j => fn j x) (m + 0)%nat - sum_f_R0 (fun j => fn j x) m = 0.
      It holds that sum_f_R0 M (m + 0)%nat - sum_f_R0 M m = 0.
      We conclude that
        | sum_f_R0 (fun j => fn j x) (m + 0)%nat - sum_f_R0 (fun j => fn j x) m |
          ≤ sum_f_R0 M (m + 0)%nat - sum_f_R0 M m.
    + We now show the induction step.
      Take k : ℕ.
      Assume that
        | sum_f_R0 (fun j => fn j x) (m + k)%nat - sum_f_R0 (fun j => fn j x) m |
          ≤ sum_f_R0 M (m + k)%nat - sum_f_R0 M m.
      It holds that (m + (k + 1))%nat = S (m + k)%nat.
      It holds that sum_f_R0 (fun j => fn j x) (S (m + k)%nat)
        = sum_f_R0 (fun j => fn j x) (m + k)%nat + fn (S (m + k)%nat) x.
      It holds that sum_f_R0 M (S (m + k)%nat) = sum_f_R0 M (m + k)%nat + M (S (m + k)%nat).
      By Hbound it holds that | fn (S (m + k)%nat) x | ≤ M (S (m + k)%nat).
      By Rabs_triang it holds that
        | (sum_f_R0 (fun j => fn j x) (m + k)%nat - sum_f_R0 (fun j => fn j x) m)
          + fn (S (m + k)%nat) x |
        ≤ | sum_f_R0 (fun j => fn j x) (m + k)%nat - sum_f_R0 (fun j => fn j x) m |
          + | fn (S (m + k)%nat) x |.
      It holds that
        | sum_f_R0 (fun j => fn j x) (S (m + k)%nat) - sum_f_R0 (fun j => fn j x) m |
          ≤ sum_f_R0 M (S (m + k)%nat) - sum_f_R0 M m.
      We conclude that
        | sum_f_R0 (fun j => fn j x) (m + (k + 1))%nat - sum_f_R0 (fun j => fn j x) m |
          ≤ sum_f_R0 M (m + (k + 1))%nat - sum_f_R0 M m.
  }
  (** The partial sums of [∑ Mₖ] converge, hence are Cauchy. *)
  By HM it holds that ∃ L ∈ ℝ, (fun n => sum_f_R0 M n) ⟶ L.
  Obtain such an L.
  By convergent_is_cauchy it holds that is_cauchy (fun n => sum_f_R0 M n) as (HMc).
  (** We verify the uniform Cauchy criterion for the partial sums. *)
  We claim that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
    | sum_f_R0 (fun k => fn k x) n - sum_f_R0 (fun k => fn k x) m | < ε.
  {
    Take ε > 0.
    By HMc it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
      | sum_f_R0 M n - sum_f_R0 M m | < ε as (HN).
    Obtain such an N1.
    Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
    We need to show that ∀ n ≥ N2, ∀ m ≥ N2, ∀ x ∈ A,
      | sum_f_R0 (fun k => fn k x) n - sum_f_R0 (fun k => fn k x) m | < ε.
    Take n ≥ N2. Take m ≥ N2. Take x ∈ A.
    By HN it holds that | sum_f_R0 M n - sum_f_R0 M m | < ε.
    By Nat.le_gt_cases it holds that (m ≤ n)%nat ∨ (n < m)%nat as (Hcases).
    Because (Hcases) either (m ≤ n)%nat or (n < m)%nat holds.
    - Case (m ≤ n)%nat.
      It holds that (m + (n - m))%nat = n.
      By Htail it holds that
        | sum_f_R0 (fun j => fn j x) (m + (n - m))%nat - sum_f_R0 (fun j => fn j x) m |
          ≤ sum_f_R0 M (m + (n - m))%nat - sum_f_R0 M m.
      It holds that
        | sum_f_R0 (fun k => fn k x) n - sum_f_R0 (fun k => fn k x) m |
          ≤ sum_f_R0 M n - sum_f_R0 M m.
      We conclude that (&
        | sum_f_R0 (fun k => fn k x) n - sum_f_R0 (fun k => fn k x) m |
          ≤ sum_f_R0 M n - sum_f_R0 M m
          ≤ | sum_f_R0 M n - sum_f_R0 M m |
          < ε).
    - Case (n < m)%nat.
      It holds that (n + (m - n))%nat = m.
      By Htail it holds that
        | sum_f_R0 (fun j => fn j x) (n + (m - n))%nat - sum_f_R0 (fun j => fn j x) n |
          ≤ sum_f_R0 M (n + (m - n))%nat - sum_f_R0 M n.
      It holds that
        | sum_f_R0 (fun k => fn k x) m - sum_f_R0 (fun k => fn k x) n |
          ≤ sum_f_R0 M m - sum_f_R0 M n.
      By Rabs_minus_sym it holds that
        | sum_f_R0 (fun k => fn k x) n - sum_f_R0 (fun k => fn k x) m |
          = | sum_f_R0 (fun k => fn k x) m - sum_f_R0 (fun k => fn k x) n |.
      By Rabs_minus_sym it holds that
        | sum_f_R0 M n - sum_f_R0 M m | = | sum_f_R0 M m - sum_f_R0 M n |.
      We conclude that (&
        | sum_f_R0 (fun k => fn k x) n - sum_f_R0 (fun k => fn k x) m |
          = | sum_f_R0 (fun k => fn k x) m - sum_f_R0 (fun k => fn k x) n |
          ≤ sum_f_R0 M m - sum_f_R0 M n
          ≤ | sum_f_R0 M m - sum_f_R0 M n |
          < ε).
  }
  By uniform_cauchy_criterion we conclude that
    ∃ g : ℝ → ℝ, converges_uniformly (fun n x => sum_f_R0 (fun k => fn k x) n) g A.
Qed.

(** ** Uniform convergence of [x/n] on a bounded interval *)

(** [fₙ(x) = x/n] converges uniformly to [0] on [[−R, R]].

    Proof idea: for [x ∈ [−R, R]] and [n ≥ 1], [|fₙ(x)| = |x|/n ≤ R/n]. The
    bound [R/n] is independent of [x] and tends to [0], giving a uniform
    threshold. *)
Lemma x_over_n_uniform (bR : ℝ) (HR : bR > 0) :
    converges_uniformly fx_over_n zero_fn (fun x => -bR ≤ x ∧ x ≤ bR).
Proof.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ (fun x => -bR ≤ x ∧ x ≤ bR), | fx_over_n n x - zero_fn x | < ε.
  Take ε > 0.
  By the Archimedean property it holds that ∃ n1 ∈ ℕ, n1 > bR / ε.
  Obtain such an n1. Choose N1 := S n1. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ (fun x => -bR ≤ x ∧ x ≤ bR), | fx_over_n n x - zero_fn x | < ε.
  Take n : ℕ. Assume that (n ≥ N1)%nat.
  Take x ∈ (fun x => -bR ≤ x ∧ x ≤ bR).
  It holds that -bR ≤ x ∧ x ≤ bR.
  It holds that | x | ≤ bR.
  It holds that (n > n1)%nat.
  It holds that INR n > INR n1.
  It holds that INR n > 0.
  (** The bound [|x| ≤ bR < n·ε] is independent of [x]. *)
  It holds that bR / ε < n.
  It holds that bR = (bR / ε) * ε.
  By Rmult_lt_compat_r it holds that (bR / ε) * ε < n * ε.
  It holds that | x | < n * ε.
  It holds that | n | = n.
  By Rabs_mult it holds that | x * / n | = | x | * | / n |.
  By Rabs_inv it holds that | / n | = / | n |.
  It holds that / n > 0.
  By Rmult_lt_compat_r it holds that | x | * / n < (n * ε) * / n.
  We need to show that | x / n - 0 | < ε.
  We conclude that (& | x / n - 0 | = | x | * / n < (n * ε) * / n = ε).
Qed.

(** ** A pointwise-only example *)

(** [fₙ(0) = 0ⁿ → 0] (pointwise value at the origin).

    For [fₙ(x) = xⁿ] on [[0,1]] and the point [x = 0], [fₙ(0) = 0ⁿ = 0] for all
    [n ≥ 1], so the sequence is eventually the constant [0]. (More generally
    [xⁿ → 0] for [0 ≤ x < 1] and [1ⁿ → 1], so the pointwise limit is the
    indicator of [{1}], which is not continuous.) *)
Lemma zero_pow_to_zero : (fun n : ℕ => (0 : ℝ) ^ n) ⟶ 0.
Proof.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | 0 ^ n - 0 | < ε.
  Take ε > 0.
  Choose N1 := 1%nat. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, | 0 ^ n - 0 | < ε.
  Take n ≥ N1.
  It holds that (0 < n)%nat.
  By pow_i it holds that 0 ^ n = 0.
  We conclude that (& | 0 ^ n - 0 | = | 0 - 0 | = 0 < ε).
Qed.

(** ** Uniform convergence of the geometric series on [[−r, r]] *)

(** Application of the _Weierstrass M-test_: for [0 ≤ r < 1], the partial sums [∑ xᵏ] converge uniformly on
    [[−r, r]].

    Proof idea: apply the Weierstrass M-test with [Mₙ = rⁿ]. For [x ∈ [−r, r]],
    [|xⁿ| = |x|ⁿ ≤ rⁿ], and [∑ rⁿ = 1/(1 - r) < ∞]. The uniform limit is
    [g(x) = 1/(1 - x)]. *)
Lemma geometric_series_uniform (r : ℝ) (Hr0 : 0 ≤ r) (Hr1 : r < 1) :
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun n x => sum_f_R0 (fun k => x ^ k) n) g (fun x => -r ≤ x ∧ x ≤ r).
Proof.
  (** The dominating series [∑ rⁿ] converges. *)
  It holds that | r | < 1.
  By geometric_series it holds that
    ∃ L : ℝ, L = 1 / (1 - r) ∧ sum_f_R0 (fun n => r ^ n) ⟶ L.
  Obtain such an L.
  It holds that sum_f_R0 (fun n => r ^ n) ⟶ L.
  We claim that ∃ L0 ∈ ℝ, (fun n => sum_f_R0 (fun k => r ^ k) n) ⟶ L0.
  {
    Choose L0 := L.
    { Indeed, L0 ∈ ℝ. }
    We conclude that (fun n => sum_f_R0 (fun k => r ^ k) n) ⟶ L0.
  }
  (** On [[-r, r]] we have [|xⁿ| = |x|ⁿ ≤ rⁿ]. *)
  We claim that ∀ n ∈ ℕ, ∀ x ∈ (fun x => -r ≤ x ∧ x ≤ r),
    | x ^ n | ≤ r ^ n.
  {
    Take n ∈ ℕ. Take x ∈ (fun x => -r ≤ x ∧ x ≤ r).
    It holds that -r ≤ x ∧ x ≤ r.
    It holds that 0 ≤ | x |.
    It holds that | x | ≤ r.
    By pow_incr it holds that | x | ^ n ≤ r ^ n.
    By RPow_abs it holds that | x | ^ n = | x ^ n |.
    We conclude that | x ^ n | ≤ r ^ n.
  }
  By (weierstrass_M_test (fun k x => x ^ k) (fun k => r ^ k)) we conclude that
    ∃ g : ℝ → ℝ,
      converges_uniformly
        (fun n x => sum_f_R0 (fun k => x ^ k) n) g (fun x => -r ≤ x ∧ x ≤ r).
Qed.

(** ** The supremum characterization of uniform convergence *)

(** _Mₙ-test_: [(fₙ) ⇉ g] uniformly on [A] iff there is a sequence [Mₙ → 0]
    that eventually dominates the pointwise errors: [|fₙ(x) - g(x)| ≤ Mₙ] for all
    [x ∈ A] and all [n ≥ N₀]. (One may take [Mₙ = sup_{x ∈ A} |fₙ(x) - g(x)|];
    the bound can only hold eventually, since finitely many [fₙ - g] may be
    unbounded on [A].)

    Proof idea: (⇒) take [Mₙ = sup Eₙ] with
    [Eₙ = {0} ∪ {min(|fₙ(x) - g(x)|, 1) : x ∈ A}], which exists since [Eₙ] is
    nonempty and bounded by [1]. For [n ≥ N(1)] the truncation has no effect,
    and for [n ≥ N(ε/2)] every element of [Eₙ] is at most [ε/2], so
    [0 ≤ Mₙ ≤ ε/2]. (⇐) [Mₙ → 0] gives a single [N] making all errors [< ε]
    simultaneously. *)
Lemma uniform_convergence_sup_characterization
    (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) :
    converges_uniformly fn g A ⇔
    (∃ M : ℕ → ℝ, ∃ N_0 ∈ ℕ,
      (∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → Rabs (fn n x - g x) ≤ M n) ∧ M ⟶ 0).
Proof.
  We show both directions.
  - We need to show that converges_uniformly fn g A ⇨
      (∃ M : ℕ → ℝ, ∃ N_0 ∈ ℕ,
        (∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → | fn n x - g x | ≤ M n)
        ∧ M ⟶ 0).
    Assume that converges_uniformly fn g A as (Hunif).
    (** [Mₙ] is the supremum of the truncated errors [min(|fₙ(x) - g(x)|, 1)]. *)
    Define E := fun (n : ℕ) (y : ℝ) =>
      y = 0 ∨ ∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1.
    We claim that ∀ n : ℕ, bound (E n) as (Hbd).
    {
      Take n : ℕ.
      We need to show that ∃ m : ℝ, is_upper_bound (E n) m.
      Choose m := 1.
      We need to show that ∀ y : ℝ, E n y → y ≤ m.
      Take y : ℝ.
      Assume that y = 0 ∨ ∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1 as (Hy).
      Because (Hy) either y = 0 or (∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1)
        holds.
      + Case y = 0.
        We conclude that y ≤ m.
      + Case (∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1).
        Obtain such an x.
        By Rmin_r it holds that Rmin (| fn n x - g x |) 1 ≤ 1.
        We conclude that y ≤ m.
    }
    We claim that ∀ n : ℕ, ∃ y : ℝ, E n y as (Hne).
    {
      Take n : ℕ.
      Choose y := 0.
      We need to show that y = 0 ∨ ∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1.
      It holds that y = 0.
      We conclude that y = 0 ∨ ∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1.
    }
    Define M := fun n : ℕ =>
      @proj1_sig ℝ (is_lub (E n)) (completeness (E n) (Hbd n) (Hne n)).
    We claim that ∀ n : ℕ, is_upper_bound (E n) (M n)
      ∧ (∀ b : ℝ, is_upper_bound (E n) b → M n ≤ b) as (Hlub).
    {
      Take n : ℕ.
      We need to show that is_lub (E n) (M n).
      By (@proj2_sig ℝ (is_lub (E n)) (completeness (E n) (Hbd n) (Hne n)))
        we conclude that is_lub (E n) (M n).
    }
    It holds that (1 : ℝ) > 0.
    By Hunif it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ x ∈ A, | fn n x - g x | < 1 as (H1).
    Obtain such an N1.
    Choose M0 := M.
    Choose N_0 := N1.
    { Indeed, N_0 ∈ ℕ. }
    We need to show that
      (∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → | fn n x - g x | ≤ M0 n)
      ∧ M0 ⟶ 0.
    We show both statements.
    + We need to show that
        ∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → | fn n x - g x | ≤ M0 n.
      Take n : ℕ. Assume that (n ≥ N_0)%nat.
      Take x ∈ ℝ. Assume that A x.
      It holds that x ∈ A.
      By H1 it holds that | fn n x - g x | < 1.
      (** For [n ≥ N_0] the truncation has no effect. *)
      By Rmin_left it holds that Rmin (| fn n x - g x |) 1 = | fn n x - g x |.
      We claim that E n (| fn n x - g x |).
      {
        We need to show that | fn n x - g x | = 0 ∨
          ∃ y : ℝ, A y ∧ | fn n x - g x | = Rmin (| fn n y - g y |) 1.
        It holds that ∃ y : ℝ, A y ∧ | fn n x - g x | = Rmin (| fn n y - g y |) 1.
        We conclude that | fn n x - g x | = 0 ∨
          ∃ y : ℝ, A y ∧ | fn n x - g x | = Rmin (| fn n y - g y |) 1.
      }
      By (Hlub n) it holds that is_upper_bound (E n) (M n)
        ∧ (∀ b : ℝ, is_upper_bound (E n) b → M n ≤ b).
      It holds that is_upper_bound (E n) (M n) as (Hub).
      By Hub we conclude that | fn n x - g x | ≤ M0 n.
    + We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | M0 n - 0 | < ε.
      Take ε > 0.
      It holds that ε / 2 > 0.
      By Hunif it holds that ∃ N2 ∈ ℕ, ∀ n : ℕ, (n ≥ N2)%nat →
        ∀ x ∈ A, | fn n x - g x | < ε / 2 as (H2).
      Obtain such an N2.
      Choose N3 := N2. { Indeed, N3 ∈ ℕ. }
      We need to show that ∀ n ≥ N3, | M0 n - 0 | < ε.
      Take n ≥ N3.
      By (Hlub n) it holds that is_upper_bound (E n) (M n)
        ∧ (∀ b : ℝ, is_upper_bound (E n) b → M n ≤ b).
      (** [ε/2] is an upper bound of [Eₙ], so [Mₙ ≤ ε/2]. *)
      We claim that is_upper_bound (E n) (ε / 2).
      {
        We need to show that ∀ y : ℝ, E n y → y ≤ ε / 2.
        Take y : ℝ.
        Assume that y = 0 ∨ ∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1 as (Hy).
        Because (Hy) either y = 0
          or (∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1) holds.
        * Case y = 0.
          We conclude that y ≤ ε / 2.
        * Case (∃ x : ℝ, A x ∧ y = Rmin (| fn n x - g x |) 1).
          Obtain such an x.
          It holds that x ∈ A.
          It holds that (n ≥ N2)%nat.
          By H2 it holds that | fn n x - g x | < ε / 2.
          By Rmin_l it holds that Rmin (| fn n x - g x |) 1 ≤ | fn n x - g x |.
          We conclude that y ≤ ε / 2.
      }
      It holds that ∀ b : ℝ, is_upper_bound (E n) b → M n ≤ b as (Hleast).
      By Hleast it holds that M n ≤ ε / 2.
      (** [0 ∈ Eₙ], so [Mₙ ≥ 0]. *)
      We claim that E n 0.
      {
        We need to show that 0 = 0 ∨
          ∃ x : ℝ, A x ∧ 0 = Rmin (| fn n x - g x |) 1.
        It holds that (0 : ℝ) = 0.
        We conclude that 0 = 0 ∨
          ∃ x : ℝ, A x ∧ 0 = Rmin (| fn n x - g x |) 1.
      }
      It holds that is_upper_bound (E n) (M n) as (Hub).
      By Hub it holds that 0 ≤ M n.
      By Rabs_pos_eq it holds that | M n | = M n.
      It holds that M n - 0 = M n.
      It holds that | M n - 0 | < ε.
      We conclude that | M0 n - 0 | < ε.
  - We need to show that
      (∃ M : ℕ → ℝ, ∃ N_0 ∈ ℕ,
        (∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → | fn n x - g x | ≤ M n)
        ∧ M ⟶ 0) ⇨ converges_uniformly fn g A.
    Assume that ∃ M : ℕ → ℝ, ∃ N_0 ∈ ℕ,
      (∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → | fn n x - g x | ≤ M n)
      ∧ M ⟶ 0.
    Obtain such an M.
    It holds that ∃ N_0 ∈ ℕ,
      (∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → | fn n x - g x | ≤ M n)
      ∧ M ⟶ 0.
    Obtain such an N_0.
    It holds that ∀ n : ℕ, (n ≥ N_0)%nat → ∀ x ∈ ℝ, A x → | fn n x - g x | ≤ M n
      as (Hbound).
    It holds that M ⟶ 0 as (HM0).
    We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ x ∈ A, | fn n x - g x | < ε.
    Take ε > 0.
    By HM0 it holds that ∃ N2 ∈ ℕ, ∀ n ≥ N2, | M n - 0 | < ε as (HN2).
    Obtain such an N2.
    Choose N1 := Nat.max N_0 N2. { Indeed, N1 ∈ ℕ. }
    We need to show that ∀ n : ℕ, (n ≥ N1)%nat → ∀ x ∈ A, | fn n x - g x | < ε.
    Take n : ℕ. Assume that (n ≥ N1)%nat.
    Take x ∈ A.
    It holds that (n ≥ N_0)%nat. It holds that (n ≥ N2)%nat.
    It holds that A x.
    By Hbound it holds that | fn n x - g x | ≤ M n.
    By HN2 it holds that | M n - 0 | < ε.
    It holds that M n < ε.
    We conclude that | fn n x - g x | < ε.
Qed.

(** ** The example [fₙ(x) = xⁿ] *)

(** [fₙ(x) = xⁿ] converges pointwise to [0] on [[0, 1)].

    Proof idea: for fixed [0 ≤ x < 1], [xⁿ → 0] (geometric decay); the rate
    depends on how close [x] is to [1]. *)
Lemma x_pow_n_pointwise :
    converges_pointwise (fun n x => x ^ n) (fun _ => 0)
      (fun x => 0 ≤ x ∧ x < 1).
Proof.
  We need to show that ∀ x ∈ (fun x => 0 ≤ x ∧ x < 1), (fun n => x ^ n) ⟶ 0.
  Take x ∈ (fun x => 0 ≤ x ∧ x < 1).
  It holds that 0 ≤ x ∧ x < 1.
  It holds that | x | < 1.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | x ^ n - 0 | < ε.
  Take ε > 0.
  By pow_lt_1_zero it holds that
    ∃ N1 : ℕ, ∀ n : ℕ, (n ≥ N1)%nat → | x ^ n | < ε as (HN).
  Obtain such an N1.
  Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
  We need to show that ∀ n ≥ N2, | x ^ n - 0 | < ε.
  Take n ≥ N2.
  By HN it holds that | x ^ n | < ε.
  We conclude that (& | x ^ n - 0 | = | x ^ n | < ε).
Qed.

(** The convergence [xⁿ → 0] on [[0, 1)] is *not* uniform.

    Proof idea: for any [n], points [x] near [1] have [xⁿ] near [1], so
    [sup_{x ∈ [0,1)} |xⁿ - 0| = 1] does not tend to [0]; equivalently the
    [Mₙ]-test fails. *)
Lemma x_pow_n_not_uniform :
    ¬ (∃ g : ℝ → ℝ,
        converges_uniformly (fun n x => x ^ n) g (fun x => 0 ≤ x ∧ x < 1)).
Proof.
  Assume that ∃ g : ℝ → ℝ,
    converges_uniformly (fun n x => x ^ n) g (fun x => 0 ≤ x ∧ x < 1).
  Obtain such a g.
  It holds that
    converges_uniformly (fun n x => x ^ n) g (fun x => 0 ≤ x ∧ x < 1) as (Hunif).
  It holds that / 2 > 0.
  By Hunif it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ (fun x => 0 ≤ x ∧ x < 1), | x ^ n - g x | < / 2 as (HN).
  Obtain such an N1.
  (** We test at [x = 1 - t] with [t = 1/(2(N + 1))]. *)
  By pos_INR it holds that 0 ≤ INR N1.
  It holds that INR N1 + 1 ≠ 0 as (Hne).
  Define t := / 2 * / (INR N1 + 1).
  It holds that / (INR N1 + 1) > 0.
  It holds that t > 0.
  Define Hinv := Rinv_r (INR N1 + 1) Hne.
  It holds that (INR N1 + 1) * t = / 2 * ((INR N1 + 1) * / (INR N1 + 1)).
  It holds that (& (INR N1 + 1) * t = / 2 * ((INR N1 + 1) * / (INR N1 + 1))
    = / 2 * 1 = / 2).
  By Rmult_le_pos it holds that 0 ≤ INR N1 * t.
  It holds that INR N1 * t = / 2 - t.
  It holds that t ≤ / 2.
  Define x := 1 - t.
  It holds that 0 ≤ x ∧ x < 1.
  (** By Bernoulli, [x^N ≥ 1 - N t = 1/2 + t > 1/2]. *)
  It holds that 0 ≤ t ∧ t ≤ 1.
  By bernoulli_inequality it holds that (1 - t) ^ N1 ≥ 1 - INR N1 * t.
  It holds that (1 - t) ^ N1 > / 2.
  It holds that x ^ N1 = (1 - t) ^ N1.
  It holds that x ^ N1 > / 2.
  (** On the other hand [g(x) = 0], since [xⁿ → 0] pointwise. *)
  By x_pow_n_pointwise it holds that
    ∀ y ∈ (fun x => 0 ≤ x ∧ x < 1), (fun n => y ^ n) ⟶ 0 as (Hpt0).
  By (uniform_implies_pointwise _ _ _ Hunif) it holds that
    converges_pointwise (fun n x => x ^ n) g (fun x => 0 ≤ x ∧ x < 1).
  It holds that
    ∀ y ∈ (fun x => 0 ≤ x ∧ x < 1), (fun n => y ^ n) ⟶ g y as (Hptg).
  It holds that x ∈ (fun x => 0 ≤ x ∧ x < 1).
  By Hpt0 it holds that (fun n => x ^ n) ⟶ 0 as (Hx0).
  By Hptg it holds that (fun n => x ^ n) ⟶ g x as (Hxg).
  By (limit_unique (fun n => x ^ n) (g x) 0 Hxg Hx0) it holds that g x = 0.
  It holds that (N1 ≥ N1)%nat.
  By HN it holds that | x ^ N1 - g x | < / 2.
  It holds that x ^ N1 < / 2.
  Contradiction.
Qed.

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
  We need to show that ∀ x ∈ (fun x => 0 ≤ x ∧ x ≤ 1),
    (fun n => Rmax 0 (INR n - (INR n) ^ 2 * | x - / INR n |)) ⟶ 0.
  Take x ∈ (fun x => 0 ≤ x ∧ x ≤ 1).
  It holds that 0 ≤ x ∧ x ≤ 1.
  (** It suffices that eventually [n ≤ n² |x - 1/n|], so that [Tₙ(x) = 0]. *)
  We claim that ∀ n : ℕ, (n > 0)%nat → / INR n ≤ | x - / INR n | →
    INR n ≤ (INR n) ^ 2 * | x - / INR n | as (Hkey).
  {
    Take n : ℕ.
    Assume that (n > 0)%nat.
    Assume that / INR n ≤ | x - / INR n |.
    It holds that INR n > 0.
    It holds that INR n ≠ 0 as (Hn0).
    Define Hinv := Rinv_r (INR n) Hn0.
    It holds that 0 ≤ (INR n) ^ 2.
    By Rmult_le_compat_l it holds that
      (INR n) ^ 2 * / INR n ≤ (INR n) ^ 2 * | x - / INR n |.
    It holds that (INR n) ^ 2 * / INR n = INR n * (INR n * / INR n).
    It holds that (& (INR n) ^ 2 * / INR n = INR n * (INR n * / INR n)
      = INR n * 1 = INR n).
    We conclude that INR n ≤ (INR n) ^ 2 * | x - / INR n |.
  }
  We claim that ∃ N1 ∈ ℕ, ∀ n ≥ N1,
    INR n ≤ (INR n) ^ 2 * | x - / INR n | as (Hev).
  {
    Either x = 0 or 0 < x.
    - Case x = 0.
      Choose N1 := 1%nat. { Indeed, N1 ∈ ℕ. }
      We need to show that ∀ n ≥ N1, INR n ≤ (INR n) ^ 2 * | x - / INR n |.
      Take n ≥ N1.
      It holds that (n > 0)%nat.
      It holds that INR n > 0.
      It holds that / INR n > 0.
      It holds that x - / INR n = - / INR n.
      By Rabs_Ropp it holds that | - / INR n | = | / INR n |.
      By Rabs_pos_eq it holds that | / INR n | = / INR n.
      It holds that / INR n ≤ | x - / INR n |.
      By Hkey we conclude that INR n ≤ (INR n) ^ 2 * | x - / INR n |.
    - Case 0 < x.
      By the Archimedean property it holds that ∃ n1 ∈ ℕ, n1 > 2 / x.
      Obtain such an n1.
      Choose N1 := S n1. { Indeed, N1 ∈ ℕ. }
      We need to show that ∀ n ≥ N1, INR n ≤ (INR n) ^ 2 * | x - / INR n |.
      Take n ≥ N1.
      It holds that (n > n1)%nat.
      It holds that (n > 0)%nat.
      It holds that INR n > INR n1.
      It holds that INR n > 0.
      It holds that INR n ≠ 0 as (Hn0).
      Define Hinv := Rinv_r (INR n) Hn0.
      (** From [n > 2/x] we get [x > 2/n], hence [x - 1/n > 1/n]. *)
      It holds that 2 / x < INR n.
      It holds that 2 = (2 / x) * x.
      By Rmult_lt_compat_r it holds that (2 / x) * x < INR n * x.
      It holds that 2 < INR n * x.
      It holds that / INR n > 0.
      By Rmult_lt_compat_r it holds that 2 * / INR n < (INR n * x) * / INR n.
      It holds that (INR n * x) * / INR n = x * (INR n * / INR n).
      It holds that (& (INR n * x) * / INR n = x * (INR n * / INR n) = x * 1 = x).
      It holds that x - / INR n ≥ / INR n.
      It holds that x - / INR n ≥ 0.
      By Rabs_pos_eq it holds that | x - / INR n | = x - / INR n.
      It holds that / INR n ≤ | x - / INR n |.
      By Hkey we conclude that INR n ≤ (INR n) ^ 2 * | x - / INR n |.
  }
  Obtain such an N1.
  We need to show that ∀ ε > 0, ∃ N2 ∈ ℕ, ∀ n ≥ N2,
    | Rmax 0 (INR n - (INR n) ^ 2 * | x - / INR n |) - 0 | < ε.
  Take ε > 0.
  Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
  We need to show that ∀ n ≥ N2,
    | Rmax 0 (INR n - (INR n) ^ 2 * | x - / INR n |) - 0 | < ε.
  Take n ≥ N2.
  By Hev it holds that INR n ≤ (INR n) ^ 2 * | x - / INR n |.
  It holds that INR n - (INR n) ^ 2 * | x - / INR n | ≤ 0.
  By Rmax_left it holds that Rmax 0 (INR n - (INR n) ^ 2 * | x - / INR n |) = 0.
  We conclude that (& | Rmax 0 (INR n - (INR n) ^ 2 * | x - / INR n |) - 0 |
    = | 0 - 0 | = 0 < ε).
Qed.

(** ** Uniform convergence of [√(x² + 1/n)] *)

(** Exercise: [fₙ(x) = √(x² + 1/n)] converges uniformly to [|x|] on all of [ℝ].

    Proof idea: [0 ≤ √(x² + 1/n) - |x| = (1/n)/(√(x² + 1/n) + |x|) ≤ √(1/n)],
    a bound independent of [x] tending to [0]. *)
Lemma sqrt_x_sq_plus_1_over_n_uniform :
    converges_uniformly (fun n x => sqrt (x ^ 2 + / INR n)) Rabs
      (fun _ => True).
Proof.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ (fun _ : ℝ => True), | sqrt (x ^ 2 + / INR n) - Rabs x | < ε.
  Take ε > 0.
  It holds that ε ^ 2 > 0.
  By the Archimedean property it holds that ∃ n1 ∈ ℕ, n1 > / (ε ^ 2).
  Obtain such an n1.
  Choose N1 := S n1. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ (fun _ : ℝ => True), | sqrt (x ^ 2 + / INR n) - Rabs x | < ε.
  Take n : ℕ. Assume that (n ≥ N1)%nat.
  Take x ∈ (fun _ : ℝ => True).
  It holds that (n > n1)%nat.
  It holds that INR n > INR n1.
  It holds that / (ε ^ 2) < INR n.
  It holds that / (ε ^ 2) > 0.
  It holds that 0 < / (ε ^ 2) * INR n.
  (** The perturbation [1/n] satisfies [0 < 1/n < ε²]. *)
  By Rinv_lt_contravar it holds that / INR n < / / (ε ^ 2).
  It holds that / / (ε ^ 2) = ε ^ 2.
  It holds that / INR n < ε ^ 2.
  It holds that INR n > 0.
  It holds that / INR n > 0.
  (** [√(x²) = |x|]. *)
  By pow2_abs it holds that | x | ^ 2 = x ^ 2.
  By sqrt_pow2 it holds that sqrt (| x | ^ 2) = | x |.
  It holds that sqrt (x ^ 2) = | x |.
  (** Upper bound [√(x² + 1/n) ≤ √(x²) + √(1/n)]. *)
  By sqrt_pos it holds that 0 ≤ sqrt (x ^ 2).
  By sqrt_pos it holds that 0 ≤ sqrt (/ INR n).
  By pow2_sqrt it holds that sqrt (x ^ 2) ^ 2 = x ^ 2.
  By pow2_sqrt it holds that sqrt (/ INR n) ^ 2 = / INR n.
  It holds that (sqrt (x ^ 2) + sqrt (/ INR n)) ^ 2
    = sqrt (x ^ 2) ^ 2 + sqrt (/ INR n) ^ 2 + 2 * sqrt (x ^ 2) * sqrt (/ INR n).
  By Rmult_le_pos it holds that 0 ≤ sqrt (x ^ 2) * sqrt (/ INR n).
  It holds that x ^ 2 + / INR n ≤ (sqrt (x ^ 2) + sqrt (/ INR n)) ^ 2.
  By sqrt_le_1_alt it holds that
    sqrt (x ^ 2 + / INR n) ≤ sqrt ((sqrt (x ^ 2) + sqrt (/ INR n)) ^ 2).
  By sqrt_pow2 it holds that
    sqrt ((sqrt (x ^ 2) + sqrt (/ INR n)) ^ 2) = sqrt (x ^ 2) + sqrt (/ INR n).
  (** Lower bound [√(x²) ≤ √(x² + 1/n)]. *)
  By sqrt_le_1_alt it holds that sqrt (x ^ 2) ≤ sqrt (x ^ 2 + / INR n).
  (** Finally [√(1/n) < √(ε²) = ε]. *)
  By sqrt_lt_1_alt it holds that sqrt (/ INR n) < sqrt (ε ^ 2).
  By sqrt_pow2 it holds that sqrt (ε ^ 2) = ε.
  It holds that sqrt (x ^ 2 + / INR n) - | x | < ε.
  It holds that 0 ≤ sqrt (x ^ 2 + / INR n) - | x |.
  By Rabs_pos_eq it holds that
    | sqrt (x ^ 2 + / INR n) - | x | | = sqrt (x ^ 2 + / INR n) - | x |.
  We conclude that | sqrt (x ^ 2 + / INR n) - Rabs x | < ε.
Qed.

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
  (** Each [fₙ] has derivative [dfnₙ] on [[a, b]]. *)
  We claim that ∀ n : ℕ, ∀ z : ℝ, a ≤ z → z ≤ b →
    derivable_pt_lim (fn n) z (dfn n z) as (Hlim).
  {
    Take n : ℕ. Take z : ℝ.
    Assume that a ≤ z and z ≤ b.
    By Hderiv it holds that
      ∃ Hd : derivable_pt (fn n) z, derive_pt (fn n) z Hd = dfn n z as (Hn).
    Obtain such a Hd.
    By derive_pt_eq_1 we conclude that derivable_pt_lim (fn n) z (dfn n z).
  }
  Take ε > 0.
  By Hdcauchy it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x : ℝ,
    a ≤ x → x ≤ b → | dfn n x - dfn m x | < ε as (HN).
  Obtain such an N1.
  Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
  We need to show that ∀ n ≥ N2, ∀ m ≥ N2, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
    a ≤ x → x ≤ b → a ≤ y → y ≤ b →
    | (fn n x - fn m x) - (fn n y - fn m y) | ≤ ε * | x - y |.
  Take n ≥ N2. Take m ≥ N2.
  (** The difference [h = fₙ - fₘ] has derivative [dfnₙ - dfnₘ]. *)
  We claim that ∀ z : ℝ, a ≤ z → z ≤ b →
    derivable_pt_lim (fun t => fn n t - fn m t) z (dfn n z - dfn m z) as (Hdiff).
  {
    Take z : ℝ.
    Assume that a ≤ z and z ≤ b.
    By Hlim it holds that derivable_pt_lim (fn n) z (dfn n z) as (Hn).
    By Hlim it holds that derivable_pt_lim (fn m) z (dfn m z) as (Hm).
    By (derivable_pt_lim_minus (fn n) (fn m) z (dfn n z) (dfn m z) Hn Hm)
      we conclude that
      derivable_pt_lim (fun t => fn n t - fn m t) z (dfn n z - dfn m z).
  }
  (** Mean value theorem on [[u, v]] for [u < v]. *)
  We claim that ∀ u : ℝ, ∀ v : ℝ, a ≤ u → u < v → v ≤ b →
    | (fn n u - fn m u) - (fn n v - fn m v) | ≤ ε * | u - v | as (Hord).
  {
    Take u : ℝ. Take v : ℝ.
    Assume that a ≤ u, u < v as (Huv) and v ≤ b.
    We claim that ∀ c : ℝ, u <= c <= v →
      derivable_pt_lim (fun t => fn n t - fn m t) c (dfn n c - dfn m c) as (Hdc).
    {
      Take c : ℝ. Assume that u <= c <= v.
      It holds that a ≤ c. It holds that c ≤ b.
      By Hdiff we conclude that
        derivable_pt_lim (fun t => fn n t - fn m t) c (dfn n c - dfn m c).
    }
    By (MVT_cor2 (fun t => fn n t - fn m t) (fun t => dfn n t - dfn m t) u v Huv Hdc)
      it holds that ∃ c : ℝ,
        (fn n v - fn m v) - (fn n u - fn m u) = (dfn n c - dfn m c) * (v - u)
        ∧ u < c < v.
    Obtain such a c.
    It holds that (fn n v - fn m v) - (fn n u - fn m u)
      = (dfn n c - dfn m c) * (v - u).
    It holds that a ≤ c. It holds that c ≤ b.
    By HN it holds that | dfn n c - dfn m c | < ε.
    It holds that | v - u | = | u - v |.
    It holds that 0 ≤ | v - u |.
    By Rmult_le_compat_r it holds that
      | dfn n c - dfn m c | * | v - u | ≤ ε * | v - u |.
    By Rabs_mult it holds that
      | (dfn n c - dfn m c) * (v - u) | = | dfn n c - dfn m c | * | v - u |.
    It holds that | (fn n u - fn m u) - (fn n v - fn m v) |
      = | (fn n v - fn m v) - (fn n u - fn m u) |.
    We conclude that | (fn n u - fn m u) - (fn n v - fn m v) | ≤ ε * | u - v |.
  }
  Take x ∈ ℝ. Take y ∈ ℝ.
  Assume that a ≤ x, x ≤ b, a ≤ y and y ≤ b.
  By Rtotal_order it holds that x < y ∨ x = y ∨ y < x as (Hcases).
  Because (Hcases) either x < y or (x = y ∨ y < x) holds.
  - Case x < y.
    By Hord we conclude that
      | (fn n x - fn m x) - (fn n y - fn m y) | ≤ ε * | x - y |.
  - Case (x = y ∨ y < x).
    It holds that x = y ∨ y < x as (Hcases2).
    Because (Hcases2) either x = y or y < x holds.
    + Case x = y.
      It holds that (fn n x - fn m x) - (fn n y - fn m y) = 0.
      It holds that | (fn n x - fn m x) - (fn n y - fn m y) | = 0.
      By Rabs_pos it holds that 0 ≤ | x - y |.
      By Rmult_le_pos it holds that 0 ≤ ε * | x - y |.
      We conclude that
        | (fn n x - fn m x) - (fn n y - fn m y) | ≤ ε * | x - y |.
    + Case y < x.
      By Hord it holds that
        | (fn n y - fn m y) - (fn n x - fn m x) | ≤ ε * | y - x |.
      It holds that | (fn n y - fn m y) - (fn n x - fn m x) |
        = | (fn n x - fn m x) - (fn n y - fn m y) |.
      It holds that | y - x | = | x - y |.
      We conclude that
        | (fn n x - fn m x) - (fn n y - fn m y) | ≤ ε * | x - y |.
Qed.

(** _Differentiability theorem_ (Abbott 6.3.3): if each [fₙ] is differentiable
    on [[a, b]] with derivative [dfnₙ], the derivatives converge uniformly to
    [h], and [(fₙ(x₀))] converges at one point [x₀ ∈ [a, b]], then [(fₙ)]
    converges uniformly on [[a, b]] to a limit [g] with [g' = h] on [(a, b)].

    Proof idea: the transfer lemma gives
    [|fₙ(x) - fₘ(x)| ≤ ε₁ |x - x₀| + |fₙ(x₀) - fₘ(x₀)|], so [(fₙ)] is uniformly
    Cauchy, hence uniformly convergent to some [g]
    ([uniform_cauchy_criterion]). The derivative of [g] on the open interval
    [(a, b)] is then obtained from Stdlib's [CVU_derivable], applied on the
    ball with centre [(a + b)/2] and radius [(b - a)/2]. *)
Theorem uniform_differentiability_theorem
    (fn : ℕ → ℝ → ℝ) (dfn : ℕ → ℝ → ℝ) (h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hderiv : ∀ n ∈ ℕ, ∀ x ∈ ℝ, a ≤ x → x ≤ b →
        ∃ Hd : derivable_pt (fn n) x, derive_pt (fn n) x Hd = dfn n x)
    (Hpt : ∃ x0 : ℝ, a ≤ x0 ∧ x0 ≤ b ∧ ∃ L : ℝ, (fun n => fn n x0) ⟶ L)
    (Hdunif : converges_uniformly dfn h (fun x => a ≤ x ∧ x ≤ b)) :
    ∃ g : ℝ → ℝ, converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b) ∧
      (∀ x : ℝ, a < x → x < b →
        ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x).
Proof.
  (** Step 1: the derivatives are uniformly Cauchy on [[a, b]]. *)
  By unif_conv_is_cauchy it holds that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, ∀ m : ℕ,
    (n ≥ N1)%nat → (m ≥ N1)%nat →
    ∀ x ∈ (fun x => a ≤ x ∧ x ≤ b), | dfn n x - dfn m x | < ε as (Hdc0).
  We claim that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x : ℝ,
    a ≤ x → x ≤ b → | dfn n x - dfn m x | < ε as (Hdcauchy).
  {
    Take ε > 0.
    By Hdc0 it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, ∀ m : ℕ,
      (n ≥ N1)%nat → (m ≥ N1)%nat →
      ∀ x ∈ (fun x => a ≤ x ∧ x ≤ b), | dfn n x - dfn m x | < ε as (HN).
    Obtain such an N1.
    Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
    We need to show that ∀ n ≥ N2, ∀ m ≥ N2, ∀ x : ℝ,
      a ≤ x → x ≤ b → | dfn n x - dfn m x | < ε.
    Take n ≥ N2. Take m ≥ N2. Take x : ℝ.
    Assume that a ≤ x and x ≤ b.
    It holds that x ∈ (fun x => a ≤ x ∧ x ≤ b).
    By HN we conclude that | dfn n x - dfn m x | < ε.
  }
  (** Step 2: the transfer lemma. *)
  By (differentiability_transfer_lemma fn dfn a b Hab Hderiv Hdcauchy)
    it holds that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      a ≤ x → x ≤ b → a ≤ y → y ≤ b →
      | (fn n x - fn m x) - (fn n y - fn m y) | ≤ ε * | x - y | as (Hlip).
  (** Step 3: [(fₙ)] is uniformly Cauchy on [[a, b]]. *)
  It holds that ∃ x0 : ℝ, a ≤ x0 ∧ x0 ≤ b ∧ ∃ L : ℝ, (fun n => fn n x0) ⟶ L.
  Obtain such an x0.
  It holds that a ≤ x0 ∧ x0 ≤ b ∧ ∃ L : ℝ, (fun n => fn n x0) ⟶ L.
  It holds that ∃ L : ℝ, (fun n => fn n x0) ⟶ L.
  Obtain such an L.
  By convergent_is_cauchy it holds that is_cauchy (fun n => fn n x0) as (Hc0).
  We claim that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
    ∀ x ∈ (fun x => a ≤ x ∧ x ≤ b), | fn n x - fn m x | < ε.
  {
    Take ε > 0.
    It holds that ε / 2 > 0.
    It holds that b - a + 1 > 0.
    It holds that b - a + 1 ≠ 0 as (Hne).
    Define ε1 := ε / 2 * / (b - a + 1).
    It holds that / (b - a + 1) > 0.
    It holds that ε1 > 0.
    Define Hinv := Rinv_r (b - a + 1) Hne.
    It holds that ε1 * (b - a + 1) = ε / 2 * ((b - a + 1) * / (b - a + 1)).
    It holds that (& ε1 * (b - a + 1) = ε / 2 * ((b - a + 1) * / (b - a + 1))
      = ε / 2 * 1 = ε / 2).
    By Hlip it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      a ≤ x → x ≤ b → a ≤ y → y ≤ b →
      | (fn n x - fn m x) - (fn n y - fn m y) | ≤ ε1 * | x - y | as (HN1).
    Obtain such an N1.
    By Hc0 it holds that ∃ N2 ∈ ℕ, ∀ n ≥ N2, ∀ m ≥ N2,
      | fn n x0 - fn m x0 | < ε / 2 as (HN2).
    Obtain such an N2.
    Choose N3 := Nat.max N1 N2. { Indeed, N3 ∈ ℕ. }
    We need to show that ∀ n ≥ N3, ∀ m ≥ N3,
      ∀ x ∈ (fun x => a ≤ x ∧ x ≤ b), | fn n x - fn m x | < ε.
    Take n ≥ N3. Take m ≥ N3. Take x ∈ (fun x => a ≤ x ∧ x ≤ b).
    It holds that a ≤ x ∧ x ≤ b.
    It holds that (n ≥ N1)%nat. It holds that (m ≥ N1)%nat.
    It holds that (n ≥ N2)%nat. It holds that (m ≥ N2)%nat.
    By HN1 it holds that
      | (fn n x - fn m x) - (fn n x0 - fn m x0) | ≤ ε1 * | x - x0 |.
    By HN2 it holds that | fn n x0 - fn m x0 | < ε / 2.
    It holds that | x - x0 | ≤ b - a.
    By Rmult_le_compat_l it holds that ε1 * | x - x0 | ≤ ε1 * (b - a).
    It holds that ε1 * (b - a) < ε1 * (b - a + 1).
    By Rabs_triang it holds that
      | ((fn n x - fn m x) - (fn n x0 - fn m x0)) + (fn n x0 - fn m x0) |
        ≤ | (fn n x - fn m x) - (fn n x0 - fn m x0) | + | fn n x0 - fn m x0 |.
    It holds that fn n x - fn m x
      = ((fn n x - fn m x) - (fn n x0 - fn m x0)) + (fn n x0 - fn m x0).
    We conclude that | fn n x - fn m x | < ε.
  }
  By uniform_cauchy_criterion it holds that
    ∃ g : ℝ → ℝ, converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b).
  Obtain such a g.
  It holds that converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b) as (Hgu).
  Choose g0 := g.
  We need to show that converges_uniformly fn g0 (fun x => a ≤ x ∧ x ≤ b) ∧
    (∀ x : ℝ, a < x → x < b →
      ∃ Hd : derivable_pt g0 x, derive_pt g0 x Hd = h x).
  We show both statements.
  - We conclude that converges_uniformly fn g0 (fun x => a ≤ x ∧ x ≤ b).
  - We need to show that ∀ x : ℝ, a < x → x < b →
      ∃ Hd : derivable_pt g0 x, derive_pt g0 x Hd = h x.
    Take x : ℝ.
    Assume that a < x and x < b.
    (** Step 4: [g' = h] on [(a, b)], via [CVU_derivable] on the open ball
        [(a, b)] with centre [(a + b)/2] and radius [(b - a)/2]. *)
    Define c := (a + b) / 2.
    It holds that 0 < (b - a) / 2 as (Hr).
    Define r := mkposreal ((b - a) / 2) Hr.
    We claim that ∀ y : ℝ, Boule c r y → a ≤ y ∧ y ≤ b as (Hball).
    {
      Take y : ℝ.
      Assume that Boule c r y as (Hy).
      It holds that | y - c | < (b - a) / 2.
      By Rabs_def2 it holds that y - c < (b - a) / 2 ∧ - ((b - a) / 2) < y - c.
      We conclude that a ≤ y ∧ y ≤ b.
    }
    We claim that CVU dfn h c r as (Hcvu).
    {
      We need to show that ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, ∀ y : ℝ,
        (N ≤ n)%nat → Boule c r y → | h y - dfn n y | < eps.
      Take eps : ℝ.
      Assume that 0 < eps.
      By Hdunif it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
        ∀ y ∈ (fun x => a ≤ x ∧ x ≤ b), | dfn n y - h y | < eps as (HN).
      Obtain such an N1.
      Choose Nb := N1.
      We need to show that ∀ n : ℕ, ∀ y : ℝ,
        (Nb ≤ n)%nat → Boule c r y → | h y - dfn n y | < eps.
      Take n : ℕ. Take y : ℝ.
      Assume that (Nb ≤ n)%nat and Boule c r y.
      By Hball it holds that a ≤ y ∧ y ≤ b.
      It holds that y ∈ (fun x => a ≤ x ∧ x ≤ b).
      It holds that (n ≥ N1)%nat.
      By HN it holds that | dfn n y - h y | < eps.
      By Rabs_minus_sym it holds that | h y - dfn n y | = | dfn n y - h y |.
      We conclude that | h y - dfn n y | < eps.
    }
    By (uniform_implies_pointwise _ _ _ Hgu) it holds that
      converges_pointwise fn g (fun x => a ≤ x ∧ x ≤ b) as (Hgpt).
    We claim that ∀ y : ℝ, Boule c r y → Un_cv (fun n => fn n y) (g y) as (Hcv).
    {
      Take y : ℝ.
      Assume that Boule c r y.
      By Hball it holds that a ≤ y ∧ y ≤ b.
      It holds that y ∈ (fun x => a ≤ x ∧ x ≤ b).
      By Hgpt it holds that (fun n => fn n y) ⟶ g y as (Hy).
      By (@proj1 _ _ (convergence_equivalence (fun n => fn n y) (g y)) Hy)
        we conclude that Un_cv (fun n => fn n y) (g y).
    }
    We claim that ∀ n : ℕ, ∀ y : ℝ, Boule c r y →
      derivable_pt_lim (fn n) y (dfn n y) as (Hdl).
    {
      Take n : ℕ. Take y : ℝ.
      Assume that Boule c r y.
      By Hball it holds that a ≤ y ∧ y ≤ b.
      By Hderiv it holds that
        ∃ Hd : derivable_pt (fn n) y, derive_pt (fn n) y Hd = dfn n y.
      Obtain such a Hd.
      By derive_pt_eq_1 we conclude that derivable_pt_lim (fn n) y (dfn n y).
    }
    It holds that | x - c | < (b - a) / 2.
    It holds that Boule c r x as (Hx).
    Define Hglim := CVU_derivable fn dfn g h c r Hcvu Hcv Hdl x Hx.
    Define Hd := @exist ℝ (fun l : ℝ => derivable_pt_abs g x l) (h x) Hglim.
    Choose Hd0 := Hd.
    We need to show that derive_pt g0 x Hd0 = h x.
    By (derive_pt_eq_0 g x (h x) Hd0 Hglim) we conclude that
      derive_pt g0 x Hd0 = h x.
Qed.

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
  (** By definition this is [uniform_cauchy_criterion] for the partial sums. *)
  We need to show that
    (∃ g : ℝ → ℝ, converges_uniformly (series_partial_sums fn) g A) ⇔
    (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      | series_partial_sums fn n x - series_partial_sums fn m x | < ε).
  By (uniform_cauchy_criterion (series_partial_sums fn) A) we conclude that
    (∃ g : ℝ → ℝ, converges_uniformly (series_partial_sums fn) g A) ⇔
    (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, ∀ x ∈ A,
      | series_partial_sums fn n x - series_partial_sums fn m x | < ε).
Qed.

(** _Term-wise continuity of a series_ (Abbott 6.4.2): if [∑ fₙ] converges
    uniformly to [g] on [A] and each [fₙ] is continuous at [a ∈ A] (relative to
    [A], as in [uniform_limit_continuous]), then [g] is continuous at [a].

    Proof idea: each partial sum is continuous at [a] (finite sum of continuous
    functions, by induction with [δ = min(δ₁, δ₂)]); apply
    [uniform_limit_continuous] to the partial sums. *)
Theorem termwise_continuity_series (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) (a : ℝ)
    (Ha : a ∈ A)
    (Hcont : ∀ n ∈ ℕ, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A,
      | x - a | < δ → | fn n x - fn n a | < ε)
    (Hunif : series_converges_uniformly fn g A) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, | x - a | < δ → | g x - g a | < ε.
Proof.
  (** Each partial sum is continuous at [a] (relative to [A]). *)
  We claim that ∀ n : ℕ, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A,
    | x - a | < δ → | series_partial_sums fn n x - series_partial_sums fn n a | < ε
    as (Hpart).
  {
    We use induction on n.
    + We first show the base case ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A,
        | x - a | < δ → | series_partial_sums fn 0 x - series_partial_sums fn 0 a | < ε.
      Take ε > 0.
      By Hcont it holds that ∃ δ > 0, ∀ x ∈ A,
        | x - a | < δ → | fn 0%nat x - fn 0%nat a | < ε as (H0).
      Obtain such a δ.
      Choose δ0 := δ. { Indeed, δ0 > 0. }
      We need to show that ∀ x ∈ A, | x - a | < δ0 →
        | series_partial_sums fn 0 x - series_partial_sums fn 0 a | < ε.
      Take x ∈ A. Assume that | x - a | < δ0.
      It holds that series_partial_sums fn 0 x = fn 0%nat x.
      It holds that series_partial_sums fn 0 a = fn 0%nat a.
      By H0 it holds that | fn 0%nat x - fn 0%nat a | < ε.
      We conclude that | series_partial_sums fn 0 x - series_partial_sums fn 0 a | < ε.
    + We now show the induction step.
      Take n : ℕ.
      Assume that ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, | x - a | < δ →
        | series_partial_sums fn n x - series_partial_sums fn n a | < ε as (IH).
      We need to show that ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, | x - a | < δ →
        | series_partial_sums fn (n + 1) x - series_partial_sums fn (n + 1) a | < ε.
      Take ε > 0.
      It holds that ε / 2 > 0.
      By IH it holds that ∃ δ > 0, ∀ x ∈ A, | x - a | < δ →
        | series_partial_sums fn n x - series_partial_sums fn n a | < ε / 2.
      Obtain such a δ1.
      It holds that ∀ x ∈ A, | x - a | < δ1 →
        | series_partial_sums fn n x - series_partial_sums fn n a | < ε / 2 as (Hδ1).
      By Hcont it holds that ∃ δ > 0, ∀ x ∈ A,
        | x - a | < δ → | fn (S n) x - fn (S n) a | < ε / 2.
      Obtain such a δ2.
      It holds that ∀ x ∈ A,
        | x - a | < δ2 → | fn (S n) x - fn (S n) a | < ε / 2 as (Hδ2).
      Choose δ := Rmin δ1 δ2.
      { By Rmin_pos we conclude that δ > 0. }
      We need to show that ∀ x ∈ A, | x - a | < δ →
        | series_partial_sums fn (n + 1) x - series_partial_sums fn (n + 1) a | < ε.
      Take x ∈ A. Assume that | x - a | < δ.
      By Rmin_l it holds that Rmin δ1 δ2 ≤ δ1.
      By Rmin_r it holds that Rmin δ1 δ2 ≤ δ2.
      By Hδ1 it holds that
        | series_partial_sums fn n x - series_partial_sums fn n a | < ε / 2.
      By Hδ2 it holds that | fn (S n) x - fn (S n) a | < ε / 2.
      It holds that (n + 1)%nat = S n.
      It holds that series_partial_sums fn (S n) x
        = series_partial_sums fn n x + fn (S n) x.
      It holds that series_partial_sums fn (S n) a
        = series_partial_sums fn n a + fn (S n) a.
      By Rabs_triang it holds that
        | (series_partial_sums fn n x - series_partial_sums fn n a)
          + (fn (S n) x - fn (S n) a) |
        ≤ | series_partial_sums fn n x - series_partial_sums fn n a |
          + | fn (S n) x - fn (S n) a |.
      It holds that
        | series_partial_sums fn (S n) x - series_partial_sums fn (S n) a | < ε.
      We conclude that
        | series_partial_sums fn (n + 1) x - series_partial_sums fn (n + 1) a | < ε.
  }
  (** Now apply [uniform_limit_continuous] to the partial sums. *)
  We claim that ∀ n ∈ ℕ, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A,
    | x - a | < δ → | series_partial_sums fn n x - series_partial_sums fn n a | < ε
    as (Hpart').
  {
    Take n ∈ ℕ.
    By Hpart we conclude that ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A,
      | x - a | < δ → | series_partial_sums fn n x - series_partial_sums fn n a | < ε.
  }
  It holds that converges_uniformly (series_partial_sums fn) g A as (Hunif').
  By (uniform_limit_continuous (series_partial_sums fn) g A a Ha Hpart' Hunif')
    we conclude that ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, | x - a | < δ → | g x - g a | < ε.
Qed.

(** _Term-wise differentiability of a series_ (Abbott 6.4.3): if each [fₙ] is
    differentiable on [[a, b]] with derivative [dfnₙ], the series of derivatives
    [∑ dfnₙ] converges uniformly to [h], and [∑ fₙ(x₀)] converges at one point
    [x₀ ∈ [a, b]], then [∑ fₙ] converges uniformly on [[a, b]] to a function
    [g] with [g' = h] on [(a, b)].

    Proof idea: apply [uniform_differentiability_theorem] to the partial sums,
    whose derivatives are the partial sums of the derivative series (by
    induction, with [derivable_pt_lim_plus]). Compact intervals are
    essential. *)
Theorem termwise_differentiability_series
    (fn : ℕ → ℝ → ℝ) (dfn : ℕ → ℝ → ℝ) (h : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hderiv : ∀ n ∈ ℕ, ∀ x ∈ ℝ, a ≤ x → x ≤ b →
        ∃ Hd : derivable_pt (fn n) x, derive_pt (fn n) x Hd = dfn n x)
    (Hpt : ∃ x0 : ℝ, a ≤ x0 ∧ x0 ≤ b ∧
        ∃ L : ℝ, (fun n => series_partial_sums fn n x0) ⟶ L)
    (Hdunif : series_converges_uniformly dfn h (fun x => a ≤ x ∧ x ≤ b)) :
    ∃ g : ℝ → ℝ, series_converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b) ∧
      (∀ x : ℝ, a < x → x < b →
        ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x).
Proof.
  (** Each [fₙ] has derivative [dfnₙ] on [[a, b]]. *)
  We claim that ∀ n : ℕ, ∀ z : ℝ, a ≤ z → z ≤ b →
    derivable_pt_lim (fn n) z (dfn n z) as (Hlim).
  {
    Take n : ℕ. Take z : ℝ.
    Assume that a ≤ z and z ≤ b.
    By Hderiv it holds that
      ∃ Hd : derivable_pt (fn n) z, derive_pt (fn n) z Hd = dfn n z.
    Obtain such a Hd.
    By derive_pt_eq_1 we conclude that derivable_pt_lim (fn n) z (dfn n z).
  }
  (** The partial sums are differentiable, with the partial sums of the
      derivatives as derivatives. *)
  We claim that ∀ n : ℕ, ∀ z : ℝ, a ≤ z → z ≤ b →
    derivable_pt_lim (series_partial_sums fn n) z (series_partial_sums dfn n z)
    as (Hsum).
  {
    We use induction on n.
    + We first show the base case ∀ z : ℝ, a ≤ z → z ≤ b →
        derivable_pt_lim (series_partial_sums fn 0) z (series_partial_sums dfn 0 z).
      Take z : ℝ.
      Assume that a ≤ z and z ≤ b.
      By Hlim it holds that derivable_pt_lim (fn 0%nat) z (dfn 0%nat z).
      We conclude that
        derivable_pt_lim (series_partial_sums fn 0) z (series_partial_sums dfn 0 z).
    + We now show the induction step.
      Take n : ℕ.
      Assume that ∀ z : ℝ, a ≤ z → z ≤ b →
        derivable_pt_lim (series_partial_sums fn n) z (series_partial_sums dfn n z)
        as (IH).
      We need to show that ∀ z : ℝ, a ≤ z → z ≤ b →
        derivable_pt_lim (series_partial_sums fn (n + 1)) z
          (series_partial_sums dfn (n + 1) z).
      Take z : ℝ.
      Assume that a ≤ z and z ≤ b.
      By IH it holds that
        derivable_pt_lim (series_partial_sums fn n) z (series_partial_sums dfn n z)
        as (H1).
      By Hlim it holds that derivable_pt_lim (fn (S n)) z (dfn (S n) z) as (H2).
      It holds that (n + 1)%nat = S n.
      By (derivable_pt_lim_plus (series_partial_sums fn n) (fn (S n)) z
        (series_partial_sums dfn n z) (dfn (S n) z) H1 H2) we conclude that
        derivable_pt_lim (series_partial_sums fn (n + 1)) z
          (series_partial_sums dfn (n + 1) z).
  }
  We claim that ∀ n ∈ ℕ, ∀ x ∈ ℝ, a ≤ x → x ≤ b →
    ∃ Hd : derivable_pt (series_partial_sums fn n) x,
      derive_pt (series_partial_sums fn n) x Hd = series_partial_sums dfn n x
    as (Hderiv').
  {
    Take n ∈ ℕ. Take x ∈ ℝ.
    Assume that a ≤ x and x ≤ b.
    By Hsum it holds that
      derivable_pt_lim (series_partial_sums fn n) x (series_partial_sums dfn n x)
      as (Hl).
    Define Hd := @exist ℝ
      (fun l : ℝ => derivable_pt_abs (series_partial_sums fn n) x l)
      (series_partial_sums dfn n x) Hl.
    Choose Hd0 := Hd.
    By (derive_pt_eq_0 (series_partial_sums fn n) x (series_partial_sums dfn n x)
      Hd0 Hl) we conclude that
      derive_pt (series_partial_sums fn n) x Hd0 = series_partial_sums dfn n x.
  }
  (** Apply [uniform_differentiability_theorem] to the partial sums. *)
  It holds that
    converges_uniformly (series_partial_sums dfn) h (fun x => a ≤ x ∧ x ≤ b)
    as (Hdunif').
  By (uniform_differentiability_theorem (series_partial_sums fn)
    (series_partial_sums dfn) h a b Hab Hderiv' Hpt Hdunif') we conclude that
    ∃ g : ℝ → ℝ, series_converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b) ∧
      (∀ x : ℝ, a < x → x < b →
        ∃ Hd : derivable_pt g x, derive_pt g x Hd = h x).
Qed.
