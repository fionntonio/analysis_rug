(** * RUG.Analysis.SequenceExamples — Examples of sequence limits.

  #<a href="../../index.html##lecture02">Lecture 2</a>#.

  Contains examples from Lecture 2: specific limit computations and standard limits.
  Formalizes examples from Abbott §2.2–2.3.

  Note: The rational-limit example and the standard limits 1/n, 1/n^2 and c^n
  are fully proved. The nth-root limits and n!/n^n are still admitted; their
  docstrings sketch elementary proofs via Bernoulli-type inequalities and the
  squeeze theorem.
  Note: In Rocq, natural numbers start from 0, but our sequences correspond
  to Abbott's sequences starting from n=1. We use (n+1) or (INR n + 1) consistently. *)

Require Import RUG.Analysis.Lib.StdlibReals.

Require Export RUG.Analysis.Sequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".


(** ** Basic limit examples from lecture 2 *)


(** ** Example: limit of (6n+7)/(3n+1)

  Claim: $\displaystyle\lim_{n\to\infty} \frac{6n+7}{3n+1} = 2$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing: the sequence is
  $$\frac{6(n+1)+7}{3(n+1)+1} = \frac{6n+13}{3n+4}$$ for n:ℕ.

  Proof sketch:
  $\begin{aligned}
  \left|\frac{6(n+1)+7}{3(n+1)+1} - 2\right| 
  &= \left|\frac{6n+13}{3n+4} - 2\right|
  = \left|\frac{6n+13 - 6n - 8}{3n+4}\right| 
  = \frac{5}{3n+4} < \frac{5}{3(n+1)}. 
  \end{aligned}$

  For any ε > 0, choose N such that 1/(N+1) < 3ε/5. Then for n ≥ N,
  $$\frac{5}{3(n+1)} \leq \frac{5}{3(N+1)} < \varepsilon.$$ *)
Lemma limit_6n_plus_7_over_3n_plus_1 :
    (fun n : ℕ => (6 * (INR n + 1) + 7) / (3 * (INR n + 1) + 1)) ⟶ 2.
Proof.
  We need to show that
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1,
      | (6 * (INR n + 1) + 7) / (3 * (INR n + 1) + 1) - 2 | < ε.
  Take ε > 0.
  It holds that 3 * ε / 5 > 0.
  By archimedean_2 it holds that
    ∃ n1 : ℕ, 1 / (INR n1 + 1) < 3 * ε / 5.
  Obtain such an n1.
  Choose N1 := n1. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1,
    | (6 * (INR n + 1) + 7) / (3 * (INR n + 1) + 1) - 2 | < ε.
  Take n ≥ N1.
  It holds that INR n ≥ INR n1.
  By pos_INR it holds that INR n ≥ 0.
  By pos_INR it holds that INR n1 ≥ 0.
  It holds that 3 * (INR n + 1) + 1 > 0.
  It holds that 3 * (INR n1 + 1) > 0.
  (** The error simplifies to [5 / (3(n+1)+1)], which is positive. *)
  It holds that
    (6 * (INR n + 1) + 7) / (3 * (INR n + 1) + 1) - 2
    = 5 / (3 * (INR n + 1) + 1).
  It holds that 0 < 5 / (3 * (INR n + 1) + 1).
  It holds that
    | (6 * (INR n + 1) + 7) / (3 * (INR n + 1) + 1) - 2 |
    = 5 / (3 * (INR n + 1) + 1).
  It holds that 3 * (INR n1 + 1) < 3 * (INR n + 1) + 1.
  By Rinv_lt_contravar it holds that
    / (3 * (INR n + 1) + 1) < / (3 * (INR n1 + 1)).
  It holds that
    5 / (3 * (INR n + 1) + 1) = 5 * / (3 * (INR n + 1) + 1).
  It holds that
    5 / (3 * (INR n1 + 1)) = 5 * / (3 * (INR n1 + 1)).
  It holds that
    5 / (3 * (INR n + 1) + 1) < 5 / (3 * (INR n1 + 1)).
  It holds that
    5 / (3 * (INR n1 + 1)) = (5 / 3) * (1 / (INR n1 + 1)).
  It holds that
    (5 / 3) * (1 / (INR n1 + 1)) < (5 / 3) * (3 * ε / 5).
  It holds that (5 / 3) * (3 * ε / 5) = ε.
  We conclude that (&
    | (6 * (INR n + 1) + 7) / (3 * (INR n + 1) + 1) - 2 |
    = 5 / (3 * (INR n + 1) + 1)
    < 5 / (3 * (INR n1 + 1))
    = (5 / 3) * (1 / (INR n1 + 1))
    < (5 / 3) * (3 * ε / 5)
    = ε
  ).
Qed.


(** ** Standard limits from lecture 2 *)


(** ** Standard limit: 1/n → 0 

  Claim: $\displaystyle\lim_{n\to\infty} \frac{1}{n} = 0$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing: the sequence is 1/(n+1).

  Proof sketch: For ε > 0, by Archimedean property, there exists N such that
  N > 1/ε. Then for n ≥ N, we have n+1 > N ≥ 1/ε, so 1/(n+1) < ε. *)
Lemma standard_limit_1_over_n :
    (fun n : ℕ => 1 / (INR n + 1)) ⟶ 0.
Proof.
  (** This is exactly the harmonic sequence, already proved in
      [Analysis.Sequences]. *)
  By harmonic_to_0 we conclude that (fun n : ℕ => 1 / (INR n + 1)) ⟶ 0.
Qed.


(** ** Standard limit: 1/n^2 → 0

  Claim: $\displaystyle\lim_{n\to\infty} \frac{1}{n^2} = 0$ (where n starts from 1 in Abbott).

  In Rocq, we use (n+1) to match Abbott's indexing: the sequence is 1/(n+1)^2.

  Proof sketch: For ε > 0, by Archimedean property, there exists N such that
  N > 1/√ε. Then for n ≥ N, we have n+1 > N ≥ 1/√ε, so (n+1)^2 > 1/ε,
  and thus 1/(n+1)^2 < ε. *)
Lemma standard_limit_1_over_n_squared :
    (fun n : ℕ => 1 / (INR n + 1)^2) ⟶ 0.
Proof.
  (** Squeeze [0 ≤ 1/(n+1)^2 ≤ 1/(n+1)] between the constant [0]
    sequence and the harmonic sequence, both of which converge to [0]. *)
  We claim that (fun _ : ℕ => 0) ⟶ 0 as (Hlow).
  {
    By constant_seq_converges we conclude that (fun _ : ℕ => 0) ⟶ 0.
  }
  We claim that (fun n : ℕ => 1 / (INR n + 1)) ⟶ 0 as (Hup).
  {
    By harmonic_to_0 we conclude that (fun n : ℕ => 1 / (INR n + 1)) ⟶ 0.
  }
  We claim that ∀ n ∈ ℕ, 0 ≤ 1 / (INR n + 1)^2 as (Hge).
  {
    Take n ∈ ℕ.
    It holds that INR n + 1 > 0.
    It holds that (INR n + 1)^2 > 0.
    We conclude that 0 ≤ 1 / (INR n + 1)^2.
  }
  We claim that ∀ n ∈ ℕ, 1 / (INR n + 1)^2 ≤ 1 / (INR n + 1) as (Hle).
  {
    Take n ∈ ℕ.
    By pos_INR it holds that INR n ≥ 0.
    It holds that INR n + 1 ≥ 1.
    It holds that INR n + 1 > 0.
    It holds that (INR n + 1)^2 = (INR n + 1) * (INR n + 1).
    It holds that (INR n + 1) ≤ (INR n + 1)^2.
    By Rinv_le_contravar it holds that
      / (INR n + 1)^2 ≤ / (INR n + 1).
    It holds that 1 / (INR n + 1)^2 = / (INR n + 1)^2.
    It holds that 1 / (INR n + 1) = / (INR n + 1).
    We conclude that 1 / (INR n + 1)^2 ≤ 1 / (INR n + 1).
  }
  By (squeeze_theorem (fun _ : ℕ => 0) (fun n : ℕ => 1 / (INR n + 1)^2)
      (fun n : ℕ => 1 / (INR n + 1)) 0 Hlow Hup Hge Hle)
    we conclude that (fun n : ℕ => 1 / (INR n + 1)^2) ⟶ 0.
Qed.


(** ** Standard limit: c^n → 0 for |c| < 1

  Claim: $\displaystyle\lim_{n\to\infty} c^n = 0$ when -1 < c < 1.

  Note: In Rocq, we start from n=0, but the behavior for large n is the same.
  The sequence c^0, c^1, c^2, ... converges to 0.

  Proof sketch: Let |c| = 1/(1+δ) where δ > 0. Then |c^n| = 1/(1+δ)^n.
  By Bernoulli's inequality, (1+δ)^n ≥ 1 + n·δ ≥ n·δ (for n ≥ 1),
  so |c^n| ≤ 1/(n·δ) → 0. *)
Lemma standard_limit_c_to_n (c : ℝ) :
    -1 < c → c < 1 → (fun n : ℕ => c^n) ⟶ 0.
Proof.
  Assume that -1 < c.
  Assume that c < 1.
  It holds that | c | < 1.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | c^n - 0 | < ε.
  Take ε > 0.
  (** [pow_lt_1_zero] from the standard library gives exactly the
      threshold we need for a base of absolute value less than 1. *)
  By pow_lt_1_zero it holds that
    ∃ Nm : ℕ, ∀ n : ℕ, (n ≥ Nm)%nat ⇨ | c^n | < ε as (HN).
  Obtain such an Nm.
  Choose N1 := Nm. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, | c^n - 0 | < ε.
  Take n ≥ N1.
  By HN it holds that | c^n | < ε.
  We conclude that | c^n - 0 | < ε.
Qed.

(** ** Standard limit: nth root of c → 1 for c > 0 *)

(** For [c > 0], [c^(1/n) → 1]. In Rocq the sequence is
    [Rpower c (1/(n+1))], matching Abbott's indexing from [n = 1].

    Proof idea: for [c ≥ 1] set [xₙ = c^(1/(n+1)) - 1 ≥ 0], so that
    [(1 + xₙ)^(n+1) = c]. Bernoulli's inequality [(1 + x)^m ≥ 1 + m x] for
    [x ≥ 0] gives [c ≥ 1 + (n+1) xₙ], hence [0 ≤ xₙ ≤ (c - 1)/(n+1)], and the
    squeeze theorem with [1/(n+1) → 0] gives [xₙ → 0]. For [0 < c < 1] apply
    this to [1/c > 1] and use [c^(1/(n+1)) = 1 / (1/c)^(1/(n+1))] together
    with the limit of a quotient. *)
Lemma standard_limit_nth_root_of_c (c : ℝ) :
    c > 0 → (fun n : ℕ => Rpower c (1 / (INR n + 1))) ⟶ 1.
Proof.
  Admitted.

(** ** Standard limit: nth root of n → 1 *)

(** [n^(1/n) → 1]. In Rocq the sequence is [Rpower (n+1) (1/(n+1))],
    matching Abbott's indexing from [n = 1].

    Proof idea: set [yₙ = (n+1)^(1/(n+1)) - 1 ≥ 0], so that
    [(1 + yₙ)^(n+1) = n+1]. Keeping only the quadratic term of the binomial
    expansion, [(1 + y)^m ≥ m(m-1)/2 · y²] for [y ≥ 0], gives
    [n+1 ≥ (n+1)n/2 · yₙ²], hence [0 ≤ yₙ ≤ √(2/n)] for [n ≥ 1]. Since
    [√(2/n) → 0], the squeeze theorem gives [yₙ → 0]. *)
Lemma standard_limit_nth_root_of_n :
    (fun n : ℕ => Rpower (INR n + 1) (1 / (INR n + 1))) ⟶ 1.
Proof.
  Admitted.

(** ** Standard limit: n! / nⁿ → 0 *)

(** [n!/nⁿ → 0]. In Rocq the sequence is [(n+1)!/(n+1)^(n+1)], with [fact]
    from [Stdlib.Arith.Factorial], matching Abbott's indexing from [n = 1].

    Proof idea: each of the factors [2, …, n+1] of [(n+1)!] is at most
    [n+1], so [(n+1)! ≤ (n+1)ⁿ]; formally, by induction,
    [(n+2)! = (n+2)·(n+1)! ≤ (n+2)·(n+1)ⁿ ≤ (n+2)^(n+1)]. Hence
    [0 < (n+1)!/(n+1)^(n+1) ≤ 1/(n+1)], and the squeeze theorem with
    [1/(n+1) → 0] gives the claim. *)
Lemma standard_limit_n_factorial_over_n_to_n :
    (fun n : ℕ => INR (Stdlib.Arith.Factorial.fact (S n)) / (INR (S n))^(S n)) ⟶ 0.
Proof.
  Admitted.

(** ** A divergent sequence *)

(** Theorem 3.6: the alternating sequence [(-1)ⁿ] does not converge.

    Proof idea: suppose [aₙ → L]. Taking [ε = 1], there is an [N] beyond which
    [|aₙ - L| < 1]. But for even [n] we have [aₙ = 1] and for odd [n] we have
    [aₙ = -1], so both [|1 - L| < 1] and [|-1 - L| < 1] would hold. By the
    triangle inequality [2 = |1 - (-1)| ≤ |1 - L| + |L - (-1)| < 2], a
    contradiction. *)
Lemma pm_1_diverges : ¬ (∃ L ∈ ℝ, (fun n => (-1) ^ n) ⟶ L).
Proof.
  (** Due to ¬ we are already in a contradiction-like setting *)
  Assume that ∃ L ∈ ℝ, (fun n ↦ (-1)^n) ⟶ L as (H).
  Obtain such an L.
  It holds that (1 > 0).
  By H it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, | (-1)^n - L | < 1 as (HN).
  Obtain such an N1.

  (** Even case: [n = 2*N1] *)
  It holds that (2 * N1)%nat ≥ N1.
  By HN it holds that (| (-1)^(2 * N1) - L | < 1).
  By pow_1_even it holds that ((-1)^(2 * N1) = 1).
  It holds that (| 1 - L | < 1).

  By Rabs_def2 it holds that (1 - L < 1 ∧ -1 < 1 - L).
  - It holds that (1 - L < 1).
  - It holds that (-1 < 1 - L).

  (** Odd case: [n = 2*N1+1] *)
  It holds that (S (2 * N1)%nat ≥ N1).
  By HN it holds that (| (-1)^(S(2 * N1)%nat) - L | < 1).
  (** Without the following line it gets very slow *)
  By pow_1_odd it holds that ((-1)^(S (2 * N1)%nat) = - 1).
  It holds that (| -1 - L | < 1).

  By Rabs_def2 it holds that (-1 - L < 1 ∧ -1 < -1 - L).
  - It holds that (-1 - L < 1).
  - It holds that (-1 < -1 - L).

  (** Contradiction: [1 - L < 1  ⇨  L > 0] and [-1 < -1 - L  ⇨  L < 0] *)
  Since (1 - L < 1) ∧ (-1 < -1 - L) it holds that
    (0 < L ∧ L < 0).
  Contradiction.
Qed.
