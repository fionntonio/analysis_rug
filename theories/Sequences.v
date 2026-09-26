(** * RUG.Analysis.Sequences — Convergence of sequences.

  #<a href="../../index.html##lecture03">Lecture 3</a>#.

  Formalizes Abbott §2.2–2.3: the ε-N definition of convergence,
  algebraic limit theorem, order limit theorem, and squeeze_theorem theorem. *)

(* begin hide *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.SeqProp.

From Waterproof Require Export Libs.Analysis.Sequences.
Require Export RUG.Analysis.Reals.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

Set Warnings "-non-reference-hint-using".
(* end hide *)

(** ** Some helpful lemmas

  These are not part of Rocq or Waterproof standard libraries,
  and will become handy for us later on. *)

(* TODO: consider moving this into reals and the next into integers *)

(** [Rdiv_lt_compat_r] is a lemma that states that if [r1 < r2] and [0 < r3], then [r1 / r3 < r2 / r3]. *)
Lemma Rdiv_lt_compat_r (r1 : ℝ) (r2 : ℝ) (r3 : ℝ) :
  r1 < r2 → 0 < r3 → r1 / r3 < r2 / r3.
Proof.
  Assume that r1 < r2 as (Hlt).
  Assume that 0 < r3 as (Hc).
  By Rmult_lt_compat_r it holds that r1 * / r3 < r2 * / r3.
  It holds that r1 * / r3 = r1 / r3. It holds that r2 * / r3 = r2 / r3.
  We conclude that r1 / r3 < r2 / r3.
Qed.

(** This lemma provides a trivial property for natural number,
    but since we are mixing up different representations of ℕ,
    from Waterproof and Rocq, we need to help the compiler
    to juggle them. *)
Lemma le_succ_cases (n N1 : ℕ) :
  n ≤ S N1 -> n = S N1 \/ n ≤ N1.
Proof.
Assume that n ≤ S N1 as (H).
(** I'd like to do
   [By (Nat.eq_dec n (S N1)) it holds that n = S N1 ∨ n ≠ S N1].
   but it is not working, so I do it manually. *)
destruct (Nat.eq_dec n (S N1)) as [Heq | Hneq].
- left. We conclude that n = S N1.
- right.
  It holds that (n ≤ S N1)%nat as (Hle_nat).
  It holds that (n ≤ N1)%nat as (Hle_nat_succ).
  We conclude that n ≤ N1.
Qed.

(** This computes the maximum of the absolute values
    of the first N+1 terms of the sequence. *)
Fixpoint partial_max (a : ℕ → R) (N1 : ℕ) : ℝ :=
  match N1 with
  | O => Rabs (a 0%nat)
  | S k => Rmax (partial_max a k) (Rabs (a (S k)))
  end.

Lemma partial_max_spec (a : ℕ → R) :
  ∀ N1 ∈ ℕ, ∀ n ∈ ℕ,
  n ≤ N1 -> | a n | ≤ partial_max a N1.
Proof.
  We use induction on N1.
  - We first show the base case ∀ n ∈ ℕ,
      n ≤ 0%nat ⇨ |a(n)| ≤ partial_max(a, 0%nat).
    Take n ∈ ℕ. Assume that n ≤ 0%nat.

    It holds that (n ≤ 0)%nat.
    It holds that n = 0%nat.
    It holds that |a(n)| = |a(0%nat)|.

    It holds that |a(0%nat)| = partial_max(a, 0%nat).

    We conclude that |a(n)| ≤ partial_max(a, 0%nat).

  - We now show the induction step.
    Take N1 ∈ ℕ.
    Assume that ∀ n ∈ ℕ, n ≤ N1 ⇨ |a(n)| ≤ partial_max(a, N1) as (IHN1).
    Take n ∈ ℕ. Assume that n ≤ (N1 + 1)%nat.

    It holds that (N1 + 1)%nat = S N1.
    It holds that S N1 = (N1 + 1)%nat.

    It holds that
      partial_max(a, S N1)
      = Rmax(partial_max(a, N1), |a (S N1)|).

    By le_succ_cases it holds that n = S N1 ∨ n ≤ N1.
    Either n = S N1 or n ≤ N1.

    * Case n = S N1.
      It holds that (&
        |a(n)|
        = |a(S N1)|
        ≤ Rmax(partial_max(a, N1), |a(S N1)|)
        = partial_max(a, S N1)
      ).
      It holds that partial_max(a, S N1) = partial_max(a, (N1 + 1)%nat).
      We conclude that |a(n)| ≤ partial_max(a, (N1 + 1)%nat).

    * Case n ≤ N1.
      By IHN1 it holds that |a(n)| ≤ partial_max(a, N1).
      It holds that (&
        partial_max(a, N1)
        ≤ Rmax(partial_max(a, N1), |a(S N1)|)
        = partial_max(a, S N1)
        = partial_max(a, (N1 + 1)%nat)
      ).
      We conclude that |a(n)| ≤ partial_max(a, (N1 + 1)%nat).
Qed.

(** ** Convergence of a sequence

    Definition: [(aₙ)] _converges_ to [a] if
    [∀ ε > 0, ∃ N, ∀ n ≥ N, |aₙ - a| < ε].
    We write [aₙ → a] or [a = lim_{n→∞} aₙ].

    In Waterproof, [aₙ ⟶ a] is equivalent to [Un_cv aₙ a]. *)

(** ** Constant and harmonic sequences *)

(** The constant sequence with value [c]. *)
Definition constant_seq (c : ℝ) := fun (n : ℕ) => c.

(** A constant sequence [aₙ = c] converges to [c]. *)
Lemma constant_seq_converges (c : ℝ) : (fun _ : ℕ => c) ⟶ c.
Proof.
  (** This is in Waterproof already, so we could just do
     [By lim_const_seq we conclude that (fun _ : ℕ => c) ⟶ c.]*)
  Define s := constant_seq c.
  We need to show
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ｜s(n) - c｜ < ε.
  Take ε > 0. Choose N1 := O. { Indeed, N1 ∈ ℕ. }

  We need to show that ∀ n ≥ N1, ｜s(n) - c｜ < ε.
  Take n ≥ N1.
  It holds that s n = c.
  We conclude that (&
    |s n - c|
    = | c - c |
    = |0| = 0 < ε
  ).
Qed.

(** The harmonic sequence. *)
Definition harmonic := fun (n : ℕ) => 1 / (n + 1).

(** The sequence [1/(n+1)] converges to [0]. *)
Lemma harmonic_to_0 : (fun n : ℕ => Rdiv 1 (INR n + 1)) ⟶ 0.
Proof.
  (** This is in Waterproof already, we could prove it with
      [By lim_d_0 we conclude that (fun n : ℕ => Rdiv 1 (INR n + 1)) ⟶ 0.]
      The proof below is an adaptation of the proof in Waterproof. *)
  We need to show
      ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ｜harmonic(n) - 0｜ < ε.
  Take ε > 0.
  By the Archimedean property it holds that ∃ n1 ∈ ℕ, n1 > / ε.
  Obtain such an n1. Choose N1 := n1. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, ｜harmonic(n) - 0｜ < ε.

  Take n ≥ N1.
  We need to show that Rabs (1 / (n + 1) - 0) < ε.
  It suffices to show that -ε < 1 / (n + 1) - 0 < ε.
  We show both -ε < 1 / (n + 1) - 0 and 1 / (n + 1) - 0 < ε.
  - It holds that 0 < n + 1. (* n + 1 > 0 is difficult? *)
    We conclude that (&
      -ε < 0 < / (n + 1) = 1 / (n + 1) - 0
    ).
  - We claim that / ε < n + 1.
    { We conclude that (& / ε < n1 <= n <= n + 1 ). }
    We conclude that (&
      1 / (n + 1) - 0 = / (n + 1)
      < / / ε = ε
    ).
Qed.

(** ** Bounded sequences *)

(** A sequence [(aₙ)] is _bounded_ if there exists [M > 0] such that
    [|aₙ| ≤ M] for all [n]. *)
Definition bounded_sequence (a : ℕ → ℝ) :=
  ∃ M ∈ ℝ, M > 0 ∧ ∀ n ∈ ℕ, | a n | ≤ M.

(** Theorem: Every convergent sequence is bounded. *)
Lemma convergent_sequence_is_bounded (a : ℕ → ℝ) (L : ℝ) :
  a ⟶ L → bounded_sequence a.
Proof.
  Assume that a ⟶ L.
  It holds that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | a n - L | < ε as (HC).
  It holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, | a n - L | < 1 as (H1).
  Obtain such an N1.
  We claim that ∀ n ≥ N1, | a n | < 1 + | L |.
  {
    Take n ≥ N1.
    It holds that | a n | ≤ | a n - L | + | L |.
    We conclude that (&
      | a n |
      ≤ | a n - L | + | L |
      < 1 + | L |
    ).
  }

  By partial_max_spec it holds that
    ∀ n ∈ ℕ, n ≤ N1 ⇨ |a(n)| ≤ partial_max(a, N1).
  We need to show that ∃ M ∈ ℝ, M > 0 ∧ ∀ n ∈ ℕ, | a n | ≤ M.
  Choose M := Rmax (partial_max a N1) (1 + | L |). { Indeed, M ∈ ℝ. }

  We need to show that M > 0 ∧ (∀ n ∈ ℕ, |a(n)| ≤ M).
  We show both statements.
  - We conclude that M > 0.
  - We need to show that ∀ n ∈ ℕ, |a(n)| ≤ M.
    Take n ∈ ℕ.
    Either n ≤ N1 or n > N1.
    - Case n ≤ N1.
      By partial_max_spec it holds that |a(n)| ≤ partial_max(a, N1).
      We conclude that |a n| ≤ M.
    - Case n > N1.
      It holds that n ≥ N1.
      It holds that (&
        | a n | < 1 + | L | ≤ M
      ).
      We conclude that |a n| ≤ M.
Qed.

(** ** Algebraic limit theorem *)

(** _Algebraic limit theorem_ (sum):
    If [aₙ → m] and [bₙ → l] then [aₙ + bₙ → m + l].

    Proof idea: the triangle inequality shows
    [|(aₙ + bₙ) - (m + l)| ≤ |aₙ - m| + |bₙ - l|].

    Choosing [N₁] and [N₂] so that the individual errors are
    below [ε/2] makes the sum below [ε]. *)
Lemma algebraic_limit_theorem_sum (a b : ℕ → ℝ) (m l : ℝ) :
    a ⟶ m → b ⟶ l → (fun n => a n + b n) ⟶ (m + l).
Proof.
  Assume that a ⟶ m as (Ha).
  Assume that b ⟶ l as (Hb).
  Define c := fun n => a n + b n.
  We need to show that c ⟶ (m + l).
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | c n - (m + l) | < ε.
  Take ε > 0.

  Since (ε/2 > 0) it holds that (∃ Nm ∈ ℕ, ∀ n ≥ Nm, | a n - m | < ε/2) as (Ha').
  Obtain such Nm.

  Since (ε/2 > 0) it holds that (∃ Nl ∈ ℕ, ∀ n ≥ Nl, | b n - l | < ε/2) as (Hb').
  Obtain such Nl.

  Choose N1 := max Nm Nl. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, |c(n) - (m + l)| < ε.

  Take n ≥ N1.
  It holds that n ≥ Nm. It holds that n ≥ Nl.
  By Ha' it holds that | a n - m | < ε / 2.
  By Hb' it holds that | b n - l | < ε / 2.

  (** Sometimes it is helpful to hint at the necessary algebraic steps
      one by one *)
  It holds that | c n - (m + l) | = | (a n + b n) - (m + l) |.
  It holds that (a n + b n) - (m + l) = (a n - m) + (b n - l).
  It holds that | c n - (m + l) | = | (a n - m) + (b n - l) |.

  By Rabs_triang it holds that (&
    | (a n - m) + (b n - l) |
    ≤ | a n - m | + | b n - l |
    < ε / 2 + ε / 2 = ε
  ).
  We conclude that (| c n - (m + l) | < ε).
Qed.

(** _Algebraic limit theorem_ (product):
    If [a ⟶ m] and [b ⟶ l], then [(a * b) ⟶ (m * l)]. *)
Lemma algebraic_limit_theorem_product (a b : ℕ → ℝ) (m l : ℝ) :
    a ⟶ m → b ⟶ l → (fun n => a n * b n) ⟶ (m * l).
Proof.
  Assume that a ⟶ m as (Ha).

  (** Importing the appropriate definitions, we could also write
      [a is bounded] instead of [bounded_sequence a] *)
  By convergent_sequence_is_bounded it holds that
    bounded_sequence a.
  It holds that ∃ Ma ∈ ℝ, Ma > 0 ∧ ∀ n ∈ ℕ, | a n | ≤ Ma as (HMa).
  Obtain such a Ma.
  It holds that Ma > 0 as (HMa_pos).
  Assume that b ⟶ l as (Hb).

  We need to show that (fun n => a n * b n) ⟶ (m * l).
  We need to show that
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1,
      | a n * b n - (m * l) | < ε.
  Take ε > 0.
  We need to show that
    ∃ N1 ∈ ℕ, ∀ n ≥ N1,
      | a n * b n - m * l| < ε.

  (** Some algebraic operation need to be aided a bit,
      for instance, here we need first to show that
      division by [2 * Ma] and [2 * | l |] is positive. *)
  It holds that / (2 * Ma) > 0.
  It holds that / (2 * (| l | + 1)) > 0.
  It holds that ε / (2 * Ma) > 0. It holds that ε / (2 * (| l | + 1)) > 0.
  It holds that
    ∃ Na ∈ ℕ, ∀ n ≥ Na, | a n - m | < ε / (2 * (| l | + 1)) as (Ha').
  Obtain such a Na.
  It holds that ∃ Nb ∈ ℕ, ∀ n ≥ Nb, | b n - l | < ε / (2 * Ma) as (Hb').
  Obtain such a Nb.

  Choose N1 := max Na Nb. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, | a n * b n - (m * l) | < ε.
  Take n ≥ N1.
  It holds that n ≥ Na. It holds that n ≥ Nb.
  It holds that | a n | ≤ Ma.

  We claim that
    | a n * b n - (m * l) | ≤ | a n | * | b n - l | + | a n - m | * | l |.
  {
    It holds that (&
      | a n * b n - (m * l) |
      = | a n * b n - a n * l + a n * l - m * l |
      = | a n * (b n - l) + (a n - m) * l |
    ) as (Hinner).

    By Rabs_triang it holds that
      | a n * (b n - l) + (a n - m) * l |
      ≤ | a n * (b n - l) | + | (a n - m) * l |
    as (Htriang).

    By Hinner and Htriang it holds that
      | a n * b n - (m * l) |
      ≤ | a n * (b n - l) | + | (a n - m) * l |.

    By Rabs_mult it holds that
      | a n * (b n - l) | = | a n | * | b n - l |.
    By Rabs_mult it holds that
      | (a n - m) * l | = | a n - m | * | l |.
    It holds that
    | a n * (b n - l) | + | (a n - m) * l |
      = | a n | * | b n - l | + | a n - m | * | l |.

    We conclude that
      | a n * b n - (m * l) |
      ≤ | a n | * | b n - l | + | a n - m | * | l |.
  }

  We claim that | a n | * | b n - l | ≤ ε / 2.
  {
    By Hb' it holds that | b n - l | < ε / (2 * Ma).
    By Rmult_div_r it holds that Ma * ε / Ma = ε.
    By Rmult_comm and Rdiv_mult_distr it holds that (&
      Ma * (ε / (2 * Ma))
      = Ma * ε /(2 * Ma)
      = Ma * ε / (Ma * 2)
      = Ma * ε / Ma / 2
      = ε / 2
    ) as (HMa_bound).
    By HMa_pos and Rmult_le_compat_r it holds that
      | a n | * | b n - l | ≤ Ma * | b n - l |.
    By Hb' and Rmult_le_compat_l it holds that (&
      | a n | * | b n - l |
      ≤ Ma * | b n - l |
      ≤ Ma * (ε / (2 * Ma))
    ) as (HFirstTerm).
    By HFirstTerm and HMa_bound we conclude that
      | a n | * | b n - l | ≤ ε / 2.
  }

  We claim that | a n - m | * | l | < ε / 2.
  {
    It holds that | l | ≥ 0.
    It holds that | l | + 1 > 0.
    It holds that | l | + 1 ≠ 0.
    By Rdiv_diag it holds that
      (| l | + 1) / (| l | + 1) = 1.
    It holds that | l | < | l | + 1.

    By Rdiv_lt_compat_r it holds that
      | l | / (| l | + 1) < (| l | + 1) / (| l | + 1)
    as (Hl_lt).

    By Hl_lt it holds that (&
      | l | / (| l | + 1)
      <  (| l | + 1) / (| l | + 1)
      = 1
    ) as (Hl_lt1).

    It holds that 2 * (| l | + 1) > 0.
    By Rmult_comm it holds that
      | l | / (2 * (| l | + 1)) = | l | / ((| l | + 1) * 2).
    By Rdiv_mult_distr it holds that
      | l | / ((| l | + 1) * 2) = | l | / (| l | + 1) / 2.
    By Hl_lt1 and Rdiv_lt_compat_r it holds that
      | l | / (2 * (| l | + 1)) < 1 / 2
    as (Hl_lt_half).

    By Ha' it holds that
      | a n - m | < ε / (2 * (| l | + 1))
    as (HAn_l).

    By Rmult_le_compat_r and HAn_l it holds that
      | a n - m | * | l |
      ≤ ε / (2 * (| l | + 1)) * | l |.

    It holds that
      ε / (2 * (| l | + 1)) * | l |
      = ε * | l | / (2 * (| l | + 1)).

    By Rmult_lt_compat_l and Hl_lt_half it holds that (&
      ε / (2 * (| l | + 1)) * | l |
      = ε * | l | / (2 * (| l | + 1))
      < ε * 1 / 2 = ε / 2
    ) as (HSecondTerm).

    By HAn_l and HSecondTerm we conclude that
      | a n - m | * | l | < ε / 2.
  }

  It holds that (&
    | a n * b n - (m * l) |
    ≤ | a n | * | b n - l | + | a n - m | * | l |
    <  ε / 2 + ε / 2 = ε
  ).

  We conclude that | a n * b n - (m * l) | < ε.
Qed.

(** _Algebraic limit theorem_ (scalar multiplication):
    If [aₙ → m] and [c ∈ ℝ], then [(c·aₙ) → c·m].

   Proof idea: |c·aₙ - c·m| = |c|·|aₙ - m|. For ε > 0, choose N so that |aₙ - m| < ε/|c| (if c ≠ 0; if c = 0, any N works). *)
Lemma algebraic_limit_theorem_const_mult (b : ℕ → ℝ) (m c : ℝ) :
    b ⟶ m → (fun n => c * b n) ⟶ (c * m).
Proof.
  Assume that b ⟶ m as (Hb).
  Define a := constant_seq c.
  By (constant_seq_converges c) it holds that a ⟶ c.
  By algebraic_limit_theorem_product it holds that
    (fun n => a n * b n) ⟶ (c * m).
  We conclude that (fun n => c * b n) ⟶ (c * m).
Qed.

(** ** Order limit theorem *)

(** _Order limit theorem_
    If [aₙ → L] and [aₙ ≤ M] for all [n], then [L ≤ M].

    Proof idea:
    if [L > M], then taking [ε = L - M > 0] we would have
    [|aₙ - L| < ε] for large [n], implying [aₙ > L - ε = M], contradicting the
    hypothesis. *)
Lemma order_limit_theorem (a : ℕ → ℝ) (L M : ℝ) :
    a ⟶ L → (∀ n ∈ ℕ, a n ≤ M) → L ≤ M.
Proof.
  Assume that a ⟶ L.
  Assume that ∀ n ∈ ℕ, a n ≤ M.
  (** [upp_bd_seq_is_upp_bd_lim: ∀ a, ∀ L, ∀ M, (∀ n ∈ ℕ, a(n) ≤ M) ⇨ a ⟶ L ⇨ L ≤ M]
      by using [upp_bd_seq_is_upp_bd_lim a L M] we help the system
      to find the appropriate arguments for the lemma. This helps
      speeding up the proof check substantially. *)
  By upp_bd_seq_is_upp_bd_lim a L M
    we conclude that L ≤ M.
Qed.


Lemma neg_limit (a : ℕ → ℝ) (L : ℝ) :
    a ⟶ L → (fun n => - a n) ⟶ - L.
Proof.
  Assume that a ⟶ L as (Ha).
  It holds that ∀ n ∈ ℕ, -1 * a n = - a n. It holds that -1 * L = - L.
  By algebraic_limit_theorem_const_mult it holds that
      (fun n => -1 * a n) ⟶ -1 * L as (Hneg).
    We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | - a n - (- L) | < ε.
    Take ε > 0.
    By Hneg it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, | -1 * a n - (-1 * L) | < ε.
    Obtain such a N1. Choose (N1). { Indeed, N1 ∈ ℕ. }
    We need to show that ∀ n ≥ N1, | - a n - (- L) | < ε.
    Take n ≥ N1.
    By Ropp_plus_distr and Rabs_Ropp it holds that (&
      | -1 * a n - (-1 * L) |
      = | -1 * (a n - L) |
      = | a n - L |
    ).
    By Hneg it holds that | -1 * a n - (-1 * L) | < ε.
    We conclude that | - a n - (- L) | < ε.
Qed.

(** _Order limit theorem_ (general form):
    If [aₙ → a] and [bₙ → b] and [aₙ ≤ bₙ] for all [n], then [a ≤ b].

    Proof idea: Since [aₙ ≤ bₙ], we have [bₙ - aₙ ≥ 0], so by part 1, [b - a ≥ 0].
    Given how we defined the order limit theorem though,
    we will need to reverse all the inequalities. *)
Lemma order_limit_theorem_le (a b : ℕ → ℝ) (A B : ℝ) :
    a ⟶ A → b ⟶ B → (∀ n ∈ ℕ, a n ≤ b n) → A ≤ B.
Proof.
  Assume that a ⟶ A as (Ha).
  Assume that b ⟶ B as (Hb).
  Assume that ∀ n ∈ ℕ, a n ≤ b n as (Hab).
  By neg_limit it holds that (fun n => - b n) ⟶ - B.
  Define c := fun n => a n - b n.
  By algebraic_limit_theorem_sum it holds that
    c ⟶ (A - B).
  By Hab it holds that ∀ n ∈ ℕ, c n ≤ 0.
  It holds that (fun n => c n) ⟶ (A - B).
  By (order_limit_theorem c (A-B) 0) it holds that A - B ≤ 0.
  We conclude that A ≤ B.
Qed.

(** _Order limit theorem_  (lower bound form):
    If [bₙ → b] and [c ≤ bₙ] for all [n], then [c ≤ b].

    Proof idea: Apply part 2 with [aₙ = c] (constant sequence). *)
Lemma order_limit_theorem_const_le (b : ℕ → ℝ) (c B : ℝ) :
    b ⟶ B → (∀ n ∈ ℕ, c ≤ b n) → c ≤ B.
Proof.
  Assume that b ⟶ B as (Hb).
  Assume that ∀ n ∈ ℕ, c ≤ b n as (Hcb).
  Define a := constant_seq c.
  By constant_seq_converges c it holds that a ⟶ c.
  By (order_limit_theorem_le a b c B) it holds that c ≤ B.
  We conclude that c ≤ B.
Qed.

(** ** Squeeze theorem *)

(** _Squeeze theorem_

    If [a ⟶ L], [c ⟶ L], and [aₙ ≤ bₙ ≤ cₙ] for all [n], then [b ⟶ L].

    Proof idea:
    for any [ε > 0], choose [N₁] and [N₂] so that [|aₙ - L| < ε] and
    [|cₙ - L| < ε] for [n ≥ max(N₁, N₂)]. Then
    [L - ε < aₙ ≤ bₙ ≤ cₙ < L + ε], so [|bₙ - L| < ε]. *)
Lemma squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ) :
    a ⟶ L → c ⟶ L →
    (∀ n ∈ ℕ, a n ≤ b n) →
    (∀ n ∈ ℕ, b n ≤ c n) →
    b ⟶ L.
Proof.
  Assume that a ⟶ L as (Ha).
  Assume that c ⟶ L as (Hc).
  Assume that ∀ n ∈ ℕ, a n ≤ b n as (Hab).
  Assume that ∀ n ∈ ℕ, b n ≤ c n as (Hbc).
  (** This is in Waterproof already so we are going to take the
      convenient route, but it could be a good and fun exercise to
      try and formalize it yourselves! *)
  By squeeze_theorem we conclude that b ⟶ L.
Qed.

(** _Algebraic limit theorem_ (quotient):
    If [a ⟶ m], [b ⟶ l] and [l ≠ 0], then [(aₙ / bₙ) ⟶ m / l].

    Proof idea: since [l ≠ 0], eventually [|bₙ| > |l|/2 > 0], so the quotient is
    well-defined for large [n]. Writing
    [aₙ/bₙ - m/l = (aₙ l - m bₙ)/(bₙ l)] and bounding numerator and denominator
    reduces the claim to the sum and product theorems together with the
    convergence of [1/bₙ] to [1/l]. *)

(** _Convergence of the reciprocal_:
    if [b ⟶ l] with [l ≠ 0], then [1/bₙ ⟶ 1/l].

    Proof idea: since [bₙ → l ≠ 0], eventually [|bₙ| > |l|/2 > 0], so the
    reciprocal is well-defined. Then
    [|1/bₙ - 1/l| = |bₙ - l| / (|bₙ|·|l|) < |bₙ - l| · 2/|l|²],
    which is made smaller than [ε] by taking [|bₙ - l| < ε·|l|²/2]. *)
Lemma inv_limit (b : ℕ → ℝ) (l : ℝ) :
    b ⟶ l → l ≠ 0 → (fun n => / b n) ⟶ / l.
Proof.
  Assume that b ⟶ l.
  Assume that l ≠ 0.
  It holds that | l | > 0.

  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | / b n - / l | < ε.

  Take ε > 0.
  It holds that | l | / 2 > 0.
  Since (| l | / 2 > 0) it holds that
    (∃ N1 ∈ ℕ, ∀ n ≥ N1, | b n - l | < | l | / 2) as (H1).

  Obtain such a N1.
  It holds that ε * (| l | * | l | / 2) > 0.
  Since (ε * (| l | * | l | / 2) > 0) it holds that
    (∃ N2 ∈ ℕ, ∀ n ≥ N2, | b n - l | < ε * (| l | * | l | / 2)) as (H2).

  Obtain such a N2.
  Choose N3 := max N1 N2. { Indeed, N3 ∈ ℕ. }
  We need to show that ∀ n ≥ N3, | / b n - / l | < ε.

  Take n ≥ N3.
  It holds that n ≥ N1. It holds that n ≥ N2.
  By H1 it holds that | b n - l | < | l | / 2.
  By H2 it holds that | b n - l | < ε * (| l | * | l | / 2).
  By Rabs_triang_inv it holds that | l | - | b n | ≤ | l - b n |.
  It holds that | l - b n | = | b n - l |.
  It holds that | b n | > | l | / 2.
  It holds that | b n | > 0.
  It holds that b n ≠ 0.
  It holds that | b n | * | l | > 0.

  (** We eliminate the inverses by cross-multiplication: after multiplying by
      the positive quantity [|bₙ|·|l|], the goal does no longer contain
      reciprocals. We use [Rinv_l] to get the necessary simplifications
      in the context. *)
  By Rinv_l it holds that / b n * b n = 1.
  By Rinv_l it holds that / l * l = 1.
  It holds that (/ b n - / l) * (b n * l) = l - b n as (Hfield).

  We claim that | / b n - / l | * (| b n | * | l |) = | b n - l | as (Hmul).
  {
    By Rabs_mult it holds that (| b n | * | l |) = | b n * l |.
    It holds that
      |/ b(n) - / l| * (|b(n)| * |l|) = |/ b(n) - / l| * |b(n) * l|.
    By Rabs_mult it holds that
      |/ b(n) - / l| * |b(n) * l| = |(/ b(n) - / l) * (b(n) * l)|.
    By Hfield it holds that
      |(/ b(n) - / l) * (b(n) * l)| = |l - b n|.
    By Rabs_minus_sym it holds that | l - b n | = | b n - l |.
    We conclude that
      | / b n - / l | * (| b n | * | l |) = | b n - l |.
  }

  It holds that
    ε * (| b n | * | l |) > ε * ((| l | / 2) * | l |).
  It holds that
    | b n - l | < ε * (| b n | * | l |).
  By Hmul it holds that | / b n - / l | * (| b n | * | l |) = | b n - l |.
  By Rmult_lt_reg_r we conclude that | / b n - / l | < ε.
Qed.

Lemma algebraic_limit_theorem_quotient (a b : ℕ → ℝ) (m l : ℝ) :
    a ⟶ m → b ⟶ l → l ≠ 0 → (fun n => a n / b n) ⟶ (m / l).
Proof.
  Assume that a ⟶ m.
  Assume that b ⟶ l.
  Assume that l ≠ 0.
  By inv_limit it holds that (fun n => / b n) ⟶ / l.
  By algebraic_limit_theorem_product it holds that
    (fun n => a n * / b n) ⟶ (m * / l).
  We need to show that (fun n => a n / b n) ⟶ (m / l).
  We conclude that (fun n => a n / b n) ⟶ (m / l).
Qed.

(** ** Uniqueness of limits *)

(** _Uniqueness of limits_: a sequence has at most one limit, i.e. if
    [a ⟶ L₁] and [a ⟶ L₂] then [L₁ = L₂].

    Proof idea: suppose [L₁ ≠ L₂] and set [ε = |L₁ - L₂|/2 > 0]. For large [n]
    both [|aₙ - L₁| < ε] and [|aₙ - L₂| < ε], so by the triangle inequality
    [|L₁ - L₂| ≤ |L₁ - aₙ| + |aₙ - L₂| < 2ε = |L₁ - L₂|], a contradiction. *)
Lemma limit_unique (a : ℕ → ℝ) (L1 L2 : ℝ) :
    a ⟶ L1 → a ⟶ L2 → L1 = L2.
Proof.
  Assume that a ⟶ L1.
  Assume that a ⟶ L2.

  We argue by contradiction.

  Assume that L1 ≠ L2.
  It holds that | L1 - L2 | > 0.
  It holds that | L1 - L2 | / 2 > 0.

  Since (| L1 - L2 | / 2 > 0) it holds that
    (∃ N1 ∈ ℕ, ∀ n ≥ N1, | a n - L1 | < | L1 - L2 | / 2) as (HA).
  Obtain such a N1.

  Since (| L1 - L2 | / 2 > 0) it holds that
    (∃ N2 ∈ ℕ, ∀ n ≥ N2, | a n - L2 | < | L1 - L2 | / 2) as (HB).
  Obtain such a N2.

  Define n := max N1 N2.

  It holds that n ≥ N1. It holds that n ≥ N2.
  By HA it holds that | a n - L1 | < | L1 - L2 | / 2.
  By HB it holds that | a n - L2 | < | L1 - L2 | / 2.

  By Rabs_triang it holds that
    | L1 - L2 | ≤ | L1 - a n | + | a n - L2 |.
  It holds that | L1 - a n | = | a n - L1 |.
  It holds that | L1 - L2 | < | L1 - L2 |.
  Contradiction.
Qed.

