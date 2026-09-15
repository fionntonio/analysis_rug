(** * RUG.Analysis.Series — Convergence of infinite series.

  #<a href="../../index.html##lecture05">Lecture 5</a>#.

  Formalizes Abbott §2.6 (Cauchy criterion) and §2.7 (series, comparison test,
  absolute convergence, alternating series test, geometric series).

  Note that the Cauchy criterion for sequences ([convergent_is_cauchy],
  [cauchy_is_convergent]) and the underlying Cauchy-sequence machinery are
  developed in [Analysis.CauchySequences] (which re-exports
  [Analysis.Subsequences]) and reused here. *)

(* begin hide *)
From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.PartSum.
From Stdlib Require Import Reals.Rpower.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import micromega.Lra.
From Waterproof Require Import Libs.Analysis.Series.
From Waterproof Require Import Libs.Analysis.Subsequences.
From Waterproof Require Import Libs.Analysis.LimsupLiminfBolzano.
Require Export RUG.Analysis.CauchySequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(* end hide *)

(** ** Series and partial sums *)

(** An infinite series [∑ aₖ] is described through its partial sums
    [Sₙ = ∑_{k=0}^n aₖ], written [partial_sums a n] (i.e. [sum_f_R0 a n]).
    The series converges to [L] when [partial_sums a ⟶ L].

    The Cauchy criterion for sequences used below ([convergent_is_cauchy] and
    [cauchy_is_convergent]) lives in [Analysis.CauchySequences]. *)

(** ** Necessary condition: terms go to zero *)

(** If [∑ aₙ] converges then [aₙ → 0].

    Proof idea: [aₙ = sₙ - sₙ₋₁]; if [sₙ → L] then both terms tend to [L], so
    their difference tends to [0]. (The converse fails, e.g. the harmonic
    series.) *)
Lemma series_convergent_terms_zero (a : ℕ → ℝ) (L : ℝ)
    (Hcv : partial_sums a ⟶ L) : a ⟶ 0.
Proof.
  We need to show that
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | a n - 0 | < ε.
  By convergent_is_cauchy it holds that partial_sums a is _Cauchy_ as (HpsC).
  
  Take ε > 0.
  By HpsC it holds that ∃ N2 ∈ ℕ, ∀ n ≥ N2, ∀ m ≥ N2,
    | (partial_sums a) n - (partial_sums a) m | < ε.
  
  Obtain such a N2.
  Choose N1 := S N2. { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, |a(n) - 0| < ε.
  
  We claim that ∀ n ∈ ℕ,
    (partial_sums a) (n + 1)%nat - (partial_sums a) n = a (n+1)%nat as (Hrec).
  {
    We use induction on n.
    + We first show the base case
        partial_sums a (0 + 1) - partial_sums a 0 = a((0 + 1)%nat).
      
      We need to show that (a 0%nat + a 1%nat)%R - a 0%nat = a 1%nat.
      We conclude that (a 0%nat + a 1%nat - a 0%nat) = a 1%nat.
    
    + We now show the induction step.
      Take n ∈ ℕ.
      Assume that partial_sums a (n + 1)%nat - partial_sums a n = a((n + 1)%nat).

      It holds that
        (partial_sums a) (S (n + 1))%nat = (partial_sums a) (n + 1)%nat + a (S (n + 1))%nat.

      It holds that S (n + 1)%nat = (n + 2)%nat.
      It holds that (n + 1 + 1)%nat = (n + 2)%nat.

      It holds that (&
        (partial_sums a) (n + 2)%nat - (partial_sums a) (n + 1)%nat
        = ((partial_sums a) (n + 1)%nat + a (n + 2)%nat) - (partial_sums a) (n + 1)%nat
        = a (n + 2)%nat
      ).

      We conclude that
        partial_sums a (n + 1 + 1) - partial_sums a (n + 1) = a((n + 1 + 1)%nat).
  }

  Take n ≥ N1.
  It holds that (n - 1)%nat ≥ N2.

  Use n := (n - 1)%nat in (Hrec). { Indeed, (n - 1)%nat ∈ ℕ. }
  It holds that
    partial_sums a (n - 1 + 1) - partial_sums a (n - 1) = a((n - 1 + 1)%nat).
  It holds that (n - 1 + 1)%nat = n.
  It holds that
    partial_sums a n - partial_sums a (n - 1)%nat = a n.

  By Hrec it holds that
    partial_sums a n - partial_sums a (n - 1)%nat =  a n.
  It holds that (&
      | a n - 0 |
      = | a n |
      = | partial_sums a n - partial_sums a (n - 1)%nat |
   ).
  By HpsC it holds that
    | partial_sums a n - partial_sums a (n - 1)%nat |  < ε.
  We conclude that | a n - 0 | < ε.
Qed.

(** ** Algebraic limit theorem for series *)

Definition sprod (a : ℕ → ℝ) (c : ℝ) := fun n : ℕ ↦ c * a n.

(** The partial sums of [c · a] are [c] times the partial sums of [a]. *)
Lemma sprod_comm (a : ℕ → ℝ) (c : ℝ) :
  ∀ n ∈ ℕ, partial_sums (sprod a c) n = sprod (partial_sums a) c n.
Proof.
      Take n ∈ ℕ.
      (** This looks a bit unreadable because I am relying on Rocq Stdlib:
          
          - [sum_f_R0 f n] := ∑_{i=0}^{n} f i
          - [scal_sum f n] says that [c * sum_f_R0 f n = sum_f_R0 (fun i : nat => c * f i) n]

          the latter is what we are trying to show with our own notation. *)
      By scal_sum it holds that
        c * sum_f_R0 a n = sum_f_R0 (fun i : nat => a i * c) n.
      It holds that ∀ i ∈ ℕ, c * a i = a i * c.
      (** Here [sum_eq] says that if [∀ i, (i ≤ N)%nat ⇨ An(i) = Bn(i)]
          then [partial_sums An N = partial_sums Bn N]*)
      By sum_eq it holds that
        sum_f_R0 (fun i : nat => c * a i) n = sum_f_R0 (fun i : nat => a i * c) n.
      It holds that sum_f_R0 (fun i : nat => c * a i) n = c * sum_f_R0 a n.
      We conclude that partial_sums (sprod a c) n = sprod (partial_sums a) c n.
Qed.

Definition ssum (a b : ℕ → ℝ) := fun n : ℕ ↦ a n + b n.

(** If [∑ aₙ = A] and [∑ bₙ = B],
    then [∑ (c·aₙ) = c·A] and [∑ (aₙ + bₙ) = A + B]. *)
Lemma series_algebraic_limit (a b : ℕ → ℝ) (A B : ℝ) :
    (partial_sums a) ⟶ A →
    (partial_sums b) ⟶ B →
    (∀ c ∈ ℝ,
      (partial_sums (sprod a c)) ⟶ (c * A)) ∧
        (partial_sums (ssum a b)) ⟶ (A + B).
Proof.
  Assume that (partial_sums a) ⟶ A as (Ha).
  Assume that (partial_sums b) ⟶ B as (Hb).

  (** This is needed because our theorem includes both
      the scalar multiplication and the sum of series.
      In general it would be more convenient to state
      and prove them separately. *)
  We show both statements.
  + We need to show that ∀ c ∈ ℝ, partial_sums (sprod a c) ⟶ (c * A).
    Take c ∈ ℝ.

    We claim that (fun n : ℕ => c * (partial_sums a) n) ⟶ (c * A).
    {
      We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1,
        | c * (partial_sums a) n - c * A | < ε.
      Take ε > 0.

      (** Case c = 0 is trivial, though it takes some care to handle the formalities. *)
      Either c = 0 or c ≠ 0.
      - Case c = 0.
        Choose N1 := 0%nat. { Indeed, N1 ∈ ℕ. }
        We need to show that ∀ n ≥ N1, |c * partial_sums a n - c * A| < ε.
        Take n ≥ N1.
        It holds that (&
          |c * partial_sums a n - c * A|
          = | 0 * (partial_sums a) n - 0 * A |
          = | 0 - 0 | = 0
        ).
        We conclude that |c * partial_sums a n - c * A| < ε.

      - Case c ≠ 0.
        (** Use convergence of (partial_sums a) with ε/|c| *)
        It holds that |c| > 0.
        It holds that  / |c| > 0.
        It holds that ε / |c| > 0.
        By Ha it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1,
          | (partial_sums a) n - A | < ε / |c|.
        Obtain such an N1.
        Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
        We need to show that ∀ n ≥ N2, |c * partial_sums a n - c * A| < ε.
        Take n ≥ N2.
        It holds that
          | c * (partial_sums a) n - c * A | = |c| * | (partial_sums a) n - A |.
        By Ha it holds that | (partial_sums a) n - A | < ε / |c|.
        It holds that (&
          |c| * | (partial_sums a) n - A |
          < |c| * (ε / |c|)
          = ε
        ).
        We conclude that | c * (partial_sums a) n - c * A | < ε.
    }
    It holds that sprod (partial_sums a) c ⟶ (c * A) as (HSc).

    By sprod_comm it holds that
      ∀ n ∈ ℕ, partial_sums (sprod a c) n = sprod (partial_sums a) c n.
    It holds that
      ∀ n ∈ ℕ, sprod (partial_sums a) c n = partial_sums (sprod a c) n as (HComm).

    We claim that partial_sums (sprod a c) ⟶ (c * A) as (Hfin).
    {
      (** I could not figure out how to formalize this step in Waterproof yet. *)
      apply eq_seq_conv_to_same_lim with
        (a := sprod (partial_sums a) c)
        (b := partial_sums (sprod a c))
        (l := c * A).
      { By HComm we conclude that
          ∀ n ∈ ℕ, sprod (partial_sums a) c n = partial_sums (sprod a c) n. }
      By HSc we conclude that sprod (partial_sums a) c ⟶ (c * A).
    }

    By Hfin we conclude that partial_sums (sprod a c)  ⟶ (c * A).

  + We need to show that (partial_sums (ssum a b)) ⟶ (A + B).

    By convergence_plus it holds that
      (fun n : ℕ => (partial_sums a) n + (partial_sums b) n) ⟶ (A + B) as (Hsum).
    We claim that
      ∀ n ∈ ℕ, partial_sums (ssum a b) n = (partial_sums a) n + (partial_sums b) n 
      as (Hpointwise).
    {
      By plus_sum we conclude that ∀ n ∈ ℕ,
        partial_sums (ssum a b) n = (partial_sums a) n + (partial_sums b) n.
    }
    It holds that ∀ n ∈ ℕ,
      (partial_sums a) n + (partial_sums b) n = ssum (partial_sums a) (partial_sums b) n
    as (Hpt).
    It holds that ∀ n ∈ ℕ,
      partial_sums (ssum a b) n = ssum (partial_sums a) (partial_sums b) n
    as (Hpt2).

    We claim that partial_sums (ssum a b) ⟶ (A + B).
    {
      apply eq_seq_conv_to_same_lim with
        (a:= ssum (partial_sums a) (partial_sums b))
        (b:= partial_sums (ssum a b))
        (l:= A + B).
      {
        By Hpt2 we conclude that ∀ n ∈ ℕ,
          ssum (partial_sums a) (partial_sums b) n = partial_sums (ssum a b) n.
      }
      We conclude that ssum (partial_sums a) (partial_sums b) ⟶ (A + B).
    }
    We conclude that (partial_sums (ssum a b)) ⟶ (A + B).
Qed.

(** ** Cauchy criterion for series *)

(** A series converges iff its partial sums form a Cauchy sequence.

    Proof idea: a series converges iff its partial sums converge, and in the
    complete space [ℝ] a sequence converges iff it is Cauchy. Concretely,
    [∑_{k=n+1}^m aₖ = sₘ - sₙ], so the Cauchy condition on partial sums is
    exactly the Cauchy criterion for the series. *)
Lemma series_cauchy_criterion (a : ℕ → ℝ) :
    (∃ L ∈ ℝ, partial_sums a ⟶ L) ↔
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
       |partial_sums a n - partial_sums a m| < ε.
Proof.
  We show both directions.
  + We need to show that (∃ L ∈ ℝ, partial_sums a ⟶ L)
      ⇨ ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
          |partial_sums a n - partial_sums a m| < ε.
    Assume that ∃ L ∈ ℝ, partial_sums a ⟶ L as (HpsConv).
    Obtain such a L.
    It holds that partial_sums a ⟶ L as (HpsConv2).
    By convergent_is_cauchy it holds that
      (partial_sums a) is _Cauchy_ as (HpsCau).
    By HpsCau it holds that
      ∀ ε > 0,
      ∃ N1 ∈ ℕ,
      ∀ n ≥ N1,
      ∀ m ≥ N1, |partial_sums a n - partial_sums a m| < ε
    as (HpsCauExp).
    Take ε > 0.
    By HpsCauExp it holds that ∃ N1 ∈ ℕ,
      ∀ n ≥ N1,
      ∀ m ≥ N1, |partial_sums a n - partial_sums a m | < ε.
    Obtain such a N1.
    Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
    We need to show that ∀ n ≥ N2, ∀ m ≥ N2,
      |partial_sums a n - partial_sums a m| < ε.
    Take n ≥ N2. Take m ≥ N2.
    We conclude that
      |partial_sums a n - partial_sums a m| < ε.

  + We need to show that
      (∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
        |partial_sums a n - partial_sums a m| < ε)
      ⇨ ∃ L ∈ ℝ, partial_sums a ⟶ L.
    Assume that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
        |partial_sums a n - partial_sums a m| < ε as (HpsC).
    We claim that partial_sums a is _Cauchy_.
    {
      unfold is_cauchy.
      Take ε > 0.
      We need to show
        ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
          |partial_sums a n - partial_sums a m | < ε.
      By HpsC it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
        |partial_sums a n - partial_sums a m| < ε.
      Obtain such a N1.
      Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
      We need to show that ∀ n ≥ N1, ∀ m ≥ N1,
        |partial_sums a n - partial_sums a m| < ε.
      Take n ≥ N2. Take m ≥ N2.
      We conclude that
        |partial_sums a n - partial_sums a m| < ε.
    }
    By cauchy_is_convergent we conclude that
      ∃ L ∈ ℝ, partial_sums a ⟶ L.
Qed.

(** ** Comparison test (left as an exercise in the lecture) *)

(** If [0 ≤ aₙ ≤ bₙ] and [∑ bₙ] converges, then [∑ aₙ] converges.

    Proof idea: the partial sums of [∑ aₙ] are nondecreasing (terms are
    nonnegative) and bounded above by [∑ bₙ], hence converge by the monotone
    convergence theorem.

    Here we prove it via monotone convergence: the partial sums of [∑ aₙ] are
    nondecreasing and bounded above by [∑ bₙ]. *)
Lemma series_comparison_test (a b : ℕ → ℝ)
    (Ha  : ∀ n ∈ ℕ, 0 ≤ a n)
    (Hab : ∀ n ∈ ℕ, a n ≤ b n)
    (Hb  : ∃ l ∈ ℝ, partial_sums b ⟶ l) :
    ∃ l ∈ ℝ, partial_sums a ⟶ l.
Proof.
  Obtain such a l.
  It holds that partial_sums b ⟶ l as (Hbl).
  (* Both partial-sum sequences are nondecreasing (nonnegative terms). *)
  By partial_sums_pos_incr it holds that Un_growing (partial_sums a) as (Hgrow_a).
  We claim that ∀ n ∈ ℕ, b n ≥ 0 as (Hb_nn).
  {
    Take n ∈ ℕ.
    It holds that 0 ≤ a n.
    It holds that a n ≤ b n.
    We conclude that b n ≥ 0.
  }
  By partial_sums_pos_incr it holds that Un_growing (partial_sums b) as (Hgrow_b).
  (* The partial sums of b are bounded above by their limit l. *)
  By convergence_equivalence it holds that
    (partial_sums b ⟶ l ⇔ Un_cv (partial_sums b) l) as (Hb_iff).
  By Hb_iff it holds that Un_cv (partial_sums b) l as (Hb_cv).
  By growing_ineq it holds that ∀ n : ℕ, partial_sums b n ≤ l as (Hb_le).
  (* Hence the partial sums of a are bounded above by l as well. *)
  We claim that ∀ n : ℕ, partial_sums a n ≤ l as (Ha_le).
  {
    Take n : ℕ.
    We claim that ∀ m : ℕ, (m ≤ n)%nat ⇒ a m ≤ b m as (Hpre).
    { Take m : ℕ. Assume that (m ≤ n)%nat. We conclude that a m ≤ b m. }
    By sum_Rle it holds that partial_sums a n ≤ partial_sums b n as (Hstep).
    By Hb_le it holds that partial_sums b n ≤ l.
    We conclude that partial_sums a n ≤ l.
  }
  (* [l] is an upper bound for the range of [partial_sums a]. *)
  We claim that bound (EUn (partial_sums a)) as (Hbound).
  {
    We need to show that ∃ m : ℝ, ∀ x : ℝ, EUn (partial_sums a) x ⇒ x ≤ m.
    Choose m := l.
    Take x : ℝ.
    Assume that EUn (partial_sums a) x as (Hx).
    It holds that ∃ i : ℕ, x = partial_sums a i.
    Obtain such an i.
    It holds that x = partial_sums a i.
    By Ha_le it holds that partial_sums a i ≤ l.
    We conclude that x ≤ m.
  }
  (* Monotone convergence gives the limit. *)
  By Un_cv_crit it holds that ∃ L : ℝ, Un_cv (partial_sums a) L as (Hex).
  Obtain such a L.
  It holds that Un_cv (partial_sums a) L as (HL).
  By convergence_equivalence it holds that
    (partial_sums a ⟶ L ⇔ Un_cv (partial_sums a) L) as (Ha_iff).
  By Ha_iff it holds that partial_sums a ⟶ L as (Ha_cv).
  Choose l0 := L. { Indeed, l0 ∈ ℝ. }
  We conclude that partial_sums a ⟶ l0.
Qed.

(** ** Absolute convergence (left as an exercise in the lecture) *)

(** If [∑ |aₙ|] converges, then [∑ aₙ] converges.

    Proof idea: use the Cauchy criterion. By the triangle inequality
    [|∑_{k=n+1}^m aₖ| ≤ ∑_{k=n+1}^m |aₖ|], so the Cauchy condition for [∑ |aₙ|]
    forces the Cauchy condition for [∑ aₙ].

    We route through the standard library's [cauchy_abs] / [cv_cauchy_2]. *)
Lemma absolute_convergence_implies_convergence (a : ℕ → ℝ)
    (labs : ℝ) (Habs : partial_sums (fun n ↦ |a n|) ⟶ labs) :
    ∃ l ∈ ℝ, partial_sums a ⟶ l.
Proof.
  (* The series of absolute values satisfies the Cauchy criterion for series. *)
  By convergence_equivalence it holds that
    (partial_sums (fun n ↦ |a n|) ⟶ labs ⇔ Un_cv (partial_sums (fun n ↦ |a n|)) labs) as (Habs_iff).
  By Habs_iff it holds that Un_cv (partial_sums (fun n ↦ |a n|)) labs as (Habs_cv).
  We claim that Cauchy_crit_series (fun n ↦ |a n|) as (Hcs_abs).
  {
    (* TODO: raw Rocq — [cv_cauchy_1] consumes a [{l | Un_cv …}] sig, which has
       no direct Waterproof phrasing. Revisit to Waterproof-ify. *)
    apply cv_cauchy_1.
    exists labs.
    exact Habs_cv.
  }
  (* By the triangle inequality the plain series is Cauchy as well. *)
  By cauchy_abs it holds that Cauchy_crit_series a as (Hcs).
  (* Completeness of ℝ turns the Cauchy criterion back into convergence. *)
  We claim that ∃ l : ℝ, Un_cv (partial_sums a) l as (Hex).
  {
    (* TODO: raw Rocq — [cv_cauchy_2] returns a [{l | Un_cv …}] sig that we
       repackage as a plain existential. Revisit to Waterproof-ify. *)
    destruct (cv_cauchy_2 a Hcs) as [l Hl].
    exists l. exact Hl.
  }
  Obtain such a l.
  It holds that Un_cv (partial_sums a) l as (Hl).
  By convergence_equivalence it holds that
    (partial_sums a ⟶ l ⇔ Un_cv (partial_sums a) l) as (Hiff).
  By Hiff it holds that partial_sums a ⟶ l as (Hcv).
  Choose l0 := l. { Indeed, l0 ∈ ℝ. }
  We conclude that partial_sums a ⟶ l0.
Qed.

(** ** Alternating series test (left as an exercise in the lecture) *)

(** If [(bₙ)] is nonnegative, decreasing, and [bₙ → 0], then [∑ (-1)ⁿ bₙ]
    converges.

    Proof idea: the even partial sums [s₂ₙ] are nonincreasing and the odd partial
    sums [s₂ₙ₊₁] are nondecreasing, with [s₂ₙ₊₁ ≤ s₂ₙ] and
    [s₂ₙ - s₂ₙ₊₁ = b₂ₙ₊₁ → 0]. The nested interval property gives a common limit.

    Here we route through the standard library's [alternated_series]; note
    [tg_alt b n = (-1)ⁿ · b n] is exactly our summand. *)
Lemma alternating_series_test (b : ℕ → ℝ)
    (Hnn  : ∀ n ∈ ℕ, 0 ≤ b n)
    (Hdecr : ∀ n ∈ ℕ, b (n + 1)%nat ≤ b n)
    (Hzero : b ⟶ 0) :
    ∃ l ∈ ℝ, partial_sums (fun n ↦ ((-1) ^ n) * b n) ⟶ l.
Proof.
  (* [b] is nonincreasing in the stdlib sense [Un_decreasing]. *)
  We claim that Un_decreasing b as (Hdec).
  {
    We need to show that ∀ n : ℕ, b (S n) ≤ b n.
    Take n : ℕ.
    It holds that b (S n) = b (n + 1)%nat as (He).
    By Hdecr it holds that b (n + 1)%nat ≤ b n.
    We conclude that b (S n) ≤ b n.
  }
  (* [b → 0] in the stdlib sense [Un_cv]. *)
  By convergence_equivalence it holds that (b ⟶ 0 ⇔ Un_cv b 0) as (Hz_iff).
  By Hz_iff it holds that Un_cv b 0 as (Hcv0).
  (* [alternated_series] provides the limit of the partial sums of [tg_alt b]. *)
  We claim that ∃ l : ℝ, Un_cv (partial_sums (fun n ↦ ((-1) ^ n) * b n)) l as (Hex).
  {
    (* TODO: raw Rocq — [alternated_series] returns a [{l | Un_cv …}] sig that
       we repackage as a plain existential; [tg_alt b] is convertible with our
       summand. Revisit to Waterproof-ify. *)
    destruct (alternated_series b Hdec Hcv0) as [l Hl].
    exists l. exact Hl.
  }
  Obtain such a l.
  It holds that Un_cv (partial_sums (fun n ↦ ((-1) ^ n) * b n)) l as (Hl).
  By convergence_equivalence it holds that
    (partial_sums (fun n ↦ ((-1) ^ n) * b n) ⟶ l
      ⇔ Un_cv (partial_sums (fun n ↦ ((-1) ^ n) * b n)) l) as (Hiff).
  By Hiff it holds that partial_sums (fun n ↦ ((-1) ^ n) * b n) ⟶ l as (Hcv).
  Choose l0 := l. { Indeed, l0 ∈ ℝ. }
  We conclude that partial_sums (fun n ↦ ((-1) ^ n) * b n) ⟶ l0.
Qed.

(** ** Geometric series (left as an exercise in the lecture) *)

(** For [|r| < 1], [∑ rᵏ = 1/(1-r)].

    Proof idea: the partial sums have the closed form
    [sₙ = (1 - r^{n+1})/(1 - r)]; since [|r| < 1] gives [r^{n+1} → 0], we get
    [sₙ → 1/(1 - r)].

    Here we obtain the closed form directly from the standard library lemma
    [GP_infinite]. *)
Lemma geometric_series (r : ℝ) (Hr : |r| < 1) :
    ∃ L : ℝ, L = 1 / (1 - r) ∧ partial_sums (fun n ↦ r ^ n) ⟶ L.
Proof.
  (* [GP_infinite] gives [Un_cv (sum_f_R0 (fun n ↦ 1 * r ^ n)) (/ (1 - r))]. *)
  By GP_infinite it holds that Pser (fun _ : ℕ ↦ 1) r (/ (1 - r)) as (Hgp).
  unfold Pser, infinite_sum in Hgp.
  We claim that partial_sums (fun n ↦ r ^ n) ⟶ (/ (1 - r)) as (Hcv).
  {
    We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1,
      R_dist (partial_sums (fun k : ℕ ↦ r ^ k) n) (/ (1 - r)) < ε.
    Take ε > 0.
    By Hgp it holds that ∃ M : ℕ, ∀ n ≥ M,
      Rdist (partial_sums (fun k : ℕ ↦ 1 * r ^ k) n) (/ (1 - r)) < ε as (HN).
    Obtain such a M.
    Choose N1 := M. { Indeed, N1 ∈ ℕ. }
    We need to show that ∀ n ≥ N1,
      R_dist (partial_sums (fun k : ℕ ↦ r ^ k) n) (/ (1 - r)) < ε.
    Take n ≥ N1.
    We claim that
      partial_sums (fun k : ℕ ↦ 1 * r ^ k) n = partial_sums (fun k : ℕ ↦ r ^ k) n
    as (Heq).
    {
      By sum_eq it suffices to show that ∀ i ≤ n, 1 * r ^ i = r ^ i.
      Take i ≤ n. We conclude that 1 * r ^ i = r ^ i.
    }
    By HN it holds that
      Rdist (partial_sums (fun k : ℕ ↦ 1 * r ^ k) n) (/ (1 - r)) < ε.
    It holds that
      Rdist (partial_sums (fun k : ℕ ↦ r ^ k) n) (/ (1 - r)) < ε as (Hfin).
    We conclude that
      R_dist (partial_sums (fun k : ℕ ↦ r ^ k) n) (/ (1 - r)) < ε.
  }
  It holds that 1 / (1 - r) = / (1 - r) as (HL).
  We claim that
    partial_sums (fun n ↦ r ^ n) ⟶ (1 / (1 - r)) as (Hcv2).
  {
    It holds that partial_sums (fun n ↦ r ^ n) ⟶ (/ (1 - r)).
    It holds that (1 / (1 - r)) = / (1 - r).
    We conclude that partial_sums (fun n ↦ r ^ n) ⟶ (1 / (1 - r)).
  }
  
  Choose L := 1 / (1 - r).
  We show both statements.
  + We conclude that L = 1 / (1 - r).
  + We conclude that partial_sums (fun n ↦ r ^ n) ⟶ L.
Qed.

(** ** Telescoping series (left as an exercise in the lecture) *)

(** The partial sums of [∑ (bₖ - b_{k+1})] telescope to [b 0 - L].

    Proof idea: the partial sums telescope,
    [∑_{k=0}^n (b(k+1) - bₖ) = b(n+1) - b 0], which tends to [L - b 0].

    We prove the telescoping identity by induction and then take limits. *)
Lemma telescoping_series (b : ℕ → ℝ) (L : ℝ) (Hb : b ⟶ L) :
    ∃ ps : ℕ → ℝ, (∀ n, ps n = partial_sums (fun k ↦ b k - b (k + 1)%nat) n) ∧
                   ps ⟶ (b 0%nat - L).
Proof.
  (* The telescoping identity: sₙ = b 0 - b (n+1). *)
  We claim that ∀ n : ℕ,
    partial_sums (fun k ↦ b k - b (k + 1)%nat) n = b 0%nat - b (n + 1)%nat as (Htel).
  {
    We use induction on n.
    + We first show the base case
        partial_sums (fun k ↦ b k - b (k + 1)%nat) 0 = b 0%nat - b (0 + 1)%nat.
      (* It holds that partial_sums (fun k ↦ b k - b (k + 1)%nat) 0 = b 0%nat - b (0 + 1)%nat.
      It holds that (b 0%nat - b (0 + 1)%nat) = b 0%nat - b (0 + 1)%nat. *) 
      We conclude that partial_sums (fun k ↦ b k - b (k + 1)%nat) 0 = b(0%nat) - b((0 + 1)%nat).

    + We now show the induction step.
      Take n : ℕ.
      Assume that partial_sums (fun k ↦ b k - b (k + 1)%nat) n = b 0%nat - b (n + 1)%nat as (IH).
      It holds that
        partial_sums (fun k ↦ b k - b (k + 1)%nat) (S n)
        = partial_sums (fun k ↦ b k - b (k + 1)%nat) n + (b (S n) - b (S n + 1)%nat) as (Hrec).
      It holds that b (S n) = b (n + 1)%nat as (Hb1).
      It holds that
        partial_sums (fun k ↦ b k - b (k + 1)%nat) (S n)
        = (b 0%nat - b (n + 1)%nat) + (b (S n) - b (S n + 1)%nat) as (Hstep).
      It holds that partial_sums (fun k ↦ b k - b (k + 1)%nat) (S n) = b 0%nat - b (S n + 1)%nat.
      We conclude that
        partial_sums (fun k ↦ b k - b (k + (0 + 1))%nat) (S n) = b 0%nat - b (S n + (0 + 1))%nat.
  }
  (* The shifted sequence n ↦ b (n+1) still converges to L. *)
  We claim that (fun n ↦ b (n + 1)%nat) ⟶ L as (Hshift).
  {
    We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | b (n + 1)%nat - L | < ε.
    Take ε > 0.
    By Hb it holds that ∃ M ∈ ℕ, ∀ n ≥ M, | b n - L | < ε as (HN).
    Obtain such a M.
    Choose N1 := M. { Indeed, N1 ∈ ℕ. }
    We need to show that ∀ n ≥ N1, | b (n + 1)%nat - L | < ε.
    Take n ≥ N1.
    It holds that (n + 1)%nat ≥ M.
    By HN we conclude that | b (n + 1)%nat - L | < ε.
  }
  (* Hence n ↦ b 0 - b (n+1) converges to b 0 - L. *)
  By lim_const_seq it holds that constant_sequence (b 0%nat) ⟶ (b 0%nat) as (Hconst).
  By convergence_minus it holds that
    (fun n ↦ constant_sequence (b 0%nat) n - b (n + 1)%nat) ⟶ (b 0%nat - L) as (Hdiff).
  Choose ps := partial_sums (fun k ↦ b k - b (k + 1)%nat).
  We show both statements.
  + We need to show that ∀ n : ℕ, ps n = partial_sums (fun k ↦ b k - b (k + 1)%nat) n.
    Take n : ℕ. We conclude that ps n = partial_sums (fun k ↦ b k - b (k + 1)%nat) n.
  + We need to show that ps ⟶ (b 0%nat - L).
    We claim that ∀ n ∈ ℕ, (fun m ↦ constant_sequence (b 0%nat) m - b (m + 1)%nat) n = ps n as (Heqseq).
    {
      Take n ∈ ℕ.
      It holds that constant_sequence (b 0%nat) n = b 0%nat.
      By Htel we conclude that
        (constant_sequence (b 0%nat) n - b (n + 1)%nat) = ps n.
    }
    (* TODO: raw Rocq — [eq_seq_conv_to_same_lim] transports convergence along a
       pointwise-equal sequence; same idiom as [series_algebraic_limit] above.
       Would like a pure Waterproof phrasing later. *)
    apply eq_seq_conv_to_same_lim with
      (a := fun m ↦ constant_sequence (b 0%nat) m - b (m + 1)%nat)
      (b := ps)
      (l := b 0%nat - L).
    { exact Heqseq. }
    exact Hdiff.
Qed.

(** ** The nth-term test for divergence *)

(** _nth-term test (divergence form)_: if [aₙ] does not converge to [0], then
    the series [∑ aₙ] diverges.

    Proof idea: the contrapositive of [series_convergent_terms_zero]. If the
    series converged its terms would tend to [0]. *)
Lemma nth_term_test_divergence (a : ℕ → ℝ) (Hnz : ¬ (a ⟶ 0)) :
    ¬ (∃ L : ℝ, partial_sums a ⟶ L).
Proof.
  Assume that ∃ L : ℝ, partial_sums a ⟶ L as (H).
  Obtain such an L.
  By series_convergent_terms_zero it holds that a ⟶ 0.
  Contradiction.
Qed.

(** ** Two classical series from Lecture 4 *)

(** _The series [∑ 1/k²] converges_.

    Proof idea (Abbott): the partial sums are increasing and bounded above,
    since [1/k² ≤ 1/(k(k-1)) = 1/(k-1) - 1/k] for [k ≥ 2], a telescoping bound
    giving [Sₙ ≤ 2]. Monotone convergence then yields a limit. (Here the terms
    are indexed as [1/(k+1)²] to match Rocq's [k : ℕ] starting at [0].) *)
(** Auxiliary telescoping bound: [1/(x+1)² ≤ 1/x - 1/(x+1)] for [x ≥ 1].

    In Rocq/Waterproof [/x] is somewhat special, and we need to help the system
    with the fact [x · /x = 1] ([Rinv_r]); once that is available, the
    partial-fraction identity [/x - /(x+1) = /x · /(x+1)] follows. *)
Lemma inv_sq_telescope (x : ℝ) (Hx : 1 ≤ x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1).
Proof.
  It holds that 0 < x as (Hx0).
  It holds that 0 < x + 1 as (Hx1).
  By Rinv_r it holds that x * / x = 1 as (Ex).
  By Rinv_r it holds that (x + 1) * / (x + 1) = 1 as (Ex1).
  We claim that / x - / (x + 1) = / x * / (x + 1) as (Hfield).
  {
    We claim that / x * ((x + 1) * / (x + 1)) = / x as (A).
    { rewrite Ex1. We conclude that / x * 1 = / x. }
    We claim that / (x + 1) * (x * / x) = / (x + 1) as (B).
    { rewrite Ex. We conclude that / (x + 1) * 1 = / (x + 1). }
    We conclude that / x - / (x + 1) = / x * / (x + 1).
  }
  By Rinv_mult it holds that / (x * (x + 1)) = / x * / (x + 1) as (Hmul).
  It holds that 0 < x * (x + 1) as (Hpos).
  It holds that x * (x + 1) ≤ (x + 1) ^ 2 as (Hle).
  By Rinv_le_contravar it holds that
    / ((x + 1) ^ 2) ≤ / (x * (x + 1)) as (Hinv).
  We conclude that 1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1).
Qed.

Lemma sum_one_over_k_sq_converges :
    ∃ L : ℝ, partial_sums (fun k => 1 / (INR k + 1) ^ 2) ⟶ L.
Proof.
  (* The telescoping bound [Sₙ ≤ 2 - 1/(n+1)], by induction on [n]. *)
  We claim that ∀ n ∈ ℕ,
    partial_sums (fun k => 1 / (INR k + 1) ^ 2) n ≤ 2 - 1 / (INR n + 1) as (Hbnd).
  {
    We use induction on n.

    + We first show the base case
        partial_sums (fun k => 1 / (INR k + 1) ^ 2) 0 ≤ 2 - 1 / (INR 0 + 1).
      It holds that INR 0%nat = 0.
      We conclude that
        partial_sums (fun k => 1 / (INR k + 1) ^ 2) 0 ≤ 2 - 1 / (INR 0 + 1).
  
    + We now show the induction step.
      Take n ∈ ℕ.
      Assume that
        partial_sums (fun k => 1 / (INR k + 1) ^ 2) n ≤ 2 - 1 / (INR n + 1) as (IH).
      
      It holds that
        partial_sums (fun k => 1 / (INR k + 1) ^ 2) (S n)
        = partial_sums (fun k => 1 / (INR k + 1) ^ 2) n
          + 1 / (INR (S n) + 1) ^ 2.
      
      By S_INR it holds that INR (S n) = INR n + 1 as (HI).
      It holds that
        partial_sums (fun k => 1 / (INR k + 1) ^ 2) (S n)
        = partial_sums (fun k => 1 / (INR k + 1) ^ 2) n
          + 1 / (INR n + 1 + 1) ^ 2.
      rewrite Nat.add_1_r. rewrite HI.
      By pos_INR it holds that 0 ≤ INR n as (Hpos).
      It holds that 1 ≤ INR n + 1 as (Hge).
      By inv_sq_telescope it holds that
        1 / (INR n + 1 + 1) ^ 2 ≤ 1 / (INR n + 1) - 1 / (INR n + 1 + 1) as (Htel).
      We conclude that
        partial_sums (fun k => 1 / (INR k + 1) ^ 2) (S n) ≤ 2 - 1 / (INR n + 1 + 1).
  }

  (* Nonnegative terms, so the partial sums are nondecreasing. *)
  We claim that ∀ n ∈ ℕ, 0 ≤ 1 / (INR n + 1) ^ 2 as (Hnn).
  {
    Take n ∈ ℕ.
    By pos_INR it holds that 0 ≤ INR n.
    It holds that 0 < (INR n + 1) ^ 2.
    It holds that 0 < / (INR n + 1) ^ 2.
    By Rlt_le we conclude that 0 ≤ 1 / (INR n + 1) ^ 2.
  }

  By partial_sums_pos_incr it holds that
    Un_growing (partial_sums (fun k => 1 / (INR k + 1) ^ 2)) as (Hgrow).
  (* [2] is an upper bound for the range of the partial sums. *)
  We claim that bound (EUn (partial_sums (fun k => 1 / (INR k + 1) ^ 2))) as (Hbound).
  {
    We need to show that ∃ m : ℝ,
      ∀ x : ℝ, EUn (partial_sums (fun k => 1 / (INR k + 1) ^ 2)) x ⇒ x ≤ m.
    Choose m := 2.
    Take x : ℝ.
    Assume that EUn (partial_sums (fun k => 1 / (INR k + 1) ^ 2)) x as (Hx).
    It holds that ∃ i : ℕ, x = partial_sums (fun k => 1 / (INR k + 1) ^ 2) i.
    Obtain such an i.
    It holds that x = partial_sums (fun k => 1 / (INR k + 1) ^ 2) i.
    By Hbnd it holds that
      partial_sums (fun k => 1 / (INR k + 1) ^ 2) i ≤ 2 - 1 / (INR i + 1) as (Hi).
    It holds that 0 < INR i + 1 as (Hip).
    It holds that 0 < 1 / (INR i + 1) as (Hinv).
    We conclude that x ≤ m.
  }
  By Un_cv_crit it holds that
    ∃ L : ℝ, Un_cv (partial_sums (fun k => 1 / (INR k + 1) ^ 2)) L as (Hex).
  Obtain such a L.
  It holds that Un_cv (partial_sums (fun k => 1 / (INR k + 1) ^ 2)) L as (HL).
  By convergence_equivalence it holds that
    (partial_sums (fun k => 1 / (INR k + 1) ^ 2) ⟶ L
      ⇔ Un_cv (partial_sums (fun k => 1 / (INR k + 1) ^ 2)) L) as (Hiff).
  By Hiff it holds that partial_sums (fun k => 1 / (INR k + 1) ^ 2) ⟶ L as (Hcv).
  Choose L0 := L.
  We conclude that partial_sums (fun k => 1 / (INR k + 1) ^ 2) ⟶ L0.
Qed.

(** _The harmonic series [∑ 1/k] diverges_.

    Proof idea (Abbott): grouping terms shows
    [1/3 + 1/4 > 1/2], [1/5 + ⋯ + 1/8 > 1/2], and in general each dyadic block
    contributes more than [1/2], so the partial sums are unbounded and cannot
    converge. (Terms indexed as [1/(k+1)] to match Rocq indexing.) *)
(** The harmonic terms are nonincreasing. *)
Lemma inv_succ_decr (x : ℝ) (Hx : 0 ≤ x) : 1 / (x + 1 + 1) ≤ 1 / (x + 1).
Proof.
  It holds that 0 < x + 1 as (H1).
  It holds that x + 1 ≤ x + 1 + 1 as (H2).
  By Rinv_le_contravar it holds that / (x + 1 + 1) ≤ / (x + 1) as (H3).
  We conclude that 1 / (x + 1 + 1) ≤ 1 / (x + 1).
Qed.

(** Each dyadic block contributes exactly [1/2] in the lower bound. *)
Lemma harmonic_block_value (x : ℝ) (Hx : 0 ≤ x) :
    (x + 1) * (1 / (2 * x + 1 + 1)) = 1 / 2.
Proof.
  It holds that 0 < 2 * x + 1 + 1 as (H1).
  By Rinv_r it holds that
    (2 * x + 1 + 1) * / (2 * x + 1 + 1) = 1 as (E).
  We conclude that (x + 1) * (1 / (2 * x + 1 + 1)) = 1 / 2.
Qed.

Lemma harmonic_series_diverges :
    ¬ (∃ L : ℝ, partial_sums (fun k => 1 / (INR k + 1)) ⟶ L).
Proof.
  (* A block of [p] consecutive terms is at least [p] times its smallest term. *)
  We claim that ∀ n : ℕ, ∀ p : ℕ,
    partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add n p)
      - partial_sums (fun k => 1 / (INR k + 1)) n
    ≥ INR p * (1 / (INR (n + p)%nat + 1)) as (Hblock).
  {
    Take n : ℕ.
    We use induction on p.
    + We first show the base case
        partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add n 0)
          - partial_sums (fun k => 1 / (INR k + 1)) n
        ≥ INR 0 * (1 / (INR (n + 0)%nat + 1)).
      It holds that (n + 0)%nat = n as (Hn0).
      rewrite Hn0.
      It holds that INR 0%nat = 0 as (Hi0).
      We conclude that
        partial_sums (fun k => 1 / (INR k + 1)) n
          - partial_sums (fun k => 1 / (INR k + 1)) n
        ≥ INR 0 * (1 / (INR n + 1)).
    + We now show the induction step.
      Take p : ℕ.
      Assume that
        partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add n p)
          - partial_sums (fun k => 1 / (INR k + 1)) n
        ≥ INR p * (1 / (INR (n + p)%nat + 1)) as (IH).
      It holds that (n + (p + 1))%nat = S (n + p)%nat as (Hidx).
      rewrite Hidx.
      It holds that partial_sums (fun k : ℕ => 1 / (INR k + 1)) (S (Nat.add n p))
        = partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add n p)
          + 1 / (INR (S (n + p)%nat) + 1) as (Hrec).
      By S_INR it holds that INR (S (n + p)%nat) = INR (n + p)%nat + 1 as (HS).
      rewrite HS in Hrec. rewrite HS.
      By plus_INR it holds that INR (p + 1)%nat = INR p + INR 1%nat as (Hp1).
      It holds that INR 1%nat = 1 as (H1).
      It holds that INR (p + 1)%nat = INR p + 1 as (Hp1').
      rewrite Hp1'.
      By pos_INR it holds that 0 ≤ INR p as (Hpp).
      By pos_INR it holds that 0 ≤ INR (n + p)%nat as (Hnp).
      By inv_succ_decr it holds that
        1 / (INR (n + p)%nat + 1 + 1) ≤ 1 / (INR (n + p)%nat + 1) as (Hdec).
      We conclude that
        partial_sums (fun k : ℕ => 1 / (INR k + 1)) (S (Nat.add n p))
          - partial_sums (fun k => 1 / (INR k + 1)) n
        ≥ (INR p + 1) * (1 / (INR (n + p)%nat + 1 + 1)).
  }
  (* If the series converged its partial sums would be Cauchy, contradicting
     the fact that the block from [N] to [2N+1] has length ≥ 1/2. *)
  Assume that ∃ L : ℝ, partial_sums (fun k => 1 / (INR k + 1)) ⟶ L as (Hcv).
  Obtain such an L.
  By convergent_is_cauchy it holds that
    partial_sums (fun k => 1 / (INR k + 1)) is _Cauchy_ as (HC).
  It holds that 1 / 2 > 0 as (Hhalf).
  By HC it holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
    | partial_sums (fun k => 1 / (INR k + 1)) n
      - partial_sums (fun k => 1 / (INR k + 1)) m | < 1 / 2 as (HCa).
  Obtain such a N1.
  By Hblock it holds that
    partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add N1 (Nat.add N1 1))
      - partial_sums (fun k => 1 / (INR k + 1)) N1
    ≥ INR (N1 + 1)%nat * (1 / (INR (N1 + (N1 + 1))%nat + 1)) as (Hb).
  By pos_INR it holds that 0 ≤ INR N1 as (HN0).
  By plus_INR it holds that INR (N1 + 1)%nat = INR N1 + INR 1%nat as (E1).
  It holds that INR 1%nat = 1 as (E2).
  By plus_INR it holds that
    INR (N1 + (N1 + 1))%nat = INR N1 + INR (N1 + 1)%nat as (E3).
  It holds that INR (N1 + 1)%nat = INR N1 + 1 as (E1').
  It holds that INR (N1 + (N1 + 1))%nat = 2 * INR N1 + 1 as (E5).
  rewrite E5 in Hb. rewrite E1' in Hb.
  By harmonic_block_value it holds that
    (INR N1 + 1) * (1 / (2 * INR N1 + 1 + 1)) = 1 / 2 as (E4).
  rewrite E4 in Hb.
  It holds that (N1 + (N1 + 1))%nat ≥ N1 as (Hge1).
  By HCa it holds that
    | partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add N1 (Nat.add N1 1))
      - partial_sums (fun k => 1 / (INR k + 1)) N1 | < 1 / 2 as (Hlt).
  By Rle_abs it holds that
    partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add N1 (Nat.add N1 1))
      - partial_sums (fun k => 1 / (INR k + 1)) N1
    ≤ | partial_sums (fun k : ℕ => 1 / (INR k + 1)) (Nat.add N1 (Nat.add N1 1))
      - partial_sums (fun k => 1 / (INR k + 1)) N1 | as (Habs).
  Contradiction.
Qed.

(** _The p-series_: the series [∑ 1/kᵖ] converges iff [p > 1].

    Proof idea: this follows from the integral test ([integral_test], in
    [Analysis.Integration]) by comparison with [∫ 1/xᵖ dx], which is finite iff
    [p > 1]. (Terms indexed as [1/(k+1)ᵖ]; real exponentiation is [Rpower].) *)
Lemma p_series (p : ℝ) :
    (∃ L : ℝ, partial_sums (fun k => 1 / Rpower (INR k + 1) p) ⟶ L) ⇔ p > 1.
Proof.
  (* Depends on the integral test ([integral_test] in [Analysis.Integration]),
     which is itself still open. *)
  Admitted.
