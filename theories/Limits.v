(** * RUG.Analysis.Limits — Functional limits (ε-δ definition).

  #<a href="../../index.html##lecture08">Lecture 8</a>#.

  Formalizes Abbott §4.2: the ε-δ definition of [lim_{x→c} f(x) = L],
  uniqueness of limits, algebraic limit theorem for functions, and
  the sequential characterization of functional limits. *)

(* begin hide *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import micromega.Lra.
From Waterproof Require Export Notations.Common.
From Waterproof Require Export Notations.Reals.
From Waterproof Require Export Notations.Sets.
From Waterproof Require Import Libs.Analysis.ContinuityDomainR.
Require Export RUG.Analysis.Sequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(* This is to avoid an annoying warning.
   We should make this use possible, it gives a noticeable speedup. *)
Set Warnings "-non-reference-hint-using".

(* end hide *)

(** ** The ε–δ definition of a functional limit

    For [f : A → ℝ] and [c] a limit point of [A], we write [lim_{x→c} f(x) = L]
    when
    [∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, 0 < |x - c| < δ ⇒ |f(x) - L| < ε].

    In Waterproof this is written [_limit_ of f in c is L]. Note that the value
    [f(c)] need not be defined or equal to [L]. *)

(** ** A linear function has a limit

    Theorem: [lim_{x→2} (3x - 1) = 5].

    Proof strategy: apply the ε–δ definition. Since
    [|f(x) - 5| = |(3x - 1) - 5| = |3x - 6| = 3|x - 2|], if [|x - 2| < δ] then
    [|f(x) - 5| < 3δ]. Choosing [δ = ε/3] makes [|f(x) - 5| < ε]. *)
Lemma limit_linear_example :
    _limit_ of (fun x => 3 * x - 1) in 2 is 5.
Proof.
  We need to show that
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - 2| < δ ⇒ |(3 * x - 1) - 5| < ε.
  Take ε > 0.
  Choose δ := ε / 3. { Indeed, δ > 0. }
  We need to show that
    ∀ x ∈ ℝ, 0 < |x - 2| < δ ⇒ |(3 * x - 1) - 5| < ε.
  Take x ∈ ℝ. Assume that 0 < |x - 2| < δ as (Hx).
  
  It holds that |x - 2| < ε / 3.
  We claim that |(3 * x - 1) - 5| = 3 * |x - 2|.
  {
    It holds that (3 * x - 1) - 5 = 3 * (x - 2).
    It suffices to show that |3 * (x - 2)| = 3 * |x - 2|.
    We conclude that |3 * (x - 2)| = 3 * |x - 2|.
  }
  
  We conclude that |(3 * x - 1) - 5| < ε.
Qed.

(** ** Algebraic limit theorem: sum of limits

    Theorem: if [lim_{x→c} f(x) = L] and [lim_{x→c} g(x) = M], then
    [lim_{x→c} (f + g)(x) = L + M].

    Proof strategy: given [ε > 0], apply the limit definitions for [f] and [g]
    with [ε/2] to obtain [δ₁] and [δ₂]. Taking [δ = min(δ₁, δ₂)] ensures that
    both [|f(x) - L| < ε/2] and [|g(x) - M| < ε/2] hold whenever [0 < |x - c| < δ].
    The triangle inequality then gives [|(f + g)(x) - (L + M)| < ε]. *)

(** The function is named [f'] rather than [f]: in Waterproof's natural-language
    statements a bare [f] resolves to the global [Stdlib.Reals.Rtopology.f], so
    an applied function argument must avoid that exact identifier. *)
Lemma functional_limit_sum (f' g : ℝ → ℝ) (c L M : ℝ)
    (Hf : _limit_ of f' in c is L)
    (Hg : _limit_ of g in c is M) :
    _limit_ of (fun x => f' x + g x) in c is (L + M).
Proof.
  We need to show that
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ
    ⇒ |(f' x + g x) - (L + M)| < ε.
  
  Take ε > 0.
  It holds that ε / 2 > 0.
  By Hf it holds that
    ∃ δ1 > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ1
    ⇒ |f' x - L| < ε / 2
  as (Hf').
  
  Obtain such a δ1.
  By Hg it holds that
    ∃ δ2 > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ2
    ⇒ |g x - M| < ε / 2
  as (Hg').

  Obtain such a δ2.
  Choose δ := Rmin δ1 δ2. { Indeed, δ > 0. }
  We need to show that
      ∀ x ∈ ℝ, 0 < |x - c| < δ
      ⇨ |(f' x + g x) - (L + M)| < ε.
  Take x ∈ ℝ. Assume that 0 < |x - c| < δ as (Hx).
  
  By Rmin_l it holds that Rmin δ1 δ2 ≤ δ1.
  By Rmin_r it holds that Rmin δ1 δ2 ≤ δ2.
  It holds that 0 < |x - c| < δ1.
  It holds that 0 < |x - c| < δ2.
  
  By Hf' it holds that |f' x - L| < ε / 2 as (HfL).
  By Hg' it holds that |g x - M| < ε / 2 as (HgM).
  
  By Rabs_triang, HfL and HgM it holds that &
    |(f' x - L) + (g x - M)|
    ≤ |f' x - L| + |g x - M|
    < ε.

  It holds that
    (f' x + g x) - (L + M) = (f' x - L) + (g x - M).

  We conclude that |(f' x + g x) - (L + M)| < ε.
Qed.

(** If [lim_{x→c} f(x) = L] and [lim_{x→c} g(x) = M], then
    [lim_{x→c} (f · g)(x) = L · M]. *)
Lemma lim_product (f' g : ℝ → ℝ) (c L M : ℝ)
    (Hf : _limit_ of f' in c is L)
    (Hg : _limit_ of g in c is M) :
    _limit_ of (fun x => f' x * g x) in c is (L * M).
Proof.
  We need to show that
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ
    ⇒ |(f' x * g x) - (L * M)| < ε.
  
  Take ε > 0.
  It holds that |L| + 1 > 0 as (HL1).
  It holds that |M| + 1 > 0 as (HM1).

  (** The next two lines are only useful to speed up the checker. *)
  It holds that / (2 * (|M| + 1)) > 0.
  It holds that / (2 * (|L| + 1)) > 0.
  It holds that ε / (2 * (|M| + 1)) > 0 as (HbM).
  It holds that ε / (2 * (|L| + 1)) > 0 as (HbL).
  
  (** Near [c], [f'] is bounded:
      [|f' x - L| < 1] forces [|f' x| < |L| + 1]. *)
  It holds that
    ∃ δ0 > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ0
    ⇒ |f' x - L| < 1
  as (Hfbd).
  
  Obtain such a δ0.
  It holds that
    ∃ δ1 > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ1
    ⇒ |f' x - L| < ε / (2 * (|M| + 1))
  as (HfM).
  
  Obtain such a δ1.
  It holds that
    ∃ δ2 > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ2
    ⇒ |g x - M| < ε / (2 * (|L| + 1))
  as (HgL).
  
  Obtain such a δ2.
  Choose δ := Rmin δ0 (Rmin δ1 δ2). { Indeed, δ > 0. }
  We need to show that
    ∀ x ∈ ℝ, 0 < |x - c| < δ
    ⇨ |(f' x * g x) - (L * M)| < ε.
  
  Take x ∈ ℝ. Assume that 0 < |x - c| < δ.
  By Rmin_l it holds that Rmin δ0 (Rmin δ1 δ2) ≤ δ0.
  By Rmin_r it holds that Rmin δ0 (Rmin δ1 δ2) ≤ Rmin δ1 δ2 as (Hmr).
  By Rmin_l it holds that Rmin δ1 δ2 ≤ δ1.
  By Rmin_r it holds that Rmin δ1 δ2 ≤ δ2.
  
  It holds that 0 < |x - c| < δ0.
  It holds that 0 < |x - c| < δ1.
  It holds that 0 < |x - c| < δ2.
  
  By Hfbd it holds that |f' x - L| < 1 as (Hb0).
  By HfM it holds that
    |f' x - L| < ε / (2 * (|M| + 1)).
  By HgL it holds that
    |g x - M| < ε / (2 * (|L| + 1)).
  
  By Rabs_triang_inv it holds that
    |f' x| - |L| ≤ |f' x - L|.

  It holds that |f' x| ≤ |L| + 1.
  It holds that |f' x| ≥ 0.
  It holds that |g x - M| ≥ 0.
  It holds that |f' x - L| ≥ 0.
  
  We claim that ∀ A ∈ ℝ,
    (|A| + 1) * (ε / (2 * (|A| + 1))) = ε / 2
  as (Heps2).
  { 
    Take A ∈ ℝ.
    It holds that |A| ≥ 0.
    It holds that |A| + 1 > 0.
    It holds that |A| + 1 ≠ 0.

    It holds that
      (|A| + 1) * (ε / (2 * (|A| + 1)))
      = (|A| + 1) * ε / (2 * (|A| + 1)).
    It holds that
      (|A| + 1) * ε / (2 * (|A| + 1))
      = ε * (|A| + 1) / (2 * (|A| + 1)).
    It holds that
      ε * (|A| + 1) / (2 * (|A| + 1))
      = ε * (|A| + 1) / ((|A| + 1) * 2).
    It holds that
      (|A| + 1) * (ε / (2 * (|A| + 1)))
      = ε * (|A| + 1) / ((|A| + 1) * 2).
    
    It suffices to show that
      ε * (|A| + 1) / ((|A| + 1) * 2) = ε / 2.

    By Rdiv_mult_r_l we conclude that
      ε * (|A| + 1) / ((|A| + 1) * 2)
      = ε / 2.
  }

  By Heps2 it holds that
    (|L| + 1) * (ε / (2 * (|L| + 1))) = ε / 2.
  By Heps2 it holds that
    (|M| + 1) * (ε / (2 * (|M| + 1))) = ε / 2.
    
  (** Split the error using
      [f'·g - L·M = f'·(g - M) + M·(f' - L)]. *)
  We claim that
    |(f' x * g x) - (L * M)|
    ≤ |f' x| * |g x - M| + |M| * |f' x - L|.
  { 
    It holds that
      (f' x * g x) - (L * M)
      = f' x * (g x - M) + M * (f' x - L).
    It holds that
      | (f' x * g x) - (L * M) |
      = | f' x * (g x - M) + M * (f' x - L)|.

    By Rabs_triang it holds that
      |f' x * (g x - M) + M * (f' x - L)|
        ≤ |f' x * (g x - M)| + |M * (f' x - L)|.
    By Rabs_mult it holds that
      |f' x * (g x - M)| = |f' x| * |g x - M|.
    By Rabs_mult it holds that
      |M * (f' x - L)| = |M| * |f' x - L|.

    We conclude that
      |(f' x * g x) - (L * M)|
      ≤ |f' x| * |g x - M| + |M| * |f' x - L|.
  }

  We claim that |f' x| * |g x - M| < ε / 2.
  {
    By Rmult_le_compat_r it holds that
      |f' x| * |g x - M| 
      ≤ (|L| + 1) * |g x - M|.
    By Rmult_lt_compat_l it holds that
      (|L| + 1) * |g x - M|
      < (|L| + 1) * (ε / (2 * (|L| + 1))).
    We conclude that |f' x| * |g x - M| < ε / 2.
  }
  We claim that |M| * |f' x - L| ≤ ε / 2.
  {
    By Rmult_le_compat_l it holds that
      |M| * |f' x - L| ≤ |M| * (ε / (2 * (|M| + 1))).
    By Rmult_le_compat_r it holds that
      |M| * (ε / (2 * (|M| + 1))) ≤ (|M| + 1) * (ε / (2 * (|M| + 1))).
    We conclude that |M| * |f' x - L| ≤ ε / 2.
  }
  
  We conclude that |(f' x * g x) - (L * M)| < ε.
Qed.

(** If [lim_{x→c} f(x) = L] and [lim_{x→c} g(x) = M] with [M ≠ 0], then
    [lim_{x→c} (f / g)(x) = L / M].

    Proof strategy: as for sequences, since [M ≠ 0] the quotient is controlled
    near [c] where [g] stays away from [0]; combine with the product and sum
    rules applied to [f · (1/g)]. *)

(** Inverse of a functional limit: if [lim_{x→c} g(x) = M ≠ 0] then
    [lim_{x→c} 1/g(x) = 1/M]. Near [c] the values [g x] stay bounded away from
    [0] (namely [|g x| > |M|/2]), and then
    [|1/g x - 1/M| = |g x - M| / (|g x|·|M|) < |g x - M| · 2/|M|²]. *)
Lemma inv_limit_fun (g : ℝ → ℝ) (c M : ℝ) (HM : M ≠ 0)
    (Hg : _limit_ of g in c is M) :
    _limit_ of (fun x => / g x) in c is (/ M).
Proof.
  It holds that | M | > 0.
  It holds that | M | / 2 > 0.

  We need to show that
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ,
    0 < |x - c| < δ ⇒ |(/ g x) - (/ M)| < ε.
  
  Take ε > 0.
  It holds that ε * (| M | * | M | / 2) > 0.
  
  It holds that
    ∃ δ1 > 0, ∀ x ∈ ℝ,
    0 < |x - c| < δ1 ⇒ |g x - M| < | M | / 2
  as (H1).

  Obtain such a δ1.
  It holds that
    ∃ δ2 > 0, ∀ x ∈ ℝ,
    0 < |x - c| < δ2 
    ⇒ |g x - M| < ε * (| M | * | M | / 2)
  as (H2).
  Obtain such a δ2.

  Choose δ := Rmin δ1 δ2. { Indeed, δ > 0. }
  We need to show that
      ∀ x ∈ ℝ, 0 < |x - c| < δ
      ⇨ |(/ g x) - (/ M)| < ε.
  Take x ∈ ℝ. Assume that 0 < |x - c| < δ.

  By Rmin_l it holds that Rmin δ1 δ2 ≤ δ1.
  By Rmin_r it holds that Rmin δ1 δ2 ≤ δ2.
  It holds that 0 < |x - c| < δ1.
  It holds that 0 < |x - c| < δ2.

  By H1 it holds that |g x - M| < | M | / 2.
  By H2 it holds that |g x - M| < ε * (| M | * | M | / 2).
  By Rabs_triang_inv it holds that | M | - |g x| ≤ | M - g x |.
  By Rabs_minus_sym it holds that | M - g x | = |g x - M| as (Habs).
  It holds that |g x| > | M | / 2.
  It holds that |g x| > 0 as (Hgt0).
  By Rmult_gt_0_compat it holds that |g x| * | M | > 0.
  
  By Hgt0 it holds that g x ≠ 0.
  It holds that / g x * g x = 1.
  It holds that / M * M = 1.

  It holds that (/ g x - / M) * (g x * M) = M - g x as (Hmulsimp).

  We claim that
    |(/ g x) - (/ M)| * (|g x| * | M |) = |g x - M|
  as (Hmul).
  {
    By Rabs_mult it holds that
      |(/ g(x) - / M) * (g(x) * M)|
      = |/ g x - / M| * |g x * M |
    as (Hstep1).
    By Rabs_mult it holds that
      |g x * M| = |g x| * | M |
    as (Hstep2).
    
    (** We can do
        [ By Hstep1 and Hstep2 it suffices to show that
          |(/ g(x) - / M) * (g(x) * M)| = |g x - M|.]
        but it is really slow. The following rewrites achieve
        the same and are nearly instantaneous. *)
    rewrite <- Rabs_mult. rewrite <- Rabs_mult.

    (** I would like to replace this [rewrite] into a
        [By Habs it suffices to show ...] but it seems to 
        get stuck. *)
    rewrite <- Habs.

    By Hmulsimp we conclude that
      |(/ g(x) - / M) * (g(x) * M)| = |M - g x|.
  }

  It holds that
    ε * (|g x| * | M |) > ε * ((| M | / 2) * | M |).
  It holds that |g x - M| < ε * (|g x| * | M |).

  By Hmul it holds that
    |/ g(x) - / M| * (|g x| * |M|) < ε * (|g x| * |M|).

  By Rmult_lt_reg_r (|g x| * |M|) we conclude that
    |(/ g x) - (/ M)| < ε.
Qed.

Lemma lim_quotient (f' g : ℝ → ℝ) (c L M : ℝ) (HM : M ≠ 0)
    (Hf : _limit_ of f' in c is L)
    (Hg : _limit_ of g in c is M) :
    _limit_ of (fun x => f' x / g x) in c is (L / M).
Proof.
  By inv_limit_fun it holds that
    _limit_ of (fun x => / g x) in c is (/ M).
  By lim_product it holds that
    _limit_ of (fun x => f' x * / g x) in c is (L * / M).
  We conclude that _limit_ of (fun x => f' x / g x) in c is (L / M).
Qed.

(** ** Sequential characterization *)

(** Forward direction:
    if [lim_{x→c} f'(x) = L] and [(aₙ) → c] with [aₙ ≠ c],
    then [f'(aₙ) → L]. *)
Lemma functional_limit_imp_seq (f' : ℝ → ℝ) (c L : ℝ) (a : ℕ → ℝ) :
    _limit_ of f' in c is L →
    (∀ n ∈ ℕ, a n ≠ c) → a ⟶ c →
    (fun n => f' (a n)) ⟶ L.
Proof.
  Assume that _limit_ of f' in c is L as (Hf).
  Assume that ∀ n ∈ ℕ, a n ≠ c as (Hne).
  Assume that a ⟶ c.
  
  We need to show that
    ∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, | f' (a n) - L | < ε.
  
  Take ε > 0.
  By Hf it holds that
    ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |f' x - L| < ε
  as (Hd).
  
  Obtain such a δ.
  It holds that δ > 0.
  Since δ > 0 it holds that
    ∃ Nn ∈ ℕ, ∀ n ≥ Nn, | a n - c | < δ
  as (HN).
  
  Obtain such a Nn.
  Choose (Nn). { Indeed, Nn ∈ ℕ. }
  We need to show that
    ∀ n ≥ Nn, | f' (a n) - L | < ε.
  
  Take n ≥ Nn.
  By HN it holds that | a n - c | < δ.
  By Hne it holds that a n ≠ c as (Hne_n).
  By Hne_n it holds that | a n - c | > 0.

  It holds that 0 < | a n - c | < δ.
  
  By Hd we conclude that | f' (a n) - L | < ε.
Qed.

(** [lim_{x→c} f(x) = L] iff for every sequence [(xₙ) → c] with [xₙ ≠ c],
    [f(xₙ) → L]. The forward direction is [functional_limit_imp_seq]; the
    backward direction requires building a witness sequence by choosing a
    counterexample point for each [δ = 1/n], which needs a form of the axiom of
    (dependent) choice not available in the pure Waterproof fragment, so it is
    left admitted here. *)
Lemma sequential_limit_characterization (f : ℝ → ℝ) (c L : ℝ) :
    (_limit_ of f in c is L) ⇔
    (∀ a : ℕ → ℝ,
      (∀ n ∈ ℕ, a n ≠ c) → a ⟶ c → (fun n => f (a n)) ⟶ L).
Proof.
  Admitted.

(** ** Divergence criterion *)

(** If two sequences approaching [c] give different limits for [f], then
    [lim_{x→c} f(x)] does not exist. *)
Lemma divergence_criterion (f' : ℝ → ℝ) (c : ℝ)
    (a b : ℕ → ℝ) (L M : ℝ) (HLM : L ≠ M)
    (Ha_ne : ∀ n ∈ ℕ, a n ≠ c) (Ha : a ⟶ c)
    (Hb_ne : ∀ n ∈ ℕ, b n ≠ c) (Hb : b ⟶ c)
    (Hfa : (fun n => f' (a n)) ⟶ L)
    (Hfb : (fun n => f' (b n)) ⟶ M) :
    ¬ (∃ L' : ℝ, _limit_ of f' in c is L').
Proof.
  We argue by contradiction.
  Assume that ¬ ¬ (∃ L', _limit_ of f' in c is L').
  It holds that ∃ L' : ℝ, _limit_ of f' in c is L'.
  
  Obtain such a L'.
  By functional_limit_imp_seq it holds that
    (fun n => f' (a n)) ⟶ L'
  as (Hfa').
  By functional_limit_imp_seq it holds that
    (fun n => f' (b n)) ⟶ L'
  as (Hfb').

  By limit_unique (fun n => f' (a n)) L L' it holds that L = L'.
  By limit_unique (fun n => f' (b n)) M L' it holds that M = L'.
  It holds that L = M.
  Contradiction.
Qed.

(** ** Absolute value is continuous

    Theorem: the function [f(x) = |x|] is continuous at every point [c ∈ ℝ].

    Proof strategy: use the key inequality [||x| - |c|| ≤ |x - c|], which follows
    from the reverse triangle inequality. For any [ε > 0], taking [δ = ε] ensures
    that [|x - c| < δ] implies [||x| - |c|| < ε]. *)
Lemma abs_continuous (c : ℝ) :
    _limit_ of Rabs in c is (Rabs c).
Proof.
  We need to show that
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |Rabs x - Rabs c| < ε.
  Take ε > 0.
  Choose δ := ε. { Indeed, δ > 0. }
  We need to show that
    ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |Rabs x - Rabs c| < ε.
  Take x ∈ ℝ. Assume that 0 < |x - c| < δ.
  By Rabs_triang_inv it holds that Rabs x - Rabs c ≤ |x - c|.
  By Rabs_triang_inv it holds that Rabs c - Rabs x ≤ |c - x|.
  It holds that |c - x| = |x - c|.
  We conclude that |Rabs x - Rabs c| < ε.
Qed.

(** ** Unfolding the limit definition

    Lemma: if [lim_{x→c} f(x) = L], then for every [ε > 0] there exists [δ > 0]
    such that for all [x] with [0 < |x - c| < δ] we have [|f(x) - L| < ε].

    Proof: this is a direct unfolding of the limit definition. *)
Lemma limit_epsilon_delta (f : ℝ → ℝ) (c L : ℝ)
    (Hf : _limit_ of f in c is L) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |f x - L| < ε.
Proof.
  (** This is precisely the definition of [limit_in_point], so the hypothesis
      [Hf] discharges the goal directly. Can you prove it step by step? *)
  exact Hf.
Qed.
