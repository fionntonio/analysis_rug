(** * RUG.Analysis.Subsequences — Monotone convergence and Bolzano-Weierstrass.

  #<a href="../../index.html##lecture04">Lecture 4</a>#.

  Formalizes Abbott §2.4–2.5: the monotone convergence theorem,
  subsequences, the Bolzano-Weierstrass theorem, and Cauchy sequences. *)

(* begin hide *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Reals.SeqProp.
Require Export RUG.Analysis.Sequences.
From Waterproof Require Import Libs.Analysis.Subsequences.
From Waterproof Require Import Libs.Analysis.LimsupLiminfBolzano.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(* end hide *)

(** ** Monotone convergence theorem *)

(** Monotone convergence theorem: a nondecreasing sequence bounded above
    converges, and the limit equals the supremum of its range. This is the key
    lemma enabling [Analysis.Series].

    Proof idea: by the axiom of completeness the range has a supremum [L]. Given
    [ε > 0], [L - ε] is not an upper bound, so some [a_N > L - ε]; monotonicity
    then gives [L - ε < a_N ≤ aₙ ≤ L] for all [n ≥ N], i.e. [|aₙ - L| < ε]. *)
Theorem monotone_convergence (a : ℕ → ℝ)
    (Hbdd : a is _bounded above_)
    (Hmono : ∀ n ∈ ℕ, a n ≤ a (n + 1)%nat) :
    ∃ L ∈ ℝ, a ⟶ L.
Proof.
  Define A := (fun x0 : ℝ => ∃ k : ℕ, x0 = a k).

  We claim that A is bounded from above as (HAbdd).
  {
    We need to show that ∃ M0 ∈ ℝ, M0 is an _upper bound_ for A.
    It holds that ∃ M ∈ ℝ, ∀ n ∈ ℕ, a n ≤ M.
    Obtain such an M.
    Choose (M). { Indeed, M ∈ ℝ. }

    We need to show that M is an _upper bound_ for A.
    We need to show that ∀ x ∈ A, x ≤ M.
    
    Take x ∈ A.
    It holds that ∃ k : ℕ, x = a k.
    Obtain such a k.
    It holds that x = a k.
    It holds that (a k ≤ M).
    We conclude that x ≤ M.
  }

  (** To show that a set is nonempty, it is often easier
      to provide an element of the set. *)
  We claim that a 0%nat ∈ A as (Hnotempty).
  {
    We need to show that ∃ k : ℕ, a 0%nat = a k.
    Choose (0%nat).
    We conclude that a 0%nat = a 0%nat.
  }

  By (R_complete A (a 0%nat) Hnotempty HAbdd) it holds that
    ∃ L ∈ ℝ, L is the _supremum_ of A as (HLsup).
  Obtain such an L.

  By sup_is_upp_bd it holds that
    L is an _upper bound_ for A as (HLup).
  Choose (L). { Indeed, L ∈ ℝ. }
  We need to show that (* a ⟶ L. *)
      ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | a n - L | < ε.

  Take ε > 0.
  By exists_almost_maximizer_ε it holds that
    ∃ y ∈ A, L - ε < y.

  Obtain such a y.
  It holds that y ∈ A.
  It holds that L - ε < y.
  It holds that
    ∃ N1 : ℕ, y = a N1.
  
  Obtain such an N1.
  It holds that y = a N1.
  (** Instead of [Choose N1 := N1], we can keep things more
      concise and just choose N1 directly with [Choose N1]. *)
  Choose (N1). { Indeed, N1 ∈ ℕ. }
  We need to show that ∀ n ≥ N1, | a n - L | < ε.
  
  Take n ≥ N1.
  It suffices to show that -ε < a n - L < ε.
  We show both a n - L < ε and -ε < a n - L.
  - We claim that a n ∈ A.
    {
      We need to show that ∃ k : ℕ, a n = a k.
      Choose k := n.
      We conclude that a n = a k.
    }
    By HLup it holds that a n ≤ L.
    We conclude that a n - L < ε.
  - It holds that L - ε < a N1.
    By nondecr_ge it holds that a N1 ≤ a n.
    We conclude that -ε < a n - L.
Qed.

(** ** Subsequences *)

(** If [a ⟶ L] and [φ] is a strictly increasing index sequence,
    then [(a ∘ φ) ⟶ L]. *)
Lemma subseq_converges (a : ℕ → ℝ) (phi : ℕ → ℕ) (L : ℝ) :
    a ⟶ L → is_index_seq phi → (fun k => a (phi k)) ⟶ L.
Proof.
  Assume that a ⟶ L.
  Assume that is_index_seq phi.
  We need to show that (fun k => a (phi k)) ⟶ L.
  We need to show that
    ∀ ε > 0, ∃ Nm ∈ ℕ, ∀ k ≥ Nm, | a (phi k) - L | < ε.

  Take ε > 0.
  Since (ε > 0) it holds that
    ∃ Nm ∈ ℕ, ∀ n ≥ Nm, | a n - L | < ε as (HNm).
  
  Obtain such an Nm.
  Choose (Nm). { Indeed, Nm ∈ ℕ. }
  We need to show that ∀ k ≥ Nm, | a (phi k) - L | < ε.
  
  Take k ≥ Nm.
  (** [index_seq_grows_0: ∀ n, is_index_seq(n) ⇨ ∀ k, (n(k) ≥ k)%nat] *)
  By index_seq_grows_0 it holds that
    (phi k ≥ k)%nat.
  It holds that (phi k ≥ Nm)%nat.
  We conclude that | a (phi k) - L | < ε.
Qed.

(** ** Bolzano-Weierstrass theorem *)

(** Bolzano–Weierstrass theorem: every bounded sequence has a convergent
    subsequence.

    Proof idea: repeatedly bisect an interval containing the sequence, each time
    keeping a half that contains infinitely many terms. This produces nested
    intervals shrinking to a point [l] and a subsequence converging to [l]. *)
Theorem bolzano_weierstrass (a : ℕ → ℝ) (Hub : has_ub a) (Hlb : has_lb a) :
    ∃ phi : ℕ → ℕ, ∃ l : ℝ,
      is_index_seq phi ∧ (fun k => a (phi k)) ⟶ l.
Proof.
  (** Formalizing the proof of this one completely in Waterproof
      is quite tricky, I am simply relying on the one already
      in Waterproof and calling it a day for the time being. *)
  By Bolzano_Weierstrass we conclude that
    ∃ phi : ℕ → ℕ, ∃ l : ℝ,
      is_index_seq phi ∧ (fun k => a (phi k)) ⟶ l.
Qed.

(** ** Cauchy sequences *)

(** A sequence is Cauchy if its terms eventually cluster arbitrarily close.
    We are going to add some extra syntax to that [is_cauchy a] can
    also be written as [a is _Cauchy_]. *)
Definition is_cauchy (a : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1,
    |a n - a m| < ε.

(* begin hide *)
Notation "a 'is' '_Cauchy_'" := (is_cauchy a) (at level 69).

Waterproof Register Expand "Cauchy";
  for is_cauchy;
  as "Definition Cauchy".

(* end hide *)

(** [is_cauchy] is equivalent to Stdlib's [Cauchy_crit]. *)
Lemma cauchy_crit_equiv (a : ℕ → ℝ) :
    (a is _Cauchy_) ⇔ Cauchy_crit a.
Proof.
  We show both directions.

  - We need to show that a is _Cauchy_
        ⇨ ∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m, (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps.
    Assume that a is _Cauchy_ as (HC).
    Take eps > 0. It holds that eps > 0.
    It holds that
      ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a(n) - a(m)| < eps as (H').
    Obtain such a N1. Choose (N1).
    Take n : ℕ. Take m : ℕ. 
    Assume that (n ≥ N1)%nat as (Hn) and (m ≥ N1)%nat as (Hm).
    By H' we conclude that ｜a(n) - a(m)｜ < eps.

  - We need to show that (∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m,
          (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps)
        ⇨ a is _Cauchy_.
    Assume that ∀ eps, eps > 0 ⇨ ∃ N, ∀ n, ∀ m,
          (n ≥ N)%nat ⇨ (m ≥ N)%nat ⇨ ｜a(n) - a(m)｜ < eps as (HC).
    We need to show that
      ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε.
    Take ε > 0.
    By HC it holds that
      ∃ N1, ∀ n, ∀ m, (n ≥ N1)%nat ⇨ (m ≥ N1)%nat ⇨ ｜a(n) - a(m)｜ < ε.
    Obtain such a N1.
    Choose N2 := N1%nat. { Indeed, N2 ∈ ℕ. }
    We need to show that
      ∀ n ≥ N2, ∀ m ≥ N2, |a(n) - a(m)| < ε.
    Take n ≥ N2. Take m ≥ N2.
    By HC we conclude that |a(n) - a(m)| < ε.
Qed.

(** Every Cauchy sequence is bounded. *)
Theorem cauchy_is_bounded (a : ℕ → ℝ) : a is _Cauchy_ → a is _bounded_.
Proof.
  Assume that a is _Cauchy_ as (HC).
  It holds that
    ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, |a n - a m| < ε as (HC').
  We need to show that a is _bounded_.
  By is_bounded_equivalence it holds that
    (is_bounded a ⇔ is_bounded_equivalent a) as (Hequiv).
  By Hequiv it suffices to show that is_bounded_equivalent a.
  We need to show that
    ∃ M > 0, ∀ n ∈ ℕ, | a n | ≤ M.
  By HC it holds that
    ∃ N1 ∈ ℕ, ∀ n ≥ N1, ∀ m ≥ N1, | a n - a m | < 1.
  Obtain such a N1.

  We claim that Cauchy_crit a as (HCr).
  { 
    By cauchy_crit_equiv it holds that a is _Cauchy_ ⇔ Cauchy_crit a.
    It suffices to show that a is _Cauchy_.
    By HC we conclude that a is _Cauchy_.
  }
  
  (** This EUn(a) is the Rocq Stdlib way of denoting the set
      of all elements of the sequence a. *)
  We claim that ∃ UB : ℝ, is_upper_bound (EUn a) UB.
  {
    (** From the StdLib
        [cauchy_maj: ∀ Un, Cauchy_crit(Un) ⇨ has_ub(Un)]
        
        Which means that every Cauchy sequence has an upper bound.
    *)
    By cauchy_maj it holds that has_ub a.
    It holds that ∃ m, m is an _upper bound_ for EUn(a).
    Obtain such an m. Choose (m).
    We conclude that m is an _upper bound_ for EUn(a).
  }
  
  Obtain such a UB.
  It holds that (is_upper_bound (EUn a) UB) as (HUB).
  We claim that ∀ n ∈ ℕ, a n ≤ UB.
  {
    Take n ∈ ℕ.
    We claim that EUn a (a n) as (Heun).
    {
      We need to show that ∃ k : ℕ, a n = a k.
      Choose k := n. We conclude that a n = a k.
    }
    By HUB we conclude that a n ≤ UB.
  }

  We claim that ∃ LB : ℝ, is_upper_bound (EUn (opp_seq a)) LB.
  { 
    By cauchy_min it holds that has_lb a.
    (** By definition of [has_lb a]: -a has an upper bound *)
    It holds that ∃ l, l is an _upper bound_ for EUn (opp_seq a).
    Obtain such an l. Choose (l). 
    We conclude that l is an _upper bound_ for EUn (opp_seq a).
  }

  Obtain such a LB.
  It holds that
    (is_upper_bound (EUn (opp_seq a)) LB) as (HLB).
  
  We claim that ∀ n ∈ ℕ, -LB ≤ a n.
  {
    Take n ∈ ℕ.
    We claim that EUn (opp_seq a) (- a n).
    { 
      We need to show that
        ∃ k : ℕ, - a n = opp_seq a k.
      Choose k := n.
      We conclude that - a n = opp_seq a k.
    }
    By HLB it holds that - a n ≤ LB.
    We conclude that -LB ≤ a n.
  }

  Choose M := (Rabs UB + Rabs LB + 1). { Indeed, M > 0. }
  
  We need to show that ∀ n ∈ ℕ,
    | a n | ≤ Rabs UB + Rabs LB + 1.
  Take n ∈ ℕ.
  It holds that (a n ≤ UB).
  It holds that (-LB ≤ a n).
  By Rle_abs it holds that UB ≤ Rabs UB.
  By Rle_abs it holds that LB ≤ Rabs LB.
  By Rle_abs it holds that -LB ≤ Rabs (-LB).
  By Rabs_Ropp it holds that (Rabs (-LB) = Rabs LB).

  We conclude that | a n | ≤ Rabs UB + Rabs LB + 1.
Qed.
