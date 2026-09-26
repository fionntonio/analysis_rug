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

