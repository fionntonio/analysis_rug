(** * RUG.Analysis.Lib.Integers

  Auxiliary facts about the integers used in the analysis files.
*)

Require Import RUG.Analysis.Lib.StdlibReals.

From Waterproof Require Import Tactics.
From Waterproof Require Import Automation.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Notations.Sets.
From Waterproof Require Import Chains.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** No nonzero integer square is twice another square: [p² ≠ 2q²] for [q ≠ 0].

    Proof idea: infinite descent, by induction on a bound [m ≥ |q|]. From
    [p² = 2q²], [p] is even, [p = 2k], so [q² = 2k²]; then [q = 2l] and
    [k² = 2l²] with [0 < |l| < |q|], contradicting the induction hypothesis. *)
Lemma no_square_double :
    ∀ m ∈ ℕ, ∀ p : Z, ∀ q : Z,
      (Z.abs q <= Z.of_nat m)%Z → (q ≠ 0)%Z → (p * p ≠ 2 * (q * q))%Z.
Proof.
  We use induction on m.
  - We first show the base case
      (∀ p : Z, ∀ q : Z,
        (Z.abs q <= Z.of_nat 0)%Z → (q ≠ 0)%Z → (p * p ≠ 2 * (q * q))%Z).
    Take p : Z. Take q : Z.
    Assume that (Z.abs q <= Z.of_nat 0)%Z as (Hq).
    Assume that (q ≠ 0)%Z as (Hq0).
    By Z.abs_nonneg it holds that (0 <= Z.abs q)%Z.
    It holds that (q = 0)%Z.
    Contradiction.
  - We now show the induction step.
    Take m ∈ ℕ.
    Assume that
      ∀ p : Z, ∀ q : Z,
        (Z.abs q <= Z.of_nat m)%Z → (q ≠ 0)%Z → (p * p ≠ 2 * (q * q))%Z
      as (IH).
    Take p : Z. Take q : Z.
    Assume that (Z.abs q <= Z.of_nat (m + 1)%nat)%Z as (Hq).
    Assume that (q ≠ 0)%Z as (Hq0).
    Assume that (p * p = 2 * (q * q))%Z as (Hpq).
    By Z.even_mul it holds that
      Z.even (p * p)%Z = (Z.even p || Z.even p)%bool.
    By Z.even_mul it holds that
      Z.even (2 * (q * q))%Z = (Z.even 2 || Z.even (q * q)%Z)%bool.
    It holds that Z.even (2 * (q * q))%Z = true.
    By Bool.orb_diag it holds that (Z.even p || Z.even p)%bool = Z.even p.
    It holds that Z.even (p * p)%Z = Z.even (2 * (q * q))%Z.
    It holds that Z.even p = true as (Hp_even).
    By (Z.even_spec p) it holds that (Z.even p = true ⇔ Z.Even p) as (Hspec_p).
    By Hspec_p it holds that Z.Even p as (Hp_Even).
    By Hp_Even it holds that ∃ k : Z, (p = 2 * k)%Z as (Hk).
    Obtain k according to (Hk).
    It holds that (q * q = 2 * (k * k))%Z as (Hqk).
    By Z.even_mul it holds that
      Z.even (q * q)%Z = (Z.even q || Z.even q)%bool.
    By Z.even_mul it holds that
      Z.even (2 * (k * k))%Z = (Z.even 2 || Z.even (k * k)%Z)%bool.
    It holds that Z.even (2 * (k * k))%Z = true.
    By Bool.orb_diag it holds that (Z.even q || Z.even q)%bool = Z.even q.
    It holds that Z.even (q * q)%Z = Z.even (2 * (k * k))%Z.
    It holds that Z.even q = true as (Hq_even).
    By (Z.even_spec q) it holds that (Z.even q = true ⇔ Z.Even q) as (Hspec_q).
    By Hspec_q it holds that Z.Even q as (Hq_Even).
    By Hq_Even it holds that ∃ l : Z, (q = 2 * l)%Z as (Hl).
    Obtain l according to (Hl).
    It holds that (k * k = 2 * (l * l))%Z as (Hkl).
    It holds that (l ≠ 0)%Z as (Hl0).
    It holds that (Z.abs l <= Z.of_nat m)%Z as (Hl_bound).
    By (IH k l Hl_bound Hl0) it holds that (k * k ≠ 2 * (l * l))%Z.
    Contradiction.
Qed.
