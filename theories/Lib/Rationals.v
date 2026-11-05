(** * RUG.Analysis.Lib.Rationals

  Auxiliary facts about rational numbers, viewed as a subset of the reals.
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

(** A real number is *rational* if it can be written [p/q] with [q ≠ 0]. *)
Definition is_rational (x : ℝ) : Prop :=
    ∃ p : Z, ∃ q : Z, (q <> 0)%Z ∧ x = IZR p / IZR q.

(** The difference of two rationals is rational.

    Proof idea: [p₁/q₁ - p₂/q₂ = (p₁q₂ - p₂q₁)/(q₁q₂)]. *)
Lemma rational_sub (x y : ℝ) :
    is_rational x → is_rational y → is_rational (x - y).
Proof.
  Assume that is_rational x as (Hx).
  Assume that is_rational y as (Hy).
  By Hx it holds that
    ∃ p1 : Z, ∃ q1 : Z, (q1 <> 0)%Z ∧ x = IZR p1 / IZR q1 as (Hx1).
  Obtain p1 according to (Hx1).
  It holds that ∃ q1 : Z, (q1 <> 0)%Z ∧ x = IZR p1 / IZR q1 as (Hx2).
  Obtain q1 according to (Hx2).
  By Hy it holds that
    ∃ p2 : Z, ∃ q2 : Z, (q2 <> 0)%Z ∧ y = IZR p2 / IZR q2 as (Hy1).
  Obtain p2 according to (Hy1).
  It holds that ∃ q2 : Z, (q2 <> 0)%Z ∧ y = IZR p2 / IZR q2 as (Hy2).
  Obtain q2 according to (Hy2).
  It holds that (q1 <> 0)%Z as (Hq1).
  It holds that (q2 <> 0)%Z as (Hq2).
  It holds that x = IZR p1 / IZR q1 as (Hxe).
  It holds that y = IZR p2 / IZR q2 as (Hye).
  By (eq_IZR_contrapositive q1 0%Z Hq1) it holds that IZR q1 ≠ 0.
  By (eq_IZR_contrapositive q2 0%Z Hq2) it holds that IZR q2 ≠ 0.
  We need to show that
    ∃ p : Z, ∃ q : Z, (q <> 0)%Z ∧ x - y = IZR p / IZR q.
  Choose p := (p1 * q2 - p2 * q1)%Z.
  Choose q := (q1 * q2)%Z.
  It holds that (q1 * q2 <> 0)%Z as (Hq).
  By minus_IZR it holds that
    IZR (p1 * q2 - p2 * q1)%Z = IZR (p1 * q2)%Z - IZR (p2 * q1)%Z.
  By mult_IZR it holds that IZR (p1 * q2)%Z = IZR p1 * IZR q2.
  By mult_IZR it holds that IZR (p2 * q1)%Z = IZR p2 * IZR q1.
  By mult_IZR it holds that IZR (q1 * q2)%Z = IZR q1 * IZR q2.
  It holds that
    IZR p1 / IZR q1 - IZR p2 / IZR q2
    = (IZR p1 * IZR q2 - IZR p2 * IZR q1) / (IZR q1 * IZR q2).
  It holds that x - y = IZR p / IZR q as (Heq).
  We conclude that (q <> 0)%Z ∧ x - y = IZR p / IZR q.
Qed.

(** [1/(n+1)] is rational.

    Proof idea: take numerator [1] and denominator [n+1]. *)
Lemma rational_inv_succ (n : ℕ) : is_rational (1 / (INR n + 1)).
Proof.
  We need to show that
    ∃ p : Z, ∃ q : Z, (q <> 0)%Z ∧ 1 / (INR n + 1) = IZR p / IZR q.
  Choose p := 1%Z.
  Choose q := Z.of_nat (S n).
  It holds that (Z.of_nat (S n) <> 0)%Z as (Hq).
  By INR_IZR_INZ it holds that INR (S n) = IZR (Z.of_nat (S n)).
  By S_INR it holds that INR (S n) = INR n + 1.
  It holds that 1 / (INR n + 1) = IZR p / IZR q as (Heq).
  We conclude that (q <> 0)%Z ∧ 1 / (INR n + 1) = IZR p / IZR q.
Qed.
