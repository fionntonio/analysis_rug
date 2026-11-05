(** * RUG.Analysis.Lib.UniformConvergence

  The plan is to move this to the Waterproof library eventually.
*)

Require Import RUG.Analysis.Lib.StdlibReals.

From Waterproof Require Import Tactics.
From Waterproof Require Import Automation.
From Waterproof Require Import Notations.Common.
From Waterproof Require Import Notations.Reals.
From Waterproof Require Import Chains.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

(** * Pointwise and uniform convergence of function sequences

A sequence of functions [fₙ] where each fₙ : ℝ → ℝ converges to
g : ℝ → ℝ:

- pointwise on [A] if for every fixed [x ∈ A] the sequence
  [fₙ(x)] converges to [g(x)];

- uniformly on [A] if the same threshold [N] works for all [x ∈ A].
*)

(** ** Definitions *)

Definition converges_pointwise
    (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) : Prop :=
  ∀ x ∈ A, (fun n ↦ fn n x) ⟶ g x.

Definition converges_uniformly
    (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) : Prop :=
  ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ A, | fn n x - g x | < ε.

(** ** Notations *)

(* Note that these definitions will raise a warning since they share
   the _converges prefactor used for sequences. Scoping should make
   sure that this rarely results in an error though. *)

Notation "fn '_converges' 'pointwise' 'on_' A 'to' g" :=
  (converges_pointwise fn g A) (at level 69).

Notation "fn 'converges' 'pointwise' 'on' A 'to' g" :=
  (converges_pointwise fn g A) (at level 69, only parsing).

Waterproof Register Expand "converges" "pointwise";
  for converges_pointwise;
  as "Definition pointwise convergence".

Notation "fn '_converges' 'uniformly' 'on_' A 'to' g" :=
  (converges_uniformly fn g A) (at level 69).

Notation "fn 'converges' 'uniformly' 'on' A 'to' g" :=
  (converges_uniformly fn g A) (at level 69, only parsing).

Waterproof Register Expand "converges" "uniformly";
  for converges_uniformly;
  as "Definition uniform convergence".

(** ** Basic facts *)

(** Uniform convergence implies pointwise convergence. *)
Lemma uniform_implies_pointwise (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) :
  fn _converges uniformly on_ A to g →
  fn _converges pointwise on_ A to g.
Proof.
  Assume that fn _converges uniformly on_ A to g as (Hunif).
  We need to show that ∀ x ∈ A, (fun n ↦ fn n x) ⟶ g x.
  Take x ∈ A.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | fn n x - g x | < ε.
  Take ε > 0.
  By Hunif it holds that
    ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat → ∀ y ∈ A, | fn n y - g y | < ε as (HN).
  Obtain such an N1.
  We need to show that ∃ N2 ∈ ℕ, ∀ n ≥ N2, |fn(n, x) - g(x)| < ε.
  Choose N2 := N1.
  * Indeed, N2 ∈ ℕ.
  * We need to show that ∀ n ≥ N2, | fn n x - g x | < ε.
    Take n ≥ N2.
    By HN it holds that ∀ y ∈ A, | fn n y - g y | < ε.
    We conclude that | fn n x - g x | < ε.
Qed.

(** The uniform Cauchy criterion (only-if direction):
    if [fₙ] converges uniformly to [g] on [A], then it is uniformly Cauchy. *)
Lemma unif_conv_is_cauchy (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) :
  fn _converges uniformly on_ A to g →
  ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, ∀ m : ℕ,
    (n ≥ N1)%nat → (m ≥ N1)%nat →
    ∀ x ∈ A, | fn n x - fn m x | < ε.
Proof.
  Assume that fn _converges uniformly on_ A to g as (Hunif).
  Take ε > 0.
  It holds that ε / 2 > 0.
  By Hunif it holds that
    ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat → ∀ x ∈ A, | fn n x - g x | < ε / 2 as (HN).
  Obtain such an N1.
  We need to show ∃ N2 ∈ ℕ, ∀ n : ℕ, ∀ m : ℕ, (n ≥ N2)%nat → (m ≥ N2)%nat →
    ∀ x ∈ A, | fn n x - fn m x | < ε.
  Choose N2 := N1.
  * Indeed, N2 ∈ ℕ.
  * We need to show that ∀ n : ℕ, ∀ m : ℕ, (n ≥ N2)%nat → (m ≥ N2)%nat →
      ∀ x ∈ A, | fn n x - fn m x | < ε.
    Take n : ℕ. Take m : ℕ.
    Assume that (n ≥ N2)%nat as (Hn) and (m ≥ N2)%nat as (Hm).
    Take x ∈ A.
    By HN it holds that | fn n x - g x | < ε / 2.
    By HN it holds that | fn m x - g x | < ε / 2.
    We conclude that & | fn n x - fn m x |
                     = | (fn n x - g x) - (fn m x - g x) |
                     ≤ | fn n x - g x | + | fn m x - g x |
                     < ε / 2 + ε / 2
                     = ε.
Qed.

(** If there is an upper bound [bₙ → 0] on [|fₙ(x) - g(x)|]
    that is independent of [x], then [fₙ] converges uniformly to [g] on [A]. *)
Lemma unif_conv_from_bound
    (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : subset ℝ) (b : ℕ → ℝ) :
  (∀ n ∈ ℕ, ∀ x ∈ A, | fn n x - g x | ≤ b n) →
  b ⟶ 0 →
  fn _converges uniformly on_ A to g.
Proof.
  Assume that ∀ n ∈ ℕ, ∀ x ∈ A, | fn n x - g x | ≤ b n as (Hb).
  Assume that b ⟶ 0 as (Hb0).
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ A, | fn n x - g x | < ε.
  Take ε > 0.
  By Hb0 it holds that
    ∃ N1 ∈ ℕ, ∀ n ≥ N1, | b n - 0 | < ε as (HN).
  Obtain such an N1.
  We need to show ∃ N2 ∈ ℕ, ∀ n : ℕ, (n ≥ N2)%nat →
    ∀ x ∈ A, | fn n x - g x | < ε.
  Choose N2 := N1.
  * Indeed, N2 ∈ ℕ.
  * We need to show that ∀ n : ℕ, (n ≥ N2)%nat → ∀ x ∈ A, | fn n x - g x | < ε.
    Take n : ℕ. Assume that (n ≥ N2)%nat.
    Take x ∈ A.
    It holds that | fn n x - g x | ≤ b n as (Hbnd).
    It holds that | b n - 0 | < ε as (Hb_eps).
    (* Here I would like to write
       We conclude that & | fn n x - g x |
                        ≤ b n
                        = | b n - 0 |
                        < ε. 
       However the intermediate step does not seem to be accepted cleanly.
       The codes below are the manual way to do it:
       - the first line uses transitivity of ≤ to replace proving
         |fn(n, x) - g(x)| < ε with proving |fn(n, x) - g(x)| < ε
       - the second line uses the definition of absolute value to replace proving
         |b(n) - 0| < ε with proving |b(n)| < ε
       - the third line uses the fact that |b(n)| = b(n) since b(n) is non-negative
       - finally we apply this to conclude the proof. *)
    apply (Rle_lt_trans _ (b n) _ Hbnd).
    rewrite Rminus_0_r in Hb_eps.
    apply Rabs_def2 in Hb_eps.
    apply Hb_eps.
Qed.

Close Scope subset_scope.
Close Scope R_scope.

