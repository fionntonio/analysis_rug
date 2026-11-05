(** * RUG.Analysis.Integration — The Riemann integral.

  #<a href="../../index.html##lecture13">Lecture 13</a># and #<a href="../../index.html##lecture14">Lecture 14</a>#.

  Formalizes Abbott §7.2–7.4: partitions and Darboux (upper/lower) sums, the
  refinement lemmas, the upper and lower integrals, the Riemann/Darboux
  criterion for integrability, integrability of continuous and of monotone
  functions, and the basic algebraic properties (linearity, monotonicity,
  additivity over intervals), and the interchange of limit and integral for
  uniformly convergent sequences of functions (Abbott 7.2.5). *)

Require Import RUG.Analysis.Lib.StdlibReals.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.ConstructiveEpsilon.
Require Export RUG.Analysis.Continuity.
Require Import RUG.Analysis.FunctionSequences.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Partitions and Darboux sums

    We build the Riemann integral from Darboux's upper and lower sums, following
    Abbott §7.2. Alongside this "from scratch" development we also reuse the
    Stdlib predicate [Riemann_integrable] and its integral [RiemannInt] for the
    algebraic property lemmas at the end of the file. *)

(** A *partition* of [[a, b]] into [n] cells is a strictly increasing sequence
    of [n + 1] nodes [x₀ = a < x₁ < ⋯ < xₙ = b]. We represent the nodes by a
    function [x : ℕ → ℝ], using only the indices [0 … n]. *)
Definition is_partition (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
    x 0%nat = a ∧ x n = b ∧ (∀ i ∈ ℕ, (i < n)%nat → x i < x (S i)).

(** [mi] is the *infimum* of [f] on the [i]-th cell [[xᵢ, xᵢ₊₁]]. *)
Definition is_inf_on_cell (f : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) (mi : ℝ) : Prop :=
    (∀ t ∈ ℝ, x i ≤ t ∧ t ≤ x (S i) → mi ≤ f t) ∧
    (∀ w ∈ ℝ, (∀ t ∈ ℝ, x i ≤ t ∧ t ≤ x (S i) → w ≤ f t) → w ≤ mi).

(** [Mi] is the *supremum* of [f] on the [i]-th cell [[xᵢ, xᵢ₊₁]]. *)
Definition is_sup_on_cell (f : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) (Mi : ℝ) : Prop :=
    (∀ t ∈ ℝ, x i ≤ t ∧ t ≤ x (S i) → f t ≤ Mi) ∧
    (∀ w ∈ ℝ, (∀ t ∈ ℝ, x i ≤ t ∧ t ≤ x (S i) → f t ≤ w) → Mi ≤ w).

(** The *lower sum* [L(f, P) = ∑ mᵢ · (xᵢ₊₁ - xᵢ)], where [mᵢ] is the infimum of
    [f] on the [i]-th cell. *)
Definition lower_sum (n : ℕ) (x m : ℕ → ℝ) : ℝ :=
    sum_f_R0 (fun i => m i * (x (S i) - x i)) (pred n).

(** The *upper sum* [U(f, P) = ∑ Mᵢ · (xᵢ₊₁ - xᵢ)], where [Mᵢ] is the supremum
    of [f] on the [i]-th cell. *)
Definition upper_sum (n : ℕ) (x M : ℕ → ℝ) : ℝ :=
    sum_f_R0 (fun i => M i * (x (S i) - x i)) (pred n).

(** A partition [Q] (with [m] cells, nodes [y]) *refines* [P] (with [n] cells,
    nodes [x]) if every node of [P] is also a node of [Q]. *)
Definition refines (n : ℕ) (x : ℕ → ℝ) (m : ℕ) (y : ℕ → ℝ) : Prop :=
    ∀ i ∈ ℕ, (i ≤ n)%nat → ∃ j ∈ ℕ, (j ≤ m)%nat ∧ y j = x i.

(** ** Refinement inequalities *)

(** _Refinement increases lower sums_: if [Q] refines [P] then
    [L(f, P) ≤ L(f, Q)].

    Proof idea: adding one node splits a cell into two; the infimum over each
    smaller cell is at least the infimum over the whole, so the corresponding
    contribution can only increase. Iterate over the added nodes. *)
Lemma refinement_increases_lower_sum (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x mx : ℕ → ℝ) (m : ℕ) (y my : ℕ → ℝ)
    (HP : is_partition a b n x) (HQ : is_partition a b m y)
    (Href : refines n x m y)
    (Hmx : ∀ i ∈ ℕ, (i < n)%nat → is_inf_on_cell f x i (mx i))
    (Hmy : ∀ j ∈ ℕ, (j < m)%nat → is_inf_on_cell f y j (my j)) :
    lower_sum n x mx ≤ lower_sum m y my.
Proof.
  Admitted.

(** _Refinement decreases upper sums_: if [Q] refines [P] then
    [U(f, Q) ≤ U(f, P)].

    Proof idea: dual to the previous lemma — the supremum over a smaller cell is
    at most the supremum over the whole. *)
Lemma refinement_decreases_upper_sum (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x Mx : ℕ → ℝ) (m : ℕ) (y My : ℕ → ℝ)
    (HP : is_partition a b n x) (HQ : is_partition a b m y)
    (Href : refines n x m y)
    (HMx : ∀ i ∈ ℕ, (i < n)%nat → is_sup_on_cell f x i (Mx i))
    (HMy : ∀ j ∈ ℕ, (j < m)%nat → is_sup_on_cell f y j (My j)) :
    upper_sum m y My ≤ upper_sum n x Mx.
Proof.
  Admitted.

(** _Refinement inequalities_ (corollary): for a common refinement [Q] of [P],
    [L(f, P) ≤ L(f, Q) ≤ U(f, Q) ≤ U(f, P)]. *)
Lemma refinement_inequalities (f : ℝ → ℝ) (a b : ℝ)
    (n : ℕ) (x mx Mx : ℕ → ℝ) (m : ℕ) (y my My : ℕ → ℝ)
    (HP : is_partition a b n x) (HQ : is_partition a b m y)
    (Href : refines n x m y)
    (Hmx : ∀ i ∈ ℕ, (i < n)%nat → is_inf_on_cell f x i (mx i))
    (HMx : ∀ i ∈ ℕ, (i < n)%nat → is_sup_on_cell f x i (Mx i))
    (Hmy : ∀ j ∈ ℕ, (j < m)%nat → is_inf_on_cell f y j (my j))
    (HMy : ∀ j ∈ ℕ, (j < m)%nat → is_sup_on_cell f y j (My j)) :
    lower_sum n x mx ≤ lower_sum m y my ∧
    lower_sum m y my ≤ upper_sum m y My ∧
    upper_sum m y My ≤ upper_sum n x Mx.
Proof.
  Admitted.

(** _Any lower sum is below any upper sum_: for arbitrary partitions [P₁], [P₂],
    [L(f, P₁) ≤ U(f, P₂)].

    Proof idea: take the common refinement [P₁ ∪ P₂] and chain the refinement
    inequalities:
    [L(f, P₁) ≤ L(f, P₁ ∪ P₂) ≤ U(f, P₁ ∪ P₂) ≤ U(f, P₂)]. *)
Lemma lower_sum_le_upper_sum (f : ℝ → ℝ) (a b : ℝ)
    (n1 : ℕ) (x1 m1 : ℕ → ℝ) (n2 : ℕ) (x2 M2 : ℕ → ℝ)
    (HP1 : is_partition a b n1 x1) (HP2 : is_partition a b n2 x2)
    (Hm1 : ∀ i ∈ ℕ, (i < n1)%nat → is_inf_on_cell f x1 i (m1 i))
    (HM2 : ∀ i ∈ ℕ, (i < n2)%nat → is_sup_on_cell f x2 i (M2 i)) :
    lower_sum n1 x1 m1 ≤ upper_sum n2 x2 M2.
Proof.
  Admitted.

(** ** Upper and lower integrals *)

(** [S] is *a lower sum of [f] on [[a, b]]*: it is [L(f, P)] for some partition
    [P] with infimum data. *)
Definition lower_sum_of (f : ℝ → ℝ) (a b s : ℝ) : Prop :=
    ∃ n ∈ ℕ, ∃ x : ℕ → ℝ, ∃ m : ℕ → ℝ,
      is_partition a b n x ∧
      (∀ i ∈ ℕ, (i < n)%nat → is_inf_on_cell f x i (m i)) ∧
      s = lower_sum n x m.

(** [S] is *an upper sum of [f] on [[a, b]]*. *)
Definition upper_sum_of (f : ℝ → ℝ) (a b s : ℝ) : Prop :=
    ∃ n ∈ ℕ, ∃ x : ℕ → ℝ, ∃ M : ℕ → ℝ,
      is_partition a b n x ∧
      (∀ i ∈ ℕ, (i < n)%nat → is_sup_on_cell f x i (M i)) ∧
      s = upper_sum n x M.

(** The *lower integral* [L(f) = sup { L(f, P) : P }] is the least upper bound of
    all lower sums. *)
Definition is_lower_integral (f : ℝ → ℝ) (a b L : ℝ) : Prop :=
    (∀ s ∈ ℝ, lower_sum_of f a b s → s ≤ L) ∧
    (∀ W ∈ ℝ, (∀ s ∈ ℝ, lower_sum_of f a b s → s ≤ W) → L ≤ W).

(** The *upper integral* [U(f) = inf { U(f, P) : P }] is the greatest lower bound
    of all upper sums. *)
Definition is_upper_integral (f : ℝ → ℝ) (a b U : ℝ) : Prop :=
    (∀ s ∈ ℝ, upper_sum_of f a b s → U ≤ s) ∧
    (∀ W ∈ ℝ, (∀ s ∈ ℝ, upper_sum_of f a b s → W ≤ s) → W ≤ U).

(** _The lower integral does not exceed the upper integral_: [L(f) ≤ U(f)].

    Proof idea: every lower sum is a lower bound for the set of upper sums (by
    [lower_sum_le_upper_sum]), hence at most the upper integral; taking the
    supremum over lower sums gives [L(f) ≤ U(f)]. *)
Lemma lower_integral_le_upper (f : ℝ → ℝ) (a b L U : ℝ)
    (HL : is_lower_integral f a b L) (HU : is_upper_integral f a b U) :
    L ≤ U.
Proof.
  Admitted.

(** ** Integrability and the Darboux criterion *)

(** [f] is *Darboux/Riemann integrable* on [[a, b]] when its upper and lower
    integrals coincide; the common value is [∫_a^b f]. *)
Definition riemann_integrable_darboux (f : ℝ → ℝ) (a b : ℝ) : Prop :=
    ∃ V ∈ ℝ, is_lower_integral f a b V ∧ is_upper_integral f a b V.

(** _Darboux criterion_ (Abbott 7.2.8): [f] is integrable on [[a, b]] iff for
    every [ε > 0] there is a partition [P] with [U(f, P) - L(f, P) < ε].

    Proof idea: (⇒) if [L(f) = U(f)], choose partitions whose lower/upper sums
    approximate this common value within [ε/2], and take their common
    refinement. (⇐) the gap [U(f) - L(f) ≤ U(f, P) - L(f, P) < ε] for all [ε],
    forcing equality. (For instance the Dirichlet function [𝟙_ℚ] fails this on
    [[0,1]], since [U(f, P) = 1] and [L(f, P) = 0] for every [P].) *)
Lemma darboux_criterion (f : ℝ → ℝ) (a b : ℝ) :
    riemann_integrable_darboux f a b ⇔
    (∀ ε > 0, ∃ n ∈ ℕ, ∃ x : ℕ → ℝ, ∃ m : ℕ → ℝ, ∃ M : ℕ → ℝ,
      is_partition a b n x ∧
      (∀ i ∈ ℕ, (i < n)%nat → is_inf_on_cell f x i (m i)) ∧
      (∀ i ∈ ℕ, (i < n)%nat → is_sup_on_cell f x i (M i)) ∧
      upper_sum n x M - lower_sum n x m < ε).
Proof.
  Admitted.

(** [step_approx g a b ε]: step functions [φ, ψ] with [|g - φ| ≤ ψ] on
    [[a, b]] and [|∫ ψ| < ε]. By definition, [Riemann_integrable g a b] is
    [∀ ε : posreal, step_approx g a b ε].

    Stdlib's [Riemann_integrable] packages the witnesses [φ, ψ] in the
    dependent pair types [sigT] and [sig] (written [{φ & {ψ | ...}}] in
    Stdlib, a notation that clashes with Waterproof's own). Naming this type
    once lets us reuse the existing [Riemann_integrable] definition, and the
    Stdlib results about it, without reinventing the wheel, while keeping
    statements free of explicit inductive types. We still occasionally need to
    deconstruct these pairs in proofs (with [projT1], [projT2], [proj1_sig],
    [proj2_sig]) or build them (with [existT] and [exist]), but we never
    need to spell out their types. *)
Definition step_approx (g : ℝ → ℝ) (a b ε : ℝ) : Type :=
  @sigT (StepFun a b) (fun phi : StepFun a b =>
    @sig (StepFun a b) (fun psi : StepFun a b =>
      (∀ t : ℝ, (& Rmin a b ≤ t ≤ Rmax a b) → | g t - phi t | ≤ psi t)
      ∧ | RiemannInt_SF psi | < ε)).

(** ** Constant functions are integrable *)

(** The constant function [x ↦ c] is Riemann integrable on [[a, b]], for any [a]
    and [b].

    Proof idea: for a constant every upper and lower sum equals [c · (b - a)],
    so the Darboux criterion holds trivially. *)
Lemma constant_integrable (a b c : ℝ) :
    Riemann_integrable (fct_cte c) a b.
Proof.
  By (RiemannInt_P14 a b c) we conclude that Riemann_integrable (fct_cte c) a b.
Qed.

(** The integral of a constant is [∫_a^b c = c · (b - a)]. *)
Lemma integral_constant (a b c : ℝ)
    (pr : Riemann_integrable (fct_cte c) a b) :
    RiemannInt pr = c * (b - a).
Proof.
  (** [By (RiemannInt_P15 pr) we conclude that …] does not finish within
      minutes on this [RiemannInt] equality, so we give the proof term
      directly. *)
  exact (RiemannInt_P15 pr).
Qed.

(** ** Continuous functions are integrable *)

(** If [f] is continuous on [[a, b]] (with [a ≤ b]), then [f] is Riemann
    integrable.

    Proof idea: a continuous function on a compact interval is uniformly
    continuous (Heine), so for [ε > 0] a fine enough uniform partition makes each
    oscillation small, giving [U(f, P) - L(f, P) < ε]; apply the Darboux
    criterion. *)
(* [a ≤ b] added: without it the hypothesis is vacuous for [b < a] while the
   conclusion still asks for integrability on [[b, a]], so the original
   statement was not provable. *)
Theorem continuous_integrable (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    Riemann_integrable f a b.
Proof.
  By continuity_implies_RiemannInt we conclude that Riemann_integrable f a b.
Qed.

(** ** Monotone functions are integrable *)

(** Exercise (Abbott): a *monotone* function on [[a, b]] is Riemann integrable.

    Proof idea: for an increasing [f] and the uniform partition with mesh
    [(b - a)/n], the total oscillation telescopes:
    [∑ (Mᵢ - mᵢ)·Δx = (f(b) - f(a))·(b - a)/n → 0]. The Darboux criterion then
    applies. (The decreasing case is symmetric.) *)
Lemma monotone_integrable (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hmono : ∀ x ∈ ℝ, ∀ y ∈ ℝ, a ≤ x → x ≤ y → y ≤ b → f x ≤ f y) :
    Riemann_integrable f a b.
Proof.
  Admitted.

(** ** The integral test *)

(** _Integral test_ (Lecture 3): for a nonnegative decreasing [f] on [[1, ∞)],
    the series [∑ f(k)] converges iff the sequence of integrals
    [∫_1^{n} f] is bounded.

    Proof idea: monotonicity gives, on each unit interval,
    [f(k+1) ≤ ∫_k^{k+1} f ≤ f(k)]; summing sandwiches the partial sums between
    consecutive integrals, so the series and the improper integral converge
    together. (Terms indexed as [f(k+1)] to match Rocq indexing.) *)
Lemma integral_test (f : ℝ → ℝ)
    (Hpos : ∀ x ∈ ℝ, 1 ≤ x → 0 ≤ f x)
    (Hdec : ∀ x ∈ ℝ, ∀ y ∈ ℝ, 1 ≤ x → x ≤ y → f y ≤ f x)
    (Hint : ∀ n : ℕ, Riemann_integrable f 1 (INR n + 1)) :
    (∃ L : ℝ, (fun n : ℕ => sum_f_R0 (fun k => f (INR k + 1)) n) ⟶ L) ⇔
    (∃ B : ℝ, ∀ n : ℕ, ∀ pr : Riemann_integrable f 1 (INR n + 1),
        RiemannInt pr ≤ B).
Proof.
  Admitted.

(** ** Linearity of the integral *)

(** The sum of two integrable functions is integrable. *)
Lemma sum_integrable (f g : ℝ → ℝ) (a b : ℝ)
    (pr1 : Riemann_integrable f a b)
    (pr2 : Riemann_integrable g a b) :
    Riemann_integrable (fun x => f x + g x) a b.
Proof.
  (** [RiemannInt_P10] gives [f + l·g]; take [l = 1] and transport along the
      pointwise equality with [Riemann_integrable_ext]. *)
  We claim that ∀ x : ℝ,
    Rmin a b ≤ x ∧ x ≤ Rmax a b → f x + 1 * g x = f x + g x as (Hext).
  {
    Take x : ℝ.
    Assume that Rmin a b ≤ x ∧ x ≤ Rmax a b.
    We conclude that f x + 1 * g x = f x + g x.
  }
  By (RiemannInt_P10 1 pr1 pr2) it holds that
    Riemann_integrable (fun x => f x + 1 * g x) a b as (Hpr).
  By (Riemann_integrable_ext (fun x => f x + 1 * g x) (fun x => f x + g x) Hext) we conclude that
    Riemann_integrable (fun x => f x + g x) a b.
Qed.

(** [∫(f + g) = ∫f + ∫g]. *)
Lemma integral_sum (f g : ℝ → ℝ) (a b : ℝ)
    (prf : Riemann_integrable f a b)
    (prg : Riemann_integrable g a b) :
    ∃ prfg : Riemann_integrable (fun x => f x + g x) a b,
      RiemannInt prfg = RiemannInt prf + RiemannInt prg.
Proof.
  Admitted.

(** [∫(c · f) = c · ∫f]. *)
Lemma integral_scalar (f : ℝ → ℝ) (a b c : ℝ)
    (prf : Riemann_integrable f a b) :
    ∃ prcf : Riemann_integrable (fun x => c * f x) a b,
      RiemannInt prcf = c * RiemannInt prf.
Proof.
  Admitted.

(** ** Monotonicity *)

(** _Monotonicity_ (order property): if [f ≤ g] on [(a, b)] then [∫f ≤ ∫g]. *)
(* [a ≤ b] added for the same reason as in [continuous_integrable]: for [b < a]
   the integrals swap sign, so the inequality does not hold as stated. *)
Lemma integral_monotone (f g : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (prf : Riemann_integrable f a b)
    (prg : Riemann_integrable g a b)
    (Hle : ∀ x, a ≤ x ∧ x ≤ b → f x ≤ g x) :
    RiemannInt prf ≤ RiemannInt prg.
Proof.
  We claim that ∀ x : ℝ, a < x ∧ x < b → f x ≤ g x as (Hlt).
  {
    Take x : ℝ.
    Assume that a < x ∧ x < b.
    By Hle we conclude that f x ≤ g x.
  }
  (** The Waterproof version of this step,
      [By (RiemannInt_P19 prf prg Hab Hlt) we conclude that …], does not finish
      within minutes: the automation is very slow on goals involving
      [RiemannInt]. So we give the proof term directly. *)
  exact (RiemannInt_P19 prf prg Hab Hlt).
Qed.

(** ** Additivity over sub-intervals *)

(** [∫_a^b f = ∫_a^c f + ∫_c^b f] for [a ≤ c ≤ b]. *)
Lemma integral_split (f : ℝ → ℝ) (a b c : ℝ)
    (Hac : a ≤ c) (Hcb : c ≤ b)
    (prf : Riemann_integrable f a b) :
    ∃ (pr1 : Riemann_integrable f a c),
    ∃ (pr2 : Riemann_integrable f c b),
      RiemannInt prf = RiemannInt pr1 + RiemannInt pr2.
Proof.
  (** [RiemannInt_P22]/[RiemannInt_P23] restrict the integrability, and
      [RiemannInt_P26] (Chasles) splits the value. The last step is an
      equality of [RiemannInt] terms, on which Waterproof automation does not
      finish within minutes, so we close it with [symmetry] and the proof
      term. *)
  It holds that a ≤ c ∧ c ≤ b as (Hacb).
  Choose pr1 := (RiemannInt_P22 prf Hacb).
  Choose pr2 := (RiemannInt_P23 prf Hacb).
  symmetry.
  exact (RiemannInt_P26 pr1 pr2 prf).
Qed.

(** ** Term-by-term integration *)

(** Auxiliary step for [uniform_limit_integrable]: if [|h - g| < η] on
    [[a, b]] with [η = (ε/2)/(b - a + 1)], and the step functions [φ, ψ] satisfy
    [|h - φ| ≤ ψ] with [|∫ ψ| < ε/2], then [φ] and [ψ + η] witness the
    [ε]-condition in the definition of Riemann integrability of [g].

    Proof idea: [|g - φ| ≤ |g - h| + |h - φ| ≤ η + ψ], and
    [|∫ (ψ + η)| ≤ |∫ ψ| + η (b - a) < ε/2 + ε/2]. *)
Lemma uniform_approx_step_functions (g h : ℝ → ℝ) (a b ε η : ℝ) (Hab : a ≤ b)
    (Hη : η > 0) (Hηdef : η = ε / 2 * / (b - a + 1))
    (Hclose : ∀ x : ℝ, a ≤ x ∧ x ≤ b → | h x - g x | < η)
    (phi psi : StepFun a b)
    (Hpsi : (∀ t : ℝ, (& Rmin a b ≤ t ≤ Rmax a b) → | h t - phi t | ≤ psi t)
      ∧ | RiemannInt_SF psi | < ε / 2) :
    step_approx g a b ε.
Proof.
  It holds that b - a + 1 ≠ 0.
  By Rinv_l it holds that / (b - a + 1) * (b - a + 1) = 1.
  It holds that η * (b - a + 1) = ε / 2 * (/ (b - a + 1) * (b - a + 1)).
  It holds that (& η * (b - a + 1) = ε / 2 * (/ (b - a + 1) * (b - a + 1))
    = ε / 2 * 1 = ε / 2).
  (** We enlarge [ψ] by the constant step function [η]. *)
  Define cη := StepFun_P4 a b η.
  Define sη := mkStepFun cη.
  Define p28 := StepFun_P28 1 psi sη.
  Define psi2 := mkStepFun p28.
  We claim that (∀ t : ℝ, (& Rmin a b ≤ t ≤ Rmax a b) → | g t - phi t | ≤ psi2 t)
    ∧ | RiemannInt_SF psi2 | < ε as (Hbound).
  {
    We show both statements.
    - We need to show that
        ∀ t : ℝ, (& Rmin a b ≤ t ≤ Rmax a b) → | g t - phi t | ≤ psi2 t.
      Take t : ℝ.
      Assume that (& Rmin a b ≤ t ≤ Rmax a b).
      By Rmin_left it holds that Rmin a b = a.
      By Rmax_right it holds that Rmax a b = b.
      It holds that a ≤ t ∧ t ≤ b.
      By Hclose it holds that | h t - g t | < η.
      By Hpsi it holds that | h t - phi t | ≤ psi t.
      It holds that psi2 t = psi t + 1 * η.
      By Rabs_triang it holds that
        | (g t - h t) + (h t - phi t) | ≤ | g t - h t | + | h t - phi t |.
      It holds that | g t - h t | = | h t - g t |.
      We conclude that | g t - phi t | ≤ psi2 t.
    - We need to show that | RiemannInt_SF psi2 | < ε.
      By (@StepFun_P30 a b 1 psi sη) it holds that
        RiemannInt_SF psi2 = RiemannInt_SF psi + 1 * RiemannInt_SF sη.
      By (@StepFun_P18 a b η) it holds that RiemannInt_SF sη = η * (b - a).
      It holds that | RiemannInt_SF psi | < ε / 2.
      It holds that η * (b - a) ≥ 0.
      It holds that η * (b - a) ≤ η * (b - a + 1).
      By Rabs_triang it holds that
        | RiemannInt_SF psi + 1 * RiemannInt_SF sη |
          ≤ | RiemannInt_SF psi | + | 1 * RiemannInt_SF sη |.
      It holds that | 1 * RiemannInt_SF sη | = η * (b - a).
      We conclude that | RiemannInt_SF psi2 | < ε.
  }
  (** The pair [(φ, ψ + η)] is the required witness. *)
  By (existT _ phi (exist _ psi2 Hbound) : step_approx g a b ε) we conclude that step_approx g a b ε.
Qed.

(** A uniform limit of Riemann integrable functions on [[a, b]] is Riemann
    integrable (first half of Abbott 7.2.5).

    Proof idea: given [ε > 0], pick [N] with [|f_N - g| < η] on [[a, b]] and
    step functions [φ, ψ] for [f_N] with [|f_N - φ| ≤ ψ], [|∫ ψ| < ε/2]; then
    [φ] and [ψ + η] work for [g] ([uniform_approx_step_functions]). Since
    Stdlib's [Riemann_integrable] is data (a [Type]), the index [N] is selected
    with [constructive_indefinite_ground_description_nat]. *)
Lemma uniform_limit_integrable (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hunif : converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b))
    (Hint : forall n : ℕ, Riemann_integrable (fn n) a b) :
    Riemann_integrable g a b.
Proof.
  We need to show that ∀ ε : posreal, step_approx g a b ε.
  Take ε : posreal.
  By (cond_pos ε) it holds that ε > 0.
  It holds that b - a + 1 > 0.
  Define η := ε / 2 * / (b - a + 1).
  It holds that η = ε / 2 * / (b - a + 1) as (Hηdef).
  It holds that / (b - a + 1) > 0.
  It holds that η > 0 as (Hη).
  (** Uniform convergence gives an index [n] with [|fₙ - g| < η] on [[a, b]]. *)
  Define P := fun n : ℕ => ∀ x : ℝ, a ≤ x ∧ x ≤ b → | fn n x - g x | < η.
  We claim that ∃ n : ℕ, P n as (Hex).
  {
    By (Hunif η Hη) it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
      ∀ x ∈ (fun x => a ≤ x ∧ x ≤ b), | fn n x - g x | < η as (HN).
    Obtain such an N1.
    Choose n := N1.
    We need to show that ∀ x : ℝ, a ≤ x ∧ x ≤ b → | fn n x - g x | < η.
    Take x : ℝ. Assume that a ≤ x ∧ x ≤ b.
    It holds that (n ≥ N1)%nat.
    By HN we conclude that | fn n x - g x | < η.
  }
  (** Since we are constructing data, we pick such an index explicitly. *)
  Define Pdec := fun n : ℕ => excluded_middle_informative (P n).
  Define Nsig := constructive_indefinite_ground_description_nat P Pdec Hex.
  Define Nε := proj1_sig Nsig.
  (** Step functions approximating [f_N] within [ε/2]. *)
  It holds that ε / 2 > 0 as (Hhalf).
  Define e2 := mkposreal (ε / 2) Hhalf.
  Define approx := Hint Nε e2.
  Define phi := projT1 approx.
  Define rest := projT2 approx.
  Define psi := proj1_sig rest.
  Define Happrox := uniform_approx_step_functions g (fn Nε) a b ε η Hab Hη Hηdef
    (proj2_sig Nsig) phi psi (proj2_sig rest).
  We conclude that step_approx g a b ε.
Qed.

(** A real-number estimate used in [uniform_limit_integral]: if [D = A - B],
    [|D| ≤ E] and [E ≤ u], then [|A - B| ≤ u] (up to renaming [A, B]).

    Proof idea: [|A' - B'| = |D| ≤ E ≤ u]. *)
Lemma abs_diff_le_of_bounds (A B A' B' D E l u : ℝ) :
    A' = A → B' = B → D = A + -1 * B → | D | ≤ E → l <= E <= u → | A' - B' | ≤ u.
Proof.
  Assume that A' = A and B' = B.
  Assume that D = A + -1 * B.
  Assume that | D | ≤ E.
  Assume that l <= E <= u.
  It holds that A' - B' = D.
  We conclude that (& | A' - B' | = | D | ≤ E ≤ u).
Qed.

(** _Interchange of limit and integral_ (Abbott 7.2.5): if [(fₙ) ⇉ g]
    uniformly on [[a, b]] and each [fₙ] is integrable, then [g] is integrable
    and [∫_a^b fₙ → ∫_a^b g].

    Here [Iseq n = ∫_a^b fₙ] and [Ig = ∫_a^b g] are the recorded integral
    values.

    Proof idea: [g] is integrable by [uniform_limit_integrable]; given [ε > 0]
    choose [N] with [|fₙ - g| < η = (ε/2)/(b - a + 1)] on [[a, b]] for [n ≥ N];
    then [|∫ fₙ - ∫ g| ≤ ∫ |fₙ - g| ≤ η (b - a) < ε]. *)
Theorem uniform_limit_integral (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hunif : converges_uniformly fn g (fun x => a ≤ x ∧ x ≤ b))
    (Hint : forall n : ℕ, Riemann_integrable (fn n) a b)
    (Iseq : ℕ → ℝ) (Ig : ℝ)
    (HI : ∀ n : ℕ, ∀ pr : Riemann_integrable (fn n) a b, Iseq n = RiemannInt pr)
    (HIg : ∀ pr : Riemann_integrable g a b, Ig = RiemannInt pr) :
    Iseq ⟶ Ig.
Proof.
  (** The limit [g] is integrable. *)
  Define prg := uniform_limit_integrable fn g a b Hab Hunif Hint.
  We need to show that ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, | Iseq n - Ig | < ε.
  Take ε > 0.
  It holds that b - a + 1 > 0.
  It holds that b - a + 1 ≠ 0 as (Hne).
  Define η := ε / 2 * / (b - a + 1).
  It holds that / (b - a + 1) > 0.
  It holds that η > 0 as (Hη).
  Define Hinv := Rinv_l (b - a + 1) Hne.
  It holds that η * (b - a + 1) = ε / 2 * (/ (b - a + 1) * (b - a + 1)).
  It holds that (& η * (b - a + 1) = ε / 2 * (/ (b - a + 1) * (b - a + 1))
    = ε / 2 * 1 = ε / 2).
  By (Hunif η Hη) it holds that ∃ N1 ∈ ℕ, ∀ n : ℕ, (n ≥ N1)%nat →
    ∀ x ∈ (fun x => a ≤ x ∧ x ≤ b), | fn n x - g x | < η as (HN).
  Obtain such an N1.
  Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
  We need to show that ∀ n ≥ N2, | Iseq n - Ig | < ε.
  Take n ≥ N2.
  Define m1 := -1.
  We claim that ∀ x : ℝ, a < x < b → 0 <= | fn n x + m1 * g x | <= η as (Hbnd).
  {
    Take x : ℝ. Assume that a < x < b.
    It holds that a ≤ x ∧ x ≤ b.
    It holds that (n ≥ N1)%nat.
    By HN it holds that | fn n x - g x | < η.
    It holds that fn n x + m1 * g x = fn n x - g x.
    It holds that 0 ≤ | fn n x + m1 * g x |.
    We conclude that 0 <= | fn n x + m1 * g x | <= η.
  }
  (** We estimate [|∫ fₙ - ∫ g| ≤ ∫ |fₙ - g| ≤ η (b - a)]. *)
  Define prn := Hint n.
  Define prd := RiemannInt_P10 m1 prn prg.
  Define pra := RiemannInt_P16 prd.
  Define HIn := HI n prn.
  Define HIprg := HIg prg.
  Define Hlin := RiemannInt_P13 prn prg prd.
  Define Habs := RiemannInt_P17 prd pra Hab.
  Define Hconst := RiemannInt_const_bound pra Hab Hbnd.
  Define Hest := abs_diff_le_of_bounds _ _ _ _ _ _ _ _ HIn HIprg Hlin Habs Hconst.
  It holds that η * (b - a) ≤ η * (b - a + 1).
  We conclude that | Iseq n - Ig | < ε.
Qed.
