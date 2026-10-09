(** * RUG.Analysis.Compactness — Compact subsets of ℝ.

  #<a href="../../index.html##lecture07">Lecture 7</a>#.

  Formalizes Abbott §3.3: the Heine-Borel theorem (compact ↔ closed and bounded),
  properties of compact sets, and the nested compact sets property. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lists.List.

From Waterproof Require Export Notations.Common.
From Waterproof Require Export Notations.Reals.
From Waterproof Require Export Notations.Sets.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
From Waterproof Require Import Libs.Analysis.Subsequences.
Require Export RUG.Analysis.Topology.
Require Export RUG.Analysis.Subsequences.
Require Export RUG.Analysis.Lib.Compactness.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs". 

(** *Sequential compactness*: every sequence in [K] has a subsequence
    converging to a point of [K]. Here [phi] is a strictly increasing index
    map. This is the "Bolzano–Weierstrass" notion of compactness used in the
    lecture. *)

Definition sequentially_compact (K : ℝ → Prop) : Prop :=
    ∀ a : ℕ → ℝ, (∀ n : ℕ, a n ∈ K) →
      ∃ phi : ℕ → ℕ, ∃ x : ℝ,
        (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K x ∧
        (fun k => a (phi k)) ⟶ x.

(** An *open cover* of [K] is a family [(U i)] of open sets whose union
    contains [K]. *)
Definition open_cover {I : Type} (U : I → (ℝ → Prop)) (K : ℝ → Prop) : Prop :=
    (∀ i : I, (U i) is _open_) ∧ (∀ x : ℝ, K x → ∃ i : I, U i x).

(** [K] admits a *finite subcover* from [(U i)] if finitely many indices
    [i₁, …, iₙ] already cover [K]. *)
Definition has_finite_subcover {I : Type} (U : I → (ℝ → Prop)) (K : ℝ → Prop)
    : Prop :=
    ∃ l : list I, ∀ x : ℝ, K x → ∃ i : I, In i l ∧ U i x. 

(** ** Closed intervals are compact *)

(** Every closed bounded interval is compact (Heine-Borel, one direction).

    Proof idea: given a sequence in [[a,b]], Bolzano–Weierstrass provides a
    convergent subsequence, and the order limit theorem places its limit in
    [[a,b]] (from [a ≤ xₙ ≤ b]). *)
Theorem segment_compact (a b : ℝ) :
    [a, b] is _compact_.
Proof.
  By closed_interval_is_compact we conclude that [a, b] is _compact_.
Qed.

(** ** Compact sets are closed and bounded *)


(** Every compact set is closed.

    Proof idea: if [x] is a limit point of [K], take a sequence in [K] converging
    to [x]. By compactness it has a subsequence converging to some [y ∈ K]; but
    subsequences of a convergent sequence share its limit, so [x = y ∈ K]. 
    
    WARNING: the main difficulties in this proof are getting waterproof to accept the 
    subsequence and limit arguments. A two line proof in natural language now becomes 
    a 70 line proof in waterproof. It is instructive on how to unpack sequences of 
    quantifiers and how to use the waterproof tactics.
    *)


Lemma Sequentially_compact_implies_closed (K : ℝ → Prop) (HK : sequentially_compact K) :
    K is closed.
Proof. 
We need to show that K is closed. 
It holds that sequentially_compact K as (HK_seq). 
By (closed_iff_contains_limit_points) it suffices to show that 
(∀ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε) → K x). 
Take x0 : R. 
Assume that 
 (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x0) < ε) as (x_lim). 
By (limit_point_characterization K x0) and x_lim it holds that
  (∃ a : ℕ → ℝ,
    (∀ n ∈ ℕ, a n ∈ K) ∧
    (∀ n ∈ ℕ, a n ≠ x0) ∧
    a ⟶ x0) as (a_seq). 
 Obtain a according to (a_seq). 
 It holds that (∀ n ∈ ℕ, a n ∈ K) as (ainK). 
 It holds that (a ⟶ x0) as (a_converges). 
 By (HK_seq) it holds that (∀ a : ℕ → ℝ, (∀ n : ℕ, a n ∈ K) →
   ∃ phi : ℕ → ℕ, ∃ x : ℝ,
     (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K x ∧
     (fun k => a (phi k)) ⟶ x) as (HK_seqe).
 Use a := a in (HK_seqe).
It holds that
  ((∀ n : ℕ, a n ∈ K) →
   ∃ phi : ℕ → ℕ, ∃ x : ℝ,
     (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K x ∧
     (fun k => a (phi k)) ⟶ x)
  as (HK_seq_a).
By (HK_seq_a) and ainK it holds that
  (∃ phi : ℕ → ℕ, ∃ x : ℝ,
    (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K x ∧
    (fun k => a (phi k)) ⟶ x)
  as (phi_x). 
Obtain phi according to (phi_x).
By subseq_converges it holds that
  (a ⟶ x0 → is_index_seq phi →
   (fun k => a (phi k)) ⟶ x0)
  as (Hsubseq). 
By (Hsubseq a_converges) it holds that
  (is_index_seq phi → (fun k => a (phi k)) ⟶ x0) 
   as (subseq_converges_to_x0).  
By (phi_x) it holds that
    (∃ x : ℝ,
    (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K x ∧
    (fun k => a (phi k)) ⟶ x) as (limphi). 
Obtain x according to (limphi).
It holds that (K x) as (x_in_K).
It holds that ((fun k => a (phi k)) ⟶ x) as (subseq_converges_to_x).

By (subseq_converges_to_x0) it holds that
  (is_index_seq phi → (fun k => a (phi k)) ⟶ x0) 
  as (subseq_converges_to_x0'). 
 It holds that
  (∀ n : ℕ, (phi n < phi (S n))%nat)
  as (Hphi_strict).

We claim that
  (is_index_seq phi) as (Hphi).
  {We need to show that
    ∀ k ∈ ℕ, (phi k < phi (S k))%nat.
  Take k ∈ ℕ.
  Use n := k in (Hphi_strict).
  It holds that (phi(k) < phi(S(k)))%nat.
  We conclude that (phi k < phi (S k))%nat.

  }
By (Hphi) it holds that
  ((fun k => a (phi k)) ⟶ x0) as (subseq_converges_to_x0''). 

By (limit_unique 
  (fun k => a (phi k)) x0 x subseq_converges_to_x0'' 
    subseq_converges_to_x) it holds that
  (x0 = x) as (x_eq).

By (x_eq) and x_in_K it holds that
  (K x0) as (x0_in_K).
We conclude that K x0.



Qed.

(** Every compact set is closed.

    Proof idea: if [x] is a limit point of [K], take a sequence in [K] converging
    to [x]. By compactness it has a subsequence converging to some [y ∈ K]; but
    subsequences of a convergent sequence share its limit, so [x = y ∈ K]. *)
Theorem compact_sets_is_closed (K : ℝ → Prop) (HK : K is _compact_) :
    K is closed.
Proof.
 We need to show that K is closed.
 By (compact_is_closed) and HK 
  it holds that (K is compact -> K is closed). 
 We conclude that K is closed.
Qed.
(** Every compact set is bounded.

    Proof idea: if [K] were unbounded, pick [xₙ ∈ K] with [|xₙ| > n]; this
    sequence has no convergent subsequence (convergent sequences are bounded),
    contradicting compactness. *)
Theorem compact_is_bounded (K : ℝ → Prop) (HK : K is _compact_) :
    K is _bounded_.
Proof.
 By (compact_is_bounded) and HK 
  we conclude that K is bounded.
  Qed.

(** ** Closed subsets of compact sets are compact *)

(** A closed subset of a compact set is compact.

    Proof idea: a sequence in [F ⊆ K] has, by compactness of [K], a subsequence
    converging to some [y ∈ K]; since [F] is closed and the subsequence lies in
    [F], the limit [y ∈ F]. *)
Theorem closed_subset_of_compact_is_compact
    (K F : ℝ → Prop)
    (HK : K is _compact_) (HF : F is _closed_)
    (Hinc : ∀ x : ℝ, F x → K x) :
    F is _compact_.
Proof.
  Admitted.

(** ** Heine-Borel theorem *)

(** Heine–Borel theorem: a subset of ℝ is compact iff it is closed and bounded.

    Proof idea: (⇒) is the two theorems above. (⇐) given a sequence in a bounded
    [K], Bolzano–Weierstrass gives a convergent subsequence, and closedness
    places its limit in [K]. *)
Theorem heine_borel (K : ℝ → Prop) :
    (K is _compact_) ⇔ (K is _closed_ ∧ K is _bounded_).
Proof.
  Admitted.

(** ** Open covers and the finite subcover property *)







(** *Heine–Borel (open-cover form)*: a set [K ⊆ ℝ] is sequentially compact iff
    every open cover of [K] has a finite subcover.

    Proof idea: (⇐) if [K] were not sequentially compact, a sequence with no
    convergent-in-[K] subsequence yields an open cover with no finite subcover.
    (⇒) sequential compactness gives [K] closed and bounded; a Lebesgue-number
    argument extracts a finite subcover from any open cover. *)

Theorem compact_iff_finite_subcover (K : ℝ → Prop) :
    sequentially_compact K ⇔
    (forall (I : Type) (U : I → (ℝ → Prop)),
        open_cover U K → has_finite_subcover U K).
Proof.
  Admitted.

(** ** Nested compact sets *)

(** A decreasing sequence of nonempty compact sets has nonempty intersection.

    Proof idea: a generalization of the nested interval property. Picking a point
    [xₙ ∈ Kₙ], compactness of [K₀] gives a subsequence converging to some [x];
    since each [Kₙ] is closed and eventually contains the tail of the
    subsequence, [x ∈ Kₙ] for every [n]. *)
Theorem nested_compact_intersection_nonempty
    (K : ℕ → (ℝ → Prop))
    (HK_nonempty : ∀ n : ℕ, ∃ x : ℝ, K n x)
    (HK_compact  : ∀ n : ℕ, (K n) is _compact_)
    (HK_nested   : ∀ n ∈ ℕ, ∀ m ∈ ℕ, (n ≤ m)%nat → ∀ x ∈ ℝ, K m x → K n x) :
    ∃ x : ℝ, ∀ n : ℕ, K n x.
Proof.
  Admitted.