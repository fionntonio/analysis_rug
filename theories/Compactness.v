(** * RUG.Analysis.Compactness — Compact subsets of ℝ.

  #<a href="../../index.html##lecture07">Lecture 7</a>#.

  Formalizes Abbott §3.3: the Heine-Borel theorem (compact ↔ closed and bounded),
  properties of compact sets, and the nested compact sets property. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import setoid_ring.Ring.


From Waterproof Require Export Notations.Common.
From Waterproof Require Export Notations.Reals.
From Waterproof Require Export Notations.Sets.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
From Waterproof Require Import Libs.Analysis.Subsequences.
Require Export RUG.Analysis.Topology.
Require Export RUG.Analysis.Sequences.
Require Export RUG.Analysis.Reals.
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

(** Every compact set is bounded.

    Proof idea: if [K] were unbounded, pick [xₙ ∈ K] with [|xₙ| > n]; this
    sequence has no convergent subsequence (convergent sequences are bounded),
    contradicting compactness. *)

Lemma Sequentially_compact_implies_bounded (K : ℝ → Prop) (HK : sequentially_compact K) :
    K is _bounded_.
Proof.
We need to show that K is bounded.
We argue by contradiction. Assume that ¬(K is _bounded_).
It holds that (¬( ∃ m : ℝ, (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M))))  as (Hnot_bounded).
By (Hnot_bounded) it holds that (∀ m : ℝ, ¬(∃ M : ℝ, ∀ x : ℝ, 
 K x → (& m ≤ x ≤ M))) as (Hnot_bounded').
By (Hnot_bounded') it holds that (∀ m : ℝ, ∀ M : ℝ, 
 ¬(∀ x : ℝ, K x → (& m ≤ x ≤ M))) as (Hnot_bounded'').
By (Hnot_bounded'') it holds that (∀ m : ℝ, ∀ M : ℝ, 
 ∃ x : ℝ, K x ∧ ¬(& m ≤ x ≤ M)) as (Hnot_bounded''').


We claim that
  (∀ n : ℕ, ∃ x : ℝ, K x ∧ ¬(& -1*(INR n) ≤ x ≤  (INR n))) as (Hnot_bounded_seq).
  {We need to show that
    ∀ n : ℕ, ∃ x : ℝ, K x ∧ ¬(& -1*(INR n) ≤ x ≤  (INR n)).
  Take n : ℕ.
  Use m :=  -1*(INR n) in (Hnot_bounded''').
  It holds that (∀ M : ℝ, ∃ x : ℝ, K(x) ∧ ¬ (& -1* n ≤ x ≤ M)) as (m1).

  Use M :=  (INR n) in (m1). 
  It holds that (∃ x : ℝ, K x ∧ ¬(& -1*(INR n) ≤ x ≤  (INR n))) as (m2).
  It holds that (∃ x : ℝ, K x ∧ ¬(& -1*(INR n) ≤ x ≤  (INR n))).
  We conclude that
    (∃ x : ℝ, K x ∧ ¬(& -1*(INR n) ≤ x ≤  (INR n))).

  }

By (countable_choice (fun n x =>  
   (K x ∧ ¬(& -1*(INR n) ≤ x ≤  (INR n))))(Hnot_bounded_seq)) 
    it holds that
    (∃ a : ℕ → ℝ, ∀ n : ℕ, a n ∈ K ∧ ¬(& -1*(INR n) ≤ a n ≤  (INR n))) as (Hseq).
  Obtain a according to (Hseq).
  It holds that (∀ n : ℕ, a n ∈ K ∧
   ¬(& -1*(INR n) ≤ a n ≤  (INR n))) as (Hseq_prop). 


  We claim that
    (∀ n : ℕ, a n ∈ K) as (Hseq_in_K).
    {We need to show that
      ∀ n : ℕ, a n ∈ K.
    Take n : ℕ.
   
    It holds that (a n ∈ K ∧ ¬(& -1*(INR n) ≤ a n ≤  (INR n))).
    It holds that (a n ∈ K).
    We conclude that a n ∈ K.

    } 
 We claim that 
    (∀ n : ℕ, ¬(& -1*(INR n) ≤ a n ≤  (INR n))) as (Hseq_not_bounded).
    {We need to show that
      ∀ n : ℕ, ¬(& -1*(INR n) ≤ a n ≤  (INR n)).
    Take n : ℕ.
   
    It holds that (a n ∈ K ∧ ¬(& -1*(INR n) ≤ a n ≤  (INR n))).
    It holds that (¬(& -1*(INR n) ≤ a n ≤  (INR n))).
    We conclude that ¬(& -1*(INR n) ≤ a n ≤  (INR n)).

    } 
  By (HK a Hseq_in_K) it holds that
    (∃ phi : ℕ → ℕ, ∃ x : ℝ,
      (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K x ∧
      (fun k => a (phi k)) ⟶ x)
    as (Hsubseq). 
  Obtain phi according to (Hsubseq).
  It holds that (∃ x, (∀ n, (phi(n) < phi(S(n)))%nat)
    ∧ K(x) ∧ ｛ k : ℕ | a(phi(k)) ｝ ⟶ x) as (phi_lim).

  Obtain x according to (phi_lim).
  It holds that (∀ n, (phi(n) < phi(S(n)))%nat) as (Hphi_strict).
 We claim that (is_index_seq phi) as (Hphi).
{
  We need to show that
    ∀ k ∈ ℕ, (phi k < phi (S k))%nat.
  Take k ∈ ℕ.
  Use n := k in (Hphi_strict).
  It holds that (phi k < phi (S k))%nat.
  We conclude that (phi k < phi (S k))%nat.
}
  It holds that ((fun k => a (phi k)) ⟶ x) as (subseq_converges_to_x). 
  By (convergent_sequence_is_bounded((fun k => a (phi k)))(x)) it holds that
    (bounded_sequence ((fun k => a (phi k)))) as (subseq_is_bounded). 
  By (subseq_is_bounded) it holds that
    (∃ M ∈ ℝ, M > 0 ∧ ∀ n ∈ ℕ, | a(phi(n)) | ≤ M)
    as (Hbounded). 
 
  Obtain M according to (Hbounded).
  It holds that (M > 0) as (Hbounded_M).
  It holds that
    ∀ n ∈ ℕ, | a(phi(n)) | ≤ M as (Hbounded'). 

  By the Archimedean property it holds that 
    (∃ n0 ∈ ℕ,  M < INR n0) as (Harch).
  Obtain n0 according to (Harch).
  It holds that (M < INR n0) as (Harch'). 
  It holds that (∀ n ∈ ℕ, | a(phi(n)) | ≤ M) as (Hbounded'').
 By index_seq_grows_0 it holds that (phi n0 ≥ n0)%nat as (Hphi_n0).
  
  Use n := n0 in (Hbounded''). { Indeed, n0 ∈ ℕ. }
  It holds that (| a(phi(n0)) | ≤ M). 
  Use n := (phi n0) in (Hseq_not_bounded).
It holds that
  ¬(& -1 * INR (phi n0) ≤ a (phi n0) ≤ INR (phi n0))
  as (Hnot_bounded_phi_n0). 

  By (abs_le_iff( a (phi n0)) (M)) it holds that
    (| a(phi(n0)) | ≤ M ⇔ ( - M ≤ a(phi n0) ∧ a(phi n0) ≤ M))
    as (Habs_le). 

  By (Habs_le) and (Hbounded'') it holds that
    (- M ≤ a(phi(n0)) ∧ a(phi(n0)) ≤ M) as (Hbounded_phi_n0). 

 (** Waterproof had a really hard time parsing the inequalities 
     So we had to split them up in an inefficient way*)
  We claim that (- INR n0 <= a(phi(n0))) as (Hlower_n0).
  {
    We need to show that - INR n0 <= a(phi(n0)).
    By (Harch') and (Hbounded_phi_n0) it holds that
      - INR n0 < a(phi(n0)).
    We conclude that - INR n0 <= a(phi(n0)).
  }
  We claim that (a(phi(n0)) <= INR n0) as (Hupper_n0).
  {
    We need to show that a(phi(n0)) <= INR n0.
    By (Harch') and (Hbounded_phi_n0) it holds that
      a(phi(n0)) < INR n0.
    We conclude that a(phi(n0)) <= INR n0.
  }

  By (le_INR n0 (phi n0) Hphi_n0) it holds that
    (INR n0 ≤ INR (phi n0)) as (Hphi_real).
  We claim that (- INR (phi n0) <= a(phi(n0))) as (Hlower_phi_n0).

  {
    We need to show that - INR (phi n0) <= a(phi(n0)).
    By (Hphi_real) and (Hlower_n0) it holds that
      - INR (phi n0) < a(phi(n0)).
    We conclude that - INR (phi n0) <= a(phi(n0)).
  }

  We claim that (a(phi(n0)) <= INR (phi n0)) as (Hupper_phi_n0).
  {
    We need to show that a(phi(n0)) <= INR (phi n0).
    By (Hphi_real) and (Hupper_n0) it holds that
      a(phi(n0)) <= INR (phi n0).
    We conclude that a(phi(n0)) <= INR (phi n0).
  }

  By (Hlower_phi_n0) and (Hupper_phi_n0) it holds that
    (& -1 * INR (phi n0) <= a(phi(n0)) <= INR (phi n0))  
    as (Hbounded_phi_n0'). 
  Contradiction. 

Qed. 

(** ** Heine-Borel theorem *)

(** Heine–Borel theorem: a subset of ℝ is compact iff it is closed and bounded.

    Proof idea: (⇒) is the two theorems above. (⇐) given a sequence in a bounded
    [K], Bolzano–Weierstrass gives a convergent subsequence, and closedness
    places its limit in [K]. *)


Theorem Sequential_Heine_Borel (K : ℝ → Prop) :
    (sequentially_compact(K)) ⇔ (K is _closed_ ∧ K is _bounded_).
Proof.
 We show both directions. 
 ++ We need to show that (sequentially_compact(K)) → (K is _closed_ ∧ K is _bounded_).
  Assume that (sequentially_compact(K)) as (HK). 
   
  By (Sequentially_compact_implies_closed K HK) it holds that
    (K is _closed_) as (Hclosed). 
  By (Sequentially_compact_implies_bounded K HK) it holds that
    (K is _bounded_) as (Hbounded). 
  We conclude that (K is _closed_ ∧ K is _bounded_).




 ++ We need to show that  
  (K is _closed_ ∧ K is _bounded_) → (sequentially_compact(K)). 
  Assume that (K is _closed_ ∧ K is _bounded_) as (Hclosed_bounded).

  By (Hclosed_bounded) it holds that (K is _closed_) as (Hclosed). 
  By (Hclosed_bounded) it holds that (K is _bounded_) as (Hbounded). 
  We need to show that (sequentially_compact(K)). 
  We need to show that
    ∀ a : ℕ → ℝ, (∀ n : ℕ, a n ∈ K) →
      ∃ phi : ℕ → ℕ, ∃ x : ℝ,
        (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K x ∧
        (fun k => a (phi k)) ⟶ x.
  Take a : ℕ → ℝ.
  Assume that (∀ n : ℕ, a n ∈ K) as (ainK). 
  By (Hbounded) it holds that (∃ m : ℝ,  
   (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M))) as (Hbounded'). 
  Obtain m according to (Hbounded'). 
  It holds that (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M)) as (Hbounded'').
  Obtain M according to (Hbounded''). 
  We claim that (has_ub a) as (Hseq_upbounded). 
  {
    We need to show that has_ub a. 
    We need to show that (bound (EUn a)). 
    We need to show that (∃ M0 : ℝ, ∀ x : ℝ, EUn a x → x ≤ M0).
    Choose M0 := M . 
    Take x : ℝ.
    Assume that (EUn a x) as (x_in_EUn).
    By (x_in_EUn) it holds that (∃ n : ℕ, x = a n) as (x_in_seq). 
    Obtain n according to (x_in_seq).
    It holds that (x = a n) as (x_eq).
    By (Hbounded'') and ainK it holds that
      (∀ n : ℕ, & m ≤ a n ≤  M) as (Hseq_bounded).  
    Use n := n in (Hseq_bounded).
    It holds that (& m ≤ a n ≤  M) as (Hseq_bounded_n). 
    By (Hseq_bounded_n) it holds that (a n ≤ M) as (Hseq_bounded_n'). 
    By (x_eq) it holds that (x ≤ M) as (Hseq_bounded_n''). 
    We conclude that x ≤ M.
  }
  We claim that (has_lb a) as (Hseq_lowbounded). 
  {
    We need to show that has_lb a. 
    We need to show that (bound (EUn (opp_seq a))). 
    We need to show that (∃ M0 : ℝ, ∀ x : ℝ, EUn (opp_seq a) x → x ≤ M0).
    Choose M0 := - m . 
    Take x : ℝ.
    Assume that (EUn (opp_seq a) x) as (x_in_EUn).
    By (x_in_EUn) it holds that (∃ n : ℕ, x = - a n) as (x_in_seq). 
    Obtain n according to (x_in_seq).
    It holds that (x = - a n) as (x_eq).
    By (Hbounded'') and ainK it holds that
      (∀ n : ℕ, & m ≤ a n ≤  M) as (Hseq_bounded).  
    Use n := n in (Hseq_bounded).
    It holds that (& m ≤ a n ≤  M) as (Hseq_bounded_n). 
    By (Hseq_bounded_n) it holds that ( m ≤ a n) as (Hseq_bounded_n'). 
    By (x_eq) it holds that (- a n ≤ - m) as (Hseq_bounded_n''). 
    By (Hseq_bounded_n'') it holds that (x ≤ - m) as (Hseq_bounded_n''').
    We conclude that x ≤ - m.
  }
  By (bolzano_weierstrass a Hseq_upbounded Hseq_lowbounded) it holds that
  (∃ phi : ℕ → ℕ, ∃ x : ℝ,
    is_index_seq phi ∧ (fun k => a (phi k)) ⟶ x)
  as (Hsubseq). 
  Obtain phi according to (Hsubseq). 
  It holds that (∃ x : ℝ, is_index_seq phi ∧  
   (fun k => a (phi k)) ⟶ x) as (Hsubseq'). 
  Obtain x according to (Hsubseq').
  It holds that (is_index_seq phi) as (Hphi).
  It holds that ((fun k => a (phi k)) ⟶ x) as (subseq_converges_to_x). 
  By (closed_iff_contains_limit_points K) and (Hclosed) it holds that
    (∀ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε) → K x) as (K_limitpoint). 
  Use x0 := x in (K_limitpoint).
  It holds that
   (∀ ε > 0, ∃ y ∈ K, 0 < |y - x| < ε) ⇨ K(x) as (K_limitpoint').
  We claim that (K x) as (x_in_K).
  {
    We need to show that K x.
    By classic it holds that
   (∃ n : ℕ, a n = x) ∨ ¬(∃ n : ℕ, a n = x)
    as (Hhit_or_not).
   Either (∃ n : ℕ, a n = x) or (¬(∃ n : ℕ, a n = x)).
  - Case (∃ n : ℕ, a n = x).
    Obtain n according to (H).
    It holds that (a n = x) as (Hn_eq_x).
    By (ainK) it holds that (a n ∈ K) as (ainK_n). 
    By (Hn_eq_x) and (ainK_n) it holds that (x ∈ K).
    We conclude that K x.



  - Case (¬(∃ n : ℕ, a n = x)).
    We need to show that K x.
    By (H) it holds that ( ∀ n : ℕ, a n ≠ x) as (Hnot_hit).
    By (K_limitpoint') it suffices to show that
      (∀ ε > 0, ∃ y ∈ K, 0 < |y - x| < ε).
    Take ε > 0.
    We need to show that ∃ y ∈ K, 0 < |y - x| < ε.
    By (subseq_converges_to_x) it holds that
    (∀ ε0 > 0, ∃ N1 ∈ ℕ,
    ∀ n : ℕ, (n ≥ N1)%nat → |a (phi n) - x| < ε0)
      as (Hconverges).
    Use ε0 := ε in (Hconverges). {Indeed, ε > 0. }
    It holds that ( ∃ N1 ∈ ℕ,
    ∀ n : ℕ, (n ≥ N1)%nat → |a (phi n) - x| < ε) as (Hconverges'). 
    Obtain N1 according to (Hconverges').
    It holds that (∀ n : ℕ, (n ≥ N1)%nat → |a (phi n) - x| < ε)
      as (Htail).
    Use n := N1 in (Htail).
    It holds that (N1 ≥ N1)%nat ⇨ |a(phi(N1)) - x| < ε.
    It holds that (|a (phi N1) - x| < ε) as (Hconverges_). 
    By ainK it holds that (a(phi(N1)) ∈ K) as (ainK_phi_N1). 
    Use n := phi(N1) in (Hnot_hit).
    It holds that (a(phi(N1)) ≠ x) as (Hnot_hit_phi_N1).  
    Choose y := a(phi(N1)). {Indeed, a(phi(N1)) ∈ K. } 
    We need to show that 0 < |a(phi(N1)) - x| < ε. 
    By (Hnot_hit_phi_N1) it holds that (|a(phi(N1)) - x| > 0) 
      as (Hnot_zero). 
    By (Hnot_zero) and (Hconverges_) it holds that
      (0 < |a(phi(N1)) - x| < ε). 
    We conclude that 0 < |a(phi(N1)) - x| < ε.

  } 
  Choose phi0 := phi. 
  Choose x0 := x.
  We need to show that
    (∀ n : ℕ, (phi0 n < phi0 (S n))%nat) ∧ K x0 ∧
    (fun k => a (phi0 k)) ⟶ x0.
  It holds that (is_index_seq phi) as (Hphi0). 
  By (Hphi0) it holds that (∀ n : ℕ, (phi n < phi (S n))%nat)  
   as (Hphi0'). 
  By (Hphi0') and (x_in_K) it holds that
    (∀ n : ℕ, (phi0 n < phi0 (S n))%nat) ∧ K x0 as (Hphi0_x0). 
  By (Hphi0_x0) and (subseq_converges_to_x) it holds that
    (∀ n : ℕ, (phi0 n < phi0 (S n))%nat) ∧ K x0 ∧
    (fun k => a (phi0 k)) ⟶ x0.
  We conclude that
    (∀ n : ℕ, (phi0 n < phi0 (S n))%nat) ∧ K x0 ∧
    (fun k => a (phi0 k)) ⟶ x0.

Qed.



(** *Heine–Borel (open-cover form)*: a set [K ⊆ ℝ] is sequentially compact iff
    every open cover of [K] has a finite subcover.

    Proof idea: (⇐) if [K] were not sequentially compact, a sequence with no
    convergent-in-[K] subsequence yields an open cover with no finite subcover.
    (⇒) sequential compactness gives [K] closed and bounded; a Lebesgue-number
    argument extracts a finite subcover from any open cover. *) 


Definition every_open_cover_has_finite_subcover (K : ℝ → Prop) : Prop :=
  forall (I : Type) (U : I → (ℝ → Prop)),
    open_cover U K → has_finite_subcover U K.

Definition centered_intervals (n : ℕ) : ℝ → Prop :=
  fun x => & -1 * (INR n +1) < x < INR n + 1.




(** Proof Strategy: Construct an open cover using open sets (-n,n) 
    then obtain a finite subcover and use the maximum index of this
    to find a bound on [K].*)


Lemma finite_subcover_implies_bounded (K : ℝ → Prop) :
    every_open_cover_has_finite_subcover K →
    K is _bounded_.
Proof.
  Assume that every_open_cover_has_finite_subcover K as (Hfinite_subcover).
  By (Hfinite_subcover) it holds that
    forall (I : Type) (U : I → (ℝ → Prop)),
      open_cover U K → has_finite_subcover U K as (Kfinite_subcover).
  Use I := ℕ in (Kfinite_subcover).
  It holds that (∀ U : ℕ → (ℝ → Prop),
    open_cover U K → has_finite_subcover U K) as (Kfinite_subcover').
  Use U := (fun n => centered_intervals n) in (Kfinite_subcover').
  It holds that (open_cover (fun n => centered_intervals n) K →
    has_finite_subcover (fun n => centered_intervals n) K)
    as (Ufinite_subcover).
 
  (* ---------- the centered intervals form an open cover of K ---------- *)
  We claim that (open_cover (fun n => centered_intervals n) K) as (Ucover).
  {
    We need to show that open_cover (fun n => centered_intervals n) K.
    We need to show that
      (∀ i : ℕ, (centered_intervals i) is _open_) ∧
      (∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x).
 
    We claim that (∀ i : ℕ, (centered_intervals i) is _open_) as (Hopen).
    {
      We need to show that
        ∀ i : ℕ, (centered_intervals i) is _open_.
      Take i : ℕ.
      By pos_INR it holds that 0 ≤ INR i as (Hi).
      It holds that 0 < INR i + 1 as (Hradius).
      It holds that (-1 * (INR i + 1) < INR i + 1) as (H1).
      By (open_interval_is_open (-1 * (INR i + 1)) (INR i + 1) (H1))
        it holds that (centered_intervals i is _open_).
      We conclude that centered_intervals i is _open_.
    }
 
    We claim that (∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x)
      as (Hcover).
    {
      We need to show that
        ∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x.
      Take x : ℝ.
      Assume that K x as (x_in_K).
      By (the Archimedean property) it holds that
        (∃ n ∈ ℕ, n > |x|) as (Harch).
      Obtain n according to (Harch).
      It holds that (n + 1 > |x|) as (Harch_n).
      It holds that (& -1 * (INR n + 1) < x < INR n + 1)
        as (Harch').
      Choose i := n.
      We need to show that centered_intervals i x.
      By (Harch') it holds that centered_intervals n x.
      We conclude that centered_intervals i x.
    }
 
    By (Hcover) and (Hopen) it holds that
      (∀ i : ℕ, (centered_intervals i) is _open_) ∧
      (∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x) as (Ucover').
    We conclude that
      (∀ i : ℕ, (centered_intervals i) is _open_) ∧
      (∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x).
  }
 
  (* ---------- extract the finite subcover ---------- *)
  By (Ucover) and (Ufinite_subcover) it holds that
    (has_finite_subcover (fun n => centered_intervals n) K) as (Hfinite).
  By (Hfinite) it holds that
    (∃ I0 : list ℕ, ∀ x : ℝ, K x → ∃ i : ℕ, In i I0 ∧ centered_intervals i x)
    as (Hfinite').
  Obtain I0 according to (Hfinite').
  It holds that (∀ x : ℝ, K x → ∃ i : ℕ, In i I0 ∧ centered_intervals i x)
    as (Hfinite_cover).
 
  (* ---------- K is bounded ---------- *)
  We claim that (∃ m : ℝ, (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M)))
    as (Hbounded).
  {
    We need to show that
      ∃ m : ℝ, (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M)).
    Choose m := -1 * (INR (fold_right max 0%nat I0) + 1).
    Choose M := INR (fold_right max 0%nat I0) + 1.
    We need to show that
      ∀ x : ℝ, K x → (& m ≤ x ≤ M).
    Take x : ℝ.
 
    We claim that (forall i0 : ℕ, In i0 I0 →
      INR (fold_right max 0%nat I0) ≥ INR i0) as (Hmax).
    {
      We need to show that
        forall i0 : ℕ, In i0 I0 → INR (fold_right max 0%nat I0) ≥ INR i0.
      Take i0 : ℕ.
      Assume that In i0 I0 as (i0_in_I0).
      We need to show that INR (fold_right max 0%nat I0) ≥ INR i0.
      By (fold_right_max_geq I0 0%nat i0) it holds that
        (fold_right max 0%nat I0 ≥ i0)%nat as (Hmax').
      By (Hmax') it holds that
        (INR (fold_right max 0%nat I0) ≥ INR i0) as (Hmax'').
      We conclude that INR (fold_right max 0%nat I0) ≥ INR i0.
    }
 
    Assume that K x as (x_in_K).
    By (Hfinite_cover) it holds that
      (∃ i : ℕ, In i I0 ∧ centered_intervals i x) as (Hcover_x).
    Obtain i according to (Hcover_x).
    It holds that (In i I0 ∧ centered_intervals i x) as (Hcover_x').
    By (Hcover_x') it holds that centered_intervals i x as (x_in_interval).
    unfold centered_intervals in x_in_interval.
    (* Waterproof had issues unfolding the definition of centered_intervals**)
    By (x_in_interval) it holds that
      (& -1 * (INR i + 1) < x < INR i + 1) as (x_bounds).
 
    It holds that
      (i ≤ fold_right max 0%nat I0)%nat as (i_le_max).
    By (i_le_max) it holds that
      (-1 * (INR (fold_right max 0%nat I0) + 1) <= -1 * (INR i + 1))
      as (lower_bound).
    By (i_le_max) it holds that
      (INR i + 1 <= INR (fold_right max 0%nat I0) + 1)
      as (upper_bound).
    By (lower_bound) and (x_bounds) it holds that
      (-1 * (INR (fold_right max 0%nat I0) + 1) < x) as (x_lower_bound).
    By (upper_bound) and (x_bounds) it holds that
      (x < INR (fold_right max 0%nat I0) + 1) as (x_upper_bound).
 
    By (x_upper_bound) and (x_lower_bound) it holds that
      (& -1 * (INR (fold_right max 0%nat I0) + 1) < x
         < INR (fold_right max 0%nat I0) + 1)
      as (x_bounds').
    By (x_bounds') we conclude that (& m ≤ x ≤ M).
  }
 
  By (Hbounded) we conclude that K is bounded.
Qed.

(** The following definitions are necessary for converting a subset K into
     an index over which we can create an open cover. This makes the entire 
     syntax of the proof increadibly convoluted and hard to follow and we must 
     repeatedly pass  x ∈ K as both an element of an index and a real number 
      in K. *)


Definition K_index (K : ℝ → Prop) : Type :=
  @sig ℝ (fun y : ℝ => K y). 



Definition K_point (K : ℝ → Prop) (i : K_index K) : ℝ :=
  @proj1_sig ℝ (fun y : ℝ => K y) i.

Definition half_ball (a y : ℝ) : ℝ → Prop :=
  fun z => y -( Rabs (y - a) / 2) < z < y + (Rabs (y - a) / 2). 


Definition K_to_half_ball (K : ℝ → Prop) (a : ℝ)
    : K_index K → ℝ → Prop :=
  fun i => half_ball a (K_point K i). 

Definition make_K_index (K : ℝ → Prop) (y : ℝ) (Hy : K y) : K_index K :=
  @exist ℝ (fun z : ℝ => K z) y Hy. 


(** Proof Strategy: Follows the exact same lines as Theorem 3.3.8 in Abbot. 
   Assume [K] not closed, meaning it has a limit point x not in [K]. Define an open cover
   based on relative distance to x and derive a contradiction from the properties of  
   said cover.   *)

Lemma finite_subcover_implies_closed (K : ℝ → Prop) :
    every_open_cover_has_finite_subcover K →
    K is _closed_.
Proof.
We argue by contradiction.
Assume that
  ¬ (every_open_cover_has_finite_subcover K ⇨ 
   K is closed) as (Kcon).  
  By (Kcon) it holds that
    every_open_cover_has_finite_subcover K ∧  
     ¬(K is closed) as (Hfinite_notclosed). 
  By (Hfinite_notclosed) it holds that every_open_cover_has_finite_subcover K
    as (Kfinite). 
  By (Hfinite_notclosed) it holds that ¬(K is closed) as (Knot_closed). 
  We claim that
    ¬((∀ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε) → K x)) as (Knot_closed'). 
    { We need to show that
      ¬(∀ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε) → K x). 
      By (closed_iff_contains_limit_points K) it holds that
        (K is closed ⇔ ∀ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε) → K x)
        as (Kclosed_iff). 
      By (Kclosed_iff) and (Knot_closed) it holds that
          ¬(∀ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε) → K x)
          as (Knot_closed'). 
      We conclude that ¬(∀ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε) → K x).
    }
  By (Knot_closed') it holds that (∃ x : ℝ, (∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε)   
   ∧ ¬(K x)) as (Klim). 
  Obtain x according to (Klim). 
  It holds that ((∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε)   
   ∧ ¬(K x)) as (xlimK). 
 By (xlimK) it holds that ((∀ ε > 0, ∃ y ∈ K, 0 < Rabs (y - x) < ε)) as (xball).  
 By (xlimK) it holds that (¬(K x)) as (Knotx).
 By (Kfinite) it holds that ( forall (I : Type) (U : I → (ℝ → Prop)),
    open_cover U K → has_finite_subcover U K) as (finite_subK). 
  Use I := K_index(K) in (finite_subK).  
  It holds that
  (∀ U : K_index K → (ℝ → Prop),
    open_cover U K → has_finite_subcover U K) as (Icover). 

  (** I have to convert K into a type and then each element of 
    the type K into a real number again using proj1_sig*) 
  Use U := (K_to_half_ball K x)  
   in (Icover).  
  It holds that
  (open_cover (K_to_half_ball K x) K →
   has_finite_subcover (K_to_half_ball K x) K)
  as (Uhasfinite). 
  We claim that (∀ i : K_index(K), K_point K i ≠ x  ) as (xnotK).
   {Take i : K_index(K). 
    We argue by contradiction. 
    Assume that (¬ (K_point K i ≠ x )). 
    It holds that (K_point K i = x) as (equalx). 
    We claim that (K (K_point K i)) as (IinK). 
    {unfold K_point.
     exact (@proj2_sig ℝ (fun y : ℝ => K y) i).
    }
    By (equalx) and (IinK) it holds that (K(x)) as (Kinx) .
    Contradiction. 
  }

  We claim that open_cover (K_to_half_ball K x) K as (Uopencover).
 
     { We need to show that open_cover (K_to_half_ball K x) K. 
     unfold open_cover. 
     We claim that (∀ i, K_to_half_ball(K, x, i) is _open_) as (openU). 
     { We need to show that ∀ i : K_index K, (K_to_half_ball K x i) is _open_. 
     Take i : K_index(K).
     Use i := i in (xnotK).
     It holds that K_point K i ≠ x as (xnotI). 
     By (neq_implies_abs_pos(K_point K i)(x) (xnotI)) it holds that 
      (0 < | x - K_point K i |) as (diffpos). 
     By (diffpos) it holds that 
      (Rabs(x - K_point K i) > 0) as (diffpos2).
     By (diffpos2) it holds that ((K_point K i - Rabs (K_point K i - x) / 2) 
     < (K_point K i + Rabs (K_point K i - x) / 2)) as 
     (Hab).
     By (open_interval_is_open (K_point K i - Rabs (K_point K i - x) / 2)  
      (K_point K i + Rabs (K_point K i - x) / 2) (Hab)) it holds that
      (K_to_half_ball(K, x, i) is open). 
      We conclude that (K_to_half_ball(K, x, i) is open).
     }

    We claim that (∀ x0, K(x0) ⇨ ∃ i, K_to_half_ball(K, x, i, x0)) as (U_iscover).
    {Take x0 : ℝ. 
     Assume that K x0 as (xincluded). 
     Choose i := make_K_index K x0 xincluded. 

     (** Here we use a little bit of rocq to get waterproof to recognise that
          our different representations of elements of K are the same object*)

        
     We claim that (K_point K (make_K_index K x0 xincluded) = x0) as (xisx).
     {unfold K_point, make_K_index. 
     reflexivity.
     }


     We need to show that (x0 ∈ half_ball x (K_point K i)). 
     We need to show that (x0 ∈ half_ball x (x0)).  
     It holds that x0 ≠ x as (x0notx).
     By (x0notx) it holds that (& x0 -( Rabs (x0 - x) / 2) < x0 <  
      x0 + (Rabs (x0 - x) / 2)) as (x0ball). 
    We conclude that (x0 ∈ half_ball x (x0)).
    }
    We conclude that ((∀ i, K_to_half_ball(K, x, i) is _open_)
     ∧ (∀ x0, K(x0) ⇨ ∃ i, 
      K_to_half_ball(K, x, i, x0))).
     }

By (Uhasfinite) and (Uopencover) it holds that 
 (has_finite_subcover (K_to_half_ball K x) K) as (Ufinitecover). 
 By (Ufinitecover) it holds that (∃ l : list (K_index(K)),  
  ∀ y : ℝ, K y → ∃ i : K_index(K), 
   In i l ∧ (K_to_half_ball K x i) y)
   as (finite_cover).  
  Obtain l according to (finite_cover).
  It holds that (∀ y : ℝ, K y → ∃ i : K_index(K), 
   In i l ∧ (K_to_half_ball K x i) y) as (lcover).


  We claim that (l ≠ nil) as (lnonempty). 
  {By (xball) it holds that
    (∃ y ∈ K, 0 < Rabs (y - x) < 1) as (yexists).
  Obtain y according to (yexists).
  It holds that y ∈ K as (yinK).
  By (lcover) and (yinK) it holds that
    (∃ i : K_index K,
      In i l ∧ (K_to_half_ball K x i) y) as (iinlist).
  Obtain i according to (iinlist).
  It holds that In i l as (iinl).

  Assume that l = nil as (Hnil). 

  By (Hnil) it holds that In i nil as (inil).
  Contradiction.

  }
  We claim that ( ∃ i : K_index K,
    In i l ∧ ∀ j : K_index K, In j l →
    Rabs (K_point K i - x) ≤ Rabs (K_point K j - x))  
    as (minrad). 

   {By (list_has_min (K_index K) (fun i => Rabs (K_point K i - x)) l) 
     we conclude that (∃ i : K_index K,
    In i l ∧ ∀ j : K_index K, In j l →
    Rabs (K_point K i - x) ≤ Rabs (K_point K j - x)).

   }
 Obtain i according to (minrad).
 It holds that ( In i l ∧ ∀ j : K_index K, In j l →
    Rabs (K_point K i - x) ≤ Rabs (K_point K j - x)) as (Imin). 

 Use ε := ( Rabs (K_point K i - x)) / 4 in (xball). 
   {We need to verify that Rabs (K_point K i - x) / 4 > 0.  
    It holds that K_point K i ≠ x as (inotx). 
    By (neq_implies_abs_pos(K_point K i)(x) (inotx)) it holds that 
      (0 < | x - K_point K i |) as (diffpos). 
     By (diffpos) it holds that 
      (Rabs(x - K_point K i) > 0) as (diffpos2).  
     We conclude that Rabs (K_point K i - x) / 4 > 0. } 
  It holds that ∃ y ∈ K,
    0 < |y - x| < |K_point(K, i) - x| / 4 as (ytight).
  Obtain y according to (ytight).



  We claim that (¬(K y)) as (ContY).
  {It holds that (& 0 < |y - x| < |K_point(K, i) - x| / 4) as (ybound).
    We argue by contradiction.
    Assume that ¬ (¬ K y) as (Hny).
    By NNPP it holds that K y as (Hy).
    By (lcover) and Hy it holds that
      (∃ j : K_index K,
        In j l ∧ (K_to_half_ball K x j) y) as (covered_y).
    Obtain j according to (covered_y).
    It holds that In j l as (Hjl).
    It holds that (K_to_half_ball K x j) y as (Hyj).

    By (Imin) it holds that
      (∀ j : K_index K, In j l →
        Rabs (K_point K i - x) ≤ Rabs (K_point K j - x)) as (Hmin).
    By (Hmin) and Hjl it holds that
      (Rabs (K_point K i - x) ≤ Rabs (K_point K j - x)) as (Hijd).
    It holds that
      (K_point K j - Rabs (K_point K j - x) / 2 < y <
       K_point K j + Rabs (K_point K j - x) / 2) as (Hyinterval).
    It holds that
      (- (Rabs (K_point K j - x) / 2) ≤ K_point K j - y ∧
       K_point K j - y ≤ Rabs (K_point K j - x) / 2) as (Hcenterbounds).
    By Rabs_le it holds that
      (Rabs (K_point K j - y) ≤ Rabs (K_point K j - x) / 2) as (Hyjdist).
    It holds that
      (0 < Rabs (K_point K j - x)) as (Hjpos).
    It holds that
      (0 < Rabs (K_point K i - x)) as (Hipos).
    It holds that
      (Rabs (y - x) < Rabs (K_point K i - x) / 4) as (Hytight).
    It holds that
      (Rabs (y - x) < Rabs (K_point K j - x) / 4) as (Hytightj).
    By Rabs_triang it holds that
      (Rabs ((K_point K j - y) + (y - x)) ≤
       Rabs (K_point K j - y) + Rabs (y - x)) as (Htriangle).
    It holds that
      ((K_point K j - y) + (y - x) = K_point K j - x) as (Hsum).
    It holds that
      (Rabs (K_point K j - x) ≤
       Rabs (K_point K j - y) + Rabs (y - x)) as (Htriangle').
    It holds that
      (Rabs (K_point K j - x) ≤
       Rabs (K_point K j - x) / 2 +
       Rabs (K_point K j - x) / 4) as (Hbound).
    By (Hjpos) it holds that
      (Rabs (K_point K j - x) / 2 +
       Rabs (K_point K j - x) / 4 <
       Rabs (K_point K j - x)) as (Hstrict).
    By (Hbound) and Hstrict we conclude that False.
  

   } 
   Contradiction.

Qed.

Definition shifted_seq (a : ℕ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun k => a ((n + k)%nat). 



Definition shifted_n (a : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := 
fun k => (n + a(k))%nat.


(** Lemma: Lebesgue Number 

 Lebesgue number: If K is sequentially compact and {U_i} 
 is an open cover of K, then there is δ > 0 such that every x ∈ K  
 has (x − δ, x + δ) ⊆ U_i for some i.

   Proof idea: Argue by contradiction. Then use the sequence of δ_n := 1/n 
   There must be an x_n such that its B(δ_n, x) is not contained in any U_i 
   use the sequential compactness of [K] to conclude that a subsequence must 
   converge in [K] to x (and be an element of some open set of the cover) and show  
   that there some centered delta balls must be completely contained within an 
   epsilon ball of x aand therefore contained in some U_j, contradicting our 
   assumption.

*)



Lemma Lebesgue_number (K : ℝ → Prop) (Index : Type)
    (U : Index → (ℝ → Prop)) :
  sequentially_compact K →
  open_cover U K →
  ∃ δ > 0, ∀ x : ℝ, K x →
    ∃ i : Index, ∀ y : ℝ, y ∈ open_ball x δ → U i y.
Proof. 
 Assume that sequentially_compact(K) as (K_comp). 
 Assume that open_cover U K as (Ucover). 
 We argue by contradiction.
 Assume that ¬ ( ∃ δ > 0, ∀ x : ℝ, K x →
    ∃ i , ∀ y : ℝ, y ∈ open_ball x δ → U i y).
 It holds that (∀ δ > 0, ¬( ∀ x : ℝ, K x →
    ∃ i , ∀ y : ℝ, y ∈ open_ball x δ → U i y)).
 It holds that ( ∀ δ > 0, ∃ x : ℝ, ¬(K x →
    ∃ i , ∀ y : ℝ, y ∈ open_ball x δ → U i y)). 
 It holds that (∀ δ > 0, ∃ x : ℝ, K x ∧ 
   ¬(∃ i , ∀ y : ℝ, y ∈ open_ball x δ → U i y)). 
 It holds that (∀ δ > 0, ∃ x : ℝ, K x ∧ 
   (∀ i, ∃ y : ℝ, ¬ (y ∈ open_ball x δ → U i y))). 
 It holds that (∀ δ > 0, ∃ x : ℝ, K x ∧ 
   (∀ i, ∃ y : ℝ, (y ∈ open_ball x δ) ∧ ¬(U i y))) as (contra). 


 We claim that (∀ n : ℕ,  ∃ x : ℝ, K x ∧ (∀ i : Index, ∃ y : ℝ,( 
   y ∈ open_ball x (/(n + 1)) ∧ ¬(U i y)))) as (n_seq). 
   { Take n : ℕ. 
     Use δ := /(n + 1) in (contra). 
     { Indeed, / (n + 1) > 0. } 
     It holds that ∃ x, K(x) ∧ (∀ i, ∃ y, 
       y ∈ B(x, / (n + 1)) ∧ ¬ U(i, y)) as (n_uncover). 
     Obtain x according to (n_uncover). 
     Choose x0 := x. 
     It holds that K x as(x_inK). 
     It holds that (∀ i : Index, ∃ y : ℝ,( 
       y ∈ open_ball x (/(n + 1)) ∧ ¬(U i y))) as (x_uncover). 
     By (x_inK) and (x_uncover) we conclude that (K x ∧ (∀ i : Index, ∃ y : ℝ,( 
       y ∈ open_ball x (/(n + 1)) ∧ ¬(U i y)))).
   }
 By (countable_choice
  (fun n x =>
    K x ∧
    (∀ i : Index, ∃ y : ℝ, y ∈ open_ball x (/(n + 1)) 
     ∧ ¬ U i y)) n_seq)

   it holds that
     (∃ g : ℕ → ℝ, ∀ n : ℕ, K (g n) ∧
     (∀ i : Index, ∃ y : ℝ,
      y ∈ open_ball (g n) (/(n + 1)) ∧ ¬ U i y))
  as (bad_seq). 
  Obtain g according to (bad_seq). 

  We claim that (∀ n, (∀ i : Index, ∃ y : ℝ,
    y ∈ open_ball (g n) (/(n + 1)) ∧ ¬ U i y)) as (n_uncover).
      {Take n : ℕ. 
       Use n0 := n in (_H4). 
       It holds that (K (g n) ∧ (∀ i : Index, ∃ y : ℝ,
         y ∈ open_ball (g n) (/(n + 1)) ∧ ¬ U i y)) as (y_bad). 
       By (y_bad) we conclude that (∀ i : Index, ∃ y : ℝ,
         y ∈ open_ball (g n) (/(n + 1)) ∧ ¬ U i y).
      } 

  We claim that ( ∀ n, K(g(n))) as (g_inK). 
  { Take n : ℕ. 
   Use n0 := n in (_H4). 
   It holds that (K (g n) ∧
     (∀ i : Index, ∃ y : ℝ,
      y ∈ open_ball (g n) (/(n + 1)) ∧ ¬ U i y)) as (n_good). 
   By (n_good) we conclude that (K(g(n))).

  }
  By K_comp it holds that
  (∀ a : ℕ → ℝ,
    (∀ n : ℕ, a n ∈ K) →
    ∃ phi : ℕ → ℕ, ∃ x : ℝ,
      (∀ n : ℕ, (phi n < phi (S n))%nat) ∧
      K x ∧ (fun k => a (phi k)) ⟶ x)
  as (K_comp_explicit).

 Use a := g in (K_comp_explicit). 
 It holds that ((∀ n : ℕ, g n ∈ K) →
    ∃ phi : ℕ → ℕ, ∃ x : ℝ,
      (∀ n : ℕ, (phi n < phi (S n))%nat) ∧
      K x ∧ (fun k => g (phi k)) ⟶ x) as (ghas_sub). 
 By (ghas_sub(g_inK)) it holds that (∃ phi : ℕ → ℕ, ∃ x : ℝ,
      (∀ n : ℕ, (phi n < phi (S n))%nat) ∧
      K x ∧ (fun k => g (phi k)) ⟶ x) as (g_sub). 
  Obtain phi according to (g_sub).
  Obtain x according to (_H5). 
  By (Ucover) it holds that ((∀ i : Index, (U i) is _open_) ∧ 
  (∀ x : ℝ, K x → ∃ i : Index, U i x)) as (K_covered).
  By (K_covered) it holds that 
   (∀ x : ℝ, K x → ∃ i : Index, U i x) as (Ucovering).
  Use x0 := x in (Ucovering). 
  It holds that K x → ∃ i : Index, U i x as (x_iscovered). 
  By (x_iscovered(_H8)) it holds that (∃ i : Index, U i x) as (xcover).
  Obtain j according to (xcover).
  It holds that ((fun k => g (phi k)) ⟶ x) as (g_lim).
   By g_lim it holds that
     (∀ ε > 0, ∃ N ∈ ℕ, ∀ k ≥ N, |g (phi k) - x| < ε)
     as (g_lim_eps).
  By (K_covered) it holds that (∀ i :Index, U i is open) as (U_open).
  Use i := j in (U_open). 
  It holds that (U j is open) as (j_open). 
  By (j_open) it holds that (∀ a ∈ U j, is_interior_point(a) (U(j)))
    as (a_interior). 
  Use a := x in (a_interior). 
   { Indeed, x ∈ U(j). }
  It holds that x is an _interior point_ of U(j) as (x_interior).
  By (x_interior) it holds that (∃ r > 0, ∀ y ∈ (open_ball x r), y ∈ U j) 
    as (x_ball). 
  Obtain r according to (x_ball). 
  It holds that (r > 0) as (rpos).
  It holds that ((∀ n : ℕ, (phi n < phi (S n))%nat) ∧
    K x ∧ (fun k => g (phi k)) ⟶ x) as (phi_x).
  Because (phi_x) both ((∀ n : ℕ, (phi n < phi (S n))%nat)) as (phi_inc)
    and (K x ∧ (fun k => g (phi k)) ⟶ x) as (phi_rest).
 
  (* the ball statement from x_ball, restated so we can name it *)
  It holds that (∀ y ∈ (open_ball x r), y ∈ U j) as (r_ball).
 
  (* --- 1. phi is strictly increasing, hence k ≤ phi k ------------- *)
  We claim that (∀ k : ℕ, (k ≤ phi k)%nat) as (phi_ge).
  { We use induction on k.
    + We first show the base case ((0 ≤ phi 0)%nat).
      We conclude that ((0 ≤ phi 0)%nat).
    + We now show the induction step.
      Take k : ℕ.
      Assume that ((k ≤ phi k)%nat) as (IH).
      Use n := k in (phi_inc).
      It holds that ((phi k < phi (S k))%nat) as (step).
      By (step) it holds that (k < phi(S k))%nat as (step2). 
      It holds that (k + 1 <= phi(S k))%nat as (step3). 
      It holds that (S k = k + 1)%nat.
      By (step3) we conclude that (( k+ 1 ≤ phi ( k + 1))%nat).
  }
 
  (* --- 2. a threshold M for the radii 1/(n+1) -------------------- *)
  It holds that (r / 2 > 0) as (rhalf_pos).
  By (archimedean_2 (r / 2) rhalf_pos) it holds that
    (∃ M : ℕ, 1 / (M + 1) < r / 2) as (arch_half).
  Obtain M according to (arch_half).
  It holds that (/ (M + 1) < r / 2) as (arch_inv).
 
  (* --- 3. a threshold N1 for the convergence, with epsilon = r/2 -- *)
  Use ε := (r / 2) in (g_lim_eps).
    { Indeed, r / 2 > 0. }
  It holds that (∃ N1 ∈ ℕ, ∀ k ≥ N1, |g (phi k) - x| < r / 2) as (half_tail).
  Obtain N1 according to (half_tail).
  It holds that (∀ k : ℕ, (k ≥ N1)%nat → |g (phi k) - x| < r / 2) as (Htail).
 
  (* --- 4. one index k that is past BOTH thresholds ---------------- *)
  We claim that (∃ k : ℕ, (k ≥ N1)%nat ∧ (k ≥ M)%nat) as (big_k).
  { Choose k0 := (N1 + M)%nat.
    We show both statements.
    + We need to show that ((N1 + M ≥ N1)%nat).
      We conclude that ((N1 + M ≥ N1)%nat).
    + We need to show that ((N1 + M ≥ M)%nat).
      We conclude that ((N1 + M ≥ M)%nat).
  }
  Obtain k according to (big_k).
  It holds that ((k ≥ N1)%nat ∧ (k ≥ M)%nat) as (k_bounds).
  Because (k_bounds) both ((k ≥ N1)%nat) as (k_N1)
    and ((k ≥ M)%nat) as (k_M).
 
  (* --- 5. the subsequence term is within r/2 of x ----------------- *)
  By (Htail k k_N1) it holds that (|g (phi k) - x| < r / 2) as (close).
 
  (* --- 6. the bad ball at index phi k has radius < r/2 ------------ *)
  By (phi_ge k) it holds that ((k ≤ phi k)%nat) as (k_phi).
  By (Nat.le_trans M k (phi k) k_M k_phi) it holds that
  (M ≤ phi k)%nat as (M_phi).
  By (le_INR M (phi k) M_phi) it holds that (INR M ≤ INR (phi k)) as (INR_le).
  By (pos_INR M) it holds that (0 ≤ INR M) as (INR_pos).
  It holds that (0 < INR M + 1) as (M_pos).
  It holds that (INR M + 1 ≤ INR (phi k) + 1) as (INR_le1).
  By (Rinv_le_contravar (INR M + 1) (INR (phi k) + 1) M_pos INR_le1)
    it holds that (/ (INR (phi k) + 1) ≤ / (INR M + 1)) as (inv_le).
  It holds that (/ (phi k + 1) < r / 2) as (rad_small).
 
  (* --- 7. the bad ball sits inside B(x, r) ------------------------ *)
  We claim that (∀ y : ℝ, y ∈ open_ball (g (phi k)) (/ (phi k + 1)) →
    y ∈ open_ball x r) as (ball_sub).
  { Take y : ℝ.
    Assume that (y ∈ open_ball (g (phi k)) (/ (phi k + 1))) as (y_in).
    By (y_in) it holds that (|y - g (phi k)| < / (phi k + 1)) as (y_abs).
    By (Rabs_triang (y - g (phi k)) (g (phi k) - x)) it holds that
      (|(y - g (phi k)) + (g (phi k) - x)|
         ≤ |y - g (phi k)| + |g (phi k) - x|) as (tri).
    It holds that ((y - g (phi k)) + (g (phi k) - x) = y - x) as (alg).
    rewrite alg in tri.
    It holds that (|y - x| < r) as (y_r).
    We conclude that (y ∈ open_ball x r).
  }
 
  (* --- 8. the contradiction --------------------------------------- *)
  By (n_uncover (phi k)) it holds that (∀ i : Index, ∃ y : ℝ,
    y ∈ open_ball (g (phi k)) (/ (phi k + 1)) ∧ ¬ U i y) as (bad_at).
  By (bad_at j) it holds that (∃ y : ℝ,
    y ∈ open_ball (g (phi k)) (/ (phi k + 1)) ∧ ¬ U j y) as (y_bad).
  Obtain y according to (y_bad).
  It holds that (y ∈ open_ball (g (phi k)) (/ (phi k + 1)) ∧ ¬ U j y)
    as (y_props).
  Because (y_props) both (y ∈ open_ball (g (phi k)) (/ (phi k + 1))) as (y_in_bad)
    and (¬ U j y) as (y_notU).
  By (ball_sub y y_in_bad) it holds that (y ∈ open_ball x r) as (y_in_r).
  By (r_ball y y_in_r) it holds that (U j y) as (y_inU).
  Contradiction.
Qed.

(** A lemma that shows that for a bounded set [K] for which a Lebesgue number type 
 property holds for a given Open Cover, then a finite a finite subcover exists for 
  said cover. 
  
  
   Proof Idea: Induct on the upper bound of [K] based on δ and lower bound a. 
    [Base Case]: Strict upper bound is lower bound and therefore [K] = ∅ 
     [Induction step]: Any element is either bounded by the previous upper bound and 
     therefore inside the finite subcover recovered from the Induction Hypothesis 
     or it is in the new increment which is entirely covered  by some open 
     set U_j by the Lebesgue number type assumption.  *)

Lemma finite_cover_on_delta (Index : Type) (U : Index → (ℝ → Prop)) (K : ℝ → Prop)
    (a δ : ℝ) :
  δ > 0 →
  (∀ x : ℝ, K x → a ≤ x) →
  (∀ x : ℝ, K x → ∃ i : Index, ∀ y : ℝ, y ∈ open_ball x δ → U i y) →
  ∀ n0 : ℕ, ∃ l : list Index, ∀ x : ℝ, K x → x < a + INR n0 * (δ / 2) →
    ∃ i : Index, In i l ∧ U i x.
Proof.
  Assume that δ > 0 as (δpos).
  Assume that (∀ x : ℝ, K x → a ≤ x) as (Hlow).
  Assume that (∀ x : ℝ, K x → ∃ i : Index,
    ∀ y : ℝ, y ∈ open_ball x δ → U i y) as (Hleb).
  We use induction on n0.
 
  (* ---------- base case: nothing lies below a ---------- *)
  + We first show the base case
      (∃ l : list Index, ∀ x : ℝ, K x → x < a + INR 0 * (δ / 2) →
        ∃ i : Index, In i l ∧ U i x).
    Choose l0 := (@nil Index).
    We need to show that
      (∀ x : ℝ, K x → x < a + INR 0 * (δ / 2) →
        ∃ i : Index, In i (@nil Index) ∧ U i x).
    Take x : ℝ.
    Assume that (K x) as (xK).
    Assume that (x < a + INR 0 * (δ / 2)) as (xlt).
    By (Hlow x xK) it holds that (a ≤ x) as (ax).
    We claim that (INR 0 = 0) as (INR0).
    { reflexivity. }
    rewrite INR0 in xlt.
    exfalso.
    Contradiction.
 
  (* ---------- induction step ---------- *)
  + We now show the induction step.
    Take n0 : ℕ.
    Assume that (∃ l : list Index, ∀ x : ℝ, K x → x < a + INR n0 * (δ / 2) →
      ∃ i : Index, In i l ∧ U i x) as (IH).
    Obtain l according to (IH).
    It holds that (∀ x : ℝ, K x → x < a + INR n0 * (δ / 2) →
      ∃ i : Index, In i l ∧ U i x) as (IHl).
    By (S_INR n0) it holds that (INR (S n0) = INR n0 + 1) as (HS).
    We claim that (a + INR (S n0) * (δ / 2) = a + INR n0 * (δ / 2) + δ / 2)
      as (Hexp).
    { 
      rewrite S_INR. 
      We conclude that (a + (n0 + 1) * (δ / 2) =
       a + n0 * (δ / 2) + δ / 2).
       }
 
    (* is the new piece K ∩ [a+n0*h, a+n0*h+h) empty or not? *)
    destruct (classic (∃ x0 : ℝ, K x0 ∧
      (a + INR n0 * (δ / 2) ≤ x0 ∧ x0 < a + INR n0 * (δ / 2) + δ / 2)))
      as [Hex | Hnex].
 
    (* --- new piece nonempty: add one index i0 to the list --- *)
    - Obtain x0 according to (Hex).
      It holds that (K x0 ∧
        (a + INR n0 * (δ / 2) ≤ x0 ∧ x0 < a + INR n0 * (δ / 2) + δ / 2))
        as (Hx0).
      Because (Hx0) both (K x0) as (x0K)
        and (a + INR n0 * (δ / 2) ≤ x0 ∧ x0 < a + INR n0 * (δ / 2) + δ / 2)
        as (x0piece).
      By (Hleb x0 x0K) it holds that
        (∃ i : Index, ∀ y : ℝ, y ∈ open_ball x0 δ → U i y) as (Hi0).
      Obtain i0 according to (Hi0).
      It holds that (∀ y : ℝ, y ∈ open_ball x0 δ → U i0 y) as (Hi0ball).
      Choose l0 := (i0 :: l).
      
      Take x : ℝ.
      Assume that (K x) as (xK).
      Assume that (x < a + INR (n0 + 1)%nat * (δ / 2)) as (xlt).
      Either x < a + INR n0 * (δ / 2) or x ≥ a + INR n0 * (δ / 2).
 
      + Case (x < a + INR n0 * (δ / 2)).
        By (IHl x xK) it holds that
          (x < a + INR n0 * (δ / 2) → ∃ i : Index, In i l ∧ U i x) as (IHx).
        By (IHx) it holds that (∃ i : Index, In i l ∧ U i x) as (Hold).
        Obtain i according to (Hold).
        It holds that (In i l ∧ U i x) as (Hi).
        Because (Hi) both (In i l) as (iinl) and (U i x) as (Uix).
        Choose i1 := i.
        We need to show that (In i (i0 :: l) ∧ U i x).
        We show both statements.
        * We need to show that (In i (i0 :: l)).
          simpl. right. exact iinl.
        * We need to show that (U i x).
          We conclude that (U i x).
 
      + Case (x ≥ a + INR n0 * (δ / 2)).
        (* x and x0 both lie in the new piece, so |x - x0| < h < δ *)
        Because (x0piece) both
        (a + INR n0 * (δ / 2) ≤ x0) as (x0lower) and
        (x0 < a + INR n0 * (δ / 2) + δ / 2) as (x0upper).
      (**the next line was really slow to verify so rocq was used to
          quicken the pace*)
       rewrite Nat.add_1_r in xlt.
       rewrite Hexp in xlt.
       We claim that
        (x < a + INR n0 * (δ / 2) + δ / 2) as (xupper).
       { exact xlt. }
        We claim that (x - x0 < δ) as (H1).
        { By (δpos) it holds that ( δ / 2 < δ) as (halfδ).
         By (x0upper) and (xupper) it holds that (x - x0 < δ / 2) 
          as (Half1).
          By (Half1) and (halfδ) we conclude that (x - x0 < δ). }
        We claim that (-δ < x - x0) as (H2).
        { We conclude that (-δ < x - x0). }
        By (Rabs_def1 (x - x0) δ H1 H2) it holds that (|x - x0| < δ) as (xabs).
        We claim that (x ∈ open_ball x0 δ) as (xball).
        { We conclude that (x ∈ open_ball x0 δ). }
        By (Hi0ball x xball) it holds that (U i0 x) as (Ui0x).
        Choose i1 := i0.
        We need to show that (In i0 (i0 :: l) ∧ U i0 x).
        We show both statements.
        * We need to show that (In i0 (i0 :: l)).
          simpl. left. reflexivity.
        * We need to show that (U i0 x).
          We conclude that (U i0 x).
 
    (* --- new piece empty: keep the old list --- *)
    - Choose l0 := l.
      We need to show that
        (∀ x : ℝ, K x → x < a + INR (n0 + 1)%nat * (δ / 2) →
          ∃ i : Index, In i l ∧ U i x).
      Take x : ℝ.
      Assume that (K x) as (xK).
      Assume that (x < a + INR (n0 + 1)%nat * (δ / 2)) as (xlt).
      Either x < a + INR n0 * (δ / 2) or x ≥ a + INR n0 * (δ / 2).
 
      + Case (x < a + INR n0 * (δ / 2)).
        By (IHl x xK) it holds that
          (x < a + INR n0 * (δ / 2) → ∃ i : Index, In i l ∧ U i x) as (IHx).
        By (IHx) we conclude that (∃ i : Index, In i l ∧ U i x).
 
      + Case (x ≥ a + INR n0 * (δ / 2)).
        (* x would be a point of the empty piece: contradiction *)
        rewrite Nat.add_1_r in xlt.
        rewrite Hexp in xlt.
        We claim that
          (x < a + INR n0 * (δ / 2) + δ / 2) as (xupper).
        { exact xlt. }
        It holds that (∃ x0 : ℝ, K x0 ∧
          (a + INR n0 * (δ / 2) ≤ x0 ∧ x0 < a + INR n0 * (δ / 2) + δ / 2))
          as (Hbad).
        exfalso.
        Contradiction.
Qed.


(** ** Heine-Borel (Open Cover) theorem *)

(** Heine–Borel theorem: a subset of ℝ is sequentially compact iff every open cover
  has a finite subcover.

    Proof idea: (⇒) Use the lebesgue number lemma to construct half open intervals I_j that cover 
    the entire bounded region [K] lies within by Heine Borel. Any non-empty I_j ⋂ [K] will be contained
    within some U_i by the property of the chosen δ. As there are finitely many I_j this means that we 
    can choose finitely many U_i to cover [K] (proven in the previous Lemma). (⇐) Use the previous 
    finite_cover lemmas and Heine Borel to conclude that [K] must be sequentially compact *)

Theorem compact_iff_finite_subcover (K : ℝ → Prop) :
    sequentially_compact K ⇔
    (forall (Index : Type) (U : Index → (ℝ → Prop)),
        open_cover U K → has_finite_subcover U K).
Proof.
(** Had to use rocq syntax here as waterproof simply could not identify the
  goals properly.*)
split.
- intros Hseq Index U Hcover.
  (* prove has_finite_subcover U K *) 
  By (Lebesgue_number(K)(Index)(U)) it holds that 
  ( sequentially_compact K →
  open_cover U K →
  ∃ δ > 0, ∀ x : ℝ, K x →
    ∃ i : Index, ∀ y : ℝ, y ∈ open_ball x δ → U i y) as (LebesgueK). 
  By (LebesgueK(Hseq)(Hcover)) it holds that ( ∃ δ > 0, ∀ x : ℝ, K x →
    ∃ i : Index, ∀ y : ℝ, y ∈ open_ball x δ → U i y) as (DeltaU). 
  Obtain δ according to (DeltaU). 
  By (Sequentially_compact_implies_bounded(K)(Hseq)) it holds that (K is _bounded_) 
   as (K_bound) . 
  By (K_bound) it holds that (∃ m : ℝ, (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M))) 
   as (exactbound). 
  Obtain m according to (exactbound). 
  By (_H1) it holds that (∃ M : ℝ, ∀ x : ℝ, K(x) ⇨ (& m ≤ x ≤ M))  
  as (Upperbound).  
  Obtain M according to (Upperbound).
  It holds that (∀ x : ℝ, K(x) ⇨ (& m ≤ x ≤ M)) as (bounds).
  We claim that (∀ x : ℝ, K(x) ⇨ ( m ≤ x)) as (lowerbound). 
  {Take x : ℝ. 
   Use x0 := x in (bounds).  
   It holds that K(x) ⇨ & m ≤ x ≤ M. 
   Assume that K(x). 
   It holds that (& m ≤ x ≤ M). 
   We conclude that (m ≤ x).
  } 
  By (finite_cover_on_delta(Index)(U)(K)(m) (δ)) it holds that
   (δ > 0 →
  (∀ x : ℝ, K x → m ≤ x) →
  (∀ x : ℝ, K x → ∃ i : Index, ∀ y : ℝ, y ∈ open_ball x δ → U i y) →
  ∀ n0 : ℕ, ∃ l : list Index, ∀ x : ℝ, K x → x < m + INR n0 * (δ / 2) →
    ∃ i : Index, In i l ∧ U i x) as (implication). 
  By (implication(_H0)(lowerbound)) it holds that 
   ((∀ x : ℝ, K x → ∃ i : Index, ∀ y : ℝ, y ∈ open_ball x δ → U i y) →
  ∀ n0 : ℕ, ∃ l : list Index, ∀ x : ℝ, K x → x < m + INR n0 * (δ / 2) →
    ∃ i : Index, In i l ∧ U i x) as (smallimp). 
  By (smallimp(_H)) it holds that (∀ n0 : ℕ, ∃ l : list Index, ∀ x : ℝ, K x → x < m + INR n0 * (δ / 2) →
    ∃ i : Index, In i l ∧ U i x) as (nlist).  
  By archimedean_1 it holds that  ∃ n : ℕ, INR n > ((2 / δ) * (M - m)) as (Hn). 
  Obtain n according to (Hn). 
  Use n0 := n in (nlist). 
  It holds that (∃ l : list Index, ∀ x : ℝ, K x → x < m + INR n * (δ / 2) →
    ∃ i : Index, In i l ∧ U i x) as (newlist). 
  We claim that (∀ x : ℝ, K x → x < m + INR n * (δ / 2)) as (naturalbound).
  { Take x : ℝ. 
    Assume that K(x) as (xinK). 
    Use x0 := x in (bounds). 
    It holds that K(x) ⇨ (& m ≤ x ≤ M) as (xbounds). 
    By (xinK) and (xbounds) it holds that (& m ≤ x ≤ M) as (xbounded).
    By (xbounded) it holds that (x <= M) as (xupper). 
    By (xupper) it holds that (x <= m + (M - m)) as (redundbound).  
    It holds that ((δ / 2) * (2 / δ) = 1) as (recip).
    By (redundbound) and (recip) it holds that  
     (x <= m + (δ / 2) * (2 / δ)* (M - m)) as (last_bound). 
    By (last_bound) and (_H3) it holds that (x < m + n * (δ / 2)). 
    We conclude that x < m + n * (δ / 2).
  }
 Obtain l according to (newlist). 
 It holds that (∀ x : ℝ, K x → x < m + INR n * (δ / 2) →
    ∃ i : Index, In i l ∧ U i x) as (listimp). 
  We claim that (∀ x : ℝ, K x →
    ∃ i : Index, In i l ∧ U i x) as (finitecover). 
    { Take x : ℝ. 
    Assume that K x as (xink). 
    Use x0 := x in (listimp). 
    It holds that (K x → x < m + INR n * (δ / 2) →
     ∃ i : Index, In i l ∧ U i x) as (xfincover). 
    By (xfincover) and (xink) it holds that (x < m + INR n * (δ / 2) →
     ∃ i : Index, In i l ∧ U i x) as (Bound_cov).  
    Use x0 := x in (naturalbound).
    It holds that K(x) ⇨ x < m + n * (δ / 2). 
    It holds that x < m + n * (δ / 2). 
    By (Bound_cov) we conclude that (∃ i, In(Index, i, l) ∧ U(i, x)).

    } 
  We need to show that (∃ l : list Index, ∀ x : ℝ, K x → ∃ i : Index, In i l ∧ U i x). 
  Choose l0 := l. 
  By (finitecover) we conclude that (∀ x, K(x) ⇨ ∃ i, In(Index, i, l0) ∧ U(i, x)).
  

- intros Hfinite.
  (* prove sequentially_compact K *) 
  By (finite_subcover_implies_bounded(K)) it holds that 
  (every_open_cover_has_finite_subcover K →
    K is _bounded_) as (Kbounds). 
  By (Hfinite) it holds that (every_open_cover_has_finite_subcover K) as (compK). 
  By (Kbounds) it holds that (K is _bounded_) as (Kbounded).
  By (finite_subcover_implies_closed(K)(compK)) it holds that (K is _closed_). 
  By (Sequential_Heine_Borel(K)) it holds that ((sequentially_compact(K)) ⇔ (K is _closed_ ∧ K is _bounded_)). 
  It holds that (K is _closed_ ∧ K is _bounded_). 
  We conclude that sequentially_compact(K).

Qed.



(** ** Nested compact sets *)

(** A decreasing sequence of nonempty compact sets has nonempty intersection.

    Proof idea: a generalization of the nested interval property. Picking a point
    [xₙ ∈ Kₙ], compactness of [K₀] gives a subsequence converging to some [x];
    since each [Kₙ] is closed and eventually contains the tail of the
    subsequence, [x ∈ Kₙ] for every [n]. *)

Theorem nested_compact_intersection_nonempty
    (K : ℕ → (ℝ → Prop))
    (HK_nonempty : ∀ n : ℕ, ∃ x : ℝ, K n x)
    (HK_compact  : ∀ n : ℕ, sequentially_compact (K n))
    (HK_nested   : ∀ n ∈ ℕ, ∀ m ∈ ℕ, (m ≤ n)%nat → ∀ x ∈ ℝ, K n x → K m x) :
    ∃ x : ℝ, ∀ n : ℕ, K n x.
Proof.
By (countable_choice(K)(HK_nonempty)) it holds that
 (∃ f : ℕ → ℝ, ∀ n : ℕ, K n (f n)) as (Nested_seq). 
 Obtain f0 according to (Nested_seq). 
 By (HK_compact) it holds that (sequentially_compact(K 0%nat))
 as (K0_compact).  
 We claim that (∀ n : ℕ, K 0%nat (f0 n)) as (f_inK0). 
 {Take n : ℕ. 
 Use n0 := n in (_H). 
 It holds that (K(n, f0(n))) as (fn_inK). 
 It holds that (0 <= n)%nat as (nsmall). 
 Use n := n in (HK_nested). { Indeed, n ∈ ℕ. }
 It holds that (∀ m ∈ ℕ, (m ≤ n)%nat → ∀ x ∈ ℝ,  
   K n x → K m x) as (Nest). 
 Use m := 0%nat in (Nest) . 
   { Indeed, 0%nat ∈ ℕ. } 
  It holds that ((0 ≤ n)%nat → ∀ x ∈ ℝ,  
   K n x → K 0%nat x) as (mbig). 
   By (mbig) and (nsmall) it holds that (∀ x ∈ ℝ,  
   K n x → K 0%nat x) as (Nested). 
   Use x := f0(n) in (Nested). 
    { Indeed, f0(n) ∈ ℝ. } 
  It holds that K(n, f0(n)) ⇨ K(0%nat, f0(n)). 
  We conclude that (K(0%nat, f0(n))).

 }
 By (K0_compact(f0)(f_inK0)) it holds that (∃ phi : ℕ → ℕ, ∃ x : ℝ,
        (∀ n : ℕ, (phi n < phi (S n))%nat) ∧ K 0%nat (x) ∧
        (fun k => f0 (phi k)) ⟶ x) as (Subcon). 
 Obtain phi according to (Subcon). 
 Obtain x according to (_H0). 
 We claim that (∀ n : ℕ, K n (x)) as (x_nested). 
 {
 It holds that (∀ k : ℕ, (phi k < phi (S k))%nat) as (Hphi_strict).
 We claim that (is_index_seq phi) as (Hphi).
 {
   We need to show that ∀ k ∈ ℕ, (phi k < phi (S k))%nat.
   Take k ∈ ℕ.
   Use k := k in (Hphi_strict).
   It holds that (phi k < phi (S k))%nat.
   We conclude that (phi k < phi (S k))%nat.
 }
 Take n : ℕ.
 By index_seq_grows_0 it holds that (phi n ≥ n)%nat.
 It holds that (n ≤ phi n)%nat. 
 Use n0 := phi n in (_H). 
 It holds that K(phi(n), f0(phi(n))). 
 Use n := phi n in (HK_compact). 
 It holds that sequentially_compact(K(phi(n))). 

 We claim that (∀ k : ℕ, K (phi n) 
   ((shifted_seq (fun j : ℕ => f0 (phi j)) n) k)) 
    as (tail_nest).

{     Take k : ℕ. 
   Use n0 := phi((n + k)%nat) in (_H). 
   It holds that K(phi((n + k)%nat),  
   f0(phi((n + k)%nat))) as (shift_in). 
   Use n0 := phi((n + k)%nat) in (HK_nested). 
    { Indeed, phi((n + k)%nat) ∈ ℕ. } 
   It holds that ∀ m ∈ ℕ, (m ≤ phi(n + k))%nat
      ⇨ ∀ x0 ∈ ℝ, K(phi((n + k)%nat), x0) 
       ⇨ K(m, x0) as (phi_nest). 
   Use m := phi(n) in (phi_nest).  
     { Indeed, phi(n) ∈ ℕ. }
   It holds that (phi(n) ≤ phi(n + k))%nat
      ⇨ ∀ x0 ∈ ℝ, K(phi((n + k)%nat), x0)  
       ⇨ K(phi(n), x0) as (phiseq). 
   Since (is_index_seq phi) it holds that
  (∀ j ∈ ℕ, (phi j < phi (S j))%nat) as (Hphi_strict1).

 We claim that (∀ k0 : ℕ, (phi n ≤ phi (n + k0))%nat) as (Hphi_mono).
{
  We use induction on k0.
  + We first show the base case (phi(n) ≤ phi(n + 0))%nat.
   It holds that (n + 0)%nat = n.
   It holds that (phi n = phi(n + 0))%nat.
    By (_H6) we conclude that (phi n ≤ phi (n + 0))%nat.

  + We now show the induction step.
   Take k0 : ℕ.
    Assume that (phi n ≤ phi (n + k0))%nat as (IH).
    Use j := (n + k0)%nat in (Hphi_strict).
  
    It holds that (phi (n + k0) < phi (S (n + k0)))%nat.
    It holds that
      (& phi n ≤ phi (n + k0) < phi (S (n + k0)))%nat. 
      It holds that (phi n <= phi (S (n + k0)))%nat.
    It holds that (S (n + k0) = (n + S k0))%nat. 
    It holds that (S k0 = k0 + 1)%nat.
    We conclude that (phi n ≤ phi (n + (k0 + 1)))%nat.
 } 

 Use k0 := k in (Hphi_mono). 
 It holds that (phi(n) ≤ phi(n + k))%nat. 
 It holds that (∀ x0 ∈ ℝ, K(phi((n + k)%nat), x0)  
       ⇨ K(phi(n), x0)) as (LastNest). 
 Use x0 := f0(phi((n + k)%nat)) in (LastNest).
   { Indeed, f0(phi((n + k)%nat)) ∈ ℝ. } 
 It holds that K(phi((n + k)%nat), f0(phi((n + k)%nat)))
    ⇨ K(phi(n), f0(phi((n + k)%nat))) as (fandphi).
 By (fandphi) and (shift_in) it holds that 
   (K(phi(n), f0(phi((n + k)%nat)))) as (shifted_in).
 By (shifted_in) we conclude that (K (phi n) 
 ((shifted_seq (fun j : ℕ => f0 (phi j)) n) k)).
  }

 Use n := phi(n) in (HK_compact).
 It holds that sequentially_compact(K(phi(n))) as (SeqK).
By SeqK it holds that
  (∀ a : ℕ → ℝ,
   (∀ k : ℕ, a k ∈ K (phi n)) →
    ∃ psi : ℕ → ℕ, ∃ y : ℝ,
    (∀ k : ℕ, (psi k < psi (S k))%nat) ∧
    K (phi n) y ∧  (fun k => a (psi k)) ⟶ y)
  as (SeqK_forall).
  Use a := (shifted_seq (fun j : ℕ => f0 (phi j)) n)
  in (SeqK_forall). 
  It holds that ((∀ k : ℕ, (shifted_seq (fun j : ℕ => f0 (phi j)) n) k ∈ K 
    (phi n)) →
    ∃ psi : ℕ → ℕ, ∃ y : ℝ,
      (∀ k : ℕ, (psi k < psi (S k))%nat) ∧
      K (phi n) y ∧  (fun k => (shifted_seq  
       (fun j : ℕ => f0 (phi j)) n) (psi k)) ⟶ y) as (long).
  By (long(tail_nest)) it holds that ( ∃ psi : ℕ → ℕ, ∃ y : ℝ,
      (∀ k : ℕ, (psi k < psi (S k))%nat) ∧
      K (phi n) y ∧  (fun k => (shifted_seq  
       (fun j : ℕ => f0 (phi j)) n) (psi k)) ⟶ y) as (new_sub).  
  Obtain psi according to (new_sub). 
  Obtain y according to (_H6). 
  It holds that
  (∀ k : ℕ, (psi k < psi (S k))%nat)
  as (psi_strict).
  We claim that (is_index_seq (shifted_n psi n)) as (another_sub).
{
  We need to show that
    ∀ k ∈ ℕ,
      (shifted_n psi n k < shifted_n psi n (S k))%nat.
  Take k ∈ ℕ.
  Use k := k in (psi_strict).
  It holds that (psi k < psi (S k))%nat.
  It holds that
    ((n + psi k)%nat < (n + psi (S k))%nat).
  We conclude that
    (shifted_n psi n k < shifted_n psi n (S k))%nat.
}
We claim that
  (∀ k : ℕ,
    (shifted_seq (fun j : ℕ => f0 (phi j)) n) (psi k)
    = f0 (phi (shifted_n psi n k)))
  as (same_sub). 
{
  Take k : ℕ.
  It holds that
    (shifted_seq (fun j : ℕ => f0 (phi j)) n) (psi k)
    = f0 (phi ((n + psi k)%nat)).
  It holds that (shifted_n psi n k = (n + psi k)%nat).
  We conclude that
    (shifted_seq (fun j : ℕ => f0 (phi j)) n) (psi k)
    = f0 (phi (shifted_n psi n k)).
}

  We claim that (y = x) as (equality). 
  {
  By (subseq_converges
    (fun j : ℕ => f0 (phi j))
    (shifted_n psi n) x _H1 another_sub) it holds that
    ((fun k : ℕ => f0 (phi (shifted_n psi n k))) ⟶ x)
    as (subseq_to_x).
  It holds that
    ((fun k : ℕ =>
      (shifted_seq (fun j : ℕ => f0 (phi j)) n) (psi k)) ⟶ y)
    as (subseq_to_y).
  By (limit_unique
    (fun k : ℕ =>
      (shifted_seq (fun j : ℕ => f0 (phi j)) n) (psi k))
    y x subseq_to_y subseq_to_x) it holds that (y = x). 
  We conclude that (y = x).
} 

It holds that (K(phi(n), x)) as (Halfway_there).
Use n := phi(n) in (HK_nested). 
{ Indeed, phi(n) ∈ ℕ. } 
It holds that ∀ m ∈ ℕ,
  (m ≤ phi(n))%nat ⇨ ∀ x0 ∈ ℝ, K(phi(n), x0) ⇨ K(m, x0) as (last_time).
Use m := n in (last_time).
   { Indeed, n ∈ ℕ. }
It holds that (n ≤ phi(n))%nat ⇨ ∀ x0 ∈ ℝ, 
 K(phi(n), x0) ⇨ K(n, x0). 
 It holds that (∀ x0 ∈ ℝ, 
 K(phi(n), x0) ⇨ K(n, x0)) as (one_more). 
 Use x0 := x in (one_more). 
   { Indeed, x ∈ ℝ. } 
  It holds that K(phi(n), x) ⇨ K(n, x).
  We conclude that K(n, x).
 
 }
 Choose x0 := x.
 By (x_nested) we conclude that 
   (∀ n, K(n, x0)).
  
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









