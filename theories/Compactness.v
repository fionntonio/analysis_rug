(** * RUG.Analysis.Compactness — Compact subsets of ℝ.

  #<a href="../../index.html##lecture07">Lecture 7</a>#.

  Formalizes Abbott §3.3: the Heine-Borel theorem (compact ↔ closed and bounded),
  properties of compact sets, and the nested compact sets property. *)

From Stdlib Require Import Reals.Reals.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.


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

(** The following is lemma to show that the maximum of a finite list is
  actually attained. Coq only has upper bound lemmas for this statement.*)


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


    We claim that (open_cover (fun n => centered_intervals n) K) as (Ucover). 
    { We need to show that open_cover (fun n => centered_intervals n) K. 
      We need to show that
       (∀ i : ℕ, (centered_intervals i) is _open_) ∧  
       (∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x)  .
       We claim that (∀ i : ℕ, (centered_intervals i) is _open_) as (Hopen). 
       { We need to show that
         ∀ i : ℕ, (centered_intervals i) is _open_.
         Take i : ℕ.  
         By pos_INR it holds that 0 ≤ INR i as (Hi).
         It holds that 0 < INR i + 1 as (Hradius).
         It holds that (-1 * (INR i + 1) < INR i + 1) as (H1).
         By (open_interval_is_open ( -1 * (INR i + 1)) (INR i + 1)(H1) ) it holds that
           (centered_intervals i is _open_). 
         We conclude that centered_intervals i is _open_.
       } 
       We claim that (∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x) 
         as (Hcover). 
       { We need to show that
         ∀ x : ℝ, K x → ∃ i : ℕ, centered_intervals i x.
         Take x : ℝ. 
         Assume that K x as (x_in_K).  

         By (the Archimedean property) it holds that
           (∃ n ∈ ℕ,  n > |x|) as (Harch). 
         Obtain n according to (Harch). 
         It holds that (n +1 > |x|) as (Harch_n). 
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
By (Ucover) and (Ufinite_subcover) it holds that
  (has_finite_subcover (fun n => centered_intervals n) K) as (Hfinite). 
By (Hfinite) it holds that
  (∃ I0 : list ℕ, ∀ x : ℝ, K x → ∃ i : ℕ, In i I0 ∧ centered_intervals i x)
  as (Hfinite').
Obtain I0 according to (Hfinite').
It holds that (∀ x : ℝ, K x → ∃ i : ℕ, In i I0 ∧ centered_intervals i x)
  as (Hfinite_cover). 
We claim that ( ∃ m : ℝ, (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M))) as (Hbounded). 
{ We need to show that
  ∃ m : ℝ, (∃ M : ℝ, ∀ x : ℝ, K x → (& m ≤ x ≤ M)).
  Choose m := -1 * (INR (fold_right max 0%nat I0) + 1). 
  Choose M := INR (fold_right max 0%nat I0) + 1. 
  We need to show that
    ∀ x : ℝ, K x → (& m ≤ x ≤ M).
  Take x : ℝ.  
  
  We claim that (forall i0 : ℕ, In i0 I0 →  
   INR(fold_right max 0%nat I0) ≥ INR i0) as (Hmax). 
  { We need to show that
   forall i0 : ℕ, In i0 I0 → INR(fold_right max 0%nat I0) ≥ INR i0.
    Take i0 : ℕ. 
    Assume that In i0 I0 as (i0_in_I0).
    We need to show that INR(fold_right max 0%nat I0) ≥ INR i0. 
    
    By (fold_right_max_geq I0 0%nat i0) it holds that
      (fold_right max 0%nat I0 ≥ i0)%nat as (Hmax'). 
    By (Hmax') it holds that (INR(fold_right max 0%nat I0) ≥ INR i0) as (Hmax''). 
    We conclude that INR(fold_right max 0%nat I0) ≥ INR i0.

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
    By (i_le_max)  it holds that 
    (-1 * (INR (fold_right max 0%nat I0) + 1) <= -1 * (INR i + 1)) 
     as (lower_bound). 
    By (i_le_max) it holds that (INR i + 1 <= INR (fold_right max 0%nat I0) + 1) 
     as (upper_bound). 
  By (lower_bound) and (x_bounds) it holds that
    ( -1 * (INR(fold_right max 0%nat I0) + 1) < x) as (x_lower_bound). 
    By (upper_bound) and (x_bounds) it holds that
    (x < INR(fold_right max 0%nat I0) + 1) as (x_upper_bound). 
  
  By (x_upper_bound) and (x_lower_bound) it holds that
    (& -1 * (INR(fold_right max 0%nat I0) + 1) < x < INR(fold_right max 0%nat I0) + 1)
    as (x_bounds'). 
  By (x_bounds') we conclude that (& m ≤ x ≤ M).

}
By (Hbounded) it holds that (K is _bounded_). 
We conclude that K is bounded.
Qed.



Theorem compact_iff_finite_subcover (K : ℝ → Prop) :
    sequentially_compact K ⇔
    (forall (I : Type) (U : I → (ℝ → Prop)),
        open_cover U K → has_finite_subcover U K).
Proof.
  Admitted.
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