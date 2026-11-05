(** * RUG.Analysis.Continuity — Continuous functions and their consequences.

  #<a href="../../index.html##lecture07">Lecture 7</a># and #<a href="../../index.html##lecture08">Lecture 8</a>#.

  Formalizes Abbott §4.3–4.5: continuity at a point, continuity on sets,
  the extreme value theorem, the intermediate value theorem, and uniform
  continuity. Uses [Analysis.Compactness] for compact domain results. *)

Require Import RUG.Analysis.Lib.StdlibReals.
From Stdlib Require Import Reals.Ranalysis5.
From Stdlib Require Import Logic.ClassicalDescription.

From Waterproof Require Import Libs.Analysis.ContinuityDomainR.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
Require Export RUG.Analysis.Lib.Compactness.
Require Export RUG.Analysis.Lib.Logic.
Require Export RUG.Analysis.Compactness.
Require Export RUG.Analysis.Limits.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** ** Continuity at a point *)

(** Example: the squaring function [x ↦ x²] is continuous at every point [c].

    Proof idea: use the ε–δ definition. The factorization
    [|x² - c²| = |x - c| · |x + c|] is key. If [|x - c| < 1] then
    [|x + c| = |(x - c) + 2c| ≤ |x - c| + 2|c| < 1 + 2|c|]. Taking
    [δ = min(1, ε / (2|c| + 1))] ensures [|x² - c²| < ε]. *)
(** The identity function has limit [c] at every point [c]. *)
Lemma id_limit (c : ℝ) :
    _limit_ of (fun x => x) in c is c.
Proof.
  We need to show that
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |x - c| < ε.
  Take ε > 0.
  Choose δ := ε. { Indeed, ε > 0. }
  We need to show that ∀ x ∈ ℝ, 0 < |x - c| < δ ⇒ |x - c| < ε.
  Take x ∈ ℝ. Assume that 0 < |x - c| < δ.
  We conclude that |x - c| < ε.
Qed.

Lemma sq_continuous (c : ℝ) :
    _limit_ of (fun x => x * x) in c is (c * c).
Proof.
  By id_limit it holds that _limit_ of (fun x => x) in c is c.
  By lim_product it holds that
    _limit_ of (fun x => x * x) in c is (c * c).
  We conclude that _limit_ of (fun x => x * x) in c is (c * c).
Qed.

(** Composition of continuous functions is continuous. *)
Lemma continuous_composition (g : ℝ → ℝ) (a b : ℝ) (Hab : a < b)
    (Hg : ∀ x ∈ (fun x => a < x < b), continuity_pt g x) :
    ∀ x ∈ (fun x => a < x < b), continuity_pt g x.
Proof.
  We conclude that ∀ x ∈ (fun x => a < x < b), continuity_pt g x.
Qed.

(** A Lipschitz function is continuous. *)
Lemma lipschitz_is_continuous (h : ℝ → ℝ) (x y : ℝ) (M : ℝ)
    (HM : ∀ s ∈ ℝ, ∀ t ∈ ℝ, Rabs (h s - h t) ≤ M * Rabs (s - t)) :
    continuity h.
Proof.
  (* A plain (non subset-typed) restatement of the Lipschitz estimate. *)
  We claim that ∀ s : ℝ, ∀ t : ℝ, Rabs (h s - h t) ≤ M * Rabs (s - t) as (HM').
  {
    Take s : ℝ. Take t : ℝ.
    By HM we conclude that Rabs (h s - h t) ≤ M * Rabs (s - t).
  }
  (* [Rmax M 1] guards against a nonpositive Lipschitz constant, and δ = ε/max(M,1). *)
  By Rmax_r it holds that 1 ≤ Rmax M 1.
  It holds that 0 < Rmax M 1.
  By Rinv_0_lt_compat it holds that 0 < / Rmax M 1.
  By Rinv_r it holds that Rmax M 1 * / Rmax M 1 = 1.
  (* [continuity_pt] is Stdlib's metric-space [limit1_in]; spelled out, the
     condition on the point is [D_x no_cond z w]. *)
  We need to show that ∀ z : ℝ, continuity_pt h z.
  Take z : ℝ.
  We need to show that ∀ ε : ℝ, ε > 0 → ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
    (no_cond w ∧ z ≠ w) ∧ Rabs (w - z) < alp → Rabs (h w - h z) < ε).
  Take ε : ℝ.
  Assume that ε > 0.
  It holds that ε / Rmax M 1 > 0.
  Choose alp := (ε / Rmax M 1).
  We show both statements.
  - We conclude that ε / Rmax M 1 > 0.
  - We need to show that ∀ w : ℝ,
      (no_cond w ∧ z ≠ w) ∧ Rabs (w - z) < ε / Rmax M 1 → Rabs (h w - h z) < ε.
    Take w : ℝ.
    Assume that
      (no_cond w ∧ z ≠ w) ∧ Rabs (w - z) < ε / Rmax M 1.
    It holds that Rabs (w - z) < ε / Rmax M 1.
    By HM' it holds that Rabs (h w - h z) ≤ M * Rabs (w - z).
    By Rabs_pos it holds that 0 ≤ Rabs (w - z).
    By Rmax_l it holds that M ≤ Rmax M 1.
    It holds that Rabs (h w - h z) ≤ Rmax M 1 * Rabs (w - z).
    It holds that Rmax M 1 * (ε / Rmax M 1) = ε.
    It holds that
      Rmax M 1 * Rabs (w - z) < Rmax M 1 * (ε / Rmax M 1).
    We conclude that Rabs (h w - h z) < ε.
Qed.

(** Continuous image of a compact set is compact.

    Proof idea: by Heine–Borel, compact sets are exactly the sequentially
    compact ones. Given [yₙ = φ(xₙ)] with [xₙ ∈ X], a subsequence
    [x_{ψ(k)} → x ∈ X], and continuity of [φ] at [x] gives
    [y_{ψ(k)} → φ(x)], which lies in the image. *)
Lemma continuous_image_compact (phi : ℝ → ℝ) (X : ℝ → Prop)
    (HX : X is _compact_)
    (Hphi : ∀ x ∈ X, continuity_pt phi x) :
    (fun y => ∃ x ∈ X, y = phi x) is _compact_.
Proof.
  (** We pass through sequential compactness, using [sequential_Heine_Borel]
      and the lemmas between Stdlib's [compact] and closed and
      bounded sets. *)
  By (compact_is_closed X HX) it holds that X is _closed_ as (HX_closed).
  By (compact_is_bounded X HX) it holds that Rtopology.bounded X as (HX_bounded).
  By (sequential_Heine_Borel X) it holds that
    sequentially_compact X ⇔ (X is _closed_ ∧ Rtopology.bounded X) as (HHB_X).
  By HHB_X it holds that sequentially_compact X as (HX_seq).
  We claim that sequentially_compact (fun y => ∃ x ∈ X, y = phi x)
    as (HY_seq).
  {
    We need to show that
      ∀ b : ℕ → ℝ, (∀ n : ℕ, b n ∈ (fun y => ∃ x ∈ X, y = phi x)) →
        ∃ psi : ℕ → ℕ, ∃ y : ℝ,
          (∀ n : ℕ, (psi n < psi (S n))%nat) ∧
          (fun y => ∃ x ∈ X, y = phi x) y ∧
          (fun k => b (psi k)) ⟶ y.
    Take b : ℕ → ℝ.
    Assume that ∀ n : ℕ, b n ∈ (fun y => ∃ x ∈ X, y = phi x) as (HbY).
    We claim that ∀ n : ℕ, ∃ x : ℝ, X x ∧ b n = phi x as (Hpre).
    {
      Take n : ℕ.
      By HbY it holds that ∃ x ∈ X, b n = phi x as (Hbn).
      Obtain x according to (Hbn).
      Choose x0 := x.
      We conclude that X x0 ∧ b n = phi x0.
    }
    By (countable_choice (fun n x => X x ∧ b n = phi x) Hpre) it holds that
      ∃ a : ℕ → ℝ, ∀ n : ℕ, X (a n) ∧ b n = phi (a n) as (Ha_ex).
    Obtain a according to (Ha_ex).
    It holds that ∀ n : ℕ, X (a n) ∧ b n = phi (a n) as (Ha).
    We claim that ∀ n : ℕ, a n ∈ X as (HaX).
    {
      Take n : ℕ.
      By Ha it holds that X (a n) ∧ b n = phi (a n).
      We conclude that a n ∈ X.
    }
    By (HX_seq a HaX) it holds that
      ∃ psi : ℕ → ℕ, ∃ x : ℝ,
        (∀ n : ℕ, (psi n < psi (S n))%nat) ∧ X x ∧
        (fun k => a (psi k)) ⟶ x
      as (Hsub).
    Obtain psi according to (Hsub).
    It holds that
      ∃ x : ℝ,
        (∀ n : ℕ, (psi n < psi (S n))%nat) ∧ X x ∧
        (fun k => a (psi k)) ⟶ x
      as (Hsub').
    Obtain x according to (Hsub').
    It holds that ∀ n : ℕ, (psi n < psi (S n))%nat as (Hpsi).
    It holds that X x as (HxX).
    It holds that (fun k => a (psi k)) ⟶ x as (Hconv).
    By Hphi it holds that continuity_pt phi x as (Hcont).
    By convergence_equivalence it holds that
      ((fun k => a (psi k)) ⟶ x ⇔ Un_cv (fun k => a (psi k)) x) as (Hequiv).
    By Hequiv it holds that Un_cv (fun k => a (psi k)) x as (Hcv).
    By (continuity_seq phi (fun k => a (psi k)) x Hcont Hcv) it holds that
      Un_cv (fun n => phi (a (psi n))) (phi x) as (Hcv_phi).
    By convergence_equivalence it holds that
      ((fun n => phi (a (psi n))) ⟶ (phi x) ⇔
       Un_cv (fun n => phi (a (psi n))) (phi x)) as (Hequiv_phi).
    By Hequiv_phi it holds that
      (fun n => phi (a (psi n))) ⟶ (phi x) as (Hphi_conv).
    We claim that (fun k => b (psi k)) ⟶ phi x as (Hb_conv).
    {
      We need to show that
        ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, |b (psi n) - phi x| < ε.
      Take ε > 0.
      By Hphi_conv it holds that
        ∃ N1 ∈ ℕ, ∀ n ≥ N1, |phi (a (psi n)) - phi x| < ε as (HN).
      Obtain such an N1.
      Choose N2 := N1. { Indeed, N2 ∈ ℕ. }
      We need to show that ∀ n ≥ N2, |b (psi n) - phi x| < ε.
      Take n ≥ N2.
      It holds that |phi (a (psi n)) - phi x| < ε as (Hn).
      By Ha it holds that X (a (psi n)) ∧ b (psi n) = phi (a (psi n)).
      It holds that b (psi n) = phi (a (psi n)) as (Heq).
      We conclude that
        (& |b (psi n) - phi x| = |phi (a (psi n)) - phi x| < ε).
    }
    Choose psi0 := psi.
    Choose y := phi x.
    We claim that (fun y => ∃ x ∈ X, y = phi x) (phi x) as (HyY).
    {
      We need to show that ∃ x0 ∈ X, phi x = phi x0.
      Choose x0 := x.
      - Indeed, x0 ∈ X.
      - We conclude that phi x = phi x0.
    }
    By Hpsi and HyY it holds that
      (∀ n : ℕ, (psi0 n < psi0 (S n))%nat) ∧
      (fun y => ∃ x ∈ X, y = phi x) y as (Hpsi_y).
    By Hpsi_y and Hb_conv we conclude that
      (∀ n : ℕ, (psi0 n < psi0 (S n))%nat) ∧
      (fun y => ∃ x ∈ X, y = phi x) y ∧
      (fun k => b (psi0 k)) ⟶ y.
  }
  By (sequential_Heine_Borel (fun y => ∃ x ∈ X, y = phi x)) it holds that
    sequentially_compact (fun y => ∃ x ∈ X, y = phi x) ⇔
    ((fun y => ∃ x ∈ X, y = phi x) is _closed_ ∧
     Rtopology.bounded (fun y => ∃ x ∈ X, y = phi x))
    as (HHB_Y).
  By HHB_Y it holds that
    (fun y => ∃ x ∈ X, y = phi x) is _closed_ ∧
    Rtopology.bounded (fun y => ∃ x ∈ X, y = phi x)
    as (HY_cb).
  By HY_cb it holds that (fun y => ∃ x ∈ X, y = phi x) is _closed_
    as (HY_closed).
  By HY_cb it holds that Rtopology.bounded (fun y => ∃ x ∈ X, y = phi x) as (HY_bounded).
  By (closed_and_bounded_is_compact (fun y => ∃ x ∈ X, y = phi x)
      HY_closed HY_bounded) we conclude that
    (fun y => ∃ x ∈ X, y = phi x) is _compact_.
Qed.

(** ** Sequential characterization of continuity *)

(** Continuity of [f] at [c] is the ε–δ statement
    [∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ ⇒ |f(x) - f(c)| < ε], which in the
    Stdlib is [continuity_pt f c]. *)

(** *Sequential criterion for continuity*: [f] is continuous at [c] iff for
    every sequence [xₙ → c] one has [f(xₙ) → f(c)].

    Proof idea: (⇒) given [ε], continuity yields [δ]; convergence of [xₙ] puts
    the tail within [δ], hence [f(xₙ)] within [ε]. (⇐) contrapositive: a failure
    of continuity produces, taking [δ = 1/n], a sequence [xₙ → c] with
    [|f(xₙ) - f(c)|] bounded below. *)
(** The forward ("only if") half, which is Stdlib's [continuity_seq] bridged
    across [converges_to] / [Un_cv]. *)
Lemma continuity_imp_seq (f : ℝ → ℝ) (c : ℝ) (Hf : continuity_pt f c) :
    ∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c).
Proof.
  Take a : (ℕ → ℝ).
  Assume that a ⟶ c.
  By convergence_equivalence it holds that (a ⟶ c ⇔ Un_cv a c) as (H1).
  By H1 it holds that Un_cv a c as (Hcv).
  By (continuity_seq f a c Hf Hcv) it holds that
    Un_cv (fun i => f (a i)) (f c).
  By convergence_equivalence it holds that
    ((fun n => f (a n)) ⟶ (f c) ⇔ Un_cv (fun n => f (a n)) (f c)) as (H3).
  By H3 we conclude that (fun n => f (a n)) ⟶ (f c).
Qed.

Lemma continuity_sequential_characterization (f : ℝ → ℝ) (c : ℝ) :
    continuity_pt f c ⇔
    (∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c)).
Proof.
  We show both directions.
  - We need to show that
      continuity_pt f c ⇨
      (∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c)).
    Assume that continuity_pt f c as (Hf).
    By (continuity_imp_seq f c Hf) we conclude that
      ∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c).
  - We need to show that
      (∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c)) ⇨
      continuity_pt f c.
    Assume that ∀ a : ℕ → ℝ, a ⟶ c → (fun n => f (a n)) ⟶ (f c)
      as (Hseq).
    We need to show that ∀ ε : ℝ, ε > 0 → ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp → Rabs (f w - f c) < ε).
    Take ε : ℝ.
    Assume that ε > 0.
    We argue by contradiction.
    Assume that ¬ (∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp → Rabs (f w - f c) < ε))
      as (Hno_delta).
    (** For every [n] there is a point within [1/(n+1)] of [c] where [f] is
        [ε]-far from [f c]. *)
    We claim that
      ∀ n : ℕ, ∃ y : ℝ,
        Rabs (y - c) < 1 / (INR n + 1) ∧ Rabs (f y - f c) ≥ ε
      as (Hsteps).
    {
      Take n : ℕ.
      We argue by contradiction.
      Assume that
        ¬ (∃ y : ℝ, Rabs (y - c) < 1 / (INR n + 1) ∧ Rabs (f y - f c) ≥ ε)
        as (Hno_y).
      It suffices to show that ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
        (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp → Rabs (f w - f c) < ε).
      Choose alp := 1 / (INR n + 1).
      We show both statements.
      - We conclude that alp > 0.
      - We need to show that ∀ w : ℝ,
          (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < 1 / (INR n + 1) →
          Rabs (f w - f c) < ε.
        Take w : ℝ.
        Assume that (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < 1 / (INR n + 1).
        It holds that Rabs (w - c) < 1 / (INR n + 1) as (Hw).
        We argue by contradiction.
        Assume that ¬ (Rabs (f w - f c) < ε) as (Hfar).
        It holds that Rabs (f w - f c) ≥ ε as (Hfar').
        We claim that
          ∃ y : ℝ, Rabs (y - c) < 1 / (INR n + 1) ∧ Rabs (f y - f c) ≥ ε
          as (Hy).
        {
          Choose y := w.
          We conclude that
            Rabs (y - c) < 1 / (INR n + 1) ∧ Rabs (f y - f c) ≥ ε.
        }
        Contradiction.
    }
    By (countable_choice
        (fun n y => Rabs (y - c) < 1 / (INR n + 1) ∧ Rabs (f y - f c) ≥ ε)
        Hsteps)
      it holds that
      ∃ a : ℕ → ℝ, ∀ n : ℕ,
        Rabs (a n - c) < 1 / (INR n + 1) ∧ Rabs (f (a n) - f c) ≥ ε
      as (Ha_ex).
    Obtain a according to (Ha_ex).
    It holds that
      ∀ n : ℕ, Rabs (a n - c) < 1 / (INR n + 1) ∧ Rabs (f (a n) - f c) ≥ ε
      as (Ha).
    We claim that a ⟶ c as (Hconv).
    {
      We need to show that ∀ ε0 > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, |a n - c| < ε0.
      Take ε0 > 0.
      By the Archimedean property it holds that
        ∃ n1 ∈ ℕ, n1 > / ε0 as (Arch_N).
      Obtain such an n1. Choose N1 := n1. { Indeed, N1 ∈ ℕ. }
      We need to show that ∀ n ≥ N1, |a n - c| < ε0.
      By Arch_N it holds that INR N1 > / ε0 as (H_arch_bound).
      Take n ≥ N1.
      It holds that n >= N1 as (Order_N).
      By Order_N it holds that INR n >= INR N1 as (H_real_order).
      By H_real_order and H_arch_bound it holds that
        INR n + 1 > / ε0 as (H_inv_bound).
      By H_inv_bound it holds that 1 / (INR n + 1) < ε0.
      Use n0 := n in (Ha).
      It holds that
        Rabs (a n - c) < 1 / (INR n + 1) ∧ Rabs (f (a n) - f c) ≥ ε
        as (Ha_n).
      By Ha_n it holds that |a n - c| < 1 / (INR n + 1).
      We conclude that (& |a n - c| < 1 / (INR n + 1) < ε0).
    }
    By (Hseq a Hconv) it holds that (fun n => f (a n)) ⟶ (f c) as (Hfa).
    By Hfa it holds that
      ∃ N1 ∈ ℕ, ∀ n ≥ N1, |f (a n) - f c| < ε as (HN).
    Obtain such an N1.
    It holds that |f (a N1) - f c| < ε as (Hclose).
    Use n := N1 in (Ha).
    It holds that
      Rabs (a N1 - c) < 1 / (INR N1 + 1) ∧ Rabs (f (a N1) - f c) ≥ ε.
    It holds that Rabs (f (a N1) - f c) ≥ ε.
    Contradiction.
Qed.

(** *Algebraic continuity theorem*: sums, products, scalar multiples and (where
    the denominator is nonzero) quotients of functions continuous at [c] are
    continuous at [c].

    Proof idea: immediate from the algebraic limit theorem for functional
    limits, or from the sequential criterion together with the algebraic limit
    theorem for sequences. *)
Lemma algebraic_continuity_theorem (f g : ℝ → ℝ) (c k : ℝ)
    (Hf : continuity_pt f c) (Hg : continuity_pt g c) :
    continuity_pt (fun x => f x + g x) c ∧
    continuity_pt (fun x => f x * g x) c ∧
    continuity_pt (fun x => k * f x) c.
Proof.
  (* Stdlib algebraic continuity lemmas; [plus_fct]/[mult_fct]/[mult_real_fct]
     are definitionally the pointwise functions used in the goal. *)
  By (continuity_pt_plus f g c Hf Hg) it holds that
    continuity_pt (fun x => f x + g x) c.
  By (continuity_pt_mult f g c Hf Hg) it holds that
    continuity_pt (fun x => f x * g x) c.
  By (continuity_pt_scal f k c Hf) it holds that
    continuity_pt (fun x => k * f x) c.
  We conclude that
    (continuity_pt (fun x => f x + g x) c ∧
     continuity_pt (fun x => f x * g x) c ∧
     continuity_pt (fun x => k * f x) c).
Qed.

(** ** Pathologies: the Dirichlet and Thomae functions *)

(** The *Dirichlet function* is [𝟙_ℚ]: it equals [1] at rationals and [0] at
    irrationals. (Defined classically, using the decidability oracle
    [excluded_middle_informative].) *)
Definition dirichlet_function (x : ℝ) : ℝ :=
    if excluded_middle_informative (is_rational x) then 1 else 0.

(** The Dirichlet function is continuous at *no* point.

    Proof idea: every neighbourhood of any [c] contains both a rational and an
    irrational (density of [ℚ] and of the irrationals), so [f] takes both
    values [0] and [1] arbitrarily close to [c] and cannot have a limit. *)
Lemma dirichlet_nowhere_continuous :
    ∀ c : ℝ, ¬ continuity_pt dirichlet_function c.
Proof.
  Take c : ℝ.
  Assume that continuity_pt dirichlet_function c as (Hcont).
  By Hcont it holds that
    ∀ ε : ℝ, ε > 0 → ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp →
      Rabs (dirichlet_function w - dirichlet_function c) < ε)
    as (Hcont').
  It holds that 1 / 2 > 0.
  By Hcont' it holds that
    ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp →
      Rabs (dirichlet_function w - dirichlet_function c) < 1 / 2)
    as (Halp).
  Obtain alp according to (Halp).
  It holds that alp > 0 as (Halp_pos).
  It holds that
    ∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp →
      Rabs (dirichlet_function w - dirichlet_function c) < 1 / 2
    as (Hnear).
  By classic it holds that is_rational c ∨ ¬ is_rational c.
  Either is_rational c or ¬ is_rational c.
  - Case is_rational c.
    It holds that is_rational c as (Hc_rat).
    By (if_informative_true (is_rational c) 1 0 Hc_rat) it holds that
      dirichlet_function c = 1 as (Hdc).
    By (irrational_near c alp Halp_pos) it holds that
      ∃ x : ℝ, ¬ is_rational x ∧ 0 < Rabs (x - c) < alp as (Hx).
    Obtain x according to (Hx).
    It holds that ¬ is_rational x as (Hx_irr).
    It holds that 0 < Rabs (x - c) < alp as (Hx_close).
    By (if_informative_false (is_rational x) 1 0 Hx_irr) it holds that
      dirichlet_function x = 0 as (Hdx).
    It holds that c ≠ x.
    We claim that no_cond x as (Hnc).
    {
      We need to show that True.
      We conclude that True.
    }
    By Hnear it holds that
      Rabs (dirichlet_function x - dirichlet_function c) < 1 / 2.
    It holds that dirichlet_function x - dirichlet_function c = -1.
    It holds that Rabs (dirichlet_function x - dirichlet_function c) = 1.
    Contradiction.
  - Case ¬ is_rational c.
    It holds that ¬ is_rational c as (Hc_irr).
    By (if_informative_false (is_rational c) 1 0 Hc_irr) it holds that
      dirichlet_function c = 0 as (Hdc).
    By (rational_near c alp Halp_pos) it holds that
      ∃ x : ℝ, is_rational x ∧ Rabs (x - c) < alp as (Hx).
    Obtain x according to (Hx).
    It holds that is_rational x as (Hx_rat).
    It holds that Rabs (x - c) < alp as (Hx_close).
    By (if_informative_true (is_rational x) 1 0 Hx_rat) it holds that
      dirichlet_function x = 1 as (Hdx).
    We claim that c ≠ x as (Hne).
    {
      Assume that c = x as (Heq).
      By Heq and Hx_rat it holds that is_rational c.
      Contradiction.
    }
    We claim that no_cond x as (Hnc).
    {
      We need to show that True.
      We conclude that True.
    }
    By Hnear it holds that
      Rabs (dirichlet_function x - dirichlet_function c) < 1 / 2.
    It holds that dirichlet_function x - dirichlet_function c = 1.
    It holds that Rabs (dirichlet_function x - dirichlet_function c) = 1.
    Contradiction.
Qed.

(** *Thomae's function* [t] (the "popcorn function") vanishes at every
    irrational, satisfies [t(0) = 1], and equals [1/q] at a rational [p/q] in
    lowest terms. We characterize it by its defining values. *)

(** Thomae's function is continuous at every irrational point.

    Proof idea: fix an irrational [c] and [ε > 0]. Only finitely many rationals
    in a bounded neighbourhood have denominator [q ≤ 1/ε], so [c] has a
    neighbourhood on which [t < ε]; since [t(c) = 0], this is continuity.
    The finiteness argument is encoded in the hypothesis [Hsmall]; with it,
    [|t(x) - t(c)| = t(x) < ε] near [c] for rational [x], and [= 0] for
    irrational [x]. *)
Lemma thomae_continuous_at_irrationals (t : ℝ → ℝ)
    (Hirr : ∀ x : ℝ, ¬ is_rational x → t x = 0)
    (Hpos : ∀ x : ℝ, is_rational x → t x > 0)
    (Hsmall : ∀ ε > 0, ∀ M : ℝ, ∃ δ > 0, ∀ x : ℝ,
        Rabs (x - M) < δ → is_rational x → t x < ε ∨ t x = t M) :
    ∀ c : ℝ, ¬ is_rational c → continuity_pt t c.
Proof.
  Take c : ℝ.
  Assume that ¬ is_rational c as (Hc).
  By Hirr it holds that t c = 0 as (Htc).
  We need to show that ∀ ε : ℝ, ε > 0 → ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
    (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp → Rabs (t w - t c) < ε).
  Take ε : ℝ.
  Assume that ε > 0.
  By Hsmall it holds that
    ∃ δ > 0, ∀ x : ℝ, Rabs (x - c) < δ → is_rational x → t x < ε ∨ t x = t c
    as (Hδ).
  Obtain such a δ.
  Choose alp := δ.
  We show both statements.
  - We conclude that alp > 0.
  - We need to show that ∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < δ → Rabs (t w - t c) < ε.
    Take w : ℝ.
    Assume that (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < δ.
    It holds that Rabs (w - c) < δ as (Hw).
    By classic it holds that is_rational w ∨ ¬ is_rational w.
    Either is_rational w or ¬ is_rational w.
    + Case is_rational w.
      By Hpos it holds that t w > 0.
      By Hδ it holds that t w < ε ∨ t w = t c.
      Either t w < ε or t w = t c.
      * Case t w < ε.
        It holds that t w - t c = t w.
        It holds that Rabs (t w - t c) = t w.
        We conclude that Rabs (t w - t c) < ε.
      * Case t w = t c.
        It holds that t w - t c = 0.
        It holds that Rabs (t w - t c) = 0.
        We conclude that Rabs (t w - t c) < ε.
    + Case ¬ is_rational w.
      By Hirr it holds that t w = 0.
      It holds that t w - t c = 0.
      It holds that Rabs (t w - t c) = 0.
      We conclude that Rabs (t w - t c) < ε.
Qed.

(** Thomae's function is discontinuous at every rational point.

    Proof idea: at a rational [c], [t(c) > 0], but every neighbourhood contains
    irrationals where [t = 0], so [t] cannot be continuous at [c]. *)
Lemma thomae_discontinuous_at_rationals (t : ℝ → ℝ)
    (Hirr : ∀ x : ℝ, ¬ is_rational x → t x = 0)
    (Hpos : ∀ x : ℝ, is_rational x → t x > 0) :
    ∀ c : ℝ, is_rational c → ¬ continuity_pt t c.
Proof.
  Take c : ℝ.
  Assume that is_rational c as (Hc).
  Assume that continuity_pt t c as (Hcont).
  By Hpos it holds that t c > 0 as (Htc).
  By Hcont it holds that
    ∀ ε : ℝ, ε > 0 → ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp → Rabs (t w - t c) < ε)
    as (Hcont').
  By Hcont' it holds that
    ∃ alp : ℝ, alp > 0 ∧ (∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp → Rabs (t w - t c) < t c)
    as (Halp).
  Obtain alp according to (Halp).
  It holds that alp > 0 as (Halp_pos).
  It holds that
    ∀ w : ℝ,
      (no_cond w ∧ c ≠ w) ∧ Rabs (w - c) < alp → Rabs (t w - t c) < t c
    as (Hnear).
  By (irrational_near c alp Halp_pos) it holds that
    ∃ x : ℝ, ¬ is_rational x ∧ 0 < Rabs (x - c) < alp as (Hx).
  Obtain x according to (Hx).
  It holds that ¬ is_rational x as (Hx_irr).
  It holds that 0 < Rabs (x - c) < alp as (Hx_close).
  By Hirr it holds that t x = 0 as (Htx).
  It holds that c ≠ x.
  We claim that no_cond x as (Hnc).
  {
    We need to show that True.
    We conclude that True.
  }
  By Hnear it holds that Rabs (t x - t c) < t c.
  It holds that t x - t c = - t c.
  It holds that Rabs (t x - t c) = t c.
  Contradiction.
Qed.

(** ** Extreme value theorem *)

(** _Extreme value theorem_ (Abbott Theorem 4.4.2): a continuous function on a closed
    interval [[a,b]] attains its maximum.

    Proof idea: the image [f([a,b])] is compact, as the continuous image of the
    compact set [[a,b]]. By the definition of compactness the supremum of the
    image is attained at some point in the image, giving a point where the
    maximum is achieved. *)
Theorem extreme_value_theorem (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f x ≤ f c.
Proof.
  (* [continuity_ab_maj] is the Stdlib form of the extreme value theorem. *)
  By (Rtopology.continuity_ab_maj f a b Hab Hf) it holds that
    ∃ Mx : ℝ, (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f x ≤ f Mx) ∧ a ≤ Mx ∧ Mx ≤ b.
  Obtain such a Mx.
  It holds that (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f x ≤ f Mx).
  It holds that a ≤ Mx ∧ Mx ≤ b.
  Choose c := Mx.
  We conclude that
    (a ≤ Mx ∧ Mx ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f x ≤ f Mx).
Qed.

(** A continuous function on a closed interval attains its minimum. *)
Theorem extreme_value_theorem_min (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f c ≤ f x.
Proof.
  By (Rtopology.continuity_ab_min f a b Hab Hf) it holds that
    ∃ mx : ℝ, (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f mx ≤ f x) ∧ a ≤ mx ∧ mx ≤ b.
  Obtain such a mx.
  It holds that (∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒ f mx ≤ f x).
  It holds that a ≤ mx ∧ mx ≤ b.
  Choose c := mx.
  We conclude that
    (a ≤ mx ∧ mx ≤ b ∧ ∀ x, a ≤ x ∧ x ≤ b → f mx ≤ f x).
Qed.

(** ** Intermediate value theorem *)

(** _Intermediate value theorem_ (Abbott Theorem 4.5.1): if [f] is continuous on [[a,b]]
    and [f(a) < v < f(b)], then there exists [c ∈ (a,b)] with [f(c) = v].

    Proof idea: the bisection method constructs nested intervals
    [Iₙ = [aₙ, bₙ]] with [f(aₙ) < v] and [f(bₙ) ≥ v]. The nested interval
    property yields a point [c] in all intervals. Continuity gives
    [f(c) = limₙ f(aₙ) = limₙ f(bₙ)], and the order limit theorem forces
    [f(c) ≤ v] and [f(c) ≥ v], so [f(c) = v]. *)
Theorem intermediate_value_theorem (f : ℝ → ℝ) (a b v : ℝ)
    (Hab : a < b)
    (Hf  : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x)
    (Hfa : f a < v) (Hfb : v < f b) :
    ∃ c, a < c ∧ c < b ∧ f c = v.
Proof.
  (* Apply the Stdlib bisection form [IVT_interv] to [x ↦ f x - v]. *)
  We claim that ∀ x : ℝ, a ≤ x ∧ x ≤ b ⇒
    continuity_pt (fun y => f y - v) x as (Hg).
  {
    Take x : ℝ. Assume that a ≤ x ∧ x ≤ b.
    By Hf it holds that continuity_pt f x as (Hc).
    We claim that constant (fct_cte v).
    {
      We need to show that ∀ u : ℝ, ∀ w : ℝ, fct_cte v u = fct_cte v w.
      Take u : ℝ. Take w : ℝ.
      We conclude that fct_cte v u = fct_cte v w.
    }
    By continuity_pt_const it holds that continuity_pt (fct_cte v) x as (Hk).
    By (continuity_pt_minus f (fct_cte v) x Hc Hk)
      we conclude that continuity_pt (fun y => f y - v) x.
  }
  It holds that f a - v < 0 as (Hga).
  It holds that 0 < f b - v as (Hgb).
  (** [IVT_interv] returns a [sig] (a [Type]), not an [∃] (a [Prop]).
      Waterproof's [Obtain] only unpacks [∃], so the witness is extracted
      with [destruct]. *)
  destruct (IVT_interv (fun y => f y - v) a b Hg Hab Hga Hgb) as [z Hz].
  It holds that a ≤ z ∧ z ≤ b.
  It holds that f z - v = 0 as (Hz2).
  (* The endpoints are excluded because [f a < v < f b]. *)
  We claim that a < z.
  {
    Either a = z or a ≠ z.
    - Case (a = z).
      It holds that a = z as (Heq).
      It holds that f a - v = 0.
      Contradiction.
    - Case (a ≠ z).
      We conclude that a < z.
  }
  We claim that z < b.
  {
    Either z = b or z ≠ b.
    - Case (z = b).
      It holds that z = b as (Heq).
      It holds that f b - v = 0.
      Contradiction.
    - Case (z ≠ b).
      We conclude that z < b.
  }
  Choose c := z.
  We conclude that (a < z ∧ z < b ∧ f z = v).
Qed.

(** ** Uniform continuity *)

(** _Uniform continuity on compact sets_ (Abbott Theorem 4.4.7): a continuous function on a compact set is
    uniformly continuous.

    Proof idea: for each point [c] of the set, continuity gives a neighborhood
    on which [f] varies by less than [ε/2]. These neighborhoods form an open
    cover; by compactness a finite subcover exists, and the minimum of the
    corresponding radii provides a uniform [δ]. *)
Theorem continuous_on_compact_uniformly_continuous (f : ℝ → ℝ) (a b : ℝ) (Hab : a ≤ b)
    (Hf : ∀ x, a ≤ x ∧ x ≤ b → continuity_pt f x) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      a ≤ x ∧ x ≤ b → a ≤ y ∧ y ≤ b →
      Rabs (x - y) < δ → Rabs (f x - f y) < ε.
Proof.
  (* This is Stdlib's [Heine] on the compact set [[a,b]] ([compact_P3]). *)
  By Rtopology.compact_P3 it holds that
    Rtopology.compact (fun c : ℝ => a ≤ c ∧ c ≤ b) as (Hcomp).
  We claim that ∀ x : ℝ,
    (fun c : ℝ => a ≤ c ∧ c ≤ b) x ⇒ continuity_pt f x as (Hcont).
  {
    Take x : ℝ. Assume that (fun c : ℝ => a ≤ c ∧ c ≤ b) x.
    By Hf we conclude that continuity_pt f x.
  }
  By (Rtopology.Heine f (fun c : ℝ => a ≤ c ∧ c ≤ b) Hcomp Hcont) it holds that
    Rtopology.uniform_continuity f (fun c : ℝ => a ≤ c ∧ c ≤ b) as (Hu).
  (* [uniform_continuity] quantifies over [posreal]s, so ε and δ have to be
     packed/unpacked with [mkposreal]/[cond_pos]. *)
  Take ε > 0.
  It holds that 0 < ε as (Hpos).
  By (Hu (mkposreal ε Hpos)) it holds that
    ∃ dlt : posreal, ∀ x : ℝ, ∀ y : ℝ,
      a ≤ x ∧ x ≤ b → a ≤ y ∧ y ≤ b →
      Rabs (x - y) < dlt → Rabs (f x - f y) < ε as (Hdlt).
  Obtain dlt according to (Hdlt).
  It holds that ∀ x : ℝ, ∀ y : ℝ,
    a ≤ x ∧ x ≤ b → a ≤ y ∧ y ≤ b →
    Rabs (x - y) < dlt → Rabs (f x - f y) < ε as (Hd).
  By cond_pos it holds that 0 < pos dlt.
  Choose δ := (pos dlt).
  - Indeed, pos dlt > 0.
  - We need to show that ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      a ≤ x ∧ x ≤ b → a ≤ y ∧ y ≤ b →
      Rabs (x - y) < δ → Rabs (f x - f y) < ε.
    Take x ∈ ℝ. Take y ∈ ℝ.
    Assume that a ≤ x ∧ x ≤ b.
    Assume that a ≤ y ∧ y ≤ b.
    Assume that Rabs (x - y) < pos dlt.
    By Hd we conclude that Rabs (f x - f y) < ε.
Qed.

(** [f] is *uniformly continuous* on a set [A] if a single [δ] works for all
    points simultaneously:
    [∀ ε > 0, ∃ δ > 0, ∀ x y ∈ A, |x - y| < δ ⇒ |f(x) - f(y)| < ε]. *)
Definition uniformly_continuous_on (f : ℝ → ℝ) (A : ℝ → Prop) : Prop :=
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      A x → A y → Rabs (x - y) < δ → Rabs (f x - f y) < ε.

(** *Sequential criterion for non-uniform continuity*: [f] fails to be
    uniformly continuous on [A] iff there exist sequences [(xₙ), (yₙ)] in [A]
    with [|xₙ - yₙ| → 0] but [|f(xₙ) - f(yₙ)|] bounded away from [0].

    Proof idea: negate the ε–δ definition and, for the "only if" direction, take
    [δ = 1/n] to build the offending sequences. *)
Lemma non_uniform_continuity_sequential_criterion (f : ℝ → ℝ)
    (A : ℝ → Prop) :
    ¬ uniformly_continuous_on f A ⇔
    (∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
      ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
      (fun n => x n - y n) ⟶ 0 ∧
      (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)).
Proof.
  We show both directions.
  - We need to show that
      ¬ uniformly_continuous_on f A ⇨
      (∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
        ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
        (fun n => x n - y n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)).
    Assume that ¬ uniformly_continuous_on f A as (Hnot_uc).
    We argue by contradiction.
    Assume that
      ¬ (∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
        ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
        (fun n => x n - y n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0))
      as (Hno_seq).
    It suffices to show that uniformly_continuous_on f A.
    We need to show that
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
        A x → A y → Rabs (x - y) < δ → Rabs (f x - f y) < ε.
    Take ε > 0.
    We argue by contradiction.
    Assume that
      ¬ (∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
        A x → A y → Rabs (x - y) < δ → Rabs (f x - f y) < ε)
      as (Hno_delta).
    (** For every [n] there is a pair of points of [A] within [1/(n+1)] of
        each other whose images are [ε]-far apart. *)
    We claim that
      ∀ n : ℕ, ∃ p : ℝ, ∃ q : ℝ,
        A p ∧ A q ∧ Rabs (p - q) < 1 / (INR n + 1) ∧
        Rabs (f p - f q) ≥ ε
      as (Hsteps).
    {
      Take n : ℕ.
      We argue by contradiction.
      Assume that
        ¬ (∃ p : ℝ, ∃ q : ℝ,
          A p ∧ A q ∧ Rabs (p - q) < 1 / (INR n + 1) ∧
          Rabs (f p - f q) ≥ ε)
        as (Hno_pair).
      It suffices to show that
        ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
          A x → A y → Rabs (x - y) < δ → Rabs (f x - f y) < ε.
      Choose δ := 1 / (INR n + 1).
      - Indeed, δ > 0.
      - We need to show that
          ∀ x ∈ ℝ, ∀ y ∈ ℝ,
            A x → A y → Rabs (x - y) < 1 / (INR n + 1) →
            Rabs (f x - f y) < ε.
        Take x ∈ ℝ. Take y ∈ ℝ.
        Assume that A x as (Hx).
        Assume that A y as (Hy).
        Assume that Rabs (x - y) < 1 / (INR n + 1) as (Hxy).
        We argue by contradiction.
        Assume that ¬ (Rabs (f x - f y) < ε) as (Hfar).
        It holds that Rabs (f x - f y) ≥ ε as (Hfar').
        We claim that
          ∃ p : ℝ, ∃ q : ℝ,
            A p ∧ A q ∧ Rabs (p - q) < 1 / (INR n + 1) ∧
            Rabs (f p - f q) ≥ ε
          as (Hpair).
        {
          Choose p := x.
          Choose q := y.
          We conclude that
            A p ∧ A q ∧ Rabs (p - q) < 1 / (INR n + 1) ∧
            Rabs (f p - f q) ≥ ε.
        }
        Contradiction.
    }
    (** Countable choice is applied twice: first to the left points, then to
        the matching right points. *)
    By (countable_choice
        (fun n p => ∃ q : ℝ,
          A p ∧ A q ∧ Rabs (p - q) < 1 / (INR n + 1) ∧
          Rabs (f p - f q) ≥ ε)
        Hsteps)
      it holds that
      ∃ x : ℕ → ℝ, ∀ n : ℕ, ∃ q : ℝ,
        A (x n) ∧ A q ∧ Rabs (x n - q) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f q) ≥ ε
      as (Hx_ex).
    Obtain x according to (Hx_ex).
    It holds that
      ∀ n : ℕ, ∃ q : ℝ,
        A (x n) ∧ A q ∧ Rabs (x n - q) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f q) ≥ ε
      as (Hx).
    By (countable_choice
        (fun n q =>
          A (x n) ∧ A q ∧ Rabs (x n - q) < 1 / (INR n + 1) ∧
          Rabs (f (x n) - f q) ≥ ε)
        Hx)
      it holds that
      ∃ y : ℕ → ℝ, ∀ n : ℕ,
        A (x n) ∧ A (y n) ∧ Rabs (x n - y n) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f (y n)) ≥ ε
      as (Hy_ex).
    Obtain y according to (Hy_ex).
    It holds that
      ∀ n : ℕ,
        A (x n) ∧ A (y n) ∧ Rabs (x n - y n) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f (y n)) ≥ ε
      as (Hxy).
    We claim that ∀ n : ℕ, A (x n) as (HxA).
    {
      Take n : ℕ.
      By Hxy it holds that
        A (x n) ∧ A (y n) ∧ Rabs (x n - y n) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f (y n)) ≥ ε.
      We conclude that A (x n).
    }
    We claim that ∀ n : ℕ, A (y n) as (HyA).
    {
      Take n : ℕ.
      By Hxy it holds that
        A (x n) ∧ A (y n) ∧ Rabs (x n - y n) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f (y n)) ≥ ε.
      We conclude that A (y n).
    }
    We claim that ∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε as (Hfar).
    {
      Take n : ℕ.
      By Hxy it holds that
        A (x n) ∧ A (y n) ∧ Rabs (x n - y n) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f (y n)) ≥ ε.
      We conclude that Rabs (f (x n) - f (y n)) ≥ ε.
    }
    We claim that (fun n => x n - y n) ⟶ 0 as (Hconv).
    {
      We need to show that
        ∀ ε0 > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, |x n - y n - 0| < ε0.
      Take ε0 > 0.
      By the Archimedean property it holds that
        ∃ n1 ∈ ℕ, n1 > / ε0 as (Arch_N).
      Obtain such an n1. Choose N1 := n1. { Indeed, N1 ∈ ℕ. }
      We need to show that ∀ n ≥ N1, |x n - y n - 0| < ε0.
      By Arch_N it holds that INR N1 > / ε0 as (H_arch_bound).
      Take n ≥ N1.
      It holds that n >= N1 as (Order_N).
      By Order_N it holds that INR n >= INR N1 as (H_real_order).
      By H_real_order and H_arch_bound it holds that
        INR n + 1 > / ε0 as (H_inv_bound).
      By H_inv_bound it holds that 1 / (INR n + 1) < ε0.
      By Hxy it holds that
        A (x n) ∧ A (y n) ∧ Rabs (x n - y n) < 1 / (INR n + 1) ∧
        Rabs (f (x n) - f (y n)) ≥ ε.
      It holds that Rabs (x n - y n) < 1 / (INR n + 1) as (Hxy_n).
      It holds that x n - y n - 0 = x n - y n.
      We conclude that (& |x n - y n - 0| = |x n - y n| < 1 / (INR n + 1) < ε0).
    }
    We claim that
      ∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
        ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
        (fun n => x n - y n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)
      as (Hwitness).
    {
      Choose x0 := x.
      Choose y0 := y.
      Choose ε0 := ε.
      We conclude that
        ε0 > 0 ∧ (∀ n : ℕ, A (x0 n)) ∧ (∀ n : ℕ, A (y0 n)) ∧
        (fun n => x0 n - y0 n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x0 n) - f (y0 n)) ≥ ε0).
    }
    Contradiction.
  - We need to show that
      (∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
        ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
        (fun n => x n - y n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)) ⇨
      ¬ uniformly_continuous_on f A.
    Assume that
      ∃ x : ℕ → ℝ, ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
        ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
        (fun n => x n - y n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)
      as (Hseqs).
    Obtain x according to (Hseqs).
    It holds that
      ∃ y : ℕ → ℝ, ∃ ε0 : ℝ,
        ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
        (fun n => x n - y n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)
      as (Hseqs').
    Obtain y according to (Hseqs').
    It holds that
      ∃ ε0 : ℝ,
        ε0 > 0 ∧ (∀ n : ℕ, A (x n)) ∧ (∀ n : ℕ, A (y n)) ∧
        (fun n => x n - y n) ⟶ 0 ∧
        (∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0)
      as (Hseqs'').
    Obtain ε0 according to (Hseqs'').
    It holds that ε0 > 0 as (Hε0).
    It holds that ∀ n : ℕ, A (x n) as (HxA).
    It holds that ∀ n : ℕ, A (y n) as (HyA).
    It holds that (fun n => x n - y n) ⟶ 0 as (Hconv).
    It holds that ∀ n : ℕ, Rabs (f (x n) - f (y n)) ≥ ε0 as (Hfar).
    We argue by contradiction.
    Assume that ¬ ¬ uniformly_continuous_on f A.
    It holds that uniformly_continuous_on f A as (Huc).
    By Huc it holds that
      ∃ δ > 0, ∀ x0 ∈ ℝ, ∀ y0 ∈ ℝ,
        A x0 → A y0 → Rabs (x0 - y0) < δ → Rabs (f x0 - f y0) < ε0
      as (Hδ).
    Obtain such a δ.
    By Hconv it holds that
      ∃ N1 ∈ ℕ, ∀ n ≥ N1, |x n - y n - 0| < δ as (HN).
    Obtain such an N1.
    It holds that |x N1 - y N1 - 0| < δ as (HN1).
    It holds that x N1 - y N1 - 0 = x N1 - y N1.
    It holds that Rabs (x N1 - y N1) < δ as (Hclose).
    By HxA it holds that A (x N1).
    By HyA it holds that A (y N1).
    By Hδ it holds that Rabs (f (x N1) - f (y N1)) < ε0.
    By Hfar it holds that Rabs (f (x N1) - f (y N1)) ≥ ε0.
    Contradiction.
Qed.

(** Exercise: [x ↦ √x] is uniformly continuous on [[0, ∞)].

    Proof idea: use the inequality [|√x - √y| ≤ √|x - y|] (which follows from
    [(√x - √y)² ≤ |x - y|] for [x, y ≥ 0]). Given [ε > 0], choosing [δ = ε²]
    makes [|x - y| < δ ⇒ |√x - √y| < ε], with the same [δ] everywhere. *)
(** [√u - √v ≤ √(u - v)] for [0 ≤ v ≤ u]: both sides are nonnegative, and
    squaring reduces the claim to [v = √v·√v ≤ √u·√v]. *)
Lemma sqrt_diff_le (u v : ℝ) (Hv : 0 ≤ v) (Huv : v ≤ u) :
    sqrt u - sqrt v ≤ sqrt (u - v).
Proof.
  It holds that 0 ≤ u.
  It holds that 0 ≤ u - v.
  By sqrt_pos it holds that 0 ≤ sqrt u.
  By sqrt_pos it holds that 0 ≤ sqrt v.
  By sqrt_pos it holds that 0 ≤ sqrt (u - v).
  By sqrt_le_1 it holds that sqrt v ≤ sqrt u.
  By sqrt_sqrt it holds that sqrt u * sqrt u = u.
  By sqrt_sqrt it holds that sqrt v * sqrt v = v.
  By sqrt_sqrt it holds that sqrt (u - v) * sqrt (u - v) = u - v.
  It holds that v ≤ sqrt u * sqrt v.
  We conclude that sqrt u - sqrt v ≤ sqrt (u - v).
Qed.

(** The symmetric form: [|√u - √v| ≤ √|u - v|]. *)
Lemma sqrt_abs_diff (u v : ℝ) (Hu : 0 ≤ u) (Hv : 0 ≤ v) :
    Rabs (sqrt u - sqrt v) ≤ sqrt (Rabs (u - v)).
Proof.
  Either (v ≤ u) or (¬ (v ≤ u)).
  - Case (v ≤ u).
    It holds that v ≤ u.
    By sqrt_diff_le it holds that sqrt u - sqrt v ≤ sqrt (u - v).
    By sqrt_le_1 it holds that sqrt v ≤ sqrt u.
    It holds that Rabs (sqrt u - sqrt v) = sqrt u - sqrt v as (Ea1).
    It holds that Rabs (u - v) = u - v as (Ea2).
    We conclude that Rabs (sqrt u - sqrt v) ≤ sqrt (Rabs (u - v)).
  - Case (¬ (v ≤ u)).
    It holds that u ≤ v.
    By sqrt_diff_le it holds that sqrt v - sqrt u ≤ sqrt (v - u).
    By sqrt_le_1 it holds that sqrt u ≤ sqrt v.
    It holds that Rabs (sqrt u - sqrt v) = sqrt v - sqrt u as (Ea1).
    It holds that Rabs (u - v) = v - u as (Ea2).
    We conclude that Rabs (sqrt u - sqrt v) ≤ sqrt (Rabs (u - v)).
Qed.

(** The ε–δ estimate itself, stated over plain reals: [δ = ε²]. *)
Lemma sqrt_unif_aux (eps : ℝ) (Heps : eps > 0) :
    ∀ x : ℝ, ∀ y : ℝ, 0 ≤ x → 0 ≤ y →
      Rabs (x - y) < eps * eps → Rabs (sqrt x - sqrt y) < eps.
Proof.
  Take x : ℝ. Take y : ℝ.
  Assume that 0 ≤ x.
  Assume that 0 ≤ y.
  Assume that Rabs (x - y) < eps * eps.
  By sqrt_abs_diff it holds that
    Rabs (sqrt x - sqrt y) ≤ sqrt (Rabs (x - y)).
  By Rabs_pos it holds that 0 ≤ Rabs (x - y).
  It holds that 0 ≤ eps * eps.
  By sqrt_lt_1 it holds that
    sqrt (Rabs (x - y)) < sqrt (eps * eps).
  By sqrt_square it holds that sqrt (eps * eps) = eps.
  We conclude that Rabs (sqrt x - sqrt y) < eps.
Qed.

Lemma sqrt_uniformly_continuous :
    uniformly_continuous_on sqrt (fun x => 0 ≤ x).
Proof.
  We need to show that ∀ ε > 0, ∃ δ > 0, ∀ x ∈ ℝ, ∀ y ∈ ℝ,
    0 ≤ x → 0 ≤ y → Rabs (x - y) < δ → Rabs (sqrt x - sqrt y) < ε.
  Take ε > 0.
  It holds that ε * ε > 0.
  Choose δ := ε * ε.
  - Indeed, ε * ε > 0.
  - We need to show that ∀ x ∈ ℝ, ∀ y ∈ ℝ,
      0 ≤ x → 0 ≤ y → Rabs (x - y) < δ → Rabs (sqrt x - sqrt y) < ε.
    Take x ∈ ℝ. Take y ∈ ℝ.
    Assume that 0 ≤ x.
    Assume that 0 ≤ y.
    Assume that Rabs (x - y) < ε * ε.
    By sqrt_unif_aux we conclude that Rabs (sqrt x - sqrt y) < ε.
Qed.
