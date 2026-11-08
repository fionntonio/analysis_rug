(** * RUG.Analysis.Topology — Open sets, closed sets, and limit points.

  #<a href="../../index.html##lecture05">Lecture 5</a># and #<a href="../../index.html##lecture06">Lecture 6</a>#.

  Formalizes Abbott §3.2–3.3: open and closed subsets of ℝ, limit points,
  closures, and the relationship between open/closed sets. *)

Require Import RUG.Analysis.Lib.StdlibReals.
From Stdlib Require Import Logic.Classical_Pred_Type.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
From Waterproof Require Import Libs.Analysis.OpenAndClosed.
Require Export RUG.Analysis.Sequences.
Require Export RUG.Analysis.Lib.Compactness.

Waterproof Enable Automation RealsAndIntegers.
Waterproof Enable Automation Intuition.

Open Scope R_scope.
Open Scope subset_scope.

Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".

(** A set [O ⊆ ℝ] is *open* if every point of [O] is interior:
    [∀ a ∈ O, ∃ ε > 0, V_ε(a) ⊆ O], where [V_ε(a) = {x : |x - a| < ε}].
    A set [F] is *closed* if its complement is open, equivalently if it contains
    all its limit points. *)

(** ** Open intervals are open *)

(** Example (Abbott Example 3.2.2(ii)): the open interval [(a, b)] is an open set.

    Proof idea: for [x ∈ (a,b)], set [ε = min(x - a, b - x) > 0]. Any [y] with
    [|y - x| < ε] satisfies [y > x - ε ≥ a] and [y < x + ε ≤ b], so
    [V_ε(x) ⊆ (a,b)]. *)
Lemma open_interval_is_open (a b : ℝ) (Hab : a < b) :
    (fun x => a < x < b) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => a < x < b), ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => a < x < b).
  Take y ∈ (fun x => a < x < b).
  It holds that a < y < b.
  Choose r := Rmin (y - a) (b - y).
  - Indeed, Rmin (y - a) (b - y) > 0.
  - We need to show that ∀ x ∈ (open_ball y r), x ∈ (fun x => a < x < b).
    Take x ∈ (open_ball y r).
    It holds that | x - y | < r.
    By Rabs_def2 it holds that x - y < r ∧ - r < x - y.
    By Rmin_l it holds that Rmin (y - a) (b - y) ≤ y - a.
    By Rmin_r it holds that Rmin (y - a) (b - y) ≤ b - y.
    We conclude that a < x < b.
Qed.

(** ** Open sets are closed under finite intersection *)

(** _Unions and intersections_ of open sets (Abbott Theorem 3.2.3(ii)): the intersection of two open sets is open.

    Proof idea: for [x ∈ A ∩ B], openness gives [ε₁] with [V_{ε₁}(x) ⊆ A] and
    [ε₂] with [V_{ε₂}(x) ⊆ B]; then [ε = min(ε₁, ε₂)] gives [V_ε(x) ⊆ A ∩ B].
    (This fails for infinite intersections: [⋂ₙ (-1/n, 1/n) = {0}] is not
    open.) *)
Lemma open_inter (A B : ℝ → Prop)
    (HA : A is _open_) (HB : B is _open_) :
    (fun x => A x ∧ B x) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => A x ∧ B x),
      ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∧ B x).
  Take y ∈ (fun x => A x ∧ B x).
  It holds that A y ∧ B y.
  It holds that A y. It holds that B y.
  By HA it holds that is_interior_point y A.
  It holds that (∃ r1 > 0, ∀ x ∈ (open_ball y r1), x ∈ A) as (HiA').
  Obtain such a r1.
  By HB it holds that is_interior_point y B.
  It holds that (∃ r2 > 0, ∀ x ∈ (open_ball y r2), x ∈ B) as (HiB').
  Obtain such a r2.
  Choose r := Rmin r1 r2.
  - Indeed, Rmin r1 r2 > 0.
  - We need to show that
      ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∧ B x).
    Take x ∈ (open_ball y r).
    It holds that | x - y | < r.
    By Rmin_l it holds that Rmin r1 r2 ≤ r1.
    By Rmin_r it holds that Rmin r1 r2 ≤ r2.
    It holds that | x - y | < r1. It holds that | x - y | < r2.
    It holds that x ∈ (open_ball y r1).
    It holds that x ∈ (open_ball y r2).
    By HiA' it holds that x ∈ A.
    By HiB' it holds that x ∈ B.
    We conclude that x ∈ (fun x => A x ∧ B x).
Qed.

(** ** Open sets are closed under arbitrary union *)

(** _Unions and intersections_ of open sets (Abbott Theorem 3.2.3(i)): the union of two open sets is open.

    Proof idea: for [x ∈ A ∪ B], say [x ∈ A]; openness of [A] gives [ε > 0] with
    [V_ε(x) ⊆ A ⊆ A ∪ B]. (The same argument works for arbitrary unions.) *)
Lemma open_union (A B : ℝ → Prop)
    (HA : A is _open_) (HB : B is _open_) :
    (fun x => A x ∨ B x) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => A x ∨ B x),
      ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∨ B x).
  Take y ∈ (fun x => A x ∨ B x).
  It holds that A y ∨ B y.
  Either (A y) or (B y).
  - Case (A y).
    By HA it holds that is_interior_point y A.
    It holds that (∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ A) as (HiA').
    Obtain such a r.
    Choose (r).
    + Indeed, r > 0.
    + We need to show that
        ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∨ B x).
      Take x ∈ (open_ball y r).
      By HiA' it holds that x ∈ A.
      We conclude that x ∈ (fun x => A x ∨ B x).
  - Case (B y).
    By HB it holds that is_interior_point y B.
    It holds that (∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ B) as (HiB').
    Obtain such a r.
    Choose (r).
    + Indeed, r > 0.
    + We need to show that
        ∀ x ∈ (open_ball y r), x ∈ (fun x => A x ∨ B x).
      Take x ∈ (open_ball y r).
      By HiB' it holds that x ∈ B.
      We conclude that x ∈ (fun x => A x ∨ B x).
Qed.

(** ** Open sets under arbitrary union *)

(** An arbitrary union of open sets is open.

    Proof idea: for [x] in the union, [x ∈ U i] for some index [i]; openness of
    [U i] gives a ball [V_ε(x) ⊆ U i], which is contained in the union. *)
Lemma open_union_arbitrary (Idx : Type) (U : Idx → (ℝ → Prop))
    (HU : ∀ i : Idx, (U i) is _open_) :
    (fun x => ∃ i : Idx, U i x) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => ∃ i : Idx, U i x),
      ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => ∃ i : Idx, U i x).
  Take y ∈ (fun x => ∃ i : Idx, U i x).
  It holds that (∃ i : Idx, U i y).
  Obtain such an i.
  It holds that U i y.
  By (HU i) it holds that is_interior_point y (U i).
  It holds that (∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (U i)) as (Hint').
  Obtain such a r.
  Choose (r).
  - Indeed, r > 0.
  - We need to show that
      ∀ x ∈ (open_ball y r), x ∈ (fun x => ∃ i : Idx, U i x).
    Take x ∈ (open_ball y r).
    By Hint' it holds that x ∈ (U i).
    It holds that U i x.
    We conclude that x ∈ (fun x => ∃ i : Idx, U i x).
Qed.

(** ** Closed intervals are closed *)

(** The upper half-line [(a, +∞)] is open.

    Proof idea: for [y > a], the ball [V_{y-a}(y)] lies in [(a, +∞)]. *)
Lemma upper_half_interval_is_open (a : ℝ) :
    (fun x => a < x) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => a < x), ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => a < x).
  Take y ∈ (fun x => a < x).
  It holds that a < y.
  Choose r := y - a.
  - Indeed, y - a > 0.
  - We need to show that ∀ x ∈ (open_ball y r), x ∈ (fun x => a < x).
    Take x ∈ (open_ball y r).
    It holds that | x - y | < r.
    By Rabs_def2 it holds that x - y < r.
    We conclude that a < x.
Qed.

(** The lower half-line [(-∞, b)] is open.

    Proof idea: for [y < b], the ball [V_{b-y}(y)] lies in [(-∞, b)]. *)
Lemma lower_half_interval_is_open (b : ℝ) :
    (fun x => x < b) is _open_.
Proof.
  We need to show that
    ∀ y ∈ (fun x => x < b), ∃ r > 0, ∀ x ∈ (open_ball y r), x ∈ (fun x => x < b).
  Take y ∈ (fun x => x < b).
  It holds that y < b.
  Choose r := b - y.
  - Indeed, b - y > 0.
  - We need to show that ∀ x ∈ (open_ball y r), x ∈ (fun x => x < b).
    Take x ∈ (open_ball y r).
    It holds that | x - y | < r.
    By Rabs_def2 it holds that - r < x - y.
    We conclude that x < b.
Qed.

(** Example (Abbott Example 3.2.9(ii)): the closed interval [[a, b]] is a closed set.

    Proof idea: the complement [(-∞, a) ∪ (b, ∞)] is open, as it is the union
    of the two open half-lines [(-∞, a)] and [(b, ∞)]
    ([lower_half_interval_is_open], [upper_half_interval_is_open] and
    [open_union]). *)
Lemma closed_interval_is_closed (a b : ℝ) (Hab : a ≤ b) :
    (fun x => a ≤ x ∧ x ≤ b) is _closed_.
Proof.
  We need to show that complement (fun x => a ≤ x ∧ x ≤ b) is _open_.
  We need to show that (fun x => ¬ (a ≤ x ∧ x ≤ b)) is _open_.

  (** Two sets described by logically equivalent propositions are equal:
      this needs functional and propositional extensionality. The
      equivalence itself is essentially De Morgan's law. *)
  We claim that
    (fun x : ℝ => ¬ (a ≤ x ∧ x ≤ b)) = (fun x : ℝ => x < a ∨ b < x)
    as (Hcomp).
  {
    By (@functional_extensionality ℝ Prop) it suffices to show that
      ∀ x : ℝ, (¬ (a ≤ x ∧ x ≤ b)) = (x < a ∨ b < x).
    Take x : ℝ.
    By propositional_extensionality it suffices to show that
      (¬ (a ≤ x ∧ x ≤ b)) ⇔ (x < a ∨ b < x).
    We show both directions.
    - We need to show that ¬ (a ≤ x ∧ x ≤ b) ⇨ x < a ∨ b < x.
      Assume that ¬ (a ≤ x ∧ x ≤ b) as (Hn).
      Either x < a or a ≤ x.
      + Case x < a.
        We conclude that x < a ∨ b < x.
      + Case a ≤ x.
        It holds that ¬ (x ≤ b).
        It holds that b < x.
        We conclude that x < a ∨ b < x.
    - We need to show that x < a ∨ b < x ⇨ ¬ (a ≤ x ∧ x ≤ b).
      Assume that x < a ∨ b < x as (Hout).
      Assume that a ≤ x ∧ x ≤ b.
      Because (Hout) either (x < a) or (b < x) holds.
      + Case x < a.
        Contradiction.
      + Case b < x.
        Contradiction.
  }

  It holds that (fun x => ¬ (a ≤ x ∧ x ≤ b)) = (fun x => x < a ∨ b < x).
  It suffices to show that (fun x => x < a ∨ b < x) is _open_.

  By open_union it suffices to show that
    ((fun x => x < a) is _open_) ∧ ((fun x => b < x) is _open_).
  By lower_half_interval_is_open it holds that (fun x => x < a) is _open_.
  By upper_half_interval_is_open it holds that (fun x => b < x) is _open_.
  We conclude that ((fun x => x < a) is _open_) ∧ ((fun x => b < x) is _open_).
Qed.

(** ** Closed sets under finite union *)

(** _Unions and intersections_ of closed sets (Abbott Theorem 3.2.14(i)): the union of two closed sets is closed.

    Proof idea: by de Morgan the complement is [Fᶜ ∩ Gᶜ], an intersection of two
    open sets, hence open ([open_inter]). *)
Lemma closed_union (F G : ℝ → Prop)
    (HF : F is _closed_) (HG : G is _closed_) :
    (fun x => F x ∨ G x) is _closed_.
Proof.
  We need to show that
    ∀ a ∈ (ℝ\(fun x => F x ∨ G x)),
      is_interior_point a (ℝ\(fun x => F x ∨ G x)).
  Take a ∈ (ℝ\(fun x => F x ∨ G x)).
  It holds that ¬ (F a ∨ G a).
  It holds that ¬ F a. It holds that ¬ G a.
  It holds that a ∈ (ℝ\F).
  It holds that a ∈ (ℝ\G).
  By HF it holds that is_interior_point a (ℝ\F).
  It holds that (∃ r1 > 0, ∀ x ∈ (open_ball a r1), x ∈ (ℝ\F)) as (HiF').
  Obtain such a r1.
  By HG it holds that is_interior_point a (ℝ\G).
  It holds that (∃ r2 > 0, ∀ x ∈ (open_ball a r2), x ∈ (ℝ\G)) as (HiG').
  Obtain such a r2.
  We need to show that
    (∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ (ℝ\(fun x => F x ∨ G x))).
  Choose r := Rmin r1 r2.
  - Indeed, Rmin r1 r2 > 0.
  - We need to show that
      ∀ x ∈ (open_ball a r), x ∈ (ℝ\(fun x => F x ∨ G x)).
    Take x ∈ (open_ball a r).
    It holds that | x - a | < r.
    By Rmin_l it holds that Rmin r1 r2 ≤ r1.
    By Rmin_r it holds that Rmin r1 r2 ≤ r2.
    It holds that | x - a | < r1. It holds that | x - a | < r2.
    It holds that x ∈ (open_ball a r1).
    It holds that x ∈ (open_ball a r2).
    By HiF' it holds that x ∈ (ℝ\F).
    By HiG' it holds that x ∈ (ℝ\G).
    It holds that ¬ F x. It holds that ¬ G x.
    It holds that ¬ (F x ∨ G x).
    We conclude that x ∈ (ℝ\(fun x => F x ∨ G x)).
Qed.

(** ** Closed sets under arbitrary intersection *)

(** _Unions and intersections_ of closed sets (Abbott Theorem 3.2.14(ii)): an arbitrary intersection of closed sets is closed.

    Proof idea: by de Morgan the complement is [⋃ᵢ Fᵢᶜ], an arbitrary union of
    open sets, hence open ([open_union_arbitrary]). *)
Lemma closed_inter_arbitrary (Idx : Type) (F : Idx → (ℝ → Prop))
    (HF : ∀ i : Idx, F i is _closed_) :
    (fun x => ∀ i : Idx, F i x) is _closed_.
Proof.
  We need to show that
    ∀ a ∈ (ℝ\(fun x => ∀ i : Idx, F i x)),
      is_interior_point a (ℝ\(fun x => ∀ i : Idx, F i x)).
  Take a ∈ (ℝ\(fun x => ∀ i : Idx, F i x)).
  It holds that ¬ (∀ i : Idx, F i a).
  By not_all_ex_not it holds that (∃ i : Idx, ¬ F i a).
  Obtain such an i.
  It holds that ¬ F i a.
  It holds that a ∈ (ℝ\(F i)).
  By (HF i) it holds that is_interior_point a (ℝ\(F i)).
  It holds that (∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ (ℝ\(F i))) as (Hint').
  Obtain such a r.
  We need to show that
    (∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ (ℝ\(fun x => ∀ i : Idx, F i x))).
  Choose (r).
  - Indeed, r > 0.
  - We need to show that
      ∀ x ∈ (open_ball a r), x ∈ (ℝ\(fun x => ∀ i : Idx, F i x)).
    Take x ∈ (open_ball a r).
    By Hint' it holds that x ∈ (ℝ\(F i)).
    It holds that ¬ F i x.
    It holds that ¬ (∀ j : Idx, F j x).
    We conclude that x ∈ (ℝ\(fun x => ∀ i : Idx, F i x)).
Qed.

(** ** Limit points *)

(** [x] is a *limit point* of [A] if every neighbourhood of [x] contains a
    point of [A] distinct from [x]. *)
Definition is_limit_point (A : ℝ → Prop) (x : ℝ) : Prop :=
    ∀ ε > 0, ∃ y ∈ A, 0 < | y - x | < ε.

Notation "x 'is' 'a' '_limit' 'point_' 'of' A" :=
  (is_limit_point A x) (at level 69).

Notation "x 'is' 'a' 'limit' 'point' 'of' A" :=
  (is_limit_point A x) (at level 69, only parsing).

Waterproof Register Expand "limit" "point";
  for is_limit_point;
  as "Definition limit point".

(** A point [x] is a limit point of [A] iff every neighbourhood contains a
    point of [A] other than [x] itself; equivalently, iff there is a sequence in
    [A \ {x}] converging to [x].

    Proof idea: (⇒) taking [ε = 1/n] gives points [aₙ ∈ A] with
    [0 < |aₙ - x| < 1/n], so [aₙ → x]. (⇐) given such a sequence and [ε > 0],
    convergence provides a term within [ε] of [x] and distinct from it. *)
Lemma limit_point_characterization (A : ℝ → Prop) (x : ℝ) :
    (x is a _limit point_ of A) ⇔
    (∃ a : ℕ → ℝ, (∀ n ∈ ℕ, a n ∈ A) ∧ (∀ n ∈ ℕ, a n ≠ x) ∧ a ⟶ x).
Proof.
  We show both directions.

  - We need to show that
      (x is a _limit point_ of A) ⇨
      (∃ a : ℕ → ℝ, (∀ n ∈ ℕ, a n ∈ A) ∧ (∀ n ∈ ℕ, a n ≠ x) ∧ a ⟶ x).

    Assume that x is a _limit point_ of A.
    It holds that ∀ ε > 0, ∃ y ∈ A, 0 < | y - x | < ε as (Hlp).
    We claim that
      ∀ n : ℕ, ∃ y : ℝ, y ∈ A ∧ 0 < | y - x | < 1 / (INR n + 1) as (Hsteps).
    {
      Take n : ℕ.
      Use ε := 1 / (INR n + 1) in (Hlp). { Indeed, 1 / (INR n + 1) > 0. }
      It holds that ∃ y ∈ A, 0 < |y - x| < 1 / (INR n + 1).
      It holds that ∃ y : ℝ, y ∈ A ∧ 0 < | y - x | < 1 / (INR n + 1).
      Indeed, ∃ y : ℝ, y ∈ A ∧ 0 < | y - x | < 1 / (INR n + 1).
    }

    By (countable_choice
        (fun n y => y ∈ A ∧ 0 < | y - x | < 1 / (INR n + 1)) Hsteps)
      it holds that
      ∃ a : ℕ → ℝ, ∀ n : ℕ, a n ∈ A ∧ 0 < | a n - x | < 1 / (INR n + 1)
      as (H_seq).
    Obtain a according to (H_seq).
    It holds that
      ∀ n : ℕ, a n ∈ A ∧ 0 < | a n - x | < 1 / (INR n + 1) as (H_a).

    We claim that ∀ n ∈ ℕ, a n ∈ A as (H_A).
    {
      Take n ∈ ℕ.
      Use n0 := n in (H_a).
      It holds that a(n) ∈ A ∧ 0 < |a(n) - x| < 1 / (n + 1).
      Indeed, a(n) ∈ A.
    }

    We claim that ∀ n ∈ ℕ, a(n) ≠ x as (H_neq).
    {
      Take n ∈ ℕ.
      Use n0 := n in (H_a).
      It holds that a(n) ∈ A ∧ 0 < |a(n) - x| < 1 / (n + 1).
      It holds that |a(n) - x| > 0.
      Indeed, a(n) ≠ x.
    }

    We claim that a ⟶ x.
    {
      We need to show
        ∀ ε > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, |a(n) - x| < ε.
      Take ε > 0.
      By the Archimedean property it holds that
        ∃ n1 ∈ ℕ, n1 > / ε as (Arch_N).
      Obtain such an n1. Choose N1 := n1. { Indeed, N1 ∈ ℕ. }

      We need to show that ∀ n ≥ N1, |a(n) - x| < ε.
      By Arch_N it holds that INR N1 > / ε as (H_arch_bound).
      Take n ≥ N1.
      It holds that n >= N1 as (Order_N).

      By Order_N it holds that INR n >= INR N1 as (H_real_order).
      By H_real_order and H_arch_bound it holds that
        INR n + 1 > / ε as (H_inv_bound).
      By H_inv_bound it holds that 1 / (INR n + 1) < ε.

      Use n0 := n in (H_a).
      It holds that a(n) ∈ A ∧ 0 < |a(n) - x| < 1 / (n + 1) as (seq_n).
      By seq_n it holds that 0 < |a(n) - x| < 1 / (n + 1) as (seq_bound).
      By seq_bound and H_inv_bound it holds that
        (& |a(n) - x| < 1 / (n + 1) < ε).
      Indeed, |a(n) - x| < ε.
    }
    Choose a0 := a.
    By H_A and H_neq it holds that
      (∀ n ∈ ℕ, a0(n) ∈ A) ∧ (∀ n ∈ ℕ, a0(n) ≠ x) ∧ a0 ⟶ x.
    We conclude that
      (∀ n ∈ ℕ, a0(n) ∈ A) ∧ (∀ n ∈ ℕ, a0(n) ≠ x) ∧ a0 ⟶ x.

  - We need to show that
      (∃ a : ℕ → ℝ, (∀ n ∈ ℕ, a n ∈ A) ∧ (∀ n ∈ ℕ, a n ≠ x) ∧ a ⟶ x) ⇒
      (x is a _limit point_ of A).
    Assume that
      ∃ a : ℕ → ℝ, (∀ n ∈ ℕ, a n ∈ A) ∧ (∀ n ∈ ℕ, a n ≠ x) ∧ a ⟶ x
      as (Hrp).
    We need to show that ∀ ε > 0, ∃ y ∈ A, 0 < Rabs (y - x) < ε.
    Take ε > 0.
    Obtain a according to (Hrp).
    By Hrp it holds that a ⟶ x as (lim_a).
    By lim_a it holds that
      ∀ ε0 > 0, ∃ N1 ∈ ℕ, ∀ n ≥ N1, |a(n) - x| < ε0 as (eps_a).
    Use ε0 := ε in (eps_a). { Indeed, ε > 0. }
    It holds that ∃ N1 ∈ ℕ, ∀ n ≥ N1, |a(n) - x| < ε as (N_eps).
    Obtain N1 according to (N_eps).
    It holds that |a(N1) - x| < ε.
    By Hrp it holds that ∀ n ∈ ℕ, a n ∈ A as (a_in).
    Use n := N1 in (a_in). { Indeed, N1 ∈ ℕ. }
    It holds that a(N1) ∈ A.
    By Hrp it holds that ∀ n ∈ ℕ, a n ≠ x as (a_neq).
    Use n := N1 in (a_neq). { Indeed, N1 ∈ ℕ. }
    It holds that a(N1) ≠ x.
    It holds that Rabs (a(N1) - x) > 0.
    Choose y := a(N1). { Indeed, y ∈ A. }
    We conclude that 0 < |y - x| < ε.
Qed.

(** ** Open/closed duality *)

(** Taking the complement twice gives back the original set. *)
Lemma complement_of_complement_is_identity (A : ℝ → Prop) :
    complement (complement A) = A.
Proof.
  By (@functional_extensionality ℝ Prop) it suffices to show that
    ∀ x : ℝ, complement (complement A) x = A x.
  Take x : ℝ.
  By propositional_extensionality it suffices to show that
    complement (complement A) x ⇔ A x.
  We show both directions.
  - We need to show that complement (complement A) x ⇨ A x.
    Assume that complement (complement A) x as (Hcc).
    It holds that ¬ ¬ A x.
    By NNPP we conclude that A x.
  - We need to show that A x ⇨ complement (complement A) x.
    Assume that A x.
    We need to show that ¬ ¬ A x.
    We conclude that ¬ ¬ A x.
Qed.

(** Complementation: [A] is open iff its complement is closed. This is immediate
    from the definition of closed as "complement is open". *)
Lemma open_iff_complement_closed (A : ℝ → Prop) :
    A is _open_ ⇔ (fun x => ¬ A x) is _closed_.
Proof.
  We show both directions.
  - We need to show that A is _open_ ⇨ (fun x => ¬ A x) is _closed_.
    Assume that A is _open_ as (Hopen).
    It holds that (fun x => ¬ A x) = complement A as (Hcomp).
    By Hcomp it holds that (fun x => ¬ A x) = complement A.

    By complement_of_complement_is_identity it holds that
      complement (complement A) = A as (Hcomp2).

    By Hcomp2 it holds that complement (complement A) = A.
    By Hopen it holds that complement (complement A) is _open_ as (Hclosed).
    By Hclosed it holds that (complement A) is _closed_ as (Hclosed2).
    By Hcomp it holds that (fun x => ¬ A x) is _closed_.
    We conclude that (fun x => ¬ A x) is _closed_.

  - We need to show that (fun x => ¬ A x) is _closed_ ⇨ A is _open_.
    Assume that (fun x => ¬ A x) is _closed_ as (Hclosed).
    It holds that (fun x => ¬ A x) = complement A as (Hcomp).
    By Hcomp it holds that (fun x => ¬ A x) = complement A.
    By Hclosed it holds that (complement A) is _closed_ as (Hclosed2).
    By Hclosed2 it holds that complement (complement A) is _open_ as (Hopen).

    By complement_of_complement_is_identity it holds that
      complement (complement A) = A as (Hcomp2).

    By Hcomp2 it holds that complement (complement A) = A.
    It holds that A = complement (complement A).

    By Hopen it holds that A is _open_.
    We conclude that A is _open_.
Qed.

(** ** Closure characterization *)

(** [A] is closed iff [A] contains all its limit points.

    Proof idea (⇒): if [A] is closed and [x] is a limit point with [x ∉ A], then
    [x ∈ Aᶜ] which is open, giving a ball [V_ε(x) ⊆ Aᶜ] disjoint from [A] —
    contradicting that [x] is a limit point. *)
Lemma closed_iff_contains_limit_points (A : ℝ → Prop) :
    A is _closed_ ⇔
    (∀ x : ℝ, x is a _limit point_ of A → A x).
Proof.
  We show both directions.
  - We need to show that
      (A is _closed_) ⇨
      (∀ x : ℝ, x is a _limit point_ of A → A x).
    Assume that (A is _closed_) as (Hcl).
    Take x : ℝ.
    Assume that (x is a _limit point_ of A).
    It holds that (∀ ε > 0, ∃ y ∈ A, 0 < | y - x | < ε) as (Hlp).
    We argue by contradiction.
    Assume that ¬ A x.
    It holds that x ∈ (ℝ\A).
    By Hcl it holds that is_interior_point x (ℝ\A).
    It holds that (∃ ε > 0, ∀ z ∈ (open_ball x ε), z ∈ (ℝ\A)) as (Hint').
    Obtain such a ε.
    By Hlp it holds that (∃ y ∈ A, 0 < | y - x | < ε).
    Obtain such a y. It holds that y ∈ A ∧ 0 < | y - x | < ε.
    It holds that y ∈ A. It holds that 0 < | y - x | < ε.
    It holds that | y - x | < ε.
    It holds that y ∈ (open_ball x ε).
    By Hint' it holds that y ∈ (ℝ\A).
    It holds that ¬ A y.
    Contradiction.
  - We need to show that
      (∀ x : ℝ, x is a _limit point_ of A → A x) ⇨
      (A is _closed_).
    Assume that
      (∀ x : ℝ, x is a _limit point_ of A → A x) as (Hlp).
    We need to show that ∀ a ∈ (ℝ\A), is_interior_point a (ℝ\A).
    Take a ∈ (ℝ\A).
    It holds that ¬ A a.
    We claim that ¬ (a is a _limit point_ of A).
    { We argue by contradiction.
      Assume that ¬ ¬ (a is a _limit point_ of A).
      It holds that (a is a _limit point_ of A).
      By Hlp it holds that A a.
      Contradiction. }
    It holds that ¬ (∀ ε > 0, ∃ y ∈ A, 0 < | y - a | < ε).
    By not_all_ex_not it holds that
      (∃ ε, ¬ (ε > 0 → (∃ y ∈ A, 0 < | y - a | < ε))).
    Obtain such a ε.
    By imply_to_and it holds that
      (ε > 0 ∧ ¬ (∃ y ∈ A, 0 < | y - a | < ε)).
    It holds that ε > 0.
    It holds that ¬ (∃ y ∈ A, 0 < | y - a | < ε).
    We need to show that (∃ r > 0, ∀ x ∈ (open_ball a r), x ∈ (ℝ\A)).
    Choose r := ε.
    + Indeed, ε > 0.
    + We need to show that ∀ x ∈ (open_ball a r), x ∈ (ℝ\A).
      Take x ∈ (open_ball a r).
      It holds that | x - a | < r.
      We argue by contradiction.
      Assume that ¬ (x ∈ (ℝ\A)).
      It holds that ¬ ¬ A x.
      By NNPP it holds that A x.
      It holds that x ∈ A.
      It holds that x ≠ a.
      It holds that x - a ≠ 0.
      By Rabs_no_R0 it holds that | x - a | ≠ 0.
      It holds that 0 < | x - a |.
      We claim that (∃ y ∈ A, 0 < | y - a | < ε).
      { Choose y := x.
        - Indeed, x ∈ A.
        - We conclude that 0 < | x - a | < ε. }
      Contradiction.
Qed.

(** ** Isolated points *)

(** A point [x ∈ A] is *isolated* in [A] if some neighbourhood of [x] meets [A]
    only at [x] itself — equivalently, [x ∈ A] is not a limit point of [A]. *)
Definition is_isolated_point (A : ℝ → Prop) (x : ℝ) : Prop :=
    A x ∧ ∃ ε > 0, ∀ y ∈ A, | y - x | < ε → y = x.

(** ** Closure *)

(** The *closure* [Ā] of [A] is [A] together with all its limit points. *)
Definition closure (A : ℝ → Prop) : ℝ → Prop :=
    fun x => A x ∨ (x is a _limit point_ of A).

(** Characterization of the closure: [x ∈ Ā] iff every neighbourhood of [x]
    contains a point of [A]. Equivalently, iff there is a sequence in [A]
    converging to [x].

    Proof idea: if [x ∈ A] every ball trivially contains [x ∈ A]; if [x] is a
    limit point every ball contains a point of [A] distinct from [x].
    Conversely, if every ball meets [A] then either [x ∈ A] or [x] is a limit
    point of [A]. *)
Lemma closure_characterization (A : ℝ → Prop) (x : ℝ) :
    closure A x ⇔ (∀ ε > 0, ∃ y ∈ A, | y - x | < ε).
Proof.
  We show both directions.
  - We need to show that
      (A x ∨ (x is a _limit point_ of A)) ⇨ (∀ ε > 0, ∃ y ∈ A, | y - x | < ε).
    Assume that (A x ∨ (x is a _limit point_ of A)).
    Take ε > 0.
    Either (A x) or (x is a _limit point_ of A).
    + Case (A x).
      Choose y := x.
      * Indeed, x ∈ A.
      * We conclude that | x - x | < ε.
    + Case (x is a _limit point_ of A).
      By H it holds that (∃ y ∈ A, 0 < | y - x | < ε).
      Obtain such a y. It holds that y ∈ A ∧ 0 < | y - x | < ε.
      It holds that y ∈ A. It holds that 0 < | y - x | < ε.
      Choose y0 := y.
      * Indeed, y ∈ A.
      * We conclude that | y - x | < ε.
  - We need to show that
      (∀ ε > 0, ∃ y ∈ A, | y - x | < ε) ⇨ (A x ∨ (x is a _limit point_ of A)).
    Assume that (∀ ε > 0, ∃ y ∈ A, | y - x | < ε) as (Hnb).
    Either (A x) or (¬ A x).
    + Case (A x). It holds that A x ∨ (x is a _limit point_ of A). We conclude that closure A x.
    + Case (¬ A x).
      It suffices to show that (x is a _limit point_ of A).
      We need to show that ∀ ε > 0, ∃ y ∈ A, 0 < | y - x | < ε.
      Take ε > 0.
      By Hnb it holds that (∃ y ∈ A, | y - x | < ε).
      Obtain such a y. It holds that y ∈ A ∧ | y - x | < ε.
      It holds that y ∈ A. It holds that | y - x | < ε.
      It holds that y ≠ x.
      It holds that y - x ≠ 0.
      By Rabs_no_R0 it holds that | y - x | ≠ 0.
      It holds that 0 < | y - x |.
      Choose y0 := y.
      * Indeed, y ∈ A.
      * We conclude that 0 < | y - x | < ε.
Qed.

(** The closure [Ā] is a closed set.

    Proof idea: one shows [Ā] contains all of its own limit points. A limit
    point of [Ā] is approximated arbitrarily well by points of [Ā], each of
    which is either in [A] or approximated by points of [A]; a diagonal argument
    then produces points of [A] arbitrarily close, so the point is already in
    [Ā]. *)
Lemma closure_is_closed (A : ℝ → Prop) :
    (closure A) is _closed_.
Proof.
  We claim that
    ∀ x : ℝ, x is a _limit point_ of (closure A) → closure A x as (Hlimpts).
  {
    Take x : ℝ.
    Assume that (x is a _limit point_ of (closure A)).
    It holds that (∀ ε > 0, ∃ y ∈ (closure A), 0 < | y - x | < ε) as (Hlp).
    We claim that ∀ ε > 0, ∃ y ∈ A, | y - x | < ε as (Happrox).
    {
      Take ε > 0.
      By Hlp it holds that (∃ y ∈ (closure A), 0 < | y - x | < ε).
      Obtain such a y.
      It holds that y ∈ (closure A) ∧ 0 < | y - x | < ε.
      It holds that closure A y.
      It holds that 0 < | y - x | < ε.
      It holds that | y - x | < ε.
      Define δ := ε - | y - x |.
      It holds that δ > 0.
      By (closure_characterization A y) it holds that
        (∀ ε' > 0, ∃ z ∈ A, | z - y | < ε') as (Hcy).
      By Hcy it holds that (∃ z ∈ A, | z - y | < δ).
      Obtain such a z.
      It holds that z ∈ A ∧ | z - y | < δ.
      It holds that z ∈ A. It holds that | z - y | < δ.
      By Rabs_triang it holds that
        |(z - y) + (y - x)| ≤ | z - y | + | y - x |.
      It holds that | z - x | ≤ | z - y | + | y - x |.
      It holds that | z - x | < ε.
      Choose z0 := z.
      - Indeed, z ∈ A.
      - We conclude that | z0 - x | < ε.
    }
    By (closure_characterization A x) we conclude that closure A x.
  }
  By (closed_iff_contains_limit_points (closure A)) it holds that
    (closure A) is _closed_ ⇔
    (∀ x : ℝ, x is a _limit point_ of (closure A) → closure A x) as (Hiff).
  By Hiff we conclude that (closure A) is _closed_.
Qed.
