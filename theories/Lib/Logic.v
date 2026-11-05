(** * RUG.Analysis.Lib.Logic

  Auxiliary facts about classical logic.
*)

Require Import RUG.Analysis.Lib.StdlibReals.
From Stdlib Require Import Logic.ClassicalDescription.

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

(** Evaluation of a classical [if] on a true condition.

    Proof idea: case analysis on the decision ([sumbool_ind]); the [right]
    branch contradicts [P]. *)
Lemma if_informative_true (P : Prop) (x y : ℝ) :
    P → (if excluded_middle_informative P then x else y) = x.
Proof.
  We claim that P → P → x = x as (Hleft).
  {
    Assume that P.
    Assume that P.
    We conclude that x = x.
  }
  We claim that ¬ P → P → y = x as (Hright).
  {
    Assume that ¬ P.
    Assume that P as (HP).
    Contradiction.
  }
  By (@sumbool_ind P (¬ P) (fun s : sumbool P (¬ P) => P → (if s then x else y) = x)
      Hleft Hright (excluded_middle_informative P))
    we conclude that P → (if excluded_middle_informative P then x else y) = x.
Qed.

(** Evaluation of a classical [if] on a false condition.

    Proof idea: case analysis on the decision ([sumbool_ind]); the [left]
    branch contradicts [¬ P]. *)
Lemma if_informative_false (P : Prop) (x y : ℝ) :
    ¬ P → (if excluded_middle_informative P then x else y) = y.
Proof.
  We claim that P → ¬ P → x = y as (Hleft).
  {
    Assume that P.
    Assume that ¬ P as (HnP).
    Contradiction.
  }
  We claim that ¬ P → ¬ P → y = y as (Hright).
  {
    Assume that ¬ P.
    Assume that ¬ P.
    We conclude that y = y.
  }
  By (@sumbool_ind P (¬ P) (fun s : sumbool P (¬ P) => ¬ P → (if s then x else y) = y)
      Hleft Hright (excluded_middle_informative P))
    we conclude that ¬ P → (if excluded_middle_informative P then x else y) = y.
Qed.
