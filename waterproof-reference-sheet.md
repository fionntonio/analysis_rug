# Waterproof Reference Sheet

A practical guide to `coq-waterproof` (v3.x on Coq/Rocq ≥ 8.17), based on the source at [impermeable/coq-waterproof](https://github.com/impermeable/coq-waterproof) and its tutorial notebooks.

Waterproof is an Ltac2/OCaml plugin that makes Coq read like an analysis textbook. You get standard math notation (`ℝ`, `∈`, `∀`, inequality chains), mandatory goal signposts, and automation that swallows routine arithmetic. Underneath, it remains standard Coq. Raw tactics like `apply`, `destruct`, `symmetry`, and `rewrite` work whenever you want them.

---

## 1. Setup

### 1.1 Installation

Students typically use the VS Code extension ("Waterproof" on the marketplace). It bundles the plugin and renders `.mv` notebook files with collapsible hints and student input boxes.

For plain `.v` files, run `opam install coq-waterproof`.

### 1.2 Preamble

Drop this at the top of every file:

```coq
From Stdlib Require Import Rbase Rfunctions.

Require Import Waterproof.Waterproof.        (* core *)
Require Import Waterproof.Notations.Common.  (* ∀, ∃, ⇒, ∧, ∨, ¬, f(x) *)
Require Import Waterproof.Notations.Reals.   (* ℝ, ℕ, ℤ, |x|, intervals *)
Require Import Waterproof.Notations.Sets.    (* ∈, ⊂, ∩, ∪, bounded quantifiers *)
Require Import Waterproof.Chains.            (* & 0 < x ≤ 1 chains *)
Require Import Waterproof.Tactics.           (* natural-language tactics *)
Require Import Waterproof.Automation.        (* hint databases *)

Waterproof Enable Automation RealsAndIntegers.

Open Scope R_scope.
Open Scope subset_scope.
Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".
```

Domain libraries live under `Waterproof.Libs.*` (`Analysis`, `Reals`, `Integers`, `Sets`, `Logic`, `Negation`, `Functions`).

### 1.3 Automation datasets

`Waterproof Enable Automation <Dataset>` loads a bundle of hint databases for `We conclude that` and `It holds that`:

| Dataset | Databases loaded |
|---|---|
| `Core` | `core` |
| `Algebra` | `wp_core, arith, zarith, wp_algebra, wp_integers, wp_negation_int` |
| `Integers` | `arith, zarith, wp_core, wp_integers, wp_negation_int` |
| `RealsAndIntegers` | `arith, zarith, real, wp_core, wp_definitions, wp_alt_chars, wp_integers, wp_reals, wp_negation_reals` |
| `Sets` | `arith, zarith, wp_core, wp_integers, wp_negation_int, wp_sets` |
| `Intuition` | `wp_intuition` |
| `Empty`, `ClassicalEpsilon` | Special-purpose |

Related controls:
- `Waterproof Disable Automation X`, `Waterproof Clear Automation`, `Waterproof List Automation Databases`
- Instructors can create datasets: `Waterproof Declare Automation MySet` followed by `Waterproof Set Main Databases MySet db1, db2` (or `Decidability` / `Shorten` in place of `Main`)
- Toggles: `Waterproof Enable/Disable Automation Shield`, `Filter Errors`, `Debug Automation`, `Hypothesis Help`, `Redirect Feedback/Errors`

The automation shield is active by default. It stops automation from silently instantiating quantifiers or splitting equivalences behind your back. Students have to write those steps themselves.

---

## 2. Notation

### 2.1 Logic

| Waterproof | Coq | Notes |
|---|---|---|
| `∀ x ..., P` / `for all x, P` | `forall` | |
| `∃ x ..., P` / `there exists x, P` | `exists` | |
| `P ⇒ Q` (also `→`, `⇨`) | `P -> Q` | `⇨` is the output form |
| `P ⇔ Q`, `↔` | `<->` | |
| `P ∧ Q`, `P ∨ Q`, `¬ P`, `x ≠ y` | `/\ , \/ , ~ , <>` | |
| `fun x ↦ t` | `fun x => t` | |
| `f(x)`, `f(x, y)` | `f x`, `f x y` | Parenthesized application |

### 2.2 Sets and bounded quantifiers (`subset_scope`)

Sets are built on `Ensemble`: `subset X` ≔ `Ensemble X`.

Set syntax: `x ∈ A`, `x ∉ A`, `A ⊂ B`, `A ∩ B`, `A ∪ B`, `A \ B`, `∅`, `Ω`, `𝒫(X)`, `{ x ∈ X | P }`, `A is empty`, `A is inhabited`, `A is disjoint from B`.

Bounded quantifiers fuse a binder with a test: `∀ x ∈ A, P`, `∃ ε > 0, P`, `∀ n ≥ N, P`, `∃ y ≠ 0, P`, and `∃! x ∈ A, P`. Recognized predicates include `∈ A`, `< y`, `≤ y`, `> y`, `≥ y`, `≠ y`. Under the hood, `∀ x > 0, P` becomes `∀ x, x > 0 ⇒ P` and `∃ x > 0, P` becomes `∃ x, x > 0 ∧ P`.

### 2.3 Numbers and analysis

`ℕ ℤ ℚ ℝ`; relations `≤ ≥`; `|x|` for `Rabs`. Intervals `[a,b]`, `[a,b)`, `(a,b]`, `(a,b)`, `[a,∞)`, `(a,∞)` live as subsets of ℝ. Limit notation: `a ⟶ c` for `converges_to`, and `Σ Cn equals x` for `infinite_sum`. Use `RealsWithSubsets` when you need ℤ or ℚ as subsets of ℝ.

### 2.4 Inequality chains

Prefix any chain with `&`:

```coq
We conclude that & 3 < 5 = 2 + 3 ≤ 6.
```

Chains turn into a conjunction of adjacent steps plus the end-to-end inequality (`3 ≤ 6`). Do not mix `<`/`≤` with `>`/`≥` in the same chain. Equality (`=`) mixes with either direction.

---

## 3. Tactics

Parenthesize any term containing spaces or operators: `(...)`. Hypotheses can be named with `as (label)`. If omitted, Waterproof assigns names like `_H`; cite unnamed hypotheses by statement using `Since (P) ...`.

### 3.1 Goals

| Sentence | What it does |
|---|---|
| `We need to show that (P).` / `To show that (P).` | Checks that the goal matches `P` (up to conversion) and reformulates the goal window. Required after case splits. |
| `We conclude that (P).` / `It follows that (P).` | Closes `P` via automation. Accepts chains: `& a ≤ b < c`. |
| `By (lemma_or_hyp) we conclude that (P).` | Closes `P`, passing automation an extra lemma or hypothesis. |
| `Since (Q) we conclude that (P).` | Same, but takes the *statement* `Q` instead of an identifier (must follow from context). |
| `It suffices to show that (P).` | Backward step: replaces current goal with `P` if automation proves `P ⇒ goal` (also `By ... it suffices ...`, `Since ... it suffices ...`). |
| `Indeed, (P).` | Discharges small side-goals, such as the membership check after `Choose`. |

### 3.2 Quantifiers

| Sentence | What it does |
|---|---|
| `Take x ∈ ℝ.` / `Take n : ℕ.` / `Take x, y : ℝ and n : ℕ.` | Introduces ∀-bound variables. Fails on ∃. Warns on variable renames. |
| `Take x : ℝ; such that (P) as (i).` | Introduces the variable and binds its bounding assumption in one step. |
| `Choose y := (2).` / `Choose (2).` | Supplies an existential witness. Bounded quantifiers leave a side-goal (`y ∈ A`, `y > 0`) that you close with `{ Indeed, ... . }`. |
| `Obtain such an n.` / `Obtain such n, m.` | Unpacks the most recently introduced ∃-hypothesis. |
| `Obtain n according to (i).` | Unpacks the ∃ from named hypothesis `(i)`. |
| `Use ε := (1/2) in (i).` | Instantiates a ∀ in hypothesis `(i)`. Bounded ∀ opens a side-condition (`1/2 > 0`) closed with `{ Indeed, ... . }`. Multiple: `Use x := a, y := b in (i).` |

### 3.3 Assumptions and forward steps

| Sentence | What it does |
|---|---|
| `Assume that (P).` / `Assume that (P) as (i).` | Introduces the antecedent of an implication or negation. Rejects statements that don't match. |
| `It holds that (P) as (i).` | Proves `P` via automation and adds it to the context. |
| `By (ref) it holds that (P).` / `Since (Q) it holds that (P).` | Adds `P` using an explicit reference or provable statement. |
| `We claim that (P) as (i).` | Asserts `P` and opens a focused subproof for you to prove manually. |
| `Define u := (t).` | Adds a local definition. |
| `Because (i) both (P) as (h1) and (Q) as (h2).` | Unpacks a conjunction `P ∧ Q` from hypothesis `(i)`. |
| `Because (i) either (P) or (Q).` | Splits on disjunction `(i)`; prove each branch under `- Case (P).` bullets. |

### 3.4 Proof structure

```coq
Either x < y or x ≥ y.            (* split on a decidable relation *)
- Case x < y.  ...
- Case x ≥ y.  ...

Either x < 0, x = 0 or x > 0.     (* three-way trichotomy *)

We show both statements.          (* goal: A ∧ B; also: We show both (A) and (B). *)
* We need to show that (A). ...
* We need to show that (B). ...

We show both directions.          (* goal: A ⇔ B *)
++ We need to show that (A ⇒ B). ...
++ We need to show that (B ⇒ A). ...

We argue by contradiction.
Assume that ¬ (P).
... Contradiction.                (* or ↯ *)

We use induction on k.
+ We first show the base case (P 0). ...
+ We now show the induction step.
  Take k ∈ ℕ. Assume that (P k). ... (* prove P (k+1) *)
```

### 3.5 Inspection and help

| Sentence | What it does |
|---|---|
| `Expand the definition of (f).` / `Expand (f).` | Prints suggested `That is, write ...` rewrites with `f` unfolded. |
| `Expand All.` | Suggestions for all recognized definitions in the goal. |
| `Help.` | Prints tactics that might make progress on the current goal. |

All three are for interactive inspection. Delete them before submitting a proof.

---

## 4. Worked example

```coq
Lemma sequence_bound :
  ∀ x ∈ ℝ, (∀ ε > 0, x < ε) ⇒ x ≤ 0.
Proof.
Take x ∈ ℝ.
Assume that ∀ ε > 0, x < ε as (i).
We argue by contradiction.
Assume that ¬ (x ≤ 0).
It holds that x > 0.
Use ε := x in (i).
{ Indeed, x > 0. }
It holds that x < x.
Contradiction.
Qed.
```

Chaining an inequality:

```coq
By f_increasing we conclude that & 2 < f(0) ≤ f(1).
```

---

## 5. Pitfalls

1. **`Take` on an existential goal.** `Take` is strictly for `∀`. Use `Choose` for `∃`.
2. **Renaming binders.** If the goal says `∀ x, ...`, running `Take y : ℝ` throws a warning (*"Expected variable name x instead of y"*). In course grading, treat warnings as fatal errors. Same for `Obtain such an m` when the binder was `n`.
3. **Mismatched types in `Take`.** `Take n : bool` against `∀ n : ℕ` fails immediately. Don't supply more variables than the goal's quantifier prefix contains.
4. **Skipping side-goals on bounded quantifiers.** `Choose y := 2` on `∃ y ∈ ℝ, ...` generates a membership subproof. Close it on the spot: `{ Indeed, y ∈ ℝ. }`, or `{ We need to verify that y ∈ ℝ. … }` (note `verify`, not `show`, and note the space before `}`). Same deal after `Use ε := 1/2 in (i)`. `Choose` also enters `y` into the context as a let-binding, so everything downstream must refer to `y` rather than to `2`.
5. **Drift in `Assume that`.** The text inside `Assume that (P)` must match the actual antecedent term-for-term. `Assume` also rejects goals that aren't implications or negations.
6. **Automation running out of gas.** `We conclude that` runs a depth-bounded search. When it gets stuck: add intermediate `It holds that` statements, hand it the key lemma (`By lem we conclude that ...`), or check which dataset is active. `By magic it holds that` skips the search limits, but nobody grades that kindly.
7. **The automation shield.** With the shield on, `It holds that` won't instantiate quantifiers or split iffs. You have to write `Use`, `Obtain`, `Choose`, and `We show both directions` yourself.
8. **Reusing hypothesis names.** `It holds that (P) as (h)` fails if `h` is already taken in the current context.
9. **Scope collisions with `ℕ`.** With `R_scope` open, nat arithmetic needs an explicit `%nat` annotation, as in `(k ≤ n(k))%nat`. Otherwise you get cryptic type errors on `≤` and `+`.
10. **Unparenthesized expressions.** The parser expects statements as `lconstr`. If a line throws a parse error, wrap the proposition in parens: `We conclude that (x + 3 = 3 + x).`
11. **Direction flipping in chains.** `& a < b > c` fails to parse. Split it into two statements. When you need the end-to-end inequality from a previous chain hypothesis, extract it with a separate `It holds that`.
12. **Missing case signposts.** Every bullet under `Either ... or ...` must begin with `Case (...)`. Every bullet under `We show both statements` must begin with `We need to show that (...)`. Drop them and the proof script fails.
13. **`Obtain` target confusion.** `Obtain such an n` grabs only the most recently introduced existential. If you need an older one, call `Obtain n according to (label)`.
14. **Grouped quantifiers in `∀` / `∃`.** The unicode notations reject multiple names in one binder block: `∀ x y : ℝ, P` and `∃ (phi : ℕ → ℕ) (x : ℝ), P` fail with *"The reference y/x was not found"*. Write `∀ x, ∀ y` or `∀ x ∈ ℝ, ∀ y ∈ ℝ, P`. (`Take x, y : ℝ` is fine; the limit applies to propositions, not tactics.)
15. **`Type`-sorted binders.** `∀ I : Type, P` chokes the unicode notation with an internal `True`/`pat` error. Fall back to ASCII `forall (I : Type), P` when quantifying over index types or sets.
16. **Variable names hijacked by the standard library.** In lines like `It holds that`, `We need to show`, or `Define`, single-letter names often resolve to Stdlib globals rather than your local binder. Common traps: `f` hits `Rtopology.f` (a family), `N` hits `BinNums.N`, `I` hits `Logic.I`, `d` hits `Sequences.d`, `d1` hits `Ranalysis1.d1`, and `E1` hits `Exp_prop.E1` (which breaks rewrites with *"Cannot find a relation to rewrite"*). Rename your parameters to `f'`, `Nn`, `Idx`, `dlt`, `Ea1` to stay out of trouble.
17. **Goal restatements after `Choose`.** After `Choose δ := ...`, a trailing bounded `∀` needs a fresh `We need to show that ∀ x ∈ ℝ, ...` before `Take x ∈ ℝ` will work.
18. **Bounded binders produce subset types.** Writing `∀ ε > 0, P` binds `ε : subset_type ℝ (> 0)`. That breaks nat arithmetic on binders (`(n + p)%nat` becomes subset addition) and prevents feeding the variable to `mkposreal`. Write `∀ n : ℕ` / `Take n : ℕ`, or expand to `∀ ε : ℝ, ε > 0 → …`.
19. **Scope leakage in lambdas.** Writing `partial_sums (fun k => 1 / (INR k + 1)) (n + p)%nat` fails with *"INR(k) has type ℝ while it is expected to have type ℕ"*. Use `(Nat.add n p)` instead.
20. **Unsupported Ltac plumbing.** Expressions like `refine (conj _ _)` and goal selectors like `split; [|split]` fail to parse. Build conjunctions by proving each piece (`By … it holds that … as (Hk)`) and finishing with `We conclude that (A ∧ B)`. `eq_sym` also fails in term position; use the `symmetry.` tactic instead.
21. **Search hangs on implicit arguments.** Calling `By … we conclude that …` with uninstantiated arguments can stall the prover for minutes. Pass arguments explicitly, or use `exact (lemma a b c H)`.
22. **Interval notation breaks pairs.** In `R_scope`, `(a, b)` and `[a, b]` represent intervals. `Choose p := (x, r)` throws *"has type ℝ ⇨ Prop"*. Wrap pair creation in a helper: `Definition idx (c r : ℝ) : ball_index := pair c r.` Same for `ℝ * ℝ`, which gets parsed as multiplication; hide it with `Definition ball_index : Type := (ℝ * ℝ)%type.`
23. **`Obtain` order with nested existentials.** `Obtain such a y` pulls from the most recent existential in the context list, not the one you wrote last in the script. For `∃ x, ∃ y, …`, restate the inner existential (`It holds that (∃ y : ℝ, …) as (Hy).`) before running the second `Obtain`.
24. **Archimedean notation syntax.** `By the Archimedean property it holds that …` cannot take an `as (label)` suffix (it is notation for `Waterproof.Libs.Reals.ArchimedN.archimedN_exists`). Label it on the next line with `It holds that … as (H).` if you need a handle.
25. **`Use` blocked during contradictions.** When the goal is "Derive a contradiction", `Use x := t in (H)` gets rejected. Restate the instance directly: `By (H) it holds that (<instance>) as (H1).`, proving the bounding condition first.

---

## 6. Standard library interop

Analysis proofs frequently lean on Coq's standard library. Put a temporary `Search "name".` in your file to locate lemmas. Reliable entry points: `continuity_ab_maj`/`_min` (EVT), `IVT_interv`, `Heine` + `compact_P3`, `continuity_seq`, `continuity_implies_RiemannInt`, `RiemannInt_P*`, `MVT`/`MVT_cor1`/`Rolle`, `derive_increasing_interv`, `compact_carac`.

Common friction points:

- **Divergent definitions.** Waterproof's `a ⟶ L` is `converges_to`, not Stdlib's `Un_cv`. Convert between them using `convergence_equivalence : a ⟶ q ⇔ Un_cv a q`. Similarly, Waterproof's `is_open`/`is_closed` does not match `Rtopology`'s `open_set`/`closed_set`.
- **Implicit arguments in integrals.** Most `RiemannInt_P*` lemmas keep almost everything implicit. If you hit *"has type … while it is expected to have type ℝ"*, strip the explicit `f a b` terms and pass only the proofs. Also, implicit resolution needs a named variable: `RiemannInt (RiemannInt_P14 a b M)` fails, but `pose (prc := RiemannInt_P14 a b M).` followed by `RiemannInt prc` succeeds.
- **Function algebra (`%F`).** Lemmas like `continuity_pt_plus` produce statements about `(f1 + g)%F`. That matches `fun x => f1 x + g x` definitionally, but not syntactically, so `apply` will reject it. Run `We need to show that continuity_pt (fun x => f1 x + g x) c.` first, or supply the result via `By (lemma f1 g c Hf Hg) it holds that <statement> as (H1).`
- **Sigma types.** Unpack sigma types like `{z | P z}` (from `IVT_interv`) using `destruct (…) as [z Hz].`, then split `Hz` with `It holds that`.
- **Missing arithmetic facts.** The automation has blind spots around `INR`. It does not know `INR (S n) = INR n + 1`, `INR 0 = 0`, `0 ≤ INR n`, or `1 ≤ INR n + 1`. Feed them manually: `By S_INR / pos_INR / plus_INR it holds that …`. Inverses also need help: `By Rinv_r it holds that b * / b = 1 as (Ei).` clears up stuck field identities.
- **Contradiction handling.** `Contradiction` runs automation to locate the clash automatically. To sharpen `a ≤ z` to `a < z`: run `Either a = z or a ≠ z.` and close the equality branch with `- Case (a = z). … Contradiction.`

---

## 7. Extending Waterproof

### 7.1 Hint databases

To register lemmas with the automation:

```coq
Lemma my_lemma : ∀ x ∈ ℝ, ... .
Proof. ... Qed.

#[export] Hint Resolve my_lemma : wp_reals.
```

For course assignments, isolate hints in a custom database:

```coq
Create HintDb course_db.
#[export] Hint Resolve my_lemma my_other_lemma : course_db.

Waterproof Declare Automation Course.
Waterproof Set Main Databases Course wp_core, real, wp_reals, course_db.
Waterproof Set Decidability Databases Course nocore, wp_decidability_reals.
Waterproof Set Shorten Databases Course wp_core.
Waterproof Enable Automation Course.
```

`Main` handles general closing search, `Decidability` powers `Either ... or ...`, and `Shorten` trims redundant steps in `Since`/`By`.

Stick to `Hint Resolve`. Avoid heavy `Hint Extern` hooks; automation search is depth-bounded, and bloated databases slow down every `We conclude that` across the file.

### 7.2 Registering definitions for `Expand`

```coq
Definition square (x : ℝ) := x^2.

Waterproof Register Expand "square";
  for square;
  as "Definition square".
```

Now `Expand square.` will suggest natural-language reformulations that students can click to apply in VS Code.

### 7.3 Custom notation

```coq
Notation "'max(' x , y )" := (Rmax x y) (format "'max(' x ,  y ')'").
Notation "a 'is' 'even'" := (Nat.Even a) (at level 68).
```

For predicate styles like `x is a lower bound for A`, inspect `theories/Libs/Analysis/SupAndInf.v` for precedence patterns (`is`-notations sit around level 68–70).

### 7.4 Adding tactics

Tactics live in `theories/Tactics/*.v` as Ltac2 notations over Ltac2 functions. Diagnostic messaging is handled by `theories/Util/MessagesToUser.v`. The heavy lifting (backtracking search, automation engines, unfolding) lives in OCaml under `src/`.

To add a sentence: write the Ltac2 function, bind it with `Ltac2 Notation "My" "tactic" x(lconstr) := ...`, re-export from `theories/Tactics.v`, and add test coverage to `tests/tactics/`. Build with `dune build`.

---

## 8. Exercise notebooks (`.mv`)

Waterproof notebooks are Markdown files with fenced Coq blocks and custom tags:

- ` ```coq ... ``` ` — Checked, read-only code.
- `<input-area> ```coq ... ``` </input-area>` — Editable student solution box.
- `<hint title="💡 Hint (click to open/close)"> ... </hint>` — Collapsible section for hints or hidden preambles.

### Template

````markdown
# Homework 3: Suprema

<hint title="📦 Imports (click to open/close)">
```coq
Require Import Waterproof.Waterproof.
Require Import Waterproof.Notations.Common.
Require Import Waterproof.Notations.Reals.
Require Import Waterproof.Notations.Sets.
Require Import Waterproof.Chains.
Require Import Waterproof.Tactics.
Require Import Waterproof.Automation.
Waterproof Enable Automation RealsAndIntegers.
Open Scope R_scope. Open Scope subset_scope.
Set Default Goal Selector "!".
Set Bullet Behavior "Waterproof Relaxed Subproofs".
```
</hint>

## Exercise 1
State the problem here.

```coq
Lemma exercise_1 : ∀ x ∈ ℝ, x + 3 = 3 + x.
Proof.
```
<input-area>
```coq

```
</input-area>
```coq
Qed.
```
````

### Course design tips

Pair every exercise with an example. Give a completed `Lemma example_...`, then an identically structured `Lemma exercise_...` with an empty `<input-area>`.

Keep `Lemma ... Proof.` and `Qed.` outside the input area so students can't alter what they are proving, and wrap imports and `Waterproof Register Expand` commands in collapsible `<hint>` blocks to keep the administrative noise out of the way.

Introduce sentences in a fixed order across the course: `We conclude that` → `We need to show that` → `Take` → `Choose`/`Indeed` → `Assume` → inequality chains → `It suffices` → `It holds` → `Use` → `Obtain` → contradiction → `Either` → `∧`/`⇔` → induction → `Expand`. Students who meet `Obtain` before `Take` tend to flounder.

Remind students that Ctrl+Space (Cmd+Space) lists the available sentence templates.

Solve every input area yourself before assigning the notebook. The concatenated file has to compile cleanly with `coqc`.

---

## 9. Quick reference card

```
Take x ∈ ℝ.                     Take n, m : ℕ and b : bool.
Take x : ℝ; such that (P) as (i).
Choose y := (t).                { Indeed, (side condition). }
Assume that (P) as (i).
It holds that (P) as (i).       By (ref) it holds that (P).     Since (Q) it holds that (P).
We claim that (P) as (i).
It suffices to show that (P).   By/Since ... it suffices to show that (P).
We need to show that (P).       To show that (P).
We conclude that (P).           By (ref) we conclude that (P).  It follows that (P).
We conclude that & a < b ≤ c.
Use x := (t) in (i).            Obtain such an x.               Obtain x according to (i).
Because (i) both (P) and (Q).   Because (i) either (P) or (Q).
Either (P) or (Q).   - Case (P). ...   - Case (Q). ...
We show both statements.        We show both (P) and (Q).       We show both directions.
We argue by contradiction.      Contradiction.  (↯)
We use induction on k.          We first show the base case (P). We now show the induction step.
Define u := (t).                Expand the definition of (f).   Expand All.    Help.
```
