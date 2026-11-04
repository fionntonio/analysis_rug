# Waterproof homework notebooks

Waterproof versions of the four peer-review homework assignments of
*Analysis (WBMA012-05)*. The statements are the ones in
[`md/Analysis-course-info.md`](../md/Analysis-course-info.md#homework-assignments).

| Notebook | Assignment | Lecture | Course library |
|---|---|---|---|
| [`hw1_infimum.mv`](hw1_infimum.mv) | infimum of a set of quotients | 1 (§1.2–1.4) | [`theories/Reals.v`](../theories/Reals.v) |
| [`hw2_series_ratio.mv`](hw2_series_ratio.mv) | comparison of series by a limit of ratios | 4 (§2.6–2.7) | [`theories/Series.v`](../theories/Series.v) |
| [`hw3_limit_point.mv`](hw3_limit_point.mv) | bounded infinite sets have a limit point | 5–6 (§3.2–3.3) | [`theories/Topology.v`](../theories/Topology.v), [`theories/Compactness.v`](../theories/Compactness.v) |
| [`hw4_uniform_convergence.mv`](hw4_uniform_convergence.mv) | uniform convergence of `n/(nx+1)` | 10 (§6.2) | [`theories/FunctionSequences.v`](../theories/FunctionSequences.v) |

Model solutions are in [`solutions/`](solutions). Each assignment is cut into
small steps, with a collapsible hint per step; only the parts inside
`<input-area>` are meant to be edited.

## Checking a notebook

All four homeworks use the course library (`RUG.Analysis.*`), so build it once:

```sh
dune build
```

In VS Code, open the `.mv` file with the Waterproof extension. From the command
line:

```sh
exercises/check_mv.sh exercises/hw2_series_ratio.mv
```

The script calls `fcc` on the notebook and prints the errors it finds (an
unfinished exercise counts as an error: `Attempt to save an incomplete proof`).
It passes the load path of the *built* library explicitly, because the two `-R`
entries of `_CoqProject` make `fcc` look for `.vo` files next to the sources.
