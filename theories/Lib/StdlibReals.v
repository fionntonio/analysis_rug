(** * RUG.Analysis.Lib.StdlibReals — the Stdlib real-number library without [Rtopology].

  This module exports everything that [From Stdlib Require Import Reals.Reals]
  provides, except the contents of [Stdlib.Reals.Rtopology] (and of
  [Ranalysis_reg], which only re-exports it and defines the [reg] tactic).

  This module exists as a "hack" to avoid an issue preventing us to use [f]:
  [Rtopology] defines a record [family] with a field named [f]. When it is
  imported, a bare [f] in a Waterproof sentence (e.g. [We claim that … f x …])
  resolves to that instead of a local function [f], so lemmas could not
  use [f] as the name of a function. [Rtopology] is still loaded, and its
  results remain available by qualified name, e.g. [Rtopology.compact]. *)

From Stdlib Require Export Rbase Rfunctions Zfloor SeqSeries Rtrigo.
From Stdlib Require Export Ranalysis1 Ranalysis2 Ranalysis3 MVT PSeries_reg
  Exp_prop Rtrigo_reg Rsqrt_def R_sqrt Rtrigo_calc Rgeom Sqrt_reg Ranalysis4
  Rpower Integration.
