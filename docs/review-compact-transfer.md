# Independent review of compact transfer

Reviewed `CompactEmbedding.lean`, `CompactCosets.lean`, `CompactUnbounded.lean`, and
`ConullAssembly.lean` against the revised manuscript's Theorem 1.1 (lines 48–66)
and the published `Def_ModNullCore20261109` / `Def_ModNullCompact20261109` bundles.
No mathematical or statement mismatch was found in these four modules.

- **Quantifiers and fixed witnesses.** `compactGroup`, its Haar probability, and
  `compactSubgroup (tensorSubspace T)` are fixed independently of the target.
  `compact_family_unbounded` uses this concrete family. In the conull argument,
  the AE-power target depends on `F`, then one `T` is chosen against that target;
  this same `T` works for every Borel conull `C`. No invariance of `C` or Borel
  choice of a family of reductions is assumed. Empty target spaces are handled
  separately using nonemptiness of a set of probability one.
- **Actual compact group and measure.** The carrier is a countable product of
  circles, with its genuine product group/topology and Borel sigma algebra.
  Haar measure is Mathlib's Haar measure normalized on the whole compact group;
  both `IsProbabilityMeasure` and `IsHaarMeasure` are proved by native results.
  Commutativity, compactness, and metrizability are actual instances.
- **Embedding variant.** The code uses `u(i)/(n+1)` modulo one instead of the
  manuscript's `u(i)/n!`. This is a valid replacement: it is additive and
  continuous, and vanishing at every positive denominator forces the real
  coordinate to vanish. Injectivity is proved directly. The transfer uses only
  continuity and injectivity, and does not assume a globally continuous inverse.
- **Cosets, Borel reductions, and complexity.** The reduction proves precisely
  `x⁻¹*y ∈ H` with the published orientation. Its map is Borel for the actual
  source and target measurable spaces. Compact images of the two K-sigma sets
  give two genuine F-sigma sets; injectivity justifies preserving their
  difference. The graph is the continuous preimage under `(x,y) ↦ x⁻¹*y`.
  `differenceFSigma_isDelta3` proves both published hierarchy clauses.
- **Explicit integration premise.** `compactSubgroup_lowComplexity` has a genuine,
  visible K-sigma-difference premise for the coordinate image of every subgroup.
  It does not assume the desired conclusion under another name. The concrete
  discharge is the tensor module's `image_coordinates_difference_ksigma`, with
  `D = treeOperator T` and `treeOperator_injective T`.

The four-module build passed with Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (3241 jobs). Axiom audits for
`compactGroup_abelian`, `source_reduces_compact`, `compactSubgroup_lowComplexity`,
`compact_family_unbounded`, and `conull_unbounded_of_unbounded` each reported
exactly `propext`, `Classical.choice`, and `Quot.sound`. The reviewed files contain
no `sorry`, added axiom, `unsafe`, or `native_decide`.

The tensor interface was also inspected independently. Its bounded coordinate
balls recover actual l1 matrices; finite row approximations converge in l1;
the universal rank-chart test is a genuine G-delta set; and the compact
finite-rank envelope minus the K-sigma union of failed tests is exactly the
tensor image. Its final build passed (3117 jobs); an independent audit of
`image_coordinates_difference_ksigma` reported exactly the same three standard
axioms. Its sole mathematical hypothesis is injectivity of the given bounded
linear operator, which `treeOperator_injective` supplies for every tree index.
The algebraic characterization in `WeakTensorCharts.lean` also built and passed
the same audit.
