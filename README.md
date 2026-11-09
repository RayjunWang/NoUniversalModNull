# No Borel upper bound modulo null sets

Lean formalization of Theorem 1.1 of *No Borel upper bound for the
Δ⁰₃ equivalence relations modulo null sets*.

The main proof and both supporting proofs are **ACCEPTED** on Prove2Me, and
their theorem records are **Proved**. Server source readbacks match the locally
compiled bytes; see `docs/prove2me-acceptance.json`. The public OpenProblem
proposal is separately **In review**.

The main declaration is `ModNullUniversality.theorem1_1` in
[`Solutions/Main.lean`](Solutions/Main.lean). One compact metrizable abelian
group, its normalized Haar probability, and its entire tree-indexed subgroup
family are fixed before the target equivalence relation. The selected tree is
fixed before every Borel conull set. Both the subgroups and their coset graphs
are Δ⁰₃; the graphs are differences of two Fσ sets.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
python3 scripts/audit.py
```

The project pins Lean `v4.30.0` and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, the published targets' supported
Prove2Me environment. The axiom audit permits only `propext`, `Classical.choice`,
and `Quot.sound`. GitHub Actions builds the proofs and checks the exact types
and axioms of the direct upload bundles.

## Contents

- `Definitions/`: unchanged published definitions and previously published foundations.
- `NoBorelUpperBound/`: proved foundations reused from the earlier Fσ project.
- `ModNullProof/`: tensor rank, compact coordinate complexity, compactification,
  ordinary unboundedness, measurable AE coding, and Haar amplification.
- `Solutions/`: the main theorem and its two proved supporting results.
- `docs/ModNullUniversality.tex`: the exact revised manuscript supplied by the author.
- `docs/proof-outline.md`: correspondence between the mathematics and Lean modules.
- `Prove2Me/`: exact direct-proof upload files and local verification manifests.
- `docs/prove2me/`: submission receipts, verdicts, and published-target readbacks.
- `scripts/`: repeatable source, type, axiom, upload preparation, and packaging checks.

The compactification uses positive-integer denominators rather than the paper's
factorials. Its continuity and injectivity are proved in Lean. The AE-power
target is a Borel relation on Baire codes with proved measurable family coding;
the proof does not require a separate formalization of the topology of L⁰.

The mission's positive Fσ universality benchmarks are separate statements and
are not dependencies of Theorem 1.1.

[Public Prove2Me proposal](https://prove2.me/my-missions/64fe8c53-821d-476f-adfe-19f21c5d18f6).
The main theorem ID is `1849a16a-9dde-4a75-b04d-f08aac7bfab3`.

Code is licensed under Apache 2.0; see `LICENSE`. The author's manuscript is
included as supplied; see `NOTICE.md`.
