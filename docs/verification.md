# Verification

The complete local build passed with 3,253 jobs using Lean 4.30.0 and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. This is the environment attached to
all three published Prove2Me targets. The shared Mathlib checkout's HEAD and
clean source status were checked directly.

`python scripts/audit.py` passed the source-integrity scan, unchanged-definition
checks, the exact main statement example, and kernel axiom audits. The main
theorem, both supporting theorems, the coordinate-complexity theorem, the fixed
family's complexity and unboundedness theorems, and measurable family coding
each depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Each direct upload retains the complete local module bodies in dependency order.
Lean's parser determines import-command byte spans and its frontend determines
module scope depth. No declarations or proofs are cut out. The exact generated
bytes are compiled locally. A second Lean check compares `solution`'s elaborated
type with the authoritative published statement using `Lean.Meta.isDefEq`.
Its axiom report is checked before submission. Per-file manifests record hashes,
all retained modules, import ranges, compile times, and type/axiom results.

The source scan excludes the parser utility `extract_module_info.lean`: that
standalone metaprogram uses Lean's unsafe frontend API solely to report parsed
source metadata. It is never imported by the mathematical proof. All proof
modules are checked for placeholders, extra axioms, unsafe declarations,
unchecked native evaluation, and kernel-check bypasses.

The revised TeX is preserved byte-for-byte. Its SHA-256 is
`d85d66e9e3d917008c2e8163d48c81230ed3be632fae431c405f185f0a0fff22`.
The source manifest records hashes for every delivered file. The archive
contains source and public evidence, with no build cache, dependency checkout,
credentials, or local account data.

All three direct proofs received **ACCEPTED** server verdicts, and all three
theorem records are **Proved**. The main submission is
`ec28315c-28dd-44e1-a3ed-c609e0b44179`. All accepted source readbacks match the
locally compiled files byte-for-byte. These records are archived in
`prove2me-acceptance.json` and `prove2me/`. The public mission proposal remains
**In review**, independently of proof verification. The GitHub workflow is provided for
the uploaded repository; no remote GitHub Actions run is claimed here.
