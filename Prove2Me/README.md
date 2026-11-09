# Direct proof files

These are the exact Lean source bytes accepted by Prove2Me for the three
published targets. Each file exposes a top-level `theorem solution` and retains
all local modules in its import closure, with no unproved theorem imports.
Its remaining imports are Mathlib modules and published definition bundles
included unchanged in this repository.

Each manifest records the authoritative target, source hashes, parsed import
spans, local compilation time, the successful exact-type comparison, and the
kernel axiom audit. The `solution` path identifies the generator's staging
file; `release_solution` identifies the corresponding delivered copy here.

To regenerate and check the files:

```sh
python3 scripts/prepare_upload.py all --target haar
python3 scripts/prepare_upload.py all --target compact
python3 scripts/prepare_upload.py all --target main
```

`docs/prove2me-acceptance.json` records server verdicts and byte-for-byte source
readback checks. Explanations are in `docs/explanation-*.md`.
