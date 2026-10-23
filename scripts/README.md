# Verification tooling

This directory contains maintained repository tooling, not exploratory research.

| File | Purpose |
|---|---|
| `verify.py` | One command to build and audit all three pinned Lake projects, or select one with `--project`. |
| `audit_trust.py` | Lexical source policy and exact inventoried `#print axioms` coverage. |
| `trust_inventory.json` | Explicit source roots and public theorem names required by each audit. |
| `test_*.py` | Trust-gate mutations, generation checks and verification-runner regressions; run in CI on Linux and Windows. |

Run `python scripts/verify.py` from the repository root, or invoke it by its full
path from another directory. It needs Python 3.10+ and elan's `lake` on PATH. It
selects toolchains through each project's `lean-toolchain`, fetches Mathlib caches,
regenerates and hash-checks the L17 proof chains, copies upstream data into the
expected paths, cleans local build outputs, then builds and audits each project.
Dependency caches are retained. A failed preparation, build or audit stops the run
with a nonzero exit code; each build's combined output remains in its `build.log`.
Select a single project with `--project core`, `--project mathlib` or `--project link`.

`make verify` is an optional alias. `make test-tooling` or
`python -m unittest discover -s scripts -p 'test_*.py' -v` runs the tooling tests.
These tests include simulated Lake processes for failure handling; the three real
Lean builds are separate CI jobs and remain necessary.

The audit is a conservative lexical/log policy, not a hostile-metaprogram sandbox.
See the root README for its coverage and trust boundary.

Historical one-off programs have moved, unchanged, to
[`analysis/experiments/`](../analysis/experiments/README.md). Maintained finite
numerical evidence and literal-machine regressions live under `analysis/` and are
run separately in CI; their test commands are in `.github/workflows/lake-build.yml`.
