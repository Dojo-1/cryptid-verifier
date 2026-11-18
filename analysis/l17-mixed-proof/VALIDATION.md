# Validation of the mixed-boundary proof

Base commit39830809a1b9afa0337955eb5890ffeec0c235af (PR #30).
The work began on affc1ff (PR #29). Main advanced during validation; the
new concrete166-step module L17ac was retained byte-for-byte and the
parameterized proof moved to L17MixedBoundary. A fresh combined clean
build and trust audit followed the integration.

The clean repository command `python3 scripts/verify.py --project link`
completed successfully using Lean4.35.0-rc4, commit
c29b6dda4f7c20e3eeaa717c4e565663c5cfa364. It regenerated the existing
1,251-step orbit chain, cleaned local build products, and completed9073
Lake jobs. The final trust gate scanned52 local Lean files and covered150
inventoried public theorems. All thirteen new axiom outputs contain only
`propext`, `Classical.choice` and `Quot.sound`; see `lean-axioms.log`.

Core and mathlib-only sources were unchanged. Their separate4.24 toolchain
builds were not rerun locally; the PR workflow runs all three projects.
The link build compiles the applicable core dependency under its pinned
4.35 toolchain. Older modules retain existing linter warnings; L17MixedBoundary builds
without warnings after the presentation fixes below.

Fresh comparator run, seed18112030:960 complete endpoints,950 full matching
traces, and identical read extrema for all cases. The ten cases over1000
steps use endpoint/extrema checks because of the comparator's fixed trace
cap. The largest case takes1360 steps. The main campaign includes176
original-C returns,176 A returns,176 C2 returns and72 cases for each of six
framed helper families. All12 planted clock,head,mode and output faults are
caught. These are bounded same-author checks, not an additional proof.

Twenty-four translated complete inputs agree in each of O2,O0 and UBSan,
compiled with g++14.2.0. All three modes have identical response hashes and
empty stderr. The main C++ run executes147030 defined transitions and
controls execute5589 per mode. The rejected initial batch is conservatively
charged147030 additional transitions, for310827 charged in total under the
registered2,000,000 cap. `raw-budget.jsonl` records the successful charges;
`rejected-attempt.json` separately records the conservative failed-batch charge.
Raw response hashes and counts were also checked against all four gzip files.

Twelve new unit methods,31 tooling/trust-gate methods,16 archived mixed-return
methods and15 archived A-stream methods pass (74 selected methods). The PR
evidence workflow additionally verifies this package's manifest and performs
a fresh comparator run with `--no-save`; it does not just trust archived results.

Setup and implementation corrections are retained here:

- The first local build used the wrong working directory to copy upstream
  machine data. That setup failed before elaborating the new module. Repeating
  the documented copy from the repository root resolved it.
- Initial proof terms needed rewrite-direction and directed-head presentation
  fixes. No mathematical source, endpoint, guard or clock was changed. The
  final clean build rechecked every local theorem and its axiom outputs.
- The initial C++ batch requested traces above the fixed1000-step limit and
  was rejected. Its entire requested transition total is charged, including
  requests it could not execute. The successful replay keeps full endpoints
  and read extrema for the larger cases.
- A Python-only preflight caught a one-cell Dpair1 encoder origin error.
  The left separator belongs at−2(v+1)−4. The encoder and a regression test
  were corrected before accepting C++ evidence; the guarded formula and
  clock were unchanged.

The full mixed calculus, the other twelve four-run rows, the five-run family,
blank-orbit membership of these generic sources and a stack bound are not
established by this contribution. The certified blank endpoint is unchanged.
