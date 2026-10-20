# L17: a blank-orbit tail excursion and a nesting induction

The conditional blank-orbit continuation now contains **three two-layer
excursions**. Each collapses back to one layer after three more rewrites. The
registered search stops after **673,467 contextual rewrites**, including literal
word normalizations, from the supplied `C(6575648756,1)` boundary. It does not
settle eventual stack growth, halting, or non-halting.

Separately, a new contextual nesting identity has a short induction with fixed
read windows. Let `U=(01)^8 1` and `T=(01)^7 1^3`. For `a>=7`, `n>=0`:

```
Ccal(a; 1 U^n 00 v) -> Ccal(0; 1^(2a-12) T^(n+1) v)
time 4a+74n+50, shift -2, arbitrary finite v.
```

`NESTING.md` gives the complete derivation for Claude. This is not a new Lean
theorem. The input and output families differ, so it does not prove unbounded
depth along one fixed trajectory. The powers themselves also have compact
one-counter encodings; depth is not a proof of an encoding lower bound.

## Blank-orbit observations

Indices count rewrites from the incoming boundary, with index zero the source.
Zero-time tape equalities count as rewrites. They are not raw TM steps.

| F1100 source checkpoint | Canonical source | Two-layer target checkpoint | Middle ones | Back to one layer |
| ---: | --- | ---: | ---: | ---: |
| 226,797 | `C(A,1) . (01)^76 1` | 226,798 | 139 | 226,801 |
| 344,264 | `C(A,1) . (01)^57 1` | 344,265 | 101 | 344,268 |
| 366,708 | `C(A,1) . (01)^59 1` | 366,709 | 105 | 366,712 |

Here A is a different exact integer in each row. Its bit length is respectively
107,633; 163,423; and 174,105. Every A is divisible by three. The F1100 endpoint
is `Ccal(0;1^(2A-12)(01)^7 1^m T)`. Divisibility makes the leading countdown end
with zero remaining ones, allowing the first `(01)^7` block to merge into the
pair counter. That explains these three observed collapses; it is not asserted
for every future F1100 event.

The first target has a full relative time/head certificate in
`replay-compact.json`; its source A has 32,401 decimal digits and the cumulative
transition count there has 64,801 decimal digits. Those are **arithmetic
evaluations of proposed rules, not raw simulations**. Later state-only phases
intentionally omit cumulative transition and physical-head totals. All complete
states are represented by exact integer word counts, mostly in hexadecimal.

The final checked section is `Ccal(0;1^N(01)^13)`, where N has 319,733 bits; its
exact value is in `deeper.json`. The stop is the registered 180-second wall
budget. A different computer can reach a different wall-budget stop.
`verify_symbolic.py` instead replays the exact recorded endpoint deterministically.

## Checks and their limits

- 268 new raw endpoints: 204 C-section nesting cases and 64 A-section cases.
- 80 read-window checks with random tape on both sides: K7, K27, K41, K60, and
  six finite A-section instances.
- 64 endpoint requests each replayed with fresh `-O0` and UBSan builds, agreeing
  exactly with `-O2`.
- 12/12 ACAF mutants caught: eight endpoint/time/head/context defects against
  literal C++ results; four guard/type-rejection defects against invalid inputs.
- 64 huge-counter arithmetic comparisons and 12 unit test methods pass.

The C++ comparator, exact periodic-word critic, and actor are separate code
paths by the same author. This campaign is not independent-authorship replication.
The consumed claims and raw requests/responses have recorded hashes. The new
`verify_results.py` checks the delivered raw evidence without importing the actor.
The separate `verify_symbolic.py` uses only declarative claim targets and periodic
cursors, then checks the recorded checkpoints and every retained choice code.

The initial harness error (text IDs instead of integer IDs) and the unexercised
short-rule bridge parameter error found in review are retained in
`failure-history.json`. The first error executed zero machine transitions. No
recorded orbit used the affected short-rule bridge.

Protocols were written locally before their respective validation phases, after
disclosed exploration. They are not externally authenticated preregistrations.
The installed ACAF skill's referenced graph wrapper/discipline files were absent;
the application here is its manual actor/critic/ambiguity/fuzzer workflow for TM
rules. No graph-specific theorem or tool result is claimed.

## Reproduction

Place this directory beside the unchanged `l17-stacked-section` and
`l17-hardening` directories from the combined archive. Python 3.12 and a C++17
compiler are sufficient. Use a fresh extracted copy for commands that regenerate
outputs.

```
python3 analysis/l17-stack/verify_results.py
python3 -m unittest discover -s analysis/l17-stack -p 'test_*.py' -v
python3 analysis/l17-stack/verify_symbolic.py
python3 analysis/l17-stack/validate_nesting.py
```

The symbolic verifier takes minutes. It omits time totals and writes only its
own new report. The raw nesting campaign builds three fresh binaries and writes
only inside this directory. Mutants operate in memory. No script calls the
network, edits Lean, or changes the older contribution directories.

`extend.py`, `discover.py`, `replay.py`, and `deeper.py` reproduce discovery
phases. The first two reproduce the first 100,000 full rewrites and the first
new F1100 boundary; `replay.py` regenerates the full-time replay through 230,000.
The verbose replay creates a large temporary JSON file. That verbose history
and its local compressed duplicate are omitted from this handoff; its complete
event-stream hash, compact witnesses, and sparse checkpoints are retained.
The `full_event_history` reference inside the compact report documents the
omitted intermediate and its hash; it is not a missing input to either verifier.

## Scope and provenance

The user reports that Claude independently replayed the prior hardening package,
checked 18 minimized rule witnesses with another simulator, and included it in
PR #6 at commit `8ff10a9`. This is externally reported confirmation; no fresh
private-repository or CI access occurred here. The incoming Lean boundary is
also supplied context. The new nesting lemma and F1100 family are not newly
formalized here. Previously supplied Lean results remain independent of the
Python/C++ cross-checks.

The archive preserves all 135 earlier payloads byte for byte and adds only this
directory. Its earlier census and status snapshots are not refreshed by this
work. No PR was opened, merged, or monitored, and no message was sent to Claude.
