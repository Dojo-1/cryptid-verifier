# Mixed-return audit

## Verdict

The specific mixed width2 boundary now has a uniform contextual return, with
exact time, head displacement and unread suffix. Thirteen guarded returns
also cover final widths2–5 on a four-run left tape with sufficient ones to
the right. Nine framed transfers explain their A/B/C/D phases. General
mixed-stack return is still open: longer stacks and buffers of only3–5 ones
need further branches. No new Lean proof, blank reachability or nonhalting
decision is claimed.

## Claim and evidence ledger

| Claim | Supporting artifact | Status/boundary |
|---|---|---|
|Named mixed return from original C|C2B/B_to_D/D_pair1/E_p composition and complete word equalities|Conditional mathematical derivation,ready for Lean|
|Six new short paths|Literal read triples in kernels.json|Finite checks plus deterministic framing argument|
|Nine variable transfers|Fixed paths and C/D/A/B sweep inductions|Conditional mathematical derivations|
|Thirteen four-run returns|Full composition table and all-parameter words|Conditional mathematical derivations,explicit sufficient guards|
|846 main endpoints agree|Raw C++ and separate Python paths,840 full traces|M: bounded checks|
|Lower named guard p≥4,c≥1|Same proof needs only K22's four pairs;16 extra corner replays|Conditional derivation and supplementary M checks|
|All arbitrary mixed stacks return|Not shown; next B-mode entry saved|H: open|
|Generic returns settle the blank run|No reachability chain is provided|R: unsupported interpretation|

## Strongest surviving result

For a≥5,c≥1 and arbitrary v,

    Ccal(a;(10)^c1101 (01·101·01·101)00v)
      → Ccal(0;1^(2a−8)(01)^(c+12)1^2v)

in4a+6c+152 defined transitions, shift−2, without reading v. The previous
166-step A witness is the specialization p=6,c=7 before the1101 entry.
This is supported by the fixed-path composition, not by fitting166.

## Load-bearing obstruction

C2B and C5B move right to B4. Their next read is an arbitrary suffix unless
enough right ones are supplied. The13-row table does not justify inventing
those ones. The next-boundary checkpoint has only three, reaches B4 at38
steps, and has not yet read its context. Moreover a full return can produce
only two leading ones at the minimal bottom counter. Neither the buffer
premise nor the source shape is a global invariant of an orbit.

## Specification–implementation–test audit

The source C head is on the last0 of a left10 run, not at a blank-left
section. Framed transfers may leave the head outside their written interval;
the outside tape is preserved and may be nonblank. Full returns use an
explicitly blank exterior and end at the first cell of the bottom run. The
two endpoint types stay distinct in declarations, code and prose.

The critic consumes the declarations and compares the entire literal state:
all written ones, state, head, clock and halt flag. Full traces are compared
for840 main cases and all16 supplementary cases. The separate Python table
does not use macro rules. Large-number unit checks verify exact arithmetic
and suffix positions; they are not huge literal simulations.

## Controls, representation and resource parity

The main846 checks contain512 returns,150 framed transfers,144 kernel
context cases and40 named compositions. The16 lower-guard named checks are
additional. Eighteen templates each use8 randomized contexts on both sides.
Forty-two matched translated inputs agree in O2,O0 andUBSan. These are the
same compiler, g++14.2.0, not independent authorship or42 new discoveries.

The cumulative C++ ledger records185,089 fresh defined transitions, below
20 million. Maximum main run length is1,188, below200,000. The exploratory
unknown-read probe has a500-step cap; its local exits are not promoted to
global sections. Initial formula probes passed before the larger campaign;
no failed formula or endpoint was discarded. The common full-return table
uses p≥6,c≥7; the named composition has the separately justified weaker
p≥4,c≥1 guard. Its supplementary guard-corner dataset is explicitly labeled.

All16 tests and20 planted in-memory mistakes pass. The negative controls
cover clocks, modes, head shifts, required zero gaps, right-prefix consumption,
output widths, incorrect fixed166 extrapolation and a weakened left window.
Only exterior zeros may be omitted. The undefined transition has zero cost.
There is no clipped score, statistical effect-size estimate or speed claim.

## Independent-witness status

The frozen C++ machine and frozen Python OPS table are separate code paths;
the result critic consumes declarations rather than the return actor. The
derivation, scripts and new tests still share an author. This is manual ACAF
discipline and same-author reference checking, not an external reproduction,
separate solver service or a passing Lean build. No messages were sent to
Claude or any third party.

## Round-trip coherence and scope decisions

The original task was the mixed width2 boundary. It becomes a named uniform
lemma and13 guarded families, while the next missing buffer branch is kept
explicit. Quantifiers were narrowed to the actual four-run shape and stated
right prefixes; a finite table was not relabeled as a global mixed calculus.
The prior packages are untouched. No current repository/CI status was inferred
from their old reports. The local transfer count is not a new affine rank
for the earlier internal D/G relation.

## Next bounded experiment

- Object: width2's B exit after only three original right ones, then actual
  next prefixes0,111,1100,1101 on the remaining context.
- Prediction: existing B-starter and framed left-transfer rows may compose
  into additional sufficient guards.
- Metric: complete tape/state/head/time/read-window equality.
- Controls: frozen C++/Python paths, arbitrary contexts and translations.
- Kill: any context/window/endpoint mismatch blocks the candidate.
- Stop: next unsupported phase or the next prospective resource cap; do not
  assert blank reachability or infinite continuation.
- Promotion: finite framed proof and induction first, then an actual Lean
  theorem/build. No new geometric metaphor is needed to represent this gap.

## Evidence map

A: explicit conditional mathematical compositions against frozen sweep
semantics. M: bounded raw checks,compiler controls,unit/mutation tests.
H: unrestricted mixed return and blank-orbit properties. R: generic return
implies a halting decision. P: no new formal Lean artifact in this package.
