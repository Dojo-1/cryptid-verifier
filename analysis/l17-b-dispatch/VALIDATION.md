# Validation on 2026-11-17

The final clean command `python3 scripts/verify.py --project link` completed
successfully on Lean4.35.0-rc4, against upstream Cryptids commit
`a0c1f56af53a76e985a656032b48015f7e48921b`. It regenerated the orbit inputs,
cleaned local proof builds, compiled the complete link project, and passed
the source policy and explicit axiom inventory. All80 inventoried link
theorems were covered; only the three permitted standard axioms occurred.
`lean-validation.json` records the source/log hashes and actual command
result. `lean-kernel-axioms.log` contains the seven new printed records.

Formal scope: six exact finite `ReachesIn` paths with clocks38,62,75,95,65,14,
and the all-parameter literal identity P_m00=0(10)^m0. Outside contexts are
arbitrary. The complete11-row B/16-row composed return table is a mathematical
derivation with bounded checks, not yet a Lean theorem. Read windows are
recorded and checked separately; the Lean statements specify exact endpoints
and clocks rather than a read-set predicate.

| Check | Result |
|---|---:|
|Repository unit methods, including the final16 new methods|196 passed|
|Raw-machine transcription smoke check|Passed|
|Final dispatcher endpoints in C++ and Python|924/924|
|Full read traces, for requests of at most1000 steps|911/911|
|Read extrema, including the13 larger requests|924/924|
|Arbitrary two-sided-context kernel instances, included above|96/96|
|Translated controls per compiler mode: O2,O0,UBSan|33/33 in each|
|Planted in-memory faults|24/24 detected|
|Unchanged earlier A-stream and mixed-return manifests|57/57 and62/62|

The initial672-case campaign is retained separately; the924 total is the
final campaign, not the sum of both. The final campaign and controls execute
238773 C++ transitions. Across both successful campaigns the measured total
is399382; with the conservative152956 charge for the failed all-trace attempt,
the ledger charges552338 against its20-million cap. Cached outputs are not
counted as new execution. `raw-budget.jsonl` preserves each charge.

The new tests include the108-step saved frontier, the166-step normalized
continuation, gap rotation, finite-tape prefix classification, guards,
huge exact arithmetic and arbitrary outside bits. `suite-results.json`
records the full suite counts; unchanged suites ran before the two added
normalization methods, and the final16 dispatcher methods were rerun.

The first Lean attempt hit a recursion limit only on the95-step path;
raising it locally to4096 resolved it, and the final clean build passed.
Review also corrected the initial claim that the A exit lay outside the
pure10-run scanner grammar. Its five-run normalization and00 continuation
are included. The initial trace transport and finite-exterior test fixes
are recorded in `AUDIT.md`. No mathematical row was silently widened.

Core and Mathlib subproject sources were unchanged; they were not separately
rebuilt locally on their4.24 toolchain. The existing CI still builds all
three projects. The updated evidence job also verifies and replays the
A-stream, mixed-return and dispatcher packages.

General five-run return, blank reachability of these generic sources,
blank-orbit stack boundedness and halting/nonhalting remain open.
