# L17 comparator and ACAF audit

## Verdict

The delivered finite L17 endpoints survive a separately implemented literal
machine comparator: 6,381 source/target cases agree in complete tape support,
state, head, exact defined-transition count and halting status. The declared
local windows survive arbitrary outside contexts. All 20 specified live-code
defects are detected. ACAF also found a genuine zero-repetition bug in the new
critic; it was corrected with the original failure retained. No original L17
formula changed. These are bounded M results by one author with separate code
paths, not new Lean theorems, external independent replication or a complete
stack/halting decision.

## Claim and evidence ledger

| Claim | Before | Artifact | Audit result | After |
| --- | --- | --- | --- | --- |
| Both residue endpoints and contextual formulas match literal TM behavior on the specified cases | M | `rule-comparisons.json`, full raw outputs, exact case queue | 4,333 historical and 2,048 new cases agree | M |
| Fixed windows preserve arbitrary outside tape | H, with derivation | `window-comparisons.json`, `kernel-witnesses.json` | 16 kernels × 12 contexts; exact read traces agree | M |
| The harness detects the selected plausible implementation faults | H | `mutation-plan.json`, `mutation-results.json` | 20/20 detected; 18 minimized in-guard rule witnesses raw-rechecked | M |
| Zero-count chunks can be passed directly to the original new-critic trimmer | H | `attempt-2/critic-failure.json` | False; `(10)^0` was changed into `1` | R |
| Corrected word comparison agrees with the declared finite/infinite-zero semantics | H | `PERIOD-COMPARATOR.md`, ten tests, representation data | Short-word oracle checks and 1,024 representations pass | M |
| Recorded huge orbit edges follow the stated macro formulas | A | `trace-comparisons.json` | Separate parsing verifies 100+2,000 edges and cumulative arithmetic | A, supported by M checks |
| Complete reachable stack closure or non-halting follows | H | No supporting artifact | Not established | H |

`P/A/M/H/S/R` follow the Recursive Research Auditor definitions: P verified
proof; A explicit assumption/conditional bridge; M bounded measurement;
H hypothesis; S semantic language; R retired claim. There is no new P-level
Lean result here.

## Strongest surviving result

All 6,381 literal endpoint comparisons pass. The C++ comparator is a new
sparse-position interpreter and parses the literal six-row machine string;
it uses no Python counter formulas, `Word`, dense interpreter or block
acceleration. Expected endpoints come from a separately consumed declarative
claim file. The exact file digest, raw request digest, binary digest and
complete raw output are bound in the execution records. The exported queue
reconstructs that identical serialized request digest.

In particular, `C(7,1).(01)^8 1 -> C(0,2).T.T`, with `T=(01)^7 1^3`, still
matches at 152 defined transitions and displacement -2. This shows failure
of universal one-tail closure, not blank reachability of that input or
unbounded stack growth.

## Load-bearing obstruction

Finite agreement cannot verify every parameter or establish reachable
closure. The actor still deliberately lacks a complete dispatch for stacked
prefixes such as `(10)^c1101v` and low guards. The incoming blank boundary is
Claude-supplied context, not a Lean artifact inspected in this environment.
The C++ comparator and declarative specification are also unverified software
by the same author. Twenty selected mutants cannot establish complete fault
coverage.

The actual bug found was in the new critic, not in an L17 formula. At ACAF
representation index 129, the pattern `101100` with repetition count zero
exposed that suffix trimming inspected a pattern which represented no cells.
The small witness is `[("10",0)] == []`; the old critic wrongly rejected it.
The fix discards zero-count chunks before examining their last symbol. The
raw rule materializer already omits zero terms; no failed physical endpoint
was observed. The corrected actor/spec and representation checks were rerun.

## Specification -> implementation -> test audit

The frozen input is the previous 59-file ZIP, SHA256
`dcddfd2b5812c189f463af0317ed4a6e23d332c67fc425786ff688b8980d5fdb`.
Every consumed actor file is checked against that snapshot before and after
execution. New work is additive; no frozen formula, Lean file or previous
result is overwritten.

The separate specification is `claims.json`, SHA256
`d0f0339d0ef045b44ab1203f29981f960383d7d045375e506f7114ff87e3f074`.
It contains 19 declared source/target schemas and guards. Its expressions
allow only named integers, constants, addition, subtraction and
multiplication. The comparator actually consumes this file. It is a separate
transcription by the same author from the delivered statements; it is not
described as an independent human transcription or an unseen fresh-agent
specification.

The intended time counts defined transitions. Undefined transitions perform
no write or movement; halting is reported even at an exact zero budget.
Only exterior trailing zeros are implicit. Leading zeros and interior zeros
retain their physical positions. All comparisons use full sorted support,
not just checksums or a selected tape substring.

The actor agrees with 6,372 directly comparable schema instances. Nine Q(q=0)
identity cases have no direct actor macro entry point and are explicitly
not applicable there; the literal comparator checks all nine identities.
They are not counted as actor passes or hidden as failures.

## Direction, type and metric audit

| Observable | Result | Unit and limitation |
| --- | ---: | --- |
| Frozen rule endpoints | 4,333 pass | Probe count, not necessarily distinct inputs |
| New ACAF rule endpoints | 2,048 pass | Guard/context stream under a fixed seed |
| Window locality | 192 pass | 16 kernels × 12 randomized outside contexts |
| Raw interpreter controls | 300 pass | Same saved complete states, independently executed in C++ |
| Analytic controls | 8 pass | Blank entry, undefined transitions, write/erase tables and leading zeros |
| Frame transformations | 192 pass | Translation, reflection and state renaming |
| Compiler parity | 84 matched requests per setting | O2, O0 and UBSan; not all 6,381 cases at all settings |
| Equivalent representations | 1,024 pass | Split periodic chunks, zero repetitions and exterior zeros |
| Huge integer cases | 64 pass | Parameters around powers up to 2^4096; no raw simulation |
| Invalid guard contracts | 28 rejected | Contract checks, not claims that weaker mathematical guards fail |
| Symbolic edges | 2,100 pass | 100 original plus 2,000 extension; overlapping prefixes are counted twice |
| Live-source mutants | 20/20 detected | Only the specified mutation set; one kill is contract-only |
| New unit tests | 10 pass | Critic, mutator, budget preflight, dependency isolation and imports |

These coordinates are not collapsed into a discovery or correctness score.
All raw probes stay at or below 200,000 transitions. Cumulative actual C++
work, including failed harness attempts and repeat executions, is
**49,268,238 defined transitions out of 80,000,000**. Consumed cached traces
and newly executed work are reported separately. No benchmark, speedup,
mixing law, asymptotic tail bound or non-halting inference is made.

## Controls and resource parity

The ACAF Actor is the frozen rule/word/block code. The Critic is the separate
specification and C++ raw machine. The Ambigator varies guard offsets,
alternating-run counts, suffix lengths/densities, physical translation and
chunk decompositions; the Fuzzer executes the fixed queues. This uses the
manual ACAF workflow for TM counters rather than inventing graph/noise data.
The installed skill's referenced graph wrapper and discipline reference are
absent; neither was represented as executed.

Every endpoint comparison receives the same literal source, initial head,
state, machine and raw budget. Frame tests transform both the table and
configuration: reflection swaps L/R and negates coordinates, and state
renaming maps the initial state as well as destinations. A separate negative
control shows that keeping the wrong start state after renaming is not a
rooted equivalence. Another changes one transition; both semantic changes
are rejected. Nine malformed literal requests are rejected, including
duplicate cells, excessive budgets, out-of-domain coordinates, invalid states
and trailing data.

All three compiler settings use the identical comparator source and 84
matched requests. Undefined-behavior sanitization reports no runtime issue
on these controls. No performance parity claim is inferred.

Literal-output caches require matching request, full uncompressed response
and compiled-binary hashes. Actor/spec expectations are recomputed after
corrections. A durable work ledger charges fresh raw batches before later
stages can fail; preflight refuses work above the remaining fixed budget.

## Independent-witness status

The new C++ parser/tape/step implementation, new declarative arithmetic
evaluator and exact word comparator are separate code paths. Their authorship,
machine string and statement provenance remain correlated with the earlier
contribution. They are not a separate model, human reviewer, externally
reproduced result or formal interpreter proof. The literal table, consumed
file identities and generated inputs are delivered for such replication.

## Representation and equivalence attacks

The word comparator uses periodic cursors with a self-contained period lemma
in `PERIOD-COMPARATOR.md`, rather than the actor's implementation. Literal
short-word comparisons test that algorithm, including the zero-count
regression. Splitting/repeating chunks, primitive-pattern changes, appending
only exterior zero tails, and counts around 2^4096 do not change the intended
physical object.

All 16 kernels are replayed with arbitrary nonzero cells on both sides of
their actual read windows. Complete exterior support is preserved and the
entire read-state/position/symbol sequence matches the frozen witness. This
directly tests the locality assumptions needed for context-parametric Lean
lemmas, rather than checking only empty suffixes.

The 20 live mutations include changed target counts, times and head shifts;
lost suffixes; deleted interior zero/one cells; stack-tail corruption; a
relaxed rejection guard; a changed dispatch result; a one-cell prefix-drop
error; and the historical leading-zero encoder bug. Counterexamples are
shrunk with at most 128 calls, without extending any raw horizon. Shrinking
is greedy, not a proof of global minimality. Nineteen detections concern
wrong physical/encoding results; one concerns only a changed guard contract.

## Round-trip coherence

The request was to harden the delivered results while Claude formalizes them.
It became fixed endpoint, context, guard and arithmetic obligations. The
implementations test those exact objects and record their complete outputs.
The returned conclusion remains finite hardening: no new machine, new orbit
extension, hidden invariant or infinite continuation is inferred. The new
abstraction is a test harness over the existing section, not a replacement
for the unresolved mathematical question.

## Corrections and retirements

1. **Critic zero repetitions.** The original critic mishandled zero copies of
   a nonzero pattern ending in zero. Preserve the original source and seed in
   `attempt-2/`; the corrected algorithm has a dedicated regression test.
2. **Mutation harness method lookup.** Its first implementation searched only
   top-level functions and could not locate `Word.drop`. It now searches the
   AST recursively, with a dedicated method-lookup test. The partial run was
   not reported as a completed 20-mutant result.
3. **Empty operational artifacts.** One O0 executable and the first raw-rule
   gzip were observed empty. No cause is inferred. The build now checks the
   executable and binds its hash before use; a second physical raw execution
   retained the complete output. Work from the first run is charged using
   its retained execution metadata rather than treating the empty file as
   zero work. The empty artifact and accounting correction remain in
   `attempt-1/`.

No L17 formula was narrowed or corrected by this campaign. The universal
one-tail closure claim was already refuted in the preceding handoff and
remains retired. Passing these tests does not promote complete stacked
dynamics or non-halting.

## Next bounded experiment

- Object: Claude's formalization of F100/F111/F1100 and the short-tail kernels.
- Prediction: each declared kernel closes under the exact read window, and
  the macro compositions need only the stated guards.
- Primary metric: actual theorem statement plus a successful trusted Lean
  build, with reachability and raw-time claims distinguished.
- Controls: the 21 regression specifications, 16 C++-checked read traces and
  unchanged frozen machine definition.
- Representation attacks: explicit suffix parameters and nonblank outside
  context; zero-count sweep and boundary cases.
- Kill condition: a counterexample, uncovered read outside a claimed window,
  stronger hidden guard or theorem statement weaker than the handoff.
- Stop condition: formalize this fixed lemma set; no new orbit search or
  richer rule family to hide a failed obligation.
- Promotion rule: report only the exact compiled theorem; global non-halting
  still needs a separate reachable-closure argument.

## Final evidence map

**M:** finite raw endpoints, locality tests, contract rejections, mutation
sensitivity, compiler controls and bounded implementation comparisons.
**A:** the supplied incoming boundary and conditional huge-time macro chain.
**H:** universal Lean theorem targets, reachable stacked closure and
unbounded-depth/non-halting claims. **R:** the buggy zero-repetition behavior
and any inference that finite success establishes infinite continuation.
No new P-level result or semantic metaphor is used as evidence.
