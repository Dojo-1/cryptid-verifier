# L17: collapse, a ranked excursion family, and a two-million-rewrite search

Read `CLAUDE-BRIEF.md` first, then `COLLAPSE.md` for the proof details. The main
new result is a terminating subsystem for two-layer reset states with a middle
run of 3z ones. The rank **k+8z** decreases by exactly one on every non-return
decision. This proves a guarded return to the four-counter S section without
requiring assumptions about front-counter digit randomness.

The immediate post-push collapse needs only E, Q and a tape equality. It applies
when Claude's F1100 output parameter is u congruent to 2 modulo 3. A broader
sufficient condition is d congruent to 1 modulo 3, making its middle ones count
divisible by three. No new fixed kernel is required for those proofs.

## What the blank continuation does

Counts are contextual GPT rewrites from the supplied C(6575648756,1) boundary,
including tape-equality normalizations. They are not Claude move counts or raw
TM steps. All continuations beyond the supplied Lean chain remain conditional
arithmetic here; no new enormous Lean certificate is produced.

| Push source | New two-layer checkpoint | Tail width c | Post-push rewrites to one layer | Return checkpoint |
| ---: | ---: | ---: | ---: | ---: |
| 226,797 | 226,798 | 76 | 3 | 226,801 |
| 344,264 | 344,265 | 57 | 3 | 344,268 |
| 366,708 | 366,709 | 59 | 3 | 366,712 |
| 1,079,641 | 1,079,642 | 74 | 3 | 1,079,645 |
| 1,363,314 | 1,363,315 | 72 | 3 | 1,363,318 |
| 1,407,520 | 1,407,521 | 71 | 17 | 1,407,538 |
| 1,803,910 | 1,803,911 | 68 | 6 | 1,803,917 |

The first exception to three-rewrite collapse has middle count 129 and follows
the residue decisions 1,2,2,1,0; the next has middle count 123 and decisions 1,0.
Both fit the ranked subsystem. Exact large integers are in `fast.json` and
`guard.json`. Closed S-to-S count formulas for both itineraries are derived and
checked against those reached endpoints.

The search stops at the registered **2,000,000 global rewrite cap**. No third
pure-tail layer, reached 1101 prefix, or unproved low guard was found. A global
bound is still open. The sufficient push predicate a%3=0 or c%3=2 is not
preserved on arbitrary S states; a small raw-checked negative control is in the
brief. This does not show that no more restrictive invariant exists.

## Checks and preserved failure

- 183 literal full endpoints and read bounds pass across both raw queues.
- 1,735,242 fresh defined raw transitions, within the shared 20-million cap;
  every request is within 200,000 transitions.
- Four fixed ranking cases exceed that per-probe horizon and are explicitly
  arithmetic-only; they were not silently extended or raw simulated.
- Six in-memory mutants are caught. Ten excluded immediate-branch guard
  instances are rejected before raw dispatch.
- 24 finite/huge checks of the long five-decision family and eight huge checks
  of the shorter return pass. The long full return is not raw simulated: even
  its smallest case exceeds five billion steps.
- Twelve test methods and 500 scalar reset-map calibration cases pass.
- An actor-free verifier replays every new state transition, including scalar
  macro accounting, through the two-million checkpoint.

The first proposed full F111/Z footprint omitted the initial A-sweep read at
the cell -2. Raw case 40 caught the too-narrow bound: actual [-11,19], proposed
[-10,19]. Endpoint, head and time matched. `critic-before-window-fix.py`, the
failed log, and `failure-history.json` preserve this. Corrected bounds were
checked against the existing hash-bound raw records; this is not described as
a second physical comparator run.

The separate declarative claims are actually consumed by the literal validator.
The new raw-record verifier has no actor dependency. The search verifier uses
the old primitive specification and a new separately transcribed reset map;
it imports neither orbit generator nor word class. These are separate code
paths by the same author, not independent-authorship reproduction.

## Search and reproduction

The original word-level 240-second phase reached 1,020,542 rewrites without a
new push. A scalar reset-section map then removes that representation overhead:
`B(N,k,s)=Ccal(0;1^N(01)^k1^s)`, N>=20. Every ordinary return has
`Nnew=10*floor(N/3)+C`, with C listed in `reset-spec.json`; the bound
`Nnew >= (10N-50)/3 > N` keeps the old lower guards valid. The map was calibrated
against the guarded word engine before use. A separate verifier consumes its
declarative specification, checks every branch and primitive-rewrite count, and
matches stored complete checkpoints. Times and physical-head totals are not
accumulated in these large search phases.

Use Python 3.12 and a C++17 compiler. This directory belongs beside the earlier
contributions in the combined archive. Use a fresh extraction for regenerating
outputs; the evidence verifiers read the delivered records.

```
python3 analysis/l17-collapse/verify_raw.py
python3 -m unittest discover -s analysis/l17-collapse -p 'test_*.py' -v
python3 analysis/l17-collapse/verify_search.py
python3 analysis/l17-collapse/validate.py
python3 analysis/l17-collapse/validate_return2.py
```

The independent search verifier takes several minutes; its registered cap is
360 seconds. Discovery generators `search.py`, `fast.py`, and
`fast.py guard-protocol.json guard` are retained with their original budgets.
Their protocols bind the original source-checkpoint hashes. Run individual
discovery phases in separate fresh copies: a wall-budget replay may stop at a
different point, and overwriting its output invalidates the next frozen
protocol's source hash. A new source requires a new protocol. The deterministic
verifier reproduces the recorded continuation without that dependency on wall
timing. These are local records after disclosed derivations and observations,
not external preregistration. No raw failing horizon was increased.

All scripts write only in this directory; none contacts GitHub or edits Lean.
The combined archive preserves all 206 older payloads unchanged. Earlier
candidate statuses and GitHub/CI reports are not refreshed. Claude's L17e proof
and independent first-event reproduction are user-provided reports, not a new
repository review in this environment.

The ACAF skill's installed graph-specific wrapper/reference were absent, as
documented in the earlier contribution; this continues its manual actor,
separate critic, adversarial input and mutation workflow for the counter rules.
