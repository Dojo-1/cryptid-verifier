# E60 — six-step moving-window recurrence (hypothesis, **not** Lean proof)

This artifact freezes a reproducible, falsifiable full-tape hypothesis for the
**26 still-unmatched** cases in the E58/E59 finite three-block census.
It changes **no** certified `ReachesIn` statement. The existing
`mixed_zero_head_widewide_exact` remains the last proved guard extension.

## Typed source and exact conjecture

Set `K=(10)^7`. The source is the existing `widthFourCutSource u v`
with right suffix `G_f(m) R`. The control state, head, both tape halves,
raw transition count and read extrema are required observables; `R` is
an arbitrary right exterior.

For `m >= 1` and `u,v >= 0` conjecture these **exact first blank-left C**
returns (the first-return property is stronger than `ReachesIn`):

```text
G1(m) = 1 K 11 01 (10)^m 111
G3(m) = 111 K 11 01 (10)^m 111

T1(m,u,v) = 214 + 6m + 2u + 4v
T3(m,u,v) = 268 + 6m + 2u + 2v

F1(m,u,v,R) = 1^(2u+6) (01)^(v+8) 010100 (10)^(16+m) R
F3(m,u,v,R) = 1^(2u+1) K 1^(2v+4) (01)^(21+m) 0 R

exit head shift = -(34+2u+2v) (both families)
read min relative to entry head = -(33+2u+2v)
read max G1 = 25 + 2m
read max G3 = 27 + 2m
```

In the candidate terminal tape, increasing `m` inserts one spatial
`10` immediately before the same untouched exterior `R`.
The time increment is **6**, but this is not a coordinate-free scalar:
the read window expands two cells. The different `4v` vs `2v` slopes
must not be identified without explicit frame transport.

The two formulas handle 20 of the 26 still-unmatched **bounded parses**
(`bridge` gives `m=5`; `shortTwo j` gives `m=8+j` in the parsed
`[first, pair, wide(1|2)]` families). Six other parse cases are not
claimed to follow these expressions.

## Counterexample / boundary

The hypothesis is **m>=1**, not m>=0:

```text
m=0, u=v=0:
first G1 return = 222 steps; naive affine extrapolation = 214
first G3 return = 256 steps; naive affine extrapolation = 268
```

Keep this failure visible in the test suite. No silent guard widening.

## Execution and evidence controls

`test_e60.py` checks **300** complete C returns (m from 1..16 and
19,20,25,30,40,50,75,100,200; six (u,v) choices), exact clock, state,
head, full tape and read extrema, with translated heads and randomized
right exteriors. It checks 16 B-entry full-tape returns for both stop
modes and the grammar's `bridge/shortTwo` witnesses. It also checks
m=0 counterexamples and the finite output-transport identity.

`analysis/l17-interleaved/check.py` independently adds **112** raw
Python/C++ differential full-trace cases (64 C checkpoint and 48 B-entry
cases), without routing through the new unittest's expected-output
functions. These remain same-author, transition-table-correlated
witnesses, not external peer review. C++ results cannot replace Lean.

The exact 6-step return-recursion lemma is **not yet proved**. The
predicate `ReachesIn` asserts the state after T transitions, not that
no earlier blank-left C state occurred. First-return minimality must be
formalized separately if it is included in the target theorem.

## Next theorem obligations / stop rule

1. Prove two base cases at m=1 preserving arbitrary suffixes and exact
   complete endpoints.
2. Construct a typed **moving-window transport lemma**. The observed
   extra pair adds a two-step outward A/B scan and a four-step inward
   return cycle. This proposed decomposition requires direct Lean
   verification, not mere clock subtraction.
3. Use induction to prove the full F1/F3 outputs and T1/T3 counts, with
   the read-window shift stated or separately instrumented.
4. Compose with *actual* scanner-token parse equalities; do not infer a
   grammar from arbitrary tape or a blank-orbit reachability theorem.
5. Reject promotion if a valid m>=1 tape context, clock, head, full tape,
   read extreme, or Lean kernel proof contradicts the claim.

Evidence: H (unproved universal recurrence) plus M (bounded replay);
P is reserved for exact Lean-compiled statements. The broader L17
nonhalting problem remains open.
