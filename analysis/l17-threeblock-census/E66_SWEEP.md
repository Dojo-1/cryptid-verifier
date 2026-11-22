# E66 / checkpoint 1 — guarded A-sweep, not global E60 return

## What this increment proves (once Lean link CI passes)

For every `n : ℕ` and arbitrary binary `ListBlank` exteriors
`L, R`, let `P = [0,1]` and `Q = [1,0]` in Lean head-nearest
orientation. The L17 raw six-state machine obeys

```text
A(P L ; 11 R)        --4 steps-->   A(L ; 11 Q R)

A(P^n L ; 11 R)      --4n steps-->  A(L ; 11 Q^n R)
```

The first theorem uses `l17_exact_steps`, retaining arbitrary exteriors.
The second is a genuine induction using the exact four-step statement,
`ListBlank.append_pow_comm` and `append_pow_succ`.

The physical read window for a nonempty sweep is
`[h - (2n-1), h+1]`; this bound is currently a **raw-test observation**,
not an independently formalized extremal-read theorem. Both exact
machine endpoints retain the full exterior tapes. The replacement of
left physical pairs `10` by right `10` pairs is positional, not a
global translation-invariant assertion that all machine states commute
with insertion.

## Measured regression

`test_e66.py` executes 1,320 randomized arbitrary-context sweeps
from n=0..40 and n=100,200,500, checking complete tapes, head, state
and read extrema. It includes a guard mutation to `10`; the claimed
four-step endpoint must then fail.

## Relationship to the E60 target

The unproved E60 C-return formulas decompose into an outbound C prelude,
a variable A-scanner, the present 4n A sweep, a fixed contextual
bridge, and final return. This PR certifies **only the sweep**. It is
independent of the E65 prelude PR #59, which must not be merged while
its Lean link CI is failing.

The remaining E66 issue #60 obligations are 77- and 95-step bridge
theorems and composition with precisely framed `width4_a_unwind`
and `width4_c_finish`, including word normalization and parameter
restrictions. Even a completed C-return `ReachesIn` theorem would not
show first-return minimality, a complete reachable grammar or L17
nonhalting.

Evidence: P = Lean statements after CI; M = 1,320 raw tests; H =
composed E60 C-return, blank orbit reachability, and nonhalting.
