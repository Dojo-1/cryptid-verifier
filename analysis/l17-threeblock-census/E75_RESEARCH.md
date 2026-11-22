# E75 — certify the actual E60 middle interval

This work is stacked on E74 (#68) and E73 (#66, now merged).
Do not merge E75 until E74 has passed integrated CI and merged.

## Mathematical target

For every `m : Nat`, arbitrary binary `ListBlank` exteriors
`L,R`, and every intermediate exact machine configuration `c`:

- G1 contextual C source: `88 ≤ t < 88 + 6*(m+1)` implies
  `c.q != some C`.
- G3 contextual C source: `126 ≤ t < 126 + 6*(m+1)` implies
  `c.q != some C`.

All configurations are quantified through `ReachesIn target t`
from the same full C source appearing in E65, not inferred from an
endpoint-only clock fit.

## Proof route (formal candidate)

1. Apply E65's already-certified exact 88/126-step C-to-A prelude.
2. Prove literal tape identity
   `0 (10)^m 111 R = (01)^(m+1) 11 R`.
3. Apply E74's universal C-free 6M A-stage at `M=m+1`.
4. Transport the safety predicate across the exact prelude with
   `multiStep_add` and the source-to-middle equality.

The proofs have no user-supplied axioms or sorry placeholders. Exact
theorem status remains **H** until Lean link and the standard-axiom
trust audit succeed on the integrated code.

## What this does not establish

Neither theorem asserts a C-free *whole return*. The starting C
configuration has a nonblank left tape; the 88/126-step fixed
preludes, 77/95-step bridges and final parametric unwinds contain C
visits. Those visits must each retain a nonblank left tape before
the final E71 return. E75 is therefore only a middle-window
safety certificate, not E72 first-return minimality, complete
mixed scanner grammar, blank-orbit reachability or L17 nonhalting.

If CI rejects the literal repacking or the E65 private abbreviations
do not normalize definitionally, repair that equality, **not** the
quantified no-C conclusion.
