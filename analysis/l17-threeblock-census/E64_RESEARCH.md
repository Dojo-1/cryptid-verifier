# E64 — parameterized A-scanner insertion diamond

## Scope

This increment composes two already verified facts without extending the
unproved global E60 recurrence:

- `a01_sweep_exact m`: any number of leading `01` scanner tokens is
  traversed in `2*m` raw steps, preserving arbitrary exterior tapes.
- `e61_A_window_insertion_diamond_exact`: the two local branches from
  `0111` and `010111` consume 2 and 8 raw steps respectively.

The public Lean theorem
`CryptidLink.L17.e64_A_scan_window_diamond_exact` expresses both exact
full-configuration endpoints, arbitrary natural `m`, and arbitrary
`ListBlank` exteriors. These two branches finish in state A at the
same head, with left prefix `01 :: (01)^m :: L` in head-nearest-first
representation; the right suffixes are `11 R` and `1110 R`.

**This is not E60's global parameterized C return.** In particular the
parameter here counts A scanner tokens, not a formally established
conjugacy between the E60 C configurations at adjacent `m` values.

## Evidence and falsification

The new independent raw transition-table test `test_e64.py` checks 540
arbitrary-context fixed-clock endpoints, full tapes, state, head,
read bounds, and the six-step branch difference. Each endpoint is
reconstructed independently of the Lean proof term and checked for both
`m=0` and positive `m`; this does not rehabilitate the invalid E60
`m=0` affine C-return extrapolation.

The existing E60/E61 tests remain the adversarial controls. No finite
campaign establishes the all-m C-checkpoint theorem.

## Remaining exact proof obligations

1. Define a typed insertion map on *whole* configurations with head
   translation when the head crosses the inserted window. State it
   relative to the actual E60 C-checkpoint head; do not use a
   coordinate-free insertion that silently shifts the suffix.
2. Prove the **pre-seam synchronization** for the two E60 families for
   every `m >= 1`, `u,v`, and exterior `R`; include read-frontier bounds.
3. Identify the local E61 seam in the two traces and use this E64 lemma
   or the E61 lemma there. Prove the **post-seam non-reading** condition,
   rather than assuming that the inserted cells stay hidden.
4. Compose the exact clock and entire tape word and prove both base
   cases at `m=1`. Keep the distinct `4v` and `2v` slopes.
5. Derive a conditional mixed B-entry theorem from actual scanner-token
   equalities, **then** examine whether any blank-orbit configurations
   satisfy the hypotheses.

**Stop rule:** do not claim an unrestricted three-block classification,
a universal first-return theorem, blank-orbit reachability, bounded stack
depth, or L17 nonhalting. Merge only on green pinned Lean CI, trust
inventory, and regressions; if compilation or source-claim inspection
fails, leave the PR open.
