# E90 — G3 C01 middle strict safety, second-left witness

**Status H / PR candidate:** never promote before pinned Lean link,
all six CI jobs, `#print axioms`, trust inventory and manual scope review.

## Frozen claim

For any p : Nat and arbitrary full right suffix R, the 2(p+1)-step
initial C01 middle of E68's G3 final C-mode path has no blank-left C
at any strictly preceding integer clock. The actual left suffix
`(01)^(u+6) ++ blank` has second-left bit 1 for all u>=0.

## Proof decomposition

- Repack exact initial configuration from `headRight C` into
  `headLeft C (10)^(p+1) ++ L`.
- First 2p steps: reuse kernel-verified E85, taking suffix `10 ++ L`
  with head 1. This does not require the actual residual L to start 1.
- Final 2-step pair: prove independently with a **third-left-cell**
  witness while control is C, then state B at odd time.
- Exact path between them: `c01_sweep_exact p` (arbitrary exterior).
- Concatenate with E80; no approximation or global simulation claim.
- Specialize L to `(01)^(u+6)`, which has a 1 at L.tail.head.
- Strict clock: `2p+2=2(p+1)`. The endpoint is not included.

## Negative cases and limitations

E85's stronger guard `L.head=1` is not satisfied by the actual G3
residual word, whose first bit is 0; silently applying E85 directly
would be invalid. The new proof needs a distinct deeper witness for
the final two steps. Without a nonzero residual suffix, the final
two-step pair can begin in blank-left C; the guard is not decorative.

This is not the complete G3 finish: the remaining `41+2u` K41short
plus C01 tail must be certified separately, including the seam
at exactly `t=2(p+1)` where control C is present with nonblank left
tape. Nor is this a full E60 G3 first-return or nonhalting proof.

## Independent control

The exact machine stepper and the existing E78 exterior counterexample
serve as reference/negative controls. A separate finite trace may
corroborate but cannot substitute for the Lean universal proof.

**Kill gate:** unexpected `sorryAx`, unsolved Lean goal, incorrect
left-tape orientation, first-visit counterexample, or lost arbitrary
right exterior. Retain a failed theorem as H; do not introduce an
unstated structure to rescue it.
