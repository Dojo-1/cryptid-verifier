# E91 — K41short, preterminal first-return safety

## Freeze

**H pending six-job CI and trust audit.** The 41-step fixed G3 finishing
kernel is the existing theorem `k41short_exact` in `L17r.lean`.
We add per-time full-configuration certificates for every t=0..41
with arbitrary left L and right R exteriors.

The new universal safety statement is *only* `t<41`. At
`t=41` the left tape becomes exactly L; with L=blank this is
blank-left C. That boundary is recorded as a machine-exact
negative control rather than silently discarded.

## Exact 41-step census

The literal reference interpreter derived from
`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`
visits control C at **0,25,37,41**. At 0,25,37 its nearest
left bit is 1. At 41 it is an arbitrary exterior L, possibly
blank. Every transition from t=0 to t=41 stays inside fixed
known guard [-11,3], never reading L or R.

The endpoint is (headRight C L (110101010101010 ++ R)),
identical to `k41short_exact` on the complete full tape.

## Proof mechanism and representation

- 42 exact full-configuration `ReachesIn` lemmas, built from literal
  `l17_exact_steps` one-step transitions and transitivity.
- Deterministic identification of any reachable state at each
  `t<41` with its certified exact configuration.
- A non-C control argument at the other 38 timestamps; at the
  three C timestamps, first-left-bit `1` excludes blank left.
- Kernel-verified negative control: blank exterior at raw t=41.
- No clock inference from the endpoint alone; no unstated
  insertion or congruence of symbolic contexts.

## Relation to E90 and remaining obligations

E90 covers the initial `2(p+1)` C01 middle of G3 final C-mode
finish. E91 will cover the subsequent 41-step K41short core
once E90's exact endpoint is aligned to this kernel's source.
The final `2u` C01 sweep still needs a sentinel proof at its
actual residual left stack, and E80 composition must check all seams.

## Gates and controls

- Kills P promotion: any Lean error, sorryAx, unverified tape
  transition, lost symbolic exterior, mismatch at C visit or
  t=41 boundary, or failing six-job CI.
- Promotion after pinned CI and standard-axiom trust only:
  exact `e91_K41short_* ` statements, not G3 E60 first-return.
- Model/data parity not applicable: deterministic literal machine.
  One independent Python reference and the Lean transition
  semantics constitute distinct implementations of the same
  underlying specified table, not independent mathematical proof.
- M=0 E60 affine extrapolation remains retired. Blank-orbit
  nonhalting, global grammar closure and G3 first-return remain open.

## Artefacts

`link/CryptidLink/L17K41shortSafety.lean`: exact proof candidates.
`analysis/l17-threeblock-census/E91_K41_CENSUS.json`:
raw per-time known-word certificates.
