# E87 — first blank-left C for the full E68 G1 final A unwind

## Frozen claim

For every `u,p : Nat` and full symbolic right exterior `R`, the
guarded E68 A source reaches blank-left C **first** at time
`T = 4p + 29 + 2u`. The guard includes a specific structural
left tape ending in blank; this does not extend to arbitrary A inputs.

**No claim is made for the earlier E60 C checkpoint or global L17
nonhalting.** E87 only certifies the final A unwind segment.

## Proof dependencies and clocks

| segment | exact path | strict preterminal safety |
|---|---|---|
| A pair sweep `4p` | E66 | E83 |
| Fixed A finish `25` | E86 | E86 |
| Sentinel-protected C01 sweep `2(u+2)` | `c01_sweep_exact` | E85 |

The full clock is `4p + 25 + 2(u+2) = 4p + 29 + 2u`.

The left-tape identity is the same as in the existing E68 proof:
`[0,0,1,0,1,0,1,0,1] ++ (01)^(u+2) = 0 ++ (01)^(u+6)`.

The right tape identity uses `rotLB`:
`(10)^p ++ 1 ++ R = 1 ++ (01)^p ++ R`.

The final A-finish configuration is converted by
`Cfg.headRight_cons` and `rotLB` into a C-mode left tape
`(10)^(u+2) ++ 1 ++ blank`, exactly the E85 sentinel source.

## Strongest positive result

Given machine-exact paths at **every seam**, E80 safety composition
proves strict exclusion of blank-left C before the clock.
E68 supplies the full exact terminal return. E84 packages these
into a local first-return theorem.

## Negative / adversarial controls

- E86 with arbitrary blank L really *can* become blank-left C at
  its 25-step endpoint. E87 does not claim safety at that endpoint;
  it instead continues from the structured nonblank E68 L.
- E85 without sentinel hypothesis is false already at time zero
  for n=1 and blank L.
- E82 G3 fixed bridge at time 95 can be blank-left C with an
  arbitrary blank exterior; none of E87 weakens that known boundary.
- E60 `M=0` affine extrapolation remains retired.
- No theorem may claim the entire G1/G3 E60 first return or
  nonhalting from this local segment.

## Evidence and next gate

**H** until the six-job pinned Lean build, new theorem trust audit,
and manual statement review complete. Lean successful compilation
will establish only the displayed local first-return theorem.

One bounded next target: integrate the independent E77 fixed-prelude
certificates plus E75 variable no-C middle and E81/E82 fixed bridge
certificates in a single proof **with full frame alignment**.
The G3 C-mode final phase also needs first-return safety; it is
not covered by this G1 result. Stop on any failed seam identity,
incomplete C-visit census, or `sorryAx`.
