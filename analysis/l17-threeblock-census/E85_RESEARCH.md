# E85 — G1 final C sweep: sentinel-dependent first-return safety

**Object.** In the merged E68 exact A unwind, the final suffix is the
machine-exact `c01_sweep_exact (u+2) ([1] ++ blank) T`, after a fixed
25-step A finish. The input is C-mode with left stack `(10)^(u+2) 1`.

## Frozen claim and boundary

For every `n : Nat`, `L,R : ListBlank (Fin 2)`, if `L.head = 1`,
every exact time `t < 2n` from
`Cfg.headLeft C ((10)^n ++ L) R` is **not** blank-left C.

The left sentinel is load-bearing: when `n=1` and `L=blank`,
time zero already has control C and blank left tape. The stronger
unconditional statement is false, and has not been introduced.

## Exact proof design

1. In one two-step pair, time 0 is C with a 1 in the second left
   cell and time 1 is B. The exact midpoint is proved with
   `l17_exact_steps`; never inferred from a C-to-C endpoint alone.
2. The existing `c01_exact` supplies the exact full-configuration
   two-step transfer, and E80 transports strict safety.
3. Induct on `n`; `(10)^n ++ L` always begins in 1 when `L`
   does. This proves safety for all `2n` preceding timestamps.
4. Specialize to the structural sentinel `1 ++ blank` in the G1
   final C sweep; use `c01_sweep_exact` and the E84 criterion to
   establish a **local** first blank-left-C time exactly `2(u+2)`.

## Independent bounded control

A separate literal six-state simulator (not a Lean proof) checked
`n=1..14`: all earlier C states have nonblank left, while the
terminal C has blank left. The n=1 blank-sentinel negative control
fails immediately at time 0 as predicted.

## Evidence and promotion

- **H**: E85 Lean statements pending the stacked PR's pinned
  six-job build, theorem inventory, and manual statement audit.
- **P**, after appropriate independent kernel checks: only the
  literal universal sentinel-dependent statements shown in E85.
- **Open**: G1 fixed 25-step A finish, G3 final C-mode finish,
  full E60 first-return composition, mixed grammar, blank-orbit
  reachability and L17 nonhalting.
- **Kill condition:** any counterexample to strict `t < 2n`,
  failure under arbitrary right exterior, `sorryAx`, or a Lean
  failure. Do not respond by weakening the test or dropping
  the sentinel hypothesis.

Parent integration: PR #78 / E84. The existing E77 prelude proof
is independently CI-green and remains separately reviewable in PR #71.
