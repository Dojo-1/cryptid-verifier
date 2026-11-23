# E92 — local first return for the complete G3 K41/C01 tail

Status **H** until pinned six-job Lean/link trust checks and manual
statement review; stacked on E91 #85 (which in turn depends on
E90 #84 and E89 #83).

## Typed objective

For any u>=0 and arbitrary right ListBlank exterior R, start with
`Cfg.headLeft C ((01)^(u+6) ++ blank) (111 ++ R)`.
Prove no blank-left C at any t<41+2u, then prove first such C at
the endpoint t=41+2u. This is the final tail of E68 G3's C finish,
not the full E60 C checkpoint.

The u=0 case is load-bearing: K41short reaches its endpoint with a
blank left tape at 41, which is the terminal time. For u>0, the
residual `(01)^u` ensures that K41's endpoint is not blank-left
and the final `2u` C01 sweep preserves a left sentinel [1].
No claim of K41strict safety at t=41 for arbitrary L.

## Machine-exact proof decomposition

- `e92_source_frame`: equality of *full* headLeft/headRight C
  configurations, using six 01 pairs.
- E91: exact 41 steps, strict preterminal safety for any L and R.
- `rotLB u blank`: the K41 endpoint is exactly
  `headLeft C ((10)^u ++ [1] ++ blank) (Ktail ++ R)`.
- E85: sentinel-dependent C01 safety for `2u` steps;
  `c01_sweep_exact` supplies the exact terminal path.
- E80: interval composition, E84: endpoint + safety implies local
  first blank-left-C.

## Negative controls and limitations

- E91 at t=41 with L=blank is genuinely blank-left C.
  The composition correctly treats this as a *terminal* visit for
  u=0 and continues only when u>0, with structural residual.
- Dropping the [1] sentinel from E85 is known false.
- G3 bridge t=95 is safe only for the structured E60 exterior.
- The initial `2(p+1)` middle segment still requires an exact
  full-configuration seam into this tail (planned E93).
- Even a complete E60 G3 first return is **not** blank-tape
  reachability, closure or nonhalting.

Kill: any Lean error, sorryAx, incorrect Ktail tape, loss of
symbolic right R, invalid clock at u=0, or failed trust audit.
