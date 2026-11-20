# E63 — split contextual kernels for the last two non-E60 bounded three-block shapes

## Exact proposed scope

Three-block C-order parses `[wide(1),wide(1),wide(1)]` and
`[wide(1),wide(1),wide(2)]`. The first valid scanner prefix consists
of five virtual 01 tokens; for the 100 stop the final implicit 101 token
must match and be removed. Both stops deposit at least **four leading
ones**. The new guard therefore consumes four terminal-residue bits,
leaving `11R` in the 00 branch and `R` in the 100 branch.

| Shape | Guard bits | Kernel clock | Exact checkpoint clock | Read interval |
|---|---:|---:|---|---|
| wide(1),wide(1),wide(1) | 49 | 279 = 90+90+99 | 328+2u+2v | [-14,51] |
| wide(1),wide(1),wide(2) | 51 | 319 = 110+110+99 | 362+2u+2v | [-20,53] |

The six local subkernels are stated with arbitrary left/right ListBlank
exteriors. Each intermediate configuration was obtained by replaying the
independently transcribed six-state transition table, then checked
against 600 arbitrary-exterior individual segments before Lean promotion.
Do not treat generated sources as proved until the linked Lean build succeeds.

`WidthFourGuard.oneTripleWide` and
`WidthFourGuard.threeTripleWide` compose those kernels with the exact
`width4_c_finish`. The new public theorem
`mixed_triple_wide_exact` is conditional on the **actual** scanner
token parse and distinguishes the 00/100 residual suffixes.

## Reproducibility and adversarial controls

Before this proposal the frozen 1,016-parse census has 992 matched and
24 unmatched. Under E63's two exact guards the predicted figures are
**996 matched and 20 unmatched**. Those final 20 are all in E60's two
moving-window families for the fixed parameters j=0..3; this is
not an unbounded classification or a proof of the E60 all-m recurrence.

Independent local finite tests already exercised 400 complete C
returns, 200 randomized arbitrary-exterior local full kernels and 600
contextual split segments; the shortened-guard negative controls change
the endpoint. Add 120 Python/C++ mixed B-entry differential traces
bringing the expected full campaign from 4,380 to 4,500. Matched controls
require exact state, head, complete tape, transition count, reader
extrema, origin translation and terminal residue, not just the clock.

**Kill and stop rule:** no merger or proof promotion without green Lean
link, trust audit, all regression families and a manually reviewed
source-to-claim map. No assertion of full three-block grammar in general,
first return in Lean, blank-orbit reachability, stack boundedness, or
L17 nonhalting.
