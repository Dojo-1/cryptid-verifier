# E74 — all 6M variable A-phase transitions avoid control state C

This research increment depends on E73's still-unmerged C-free pair-sweep.
Its branch is based on E73's corrected proof commit, not on the current
main branch. It must not be merged before E73 passes Lean link/trust
audit and merges.

## Exact proposed theorem

For any `M : Nat` and arbitrary two-sided binary `ListBlank` exteriors
`L,R`, a machine configuration
`A(L ; (01)^M 11 R)` contains **no C state** in any of its first
`6*M` complete raw-machine configurations.

This unifies:
- 2*M steps in the previously proved `a01_sweep_exact` scanner,
  strengthened by `e74_all_01_scans_C_free` (induction on the
  two-step A->B->A scanner cycle);
- 4*M steps in E66's exact pair sweep, strengthened by E73
  `e73_all_pair_sweeps_C_free` (induction on the A->E->F->D->A cycle);
- a certified `multiStep_add` composition lemma joining their safety
  intervals along the exact scanner endpoint.

This is stronger than endpoint equality: it quantifies over every
defined intermediate machine configuration and its control state.

## Evidence and limitations

**P input:** the pinned Cryptids `ReachesIn` semantics,
`multiStep_add`, E66 pair-sweep, and exact A01 scanner.

**H until Lean CI:** the one-token state path, arbitrary-scanner
state safety, C-free composition, and the complete 6*M C-free
variable interval. The proof creates no axioms; proof failure must
not be silently filled with `sorry`.

**M:** E72's 930 bounded complete-tape trajectories have zero C-state
visits in this variable-length phase, including adversarial right
exteriors. Agreement is finite only.

Even after verification this does **not** prove the preceding 88/126
C-to-A preludes' left-witness property or the following 77/95 bridges
and parameterized final unwinds. Thus it does not prove the entire
E60 first-return minimum, full scanner grammar, blank-orbit
reachability, or universal L17 nonhalting.

## Merge gate

First merge E73 after six green CI jobs and standard-axiom trust audit;
rebase this branch onto that head preserving only the new E74 module,
import, trust additions and documentation. Then rerun all CI on the
reconciled head and inspect the exact theorem statements.
