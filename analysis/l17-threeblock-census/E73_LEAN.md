# E73 — C-free 4n A-pair sweep (candidate)

This is the first targeted formal safety refinement of E71's exact
reachable return, motivated by E72's bounded C-event census.

## Exact statement

`E73NoCBefore source clock` means:

```
for every t < clock and every full configuration c,
  if ReachesIn target t source c then c.q != some C.
```

Two Lean proof candidates in `L17NoCWindow.lean`:

1. `e73_one_pair_C_free`: every intermediate control state in the
   4-step transfer is non-C, explicitly A/E/F/D.
2. `e73_all_pair_sweeps_C_free`: for every natural n and arbitrary
   left/right ListBlanks, none of the first 4n states in
   `A((01)^n L ; 11 R)` is C.

The inductive step uses the **already-proved** exact four-step E66
transition and the pinned upstream `multiStep_add` law. It splits
clock t into `t<4` and `t=4+j`; the second case transports
through the exact E66 endpoint to the induction hypothesis.

### Evidence and boundaries

- **H until Lean CI:** Both declarations are unverified candidates,
  including the local 1/2/3-step full configurations.
- **P (upstream):** E66 exact 4n step endpoints; E71 complete E60
  return. Neither already implies intermediate C-state absence.
- **M:** E72's 440-case first-return census observed no C-state
  events during the combined A scanner/pair sweep.

This proof, if checked, would establish C-free safety only for E66's
pair-sweep. It would not certify the 2m A scanner, the C-state
schedules in E72, the left-of-head witness at each other C event,
first-return minimality, blank-orbit reachability, or nonhalting.

Stop if the link build fails, the theorem states are weakened, an
unsound tactic/axiom appears, or the trust inventory detects `sorryAx`.
