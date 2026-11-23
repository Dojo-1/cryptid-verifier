# E80 — machine-level temporal composition for first-return safety

The merged E71 proof fixes the exact positive-width E60 return
configuration and clock. Its first-return minimality requires a
separate universal claim:

```text
forall t < T, forall c,
  ReachesIn target t source c -> not E76BlankLeftC(c).
```

The predicate `E80NoBlankLeftCBefore source T` records precisely
this safety property with an arbitrary, exact whole configuration.

## Three propositions to certify

1. `e80_safe_of_C_free`: an interval with no control-C visit is
   automatically blank-left-C-free. **Not conversely.** The C
   state appears repeatedly in fixed phases with nonblank left tape.
2. `e80_safe_trans`: given an exact `m`-step trajectory from
   source to middle, safety on `[0,m)` and safety on
   middle's `[0,n)` compose into safety on `[0,m+n)`.
   The proof uses pinned `multiStep_add` and `Option.bind_some`.
3. `e80_safe_then_C_free`: convenient form connecting a
   safety-certified fixed prelude to the stronger C-free variable
   middle phase (E75).

These have *zero new raw machine paths* and no witness schedules.
They are formal algebraic interfaces that make the final E60
first-return composition possible without repeating thousands of
transition reductions or assuming any informal time shift.

**H until Lean link CI and standard-axiom audit:** the E80
theorem declarations. All are registered in the trust inventory.
The previously merged E71/E75/E76 theorem boundaries remain P.

**Still open:** universal complete fixed-prelude safety E77,
bridge safety/structured endpoint E78/E79, parameterized final
unwind safety, and the resulting canonical E60 first-return
theorem. E80 does not prove mixed scanner grammar, blank orbit
reachability, or universal L17 nonhalting.
