# E76 — exact first 26-step C-guard certificate

This module starts the finite-prelude side of issue #67 after E71
certified the complete positive-width returns and E74 certified the
C-free variable A window.

## Scope

The machine begins in state C and revisits C at raw step **25** in
both fixed prelude families. Consequently, a theorem that the prelude
*never enters C* is false.

The mathematically relevant target is narrower:

```text
E76BlankLeftC c := exists Z, c = Cfg.headRight C default Z

forall L R t < 26 c,
  ReachesIn target t (C(X_f L; W_f R)) c ->
  not (E76BlankLeftC c)
```

where `X_f`, `W_f` are the exact 6/25-bit (G1) or 9/27-bit
(G3) framed input words from E65. `L` and `R` are arbitrary
half-tape exteriors; no zero-extending assumption is used.

## Proof approach

`L17First26CGuard.lean` supplies **26 exact whole-configuration
path statements per family**, for every raw time 0..25. Each endpoint
is computed from the frozen six-state transition table and checked by
the previously used `l17_exact_steps` tactic with *symbolic* L/R.
The finite time case split is exhaustive by `omega`; no trace
sampling is substituted for the Lean proof.

Two local machine facts discharge the resulting cases:

1. If `c.q != some C`, `c` cannot be blank-left C.
2. If the nearest left tape symbol is `1`, `c` cannot
   be blank-left C, regardless of its control state or right tape.

The only C-state visits among the 26 candidates are at `t=0` and
`t=25`; both have a head-nearest left bit `1`.

## Evidential gates

- **H** pending pinned Lean link CI and standard-axiom audit:
  `e76_one_first26_noBlankLeftC`,
  `e76_three_first26_noBlankLeftC`.
- **M** from E72: 930 bounded complete raw trajectories with no
  earlier blank-left C; these are independent of this Lean certification.
- **P** prerequisite: E65 exact contextual 88/126-step preludes,
  E71 exact terminal returns, E74 C-free variable A phase.

The remaining fixed prelude times **26..87** (G1) and **26..125**
(G3) still require corresponding certificates, followed by the
77/95 bridge C visits and the parameterized final unwind. This PR
does not prove entire first-return minimality, blank-orbit
reachability, or global L17 nonhalting.

**Stop rule:** any failed exact symbolic state, omitted time, trust
audit failure or hidden assumption blocks promotion from H to P.
