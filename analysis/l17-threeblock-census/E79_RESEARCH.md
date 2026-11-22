# E79 — structured G3 left exterior excludes a premature return at bridge exit

The G3 fixed 95-step A-to-C bridge has the exact endpoint

```text
A(threeBridgeWord ++ L; 11 ++ R) --95--> C(L; 11 (01)^21 0 ++ R).
```

The E78 boundary counterexample is real: choosing arbitrary exterior
`L=default` makes that endpoint *blank-left C*. It follows that
no universal statement forbidding a blank-left C at step 95 for
**every** left exterior can be true.

The actual E60 positive-width return proof uses instead the structured
exterior

```text
L3(u,v) = (01)^(v+2) ++ 0 ++ (01)^(u+6) ++ blank.
```

For every `u,v : Nat`, `v+2 >= 2`; consequently the head-nearest
two left bits are `0,1`. The **second** cell witnesses that
`L3(u,v)` cannot equal blank, despite the first cell being 0.

## Exact Lean target

The module `L17BridgeBoundary.lean` proposes two public theorems:

- `e79_structured_left_second_one u v`, a `ListBlank`
  pair-power identity valid for all natural `u,v`.
- `e79_three_bridge_C95_nonblank_in_E60_context u v R`,
  which composes the first result with E67's already-proved exact
  95-step bridge, for every arbitrary right exterior `R`.

Both are **H until Lean link CI and trust audit** on PR #73.
There is no new machine-simulation oracle: the transition path is
E67's existing kernel-checked theorem.

This result would address the important **G3 bridge endpoint**
at the exact machine boundary. It does **not** certify every earlier
C visit of that bridge, the G1 bridge, the parametrized C unwinds,
or overall E60 first-return minimality. It does not show full
reachable scanner grammar, blank-orbit reachability, or nonhalting.

Stop if the exponent identity, endpoint frame, type preservation
or trust-audit provenance fails.
