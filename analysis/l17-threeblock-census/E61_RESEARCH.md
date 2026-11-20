# E61 — a local six-step insertion diamond, plus a bounded phase-transport probe

## Scope and result status

The research target remains the E60 all-m right-window recurrence at L17's
mixed width-five C checkpoint. This PR proves a *local* two-versus-eight-step
diamond with arbitrary exteriors, and measures whether the two E60 paths
synchronize by a moving insertion frame. The latter has **not** been proved
for all m, u, v or R. Nothing here proves blank-orbit nonhalting.

The exact Lean theorem is
`CryptidLink.L17.e61_A_window_insertion_diamond_exact`:

```text
A(L ; 0111 R)   -- 2 steps --> A(01 L ; 11 R)
A(L ; 010111 R) -- 8 steps --> A(01 L ; 1110 R)
```

`01 L` on the left is expressed in Lean's head-nearest-first
`ListBlank` representation; the physically written cells to the left of
the new head are `10`. The longer branch factors as an exact two-step
prefix followed by the six-step `e60_A_detour_exact`.
Both statements preserve arbitrary left and right exteriors.

## The phase-transport hypothesis (H; bounded checks only)

Let f=1 or 3, m>=1, and let S_f(m;u,v,R) be E60's actual C checkpoint.
Increasing m inserts a spatial `10` before the last `111`.
In entry-head coordinates the insertion begins at

```text
p_in  = 22 + f + 2m
p_out = p_in + 3
t_sync = (88 if f=1 else 126) + 2m
```

Define I_p on complete configurations by inserting two cells `10`
at positions p,p+1; all occupied cells and the head at positions >=p
are shifted right by two, and the control state is unchanged.

The measured two-phase relationship is:

```text
I_p_in (Phi^t S_f(m)) == Phi^t S_f(m+1)    for 0 <= t < t_sync-1
I_p_out(Phi^t S_f(m)) == Phi^(t+6) S_f(m+1) for t_sync <= t <= T_f(m)
```

At t_sync the shorter trajectory is in A with **11 followed by arbitrary
right suffix**. The longer trajectory is in A at the same head with
`0111`; the formal six-step local detour moves the extra pair outside
the remaining read frontier. The earliest new insertion is outside the
measured read window, but this is not yet a Lean-certified global
read-bound or all-m transport.

Do **not** replace the arbitrary shorter suffix by a fixed `1110`.
That overstrong intermediate conjecture was falsified immediately by an
exterior beginning `0`, and was corrected before the regression passed.

The test `test_e61.py` uses an independently transcribed raw six-state
transition table, not E60's expected-output function. It compares 240
entire short/long trajectory pairs and 240 arbitrary-context local
diamonds, with state, head, full set of written ones, and phase
translation. It checks the right-read bound for each finite trace.
The independent table is still same-project evidence, not external review.

## Promotion and stop rules

* P: the Lean-checked local 2/8-step diamond only, after green link CI and
  trust audit with standard axioms.
* M: finite phase-conjugacy, observed six-step clock increment and
  first-return clock/tape probes.
* H: the universal phase transport and E60 all-m theorem.
* R: the incorrect fixed `1110` assertion for the shorter branch and
  extrapolation to m=0.

Kill the global hypothesis on any true full-configuration transport
failure for m>=1 after accounting for the typed insertion. Do not
promote a local diamond to a quantified all-m theorem without proving
the pre-sync scanner transport and the post-sync non-reading bound.
No new geometry is needed until this exact obstruction is resolved.
