# E65 — fixed C preludes expose the moving A window

## The two new local exact statements

The two E60 C-checkpoint families have different fixed prefixes, but
both have a constant-time C-to-A prelude independent of the later variable
pair count and independent of either exterior tape:

| C family | Raw prelude | Entry read window | Head shift |
| --- | ---: | --- | ---: |
| one-headed (G1) | 88 | [-6, 24] | +24 |
| three-headed (G3) | 126 | [-9, 26] | +26 |

`e65_one_prelude_exact` and `e65_three_prelude_exact` state these
configurations over arbitrary `ListBlank` left/right exteriors. The
specific finite read windows were extracted from the raw six-state
transition trace and checked against 400 randomized exterior instances,
with full tape equality. They are explanatory bounds from the separate
literal replay, **not** separate formal proofs of those extrema.

## Composed all-m C-to-A entry theorem

Let `X_f`, `W_f`, `Y_f` be the finite left, right and output lists
in `L17WindowPrelude.lean`. Put `Q=[1,0]`, `P=[0,1]`, and let `L,R`
be arbitrary exterior `ListBlank` tapes.

For **every** `m : Nat` there are exact machine paths:

```
C(X_f L ; W_f Q^m 111 R)
  -- (N_f + 2m + 2) steps -->
A(01 P^m Y_f L ; 11 R)

C(X_f L ; W_f Q^m 10111 R)
  -- (N_f + 2m + 8) steps -->
A(01 P^m Y_f L ; 1110 R)
```

with `N_1=88` and `N_3=126`. Both reach the **same A head
and full left tape**, and the longer branch has a distinct complete right
remainder `1110R` versus `11R`. The six-step difference is an
exact local machine phenomenon, not merely an affine clock fit.

The theorem uses `rotLB0` to turn the physical suffix `0(10)^m`
into the A scanner's `(01)^m0` and composes E64. The proof is **not**
an induction on the original E60 return; it handles only the outbound
phase up to the A seam. Arbitrary `u,v` in the E60 width-four frame
must still be transported through an explicit left-tape decomposition,
even though the raw read windows are small.

## Tests and evidence levels

The added `test_e65.py` independently replays the raw six-state
transitions for 400 fixed contextual preludes and 800 variable-suffix
compositions, asserting complete tapes, control states, heads and read
windows. Earlier local experiments separately checked 600 fixed and
1,600 composed randomized contexts.

**P**, conditional on passing pinned Lean CI and axiom audit:
the four precise `ReachesIn` theorems.

**M**: finite read-window extrema and the 1,200 committed raw tests.

**H**: the E60 C-to-C return recurrence, all-m trajectory insertion
conjugacy, first-return minimality, and source reachability on the blank
orbit.

## Next obstruction

E65 ends at A, at the seam. E61/E64 identify six extra steps and
the changed right remainder. The remaining task is to show that
the **entire post-seam machine run** from the two A endpoints is related
by a typed insertion map, with the inserted pair outside the
subsequent read frontier. For each family, also prove the first base
C return at E60 `m=1` with its complete tape and separate
`4v` or `2v` slope. Then, and only then, compose an exact
all-m C-return theorem.

The historical E60 false `m=0` clock extrapolations remain retired:
222 rather than 214 for G1 and 256 rather than 268 for G3.

Stop without merging if any Lean, axiom, clock, full-tape, context
or semantic-bridge check fails. This is **not** a proof that L17
never halts.
