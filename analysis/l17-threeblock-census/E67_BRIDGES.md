# E67 — two fixed contextual return bridges

The exact L17 candidate bridge kernels are:

| Family | Entry control | Steps | Exit control | Observed read window |
|---|---|---:|---|---|
| G1 / one-headed | A | 77 | A | [-34,1] |
| G3 / three-headed | A | 95 | C | [-42,1] |

Both are stated over arbitrary binary `ListBlank` exterior tapes.
The left input words are head-nearest-first and consist of 35 and
43 bits, respectively.

```
A(oneBridgeWord L ; 11 R)
    --77 steps--> A(L ; 11100 (10)^16 R)

A(threeBridgeWord L ; 11 R)
    --95 steps--> C(L ; 11 (01)^21 0 R)
```

The two precise theorem declarations live in
`link/CryptidLink/L17FixedBridges.lean` and use `l17_exact_steps`,
not an externally assumed transition invariant.

## Independent raw checks

`test_e67.py` provides 800 arbitrary-context exact endpoint tests
and two negative controls which flip the first head-nearest left bit.
It matches state, head position, every one on the complete tape, and
read extrema. The raw table is separately transcribed, not a call to
the Lean proof generator. These are bounded **M** observations.

## Composition interface still to prove

For E60 width parameter `M >= 1`, E65's internal scanner parameter
is `m=M-1`: its fixed `W` prefix has already consumed one `10`
pair. Thus E65's A source has `P^M` at the left of the A head.
E66's exact `4*M` pair sweep removes *all* of them.

The bridge input then is `Y_f` followed by a short part of the
original left exterior. For G1 the extra five bits are `00101`;
for G3 the extra eight bits are `01010101`. The remaining left tape
is the required input to the respective final unwind lemma.

The fixed bridges alone do not prove these global frame decompositions,
the E60 return, first-return minimality, blank-orbit reachability, or
L17 nonhalting. Next prove the tape equalities and compose with E65
and E66 after CI. Retain the failed E60 M=0 extrapolation explicitly.

**Merge gate:** pinned Lean link/core/Mathlib builds, standard-axiom
inventory, and all regressions must pass, followed by direct patch
review. Otherwise leave the PR open.
