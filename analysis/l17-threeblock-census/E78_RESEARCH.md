# E78 — deep left witness and an exact counterexample to overstrong safety

A first-return statement must distinguish **nonblank left tape**
from the stronger, false requirement that the immediate left symbol
always equals 1 at every intermediate state C.

## Observed local bridge behavior

From the exact machine table, the 77-step G1 A-to-A bridge
has C-state visits at 17, 55, 67 and 71. The head-nearest fixed
left prefixes at those C visits are:

| Raw bridge step | Head-nearest left word | Immediate bit | Evidence |
| ---: | --- | --- | --- |
| 17 | `110010101010101010010101000101` | 1 | M |
| 55 | `110101000101` | 1 | M |
| 67 | `10000101` | 1 | M |
| 71 | `0101` | **0** | M / proposed P |

Step 71 still has a 1 in the **second** left cell, independent
of arbitrary exterior `L`. The theorem
`e78_one_bridge_C71_deep_witness` proposes to prove this by an
exact 71-step symbolic machine run plus a second-left-cell witness.

From the 95-step G3 A-to-C bridge, control visits C at steps 17,
79 and 91, all with a head-nearest left 1. The endpoint at step 95
is **C(L; 11 (01)^21 0 R)**, *with left tape exactly the arbitrary
exterior L*. Thus setting L=blank yields an actual blank-left C
return at step 95. This is not a contradiction of E71: the E60
checkpoint has a *specific nonblank L*, not arbitrary blank L.

The theorem
`e78_three_bridge_blankLeft_at95_if_left_exterior_blank`
uses the already-certified E67 exact 95-step path as a constructive
counterexample to the false claim of safety through the endpoint
for all L. It is a rigorous negative control.

## Evidence and proof gating

Both E78 Lean statements are **H until link CI and standard-axiom
audit**. Neither requires a new axiom; the initial finite trace
is only a proposed endpoint and is kernel-checked in the proof.

The safety specification for subsequent E78/E79 is:

- For each G1/G3 bridge, no blank-left C at `0 <= t < N`,
  `N=77,95`, with arbitrary exterior L/R.
- For the G3 **exit t=95**, require the actual E60 structured
  nonblank left tail. Do not falsely quantify that safety over
  arbitrary blank L.
- For E68 final unwind, prove nonblank-left at each earlier C
  visit even when the nearest-left symbol is 0.

Only after these conditions and E77's entire-prelude result compile
can the first-return invariant be composed across E65–E71.

Blank-orbit reachability, scanner completeness and L17 nonhalting
are not inferred.
