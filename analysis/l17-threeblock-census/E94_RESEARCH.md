# E94 — positive-width G3 E60 first blank-left-C theorem target

Status: **H**, stacked on E93, E92, E91, E90, E89. No promotion
before pinned Lean kernel, six-job CI, trust inventory and manual
statement review. Original E71 exact endpoint proof already exists.

## Precise claim

For every m,u,v:Nat, physical M=m+1>=1, and arbitrary right
exterior R, the full canonical G3 E60 C-checkpoint first visits
blank-left C at raw clock

  T = 268 + 6M + 2u + 2v.

This is first-return minimality *within the source family*, not
a nonhalting proof from the blank initialization or global
closure of all scanner shapes.

## Four exact safety phases

| Phase | Raw clock | Safety |
|---|---:|---|
| Fixed G3 C-to-A prelude | 126 | E77 |
| C-free moving A window | 6M | E74/E75 |
| Structured fixed A-to-C bridge | 95 | E89 through t=95 |
| G3 C finish | 2(v+3)+41+2u | E93 candidate |

Sum: `126+6M+95+2(v+3)+41+2u = 268+6M+2v+2u`.
Every intermediate source/endpoint is matched as a complete
`Cfg` object with both symbolic full half-tapes.

The E94 source is the **original** `widthFourCutSource` E60 G3
constructor, definitionally identified with the E69 contextual
C source using the exact E70 normal form. E71 supplies the
complete F3 output tape; E84 packages exact endpoint plus
strict no-earlier-blank-left-C safety.

## Controls, falsifiers and representation attacks

- Do not treat a control-C visit with nonblank left as return.
- E78's arbitrary blank-exterior G3 bridge t=95 counterexample
  remains true. E89 applies only to E60's structured exterior.
- E91's K41 t=41 blank-exterior counterexample remains true.
  E92 handles u=0 as an endpoint and u>0 by sentinel.
- M=0 affine extrapolation is retired; it is excluded by M=m+1.
- Equalities of moving window, fixed bridge, final C source
  are complete full-tape configurations, not clock-only matches.
- Independent literal reference simulator in the working
  session checked 976 fixed/seeded G3 examples with arbitrary
  right exteriors, including full E71 terminal tapes; finite
  reproduction is evidence M, not a universal proof.

## Next gate

Pinned six-job Lean build; `#print axioms` standard inventory,
no `sorryAx`; manual theorem-scope audit, cross-check source
frame; then reconcile branch ancestry and merge if green.

Global mixed scanner grammar, reachability of this family from
blank tape, its recurrence closure, and L17 nonhalting remain open.
