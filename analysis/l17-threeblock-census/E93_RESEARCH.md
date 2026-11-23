# E93 — G3 C-mode finishing segment: exact first blank-left C

**H** pending pinned Lean six-job CI, trust inventory, and statement
review. Stacked on E92 #86, E91 #85, E90 #84, E89 #83.

## Claim

For any u,p:Nat and any full arbitrary right suffix R, the E68 G3
finishing C source first reaches blank-left C after
`2(p+1) + (41+2u)` raw machine steps. This is **local** to the C
finish and not the complete E60 G3 checkpoint.

## Seam proof

At the E90 middle endpoint:
`headLeft C ((01)^(u+6) ++ blank) ((11)^(p+1) ++ 1 ++ R)`.

The exact word identity
`(11)^(p+1) ++ 1 ++ R = 111 ++ 1^(2p) ++ R`
identifies E92's K41 source without replacing any full tape
context. This is the exact equality already used in E68
`width4_c_finish`; the new formal proof explicitly reproduces
it as `e93_middle_right_seam`.

E90 proves no early blank-left C during 2(p+1) raw steps.
E92 proves no early blank-left C during 41+2u steps,
including u=0 and the sharp t=41 K41 boundary.
E80 composes safety; E68 supplies exact endpoint; E84
proves **first** blank-left C for this guarded source.

## Controls and promotion

- E91 t=41 with blank left exterior is a real boundary witness,
  not a counterexample to E93, since the E92 continuation
  has a structural u-dependent left stack.
- E89 t=95 is protected only by the actual E60 G3 second-left
  witness. Arbitrary blank exterior fails at that same clock.
- The G3 total E60 first return still requires prelude +
  variable A window + structured bridge + E93 exact frame joins.
- M=0 affine extrapolation remains retired; global grammar
  and blank-orbit reachability remain open.

Promote H to P only after Lean kernel and standard-axiom trust,
six-job CI, manual theorem-type review and negative-control audit.
Kill if seam identity fails, symbolic R is lost, or sorryAx appears.
