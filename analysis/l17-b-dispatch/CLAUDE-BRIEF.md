# L17 handoff: short-buffer B dispatch

The former saved R(6,7,2,2;3,001101) boundary now returns in 108 raw
transitions, C at −36. This is a generic source, not a blank-orbit extension.

`DERIVATION.md` gives eleven B rows and sixteen C2/C5 compositions with
whole words, head frames and clocks. Shared sufficient guards: p≥6,c≥7.
The right terminal classes are0,111,1100,1101 after a B scan of(10)^j.
The 1101 result is a typed A exit; no general return is claimed for it.

New Lean file: `link/CryptidLink/L17l.lean`. Its six declarations have
symbolic arbitrary left and right exterior tapes and exact `ReachesIn`
clocks. They are the finite kernels only, not the parametric return table.
The seventh declaration, `short_gap_rotation`, proves the word identity
P_m00=0(10)^m0 for all m and arbitrary context.

| Declaration | Clock | Read interval / exit |
|---|---:|---|
|short_C2B_exact|38|[−6,3] / B4|
|short_C5B_exact|62|[−14,3] / B4|
|short_B1100_n5_exact|75|[−20,3] / C−21|
|short_B1100_n6_exact|95|[−26,3] / C−27|
|short_B1100_n7_exact|65|[−18,3] / C−19|
|short_B1101_exact|14|[−4,3] / A4|

To formalize the table, use existing sweepC/sweepD/sweepA, K60T, K7,
K22 and K41short from the mixed-return derivation. Define bottom finishes
F_p=K41short;C01^(p−6), E_p=K22;C01^(p−4). Then:

1. B0: one B0 step;C01^n;C_pair1(c);F_p.
2. B111: B_to_D(n);D_pair1(c,n+1);E_p.
3. B1100,n5: short_B1100_n5_exact;C01^(c−3);F_p.
4. B1100,n6: short_B1100_n6_exact;C01^(c−5);F_p.
5. B1100,n7: short_B1100_n7_exact;C01^c;F_p.
6. B1100,n≥8: B1;K60T;C01^(n−7);C_pair1(c);F_p.
7. B1101: short_B1101_exact, or B1;K7;A01^3.

C2 with previous width2 has n=5 and entry clock 38. C5 with previous
width3 has n=9 and entry clock 62. Scan j extra10 pairs before dispatch.
Their1101 exits have A at 8+2j. Normalize P_(n−2)00 by
`short_gap_rotation`: the left stack has widths[p,c,1,n−2,3]. This is
within the general scanner grammar; the three-run homogeneous return
theorem does not directly cover it.

When the next two cells are 00, continue with A00L in 10 steps. The result
is R(p,c,1,n−2;9,v). For n=5,6,7 use the old C3,C4,C5_s1 rows with
s=1,m=9. For n≥8 use C_large(n−2);C_pair1(c);F_p. These four B rows
and five C compositions close the former 52-step A checkpoint in 166 total
steps. Their complete outputs and clocks are in the secondary table.
General return after unbounded further A-scanner tokens stays open.

For formalization, the secondary entry can first be stated as
R(p,c,2,2;3,(10)^j110100v) reaching R(p,c,1,j+3;9,v) in 62+2j steps,
shift2j. The C5 version uses source(3,5), target j+7 and clock 86+2j.
Then apply the old four-run return rows in that translated frame.

The two earlier standalone packages are imported byte-identically as
`analysis/l17-a-stream` and `analysis/l17-mixed-return`. They are analytic
derivations plus finite evidence. They have not become Lean theorems merely
by entering this repository. The prior `l17-halting/DERIVATION.md` is included
as a reference document, without its separate large backward-search data.

Checks: 924 new endpoints,911 traces, 96 arbitrary-context kernel cases,
33 translated controls in three builds, 16 unit methods, 24 caught faults.
The six finite declarations and gap identity are audited in `VALIDATION.md`.
Universal return, blank reachability and a blank-orbit stack bound stay open.
