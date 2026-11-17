# The short-buffer B dispatcher

Use the literal L17 machine
`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`.
Times count defined transitions; F reading1 performs no transition.

Write P_n=(01)^n, T=P_7 111, H_p=1^(2p−10)P_7. A C-section
`Ccal(0;w)` means a blank left tape, C scanning the first cell of w.
An intermediate C or A configuration need not be a C-section.

## Source and coordinates

The B source has written word

    (10)^p 0(10)^c 0(10) P_n B>terminal v

where B scans the first symbol of `terminal`, at coordinate0. Put
L=2p+2c+2n+4. The first cell of the written word is at−L; all cells
to its left are zero. In the following table p≥6,c≥7. The arbitrary
context v is never read. These are sufficient guards, not minimal ones.

The seven rows give whole tapes, not just a right suffix. In each of the
first six rows the result is `Ccal(0;target)`, with C at−L.

| Terminal / guard | Complete target word | Defined transitions |
|---|---|---:|
|0, n≥5|H_p 1^(2c−3) 010 1^(2n+1) v|2p+2c+2n+34|
|111, n≥5|1^(2p−6) P_(c+n+6) 0v|2p+4c+4n+28|
|1100, n=5|H_p 1^(2c−9) P_10 111v|2p+2c+98|
|1100, n=6|H_p 1^(2c−13) P_6 0011 P_5 111v|2p+2c+114|
|1100, n=7|H_p 1^(2c−3) P_9 111v|2p+2c+94|
|1100, n≥8|H_p 1^(2c−3) 010 1^(2n−13) T v|2p+2c+2n+80|
|1101, n≥5|(10)^p0(10)^c0(10) P_(n−2) 00(10)^3 A>v|14|

The last row has A at4; its word still begins at−L. It is a typed exit,
not a return theorem. In particular its two consecutive zeros must remain.
All full-return rows read within[−L,len(terminal)−1]. The last row reads
within[−4,3]. The final C/A head cell can be unread at the endpoint.

## Derivation from contextual rules

The previously established framed sweeps cost2/4/2/2 transitions per
C/D/A/B pair. Use the transfers from `../l17-mixed-return/DERIVATION.md`:

    F_p = K41short; C01^(p−6), cost2p+29.
    E_p = K22; C01^(p−4), cost2p+14.

F_p finishes a bottom10 run from a C head at its last0 with a111 right
prefix. E_p finishes the corresponding D gap. Both require the blank
left exterior used here; they are not operations on an arbitrary stack.

| Row | Composition |
|---|---|
|0|B0; C01^n; C_pair1(c); F_p|
|111|B_to_D(n); D_pair1(c,n+1); E_p|
|1100,n=5|B1100_n5; C01^(c−3); F_p|
|1100,n=6|B1100_n6; C01^(c−5); F_p|
|1100,n=7|B1100_n7; C01^c; F_p|
|1100,n≥8|B1; K60T; C01^(n−7); C_pair1(c); F_p|
|1101|B1; K7; A01^3|

For example, the0 row costs
1+2n+(2c+4)+(2p+29). Its intermediate right word after C_pair1 is
1^(2c+1)0101^(2n+1)v. F_p and the literal equality
`(10)^h1=1(01)^h` give the stated target. The111 row costs
(4n+4)+(4c+10)+(2p+14). The large1100 row uses K60T only when
at least eight alternating pairs are available to its left.

The three short1100 rows use new finite paths. With entry B at0, each
reads exactly the indicated closed interval and exits C one cell to its
left. Outside tape is arbitrary and unchanged.

| Kernel | Input on read interval | Interval | Output on interval | Time / exit |
|---|---|---|---|---|
|B1100_n5|0(10)^3 0(10)P_5 1100|[−20,3]|(10)^10 1111|75 / C−21|
|B1100_n6|0(10)^5 0(10)P_6 1100|[−26,3]|1P_6 0011 P_5 111|95 / C−27|
|B1100_n7|00(10)P_7 1100|[−18,3]|(10)^9 1111|65 / C−19|

For n=5,6,7 respectively, the remaining C sweeps use c−3,c−5,c pairs.
For n=6, the right word before F_p is
1^(2c−9)P_6 0011 P_5 111v. Its zero gap is internal even at c=7.
These fixed paths and sweep inductions justify the formulas for all
guarded parameters. The coefficients are not promoted from fitted data.
Literal read triples are retained in `kernels.json`.

`B1101` is also a finite path: input P_2 1101 on[−4,3], output00(10)^3,
time14, exit A4. The two older C→B entry kernels, C2B38 and C5B62,
are framed again. These six finite paths are stated separately in
`link/CryptidLink/L17l.lean`; their exact execution claims are distinct
from formalizing the whole parametric table above.

## The apparent mixed gap and a second return subfamily

The literal identity

    P_m 00 = 0(10)^m0

rewrites the A exit's complete left word as the five-run stack

    (10)^p0(10)^c0(10)^1 0(10)^(n−2)0(10)^3.

This is in the general 10-run scanner grammar. The older homogeneous
return theorem has only three initial runs, so its full return formulas
cannot be substituted unchanged. The existing scanner itself does apply.
`short_gap_rotation` in `L17l.lean` formalizes the identity for every m
and arbitrary right context, using the already-proved `rotLB0`.

If the next two cells are 00, A00L takes 10 steps and leaves the earlier
four-run C source R(p,c,1,n−2;9,v). Thus four additional B-return rows
cover terminal 110100:

| Guard | Complete C target at−L | Total time from B |
|---|---|---:|
|n=5|H_p 1^(2c−9) P_9 0 1^6v|2p+2c+102|
|n=6|H_p 1^(2c−13) P_6 0011 P_4 0 1^6v|2p+2c+118|
|n=7|H_p 1^(2c−3) P_8 0 1^6v|2p+2c+98|
|n≥8|H_p 1^(2c−3) 010 1^(2n−13) P_6 0 1^6v|2p+2c+2n+84|

All read within[−L,5], never into v. The first three are B1101;A00L;
the old C3/C4/C5_s1 row with s=1,m=9. For n≥8, put r=n−2≥6:
B1101;A00L;C_large(r);C_pair1(c);F_p. Its clock is
14+10+(2r+31)+(2c+4)+(2p+29). Six of the nine known ones remain
unread in every target, explaining the 1^6 suffix.

These four secondary rows overlap the earlier typed1101 exit on purpose:
they continue it when its context begins00. They are not four additional
disjoint terminal classes.

## Dispatcher and composition with the earlier C exits

B changes a leading `(10)^j` into P_j in2j transitions and shifts2j.
This joins P_n on its left to make P_(n+j). Every finite right word with
zero exterior has exactly one first terminal0,111,1100 or1101 after this
scan. A final written1 can pair with an exterior0; it must not be dropped
from the scan. The classifier has this convention explicitly.

In the four-run notation of the previous handoff, begin at R(p,c,s,r;3,w),
with C scanning the last0 of the final10 run:

* r=2,s=2: C2B38 leaves the B source above with n=5 and B at4.
* r=5,s=3: C5B62 leaves the same shape with n=9 and B at4.

If w=(10)^j terminal v, add2j and use n=5+j or9+j in the table.
Add the entry clock 38 or62. A C-return finishes at the original word's
first cell; an1101 exit finishes A at 8+2j. The context v is unread.
`claims.json` records eleven primary composed rows, including the three
separate j=0,1,2 cases on the C2/1100 branch. This partitions the finite
right tape for these two guarded source shapes into six C-return cases
and one typed A exit, rather than assuming a longer one buffer. Five more
compositions add the secondary 110100 returns, giving 16 composed rows and
11 B rows in total.

More explicitly, the secondary entry alone gives

    R(p,c,2,2;3,(10)^j110100v) → R(p,c,1,j+3;9,v),

in 62+2j steps with head shift2j. For C5 replace(2,2) by(3,5), j+3 by
j+7, and 62 by 86. This is just C2B/C5B;B10^j;B1101;A00L followed by
the gap identity. It exposes the precise four-run source to which the
return rows apply, without hiding a change of head frame.

## The saved frontier and the remaining obstruction

The source in `../l17-mixed-return/next-boundary.json` is
R(6,7,2,2;3,001101). Here j=0, terminal0, v=01101. It reaches

    Ccal(0; 11 P_7 1^11 010 1^11 01101)

in 108 defined transitions, with head−36. The maximum read position is4:
only the first0 of the old arbitrary context has been consumed. The
remaining01101 is untouched. `frontier.json` retains the exact endpoint.

For the same counters but w=1101001101, the primary dispatcher first reaches

    (10)^6 0(10)^7 0(10) P_3 00(10)^3 A>001101

in 52 transitions, A at 8. The last context begins at 8 and was not read.
It begins00, so the secondary rule returns to C at −36 in 166 total steps,
with word H_6 1^5 P_9 0 1^6 1101. The residual1101 is unread.
`joined-frontier.json` records this endpoint. The 52-step checkpoint is
valid, but labelling it an uncovered return boundary was wrong; review
found the gap identity before publication.

`next-boundary.json` instead records a five-run A entry with context
101001101. The existing A scanner can consume its leading101 and grow
the run list. This table does not supply a return for arbitrary further
scanner tokens. The remaining obligation is a general return analysis
of that five-run family, not a claim that no existing rule can advance
this particular example. None of these sources is asserted reachable
from blank. No global stack bound or halting decision follows.

## Verification scope

The fixed confirmatory seed is17112028. The campaign compares 924 full
endpoints and 911 full read traces between a frozen C++ literal machine
and a separate frozen Python table. It includes 96 kernel instances with
random tape on both sides. Twenty-four planted faults are caught; 33 translated
controls agree in O2,O0 and UBSan builds. Same-author implementations and
compiler modes are controls, not external replication.

Exploratory Python probes preceded the recorded protocol. The first C++
attempt was rejected for marking requests longer than1000 steps for full
trace output. That transport flag was corrected; a conservative152956
transition upper bound for that invocation is charged in the budget ledger.
The first prefix-partition test also needed to account for an exterior0
after a final written1. Neither correction changed a mathematical row.
