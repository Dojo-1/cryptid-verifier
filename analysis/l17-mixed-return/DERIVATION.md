# Mixed small-width returns for L17

These are guarded mathematical compositions and bounded execution checks,
not new Lean theorems. The literal machine is
`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`.
An undefined transition performs no write or move and counts as zero defined
transitions. All times below count defined transitions.

## 1. The exact source and its coordinate frame

Let R(p,c,s,r;m,v) have zero exterior and written word

    (10)^p 0(10)^c 0(10)^s 0(10)^r 1^m v,

with C scanning the **last0 of the final10 run**. That head is coordinate0.
The first symbol of the word is at

    -B, where B=2p+2c+2s+2r+2.

Thus this source has a nonblank left tape. It is not a Ccal section. The
complete returns in Section4 end with C at−B and a blank left tape. Every
displayed target word starts on that final C head. The finite right context
v is arbitrary; only the stated initial3/6/9 ones are read. Extra leading
ones and v are carried through exactly. The guards are sufficient; no claim
of minimal necessary guards is made.

## 2. Why widths2 and5 bounce right

The local unknown-read probe starts at C on the final0, fixes the preceding
zero gap and preceding run's last0, then fixes three right ones. Before the
first unknown read, widths2,3,4,5 reach B,A,C,D respectively. An unknown-read
boundary is a local exit, not a completed blank-left section.

The following framed finite paths make those exits useful. Coordinates are
relative to the entry head0. Every cell outside the input interval is
arbitrary and unchanged; all reads stay in the interval. `kernels.json`
retains every literal read triple.

| Kernel | Required input | Entry→exit | Time | Complete output on interval |
|---|---|---|---:|---|
|C2B|[−6,3]:1001010111|C0→B4|38|(01)^5|
|C3D|[−8,3]:100101010111|C0→D−9|33|(10)^6|
|C4|[−9,3]:0010101010111|C0→C−10|32|1011010101010|
|C5D|[−11,3]:001010101010111|C0→D−12|42|(01)^7 0|
|C5B|[−14,3]:(10)^2 0(10)^5 111|C0→B4|62|(01)^9|
|Dgap0|[−3,2]:100010|D0→A2|14|010100|

C2B needs one pair of the previous run. C5B needs two. For previous width1,
use C5D followed by D1,E0,B0 instead: on local input001 this3-step path
writes101 and exits C three cells to the left. C3D includes the3-step A11
finish after the30-step local C3 exit. None of these finite paths reads the
context after the first three right ones.

B4 is genuinely a rightward exit. A purported ranking by a head coordinate
decreasing at every local row would fail here. Phase and buffer conditions
must be part of the state.

## 3. Framed transfer lemmas

These nine statements are the modular proof pieces. Their source and target
words occupy the same interval; an exit outside it does not mean its outside
context is blank. Put P_n=(01)^n. The right context after the input word is
arbitrary and unread. The full declarations with coordinates are in claims.json.

| Name / guards | Input word | Entry→exit | Time | Output word |
|---|---|---|---:|---|
|C_large(r),r≥6|0(10)^r111 on[−2r,3]|C0→C(−2r−1)|2r+31|1^(2r−9)P_6 0|
|C_pair1(s),s≥1|0(10)^s0(10) on[−2s−3,0]|C0→C(−2s−4)|2s+4|1^(2s+1)010|
|C_pair4(s),s≥1|0(10)^s0(10)^4 111 on[−2s−9,3]|C0→C(−2s−10)|2s+32|1^(2s+1)011P_4 0|
|B_to_D(n),n≥1|P_n111 on[−2n,2]|B0→D(−2n)|4n+4|0(10)^(n+1)|
|D_large(r,n),r≥4,n≥2|0(10)^r0(10)^n on[−2r−1,2n]|D0→C(−2r−2)|2r+16|1^(2r−5)P_(n+3)0|
|D_pair1(s,n),s,n≥1|0(10)^s0(10)0(10)^n on[−2s−4,2n]|D0→D(−2s−4)|4s+10|0(10)^(s+n+2)|
|D_pair2(s,n),s,n≥1|0(10)^s0(10)^2 0(10)^n on[−2s−6,2n]|D0→C(−2s−7)|2s+13|1^(2s+1)P_1 1 P_(n+1)0|
|D_three_B(n),n≥1|(10)^2 0(10)^3 0(10)^n on[−11,2n]|D0→B(2n+1)|2n+37|P_(n+6)|
|D_zero_turn(c,n),c,n≥1|(10)^c00(10)^n111 on[−2c−1,2n+3]|D0→D−3|6n+25|(10)^(c−1)0(10)^(n+3)|

They compose as follows, using the previously established C01/D10/A01/B10
sweeps (2/4/2/2 steps per pair):

    C_large(r): K41short; C01^(r−5).
    C_pair1(s): Cpop; C01^s.
    C_pair4(s): C4; C01^s.
    B_to_D(n): B111; D10^(n−1).
    D_large(r,n): K22; C01^(r−3).
    D_pair1(s,n): J1K; D10^s.
    D_pair2(s,n): J2K; C01^s.
    D_three_B(n): J3K; B10^(n−1).
    D_zero_turn(c,n): Dgap0; A01^n; A11; D10^(n+2).

The B111 starter is8 steps (B1,A1,E1,F0,D0,A1,E1,F0). With its left cell1,
it maps1111 on[−1,2] to1010 and ends at D−2. Existing J1K/J2K/J3K,
K22,K41short are also included and framed again in the new kernel data.

D_zero_turn handles an empty run between two zero gaps. Its A scan consumes
the first of the three right ones; A11 consumes the other two. It changes
phase back to D with head−3, reduces the indicated left width by1, and raises
the indicated right width by3. It is a typed local transfer, not a repeated
global descent rule. Afterward the gap type has changed.

For each transfer, induction on its sweep count proves the variable-length
part. Fixed paths never read their exterior. Literal word equalities identify
the next required window. No numerical interpolation is used for the
coefficients. Random outside-context checks test this framing implementation.

## 4. Complete guarded four-run returns

In the following table p≥6,c≥7; s and the sufficient number t of right ones
are specified per row. Define

    H_p=1^(2p−10)P_7, V_t=1^(m−t)v, m≥t.

Every endpoint is Ccal(0;target), head at−B. Internal zero gaps remain literal.

| r | s / t | Complete target word | Time |
|---:|---|---|---:|
|2|s=1,t=9|H_p1^(2c−11)P_12 0V_9|2p+2c+166|
|2|s=2,t=6|1^(2p−6)P_(c+11)0V_6|2p+4c+86|
|2|s=3,t=6|H_p1^(2c−3)P_1 1P_7 0V_6|2p+2c+104|
|2|s=4,t=9|H_p1^(2c−13)P_16 0V_9|2p+2c+204|
|2|s≥5,t=6|H_p1^(2c−13)P_6 0 1^(2s−10)P_9 0V_6|2p+2c+2s+136|
|3|s≥1,t=3|H_p1^(2c−9)P_(s+8)0V_3|2p+2c+4s+74|
|4|s≥1,t=3|H_p1^(2c−13)P_6 0 1^(2s−2)011P_4 0V_3|2p+2c+2s+92|
|5|s=1,t=3|H_p1^(2c−3)P_8 0V_3|2p+2c+74|
|5|s=2,t=9|H_p1^(2c−11)P_16 0V_9|2p+2c+230|
|5|s=3,t=6|1^(2p−6)P_(c+15)0V_6|2p+4c+126|
|5|s=4,t=6|H_p1^(2c−3)P_1 1P_11 0V_6|2p+2c+144|
|5|s=5,t=9|H_p1^(2c−13)P_20 0V_9|2p+2c+268|
|5|s≥6,t=6|H_p1^(2c−13)P_6 0 1^(2s−12)P_13 0V_6|2p+2c+2s+174|

In particular, with nine right ones all s≥1 and r=2,3,4,5 are covered for
this **four-run source shape**. This is not a claim for an arbitrarily long
mixed stack, or a buffer with fewer ones. At s=5 in the C2 large row and
s=6 in the C5 large row a middle exponent is0; the adjacent zero must stay.

### Composition table for formalization

Define bottom finishes

    F_p=K41short; C01^(p−6), time2p+29;
    E_p=K22; C01^(p−4), time2p+14.

F_p starts at the final0 of the bottom10 run with a111 right prefix.
E_p starts at a D gap after that bottom run. They reach the first cell of
the bottom run; its left exterior is blank in the full source.

| Row | Exact execution order |
|---|---|
|C2,s1|C2B; B_to_D(5); D_zero_turn(c,6); D_large(c−1,9); F_p|
|C2,s2|C2B; B_to_D(5); D_pair1(c,6); E_p|
|C2,s3|C2B; B_to_D(5); D_pair2(c,6); F_p|
|C2,s4|C2B; B_to_D(5); D_three_B(6); B_to_D(12); D_large(c−2,13); F_p|
|C2,s≥5|C2B; B_to_D(5); D_large(s−1,6); C_large(c); F_p|
|C3|C3D; D10^(s−1); D_large(c,s+5); F_p|
|C4|C4; C01^s; C_large(c); F_p|
|C5,s1|C5D; D1,E0,B0; C01^c; F_p|
|C5,s2|C5B; B_to_D(9); D_zero_turn(c,10); D_large(c−1,13); F_p|
|C5,s3|C5B; B_to_D(9); D_pair1(c,10); E_p|
|C5,s4|C5B; B_to_D(9); D_pair2(c,10); F_p|
|C5,s5|C5B; B_to_D(9); D_three_B(10); B_to_D(16); D_large(c−2,17); F_p|
|C5,s≥6|C5B; B_to_D(9); D_large(s−2,10); C_large(c); F_p|

The first B_to_D uses three more original ones after C2B/C5B used three.
An additional D_zero_turn or second B_to_D consumes three more, explaining
the sufficient3/6/9 prefix guards. After that all reads are in material
already written by these paths or in the known left runs.

For example C2,s2 takes

    38+24+(4c+10)+(2p+14)=2p+4c+86.

C5,s5 takes

    62+40+57+68+(2c+12)+(2p+29)=2p+2c+268.

The corresponding framed outputs give exactly the table words. C_large
may leave only three leading ones; this is why the theorem does not say its
outputs automatically satisfy a nine-one guard for a later reduction.

## 5. The saved166-step example becomes a uniform lemma

Put S=01·101·01·101. From

    0∞(10)^p0(10)^c0(10)^3 A>S00v0∞,

the previous exact scanner takes30 steps and shifts10, producing left widths
`[p,c,2,2,3]`. A00L adds10 steps and leaves C at coordinate2, with left
widths p,c,2,2 and nine right ones. Apply the C2,s2 row. The resulting
blank-left C head is at−(2p+2c+8), with complete word

    1^(2p−6)(01)^(c+12)1^2 v,

in2p+4c+126 steps. The final pair joins by the literal word equality
`0111=(01)11`; no transition is hidden.

This particular composition uses E_p, not F_p. Its sufficient guards weaken
to **p≥4,c≥1**, because K22 needs four bottom pairs and D_pair1 needs only
one previous pair. Sixteen additional literal guard-corner checks cover
p=4,5 and c=1,2 from both A and original C sources. They are supplementary,
separate from the main846 cases.

Prepend the previously derived1101 entry with a=p+1. For **a≥5,c≥1**:

    Ccal(a;(10)^c1101 S00v)
      → Ccal(0;1^(2a−8)(01)^(c+12)1^2 v)

in **4a+6c+152** steps, head displacement **−2**. The right context v is
never read. The containing read bound is[−2,2a+2c+15]. At a=7,c=7 this
is222 steps. Removing the1101 entry gives the earlier p=6,c=7 A witness's
166 steps. At a=5,c=1 it is178 steps.

## 6. What remains open

The original width2 boundary is now covered. The new theorem covers four
left runs with sufficient buffers, not every stack produced by arbitrary
mixed scanning. Earlier C_large can generate only three leading ones, and
C_pair1 can also generate three, so a future small-width bounce may fail a
six/nine-one premise. Longer stacks can contain multiple small widths before
the two large bottom runs. Their typed A/B/C/D exits remain relevant.

The next bounded task is to dispatch widths2/5 when the following buffer has
only3–5 ones, using the actual next bits rather than assuming more ones.
The framed transfer table exposes those entry modes but does not establish
a global termination rank, closed infinite counter calculus, blank reachability,
or a stack-depth bound on the blank orbit.

## 7. Checks and proof status

All846 main endpoints agree between frozen C++ and separate Python raw paths;
840 have identical complete traces. The main count contains512 four-run
returns,150 framed transfers,144 random outside-context kernel checks and
40 named mixed A/C compositions. The16 supplementary low-guard cases are
separate. The42 matched translated controls agree in O2,O0 andUBSan. All16
unit tests and20 planted in-memory mutations pass. Maximum main raw time is
1,188, below200,000; the cumulative C++ ledger is185,089, below20 million.

The all-parameter identities come from the finite paths and sweep inductions,
not from interpolating those numerical results. All code paths here share
an author. No new Lean proof/build or blank-orbit extension is claimed.
