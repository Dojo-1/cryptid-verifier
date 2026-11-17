# L17 A-stream: an exact scanner and an unbounded return family

This continues the preceding `1101` handoff. No Lean code or repository was
modified. The statements below are mathematical compositions of fixed paths
and sweep inductions, accompanied by bounded literal checks. They have not
been built as Lean theorems here.

The machine is `1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`.
Undefined F1 performs no write or move and counts as zero defined steps.
Both exterior tapes are zero. A word before a marked head is actual written
tape, not a counter-section abbreviation. Every interior0 must be retained.

## 1. A scanner for arbitrary finite tails

Suppose the A head has at least two10 pairs immediately to its left. Then:

    L(10)^n A>01v  → L(10)^(n+1) A>v, in2 steps;
    L(10)^n A>101v → L(10)^(n−2)0(10)^3 A>v, in13 steps.

The first rule is A0,B1. The second is the old K7 followed by three A01
sweeps. It reads positions−4…2 relative to its initial A head, changes
`(10)^2 101` into `0(10)^3`, and moves the head3 cells right. It never reads v.
Its full13-step path is in `kernels.json`.

Represent the left word by runs `[r0,…,rk]`, meaning

    (10)^r0 0(10)^r1 0 … 0(10)^rk.

The two scanning tokens act as:

    01:  […,n] → […,n+1], time2, displacement2;
    101: […,n] → […,n−2,3], time13, displacement3.

Starting with last width at least3 preserves positive widths on all inserted
internal runs and last width at least3. The arbitrary finite right tail has
a unique parsing into a word of tokens01/101 followed by one of00,100,11.
Indeed, first bit0 distinguishes00/01; first bit1 distinguishes11/10, and
the third bit distinguishes100/101. Exterior zeros guarantee termination
of the parsing. This is parsing termination, not a nonhalting theorem about
the subsequent machine computation. The scanner itself cannot halt because
each token is a complete defined fixed path.

If there are z tokens01 and j tokens101, scanner time is2z+13j and
displacement2z+3j. The compiler preserves every gap and the exact unchanged
right context. `scanner.py` uses run counters. The result critic independently
uses literal word substitution, removing the final1010 and appending0101010
for a101 token; it does not import the counter-stack compiler.

### Exact left-stack normal form

Starting from `[p,c,3]`, write a parsed token string as

    (01)^z0 101 (01)^z1 101 … 101 (01)^zj.

For j≥1 its exact resulting stack is

    [p,c,1+z0,1+z1,…,1+z(j−1),3+zj].

For j=0 it is `[p,c,3+z0]`. This follows directly by induction on the
tokens and also shows that mixed scans can create every positive internal
width. In particular a fixed number of left gaps cannot describe all these
generic A inputs. No blank-orbit occurrence is inferred.

For the homogeneous prefix `(101)^j`, this specializes to

    [p,c,1,…,1,3] with exactly j inserted width1 runs.

For j≥1 the written left word is

    (10)^p0(10)^c0 10(010)^(j−1)0(10)^3.

The arbitrarily long stack is therefore compressed by one repetition counter.
The next section returns every member of this family to a blank-left C-state.

## 2. Fixed return kernels

All coordinates are relative to the entry head0. Outside the given interval,
both tape contexts are arbitrary and remain unchanged. All read triples are
retained in `kernels.json`.

| Kernel | Input interval and word | Entry→exit | Steps | Output | Actual reads |
|---|---|---|---:|---|---|
|A101|[−4,2]:1010101|A0→A3|13|0101010|[−4,2]|
|A00L|[−7,1]:0(10)^3 00|A0→C−8|10|1^9|[−7,1]|
|A100|[−4,2]:(10)^2 100|A0→C−5|19|1^7|[−4,2]|
|Cpop|[−3,0]:0010|C0→C−4|4|1010|[−3,0]|
|C6|[−5,0]:010010|C0→C−6|6|111010|[−5,0]|
|D6|[−5,0]:010010|D0→D−6|14|101010|[−5,0]|

A00L is A00 followed by four existing C01 sweeps. A100 is the19-step
initial part of K60: K60 factors as A100 followed by K41short. Cpop,C6,D6
have literal paths:

    Cpop: C0,D1,E0,B0;
    C6:   C0,D1,E0,B0,C1,B0;
    D6:   D0,A1,E1,F0,D0,A0,B1,A1,E0,B0,C0,D1,E1,F0.

Thus induction gives two periodic sweeps. With the input block ending on the
entry head, and its other context untouched:

    C: (010010)^h → (111010)^h, time6h, displacement−6h;
    D: (010010)^h → (101010)^h, time14h, displacement−6h.

They have the same spatial displacement and different raw clocks. Their times
must not be conflated. The h=0 case is identity.

The complete fixed-kernel data also includes old A01,A00,A11,C01,D10,
K41short,J1K,K22, checked again with arbitrary contexts. Useful specifications:

* K41short: C0 on `[−11,3]:(10)^6 111` reaches C−11 in41 steps,
  writing `11(01)^6 0`. A following1 may join its final0 into a seventh pair.
* J1K: D0 on `[−4,2]:0010010` reaches D−4 in10 steps, writing0101010.
* K22: D0 on `[−8,4]:1010101001010` reaches C−8 in22 steps,
  writing `11(01)^5 0`.

## 3. Uniform homogeneous return theorem

Fix p≥6,c≥7, any h≥0, and arbitrary finite context v. Define

    A(p,c;w)=0∞(10)^p0(10)^c0(10)^3 A>w0∞,
    X=111010, and Ccal(0;u)=0∞C>u0∞.

The entry A head is coordinate0. Put B=2p+2c+8, the length of its written
left word. Every return below ends at C at coordinate−B. Thus the entire
left tape is blank at the endpoint. The target word is the complete physical
word starting there. In particular none is only a substring of a larger tape.

| Right input w | Complete C target word | Time from A |
|---|---|---:|
|00v|1^(2p−10)(01)^7 1^(2c−13)(01)^7 1^5 v|2p+2c+70|
|(101)^(2h+2)00v|1^(2p−10)(01)^7 1^(2c−13)(01)^6 0010 X^h 1^9 v|2p+2c+102+32h|
|(101)^(2h+1)00v|1^(2p−10)(01)^7 1^(2c−3)010 X^h 1^9 v|2p+2c+56+32h|
|(101)^(2h)100v|1^(2p−10)(01)^7 1^(2c−3)010 X^h 1^7 v|2p+2c+52+32h|
|(101)^(2h+1)100v|1^(2p−10)(01)^7 1^(2c−13)(01)^6 0010 X^h 1^7 v|2p+2c+98+32h|
|(101)^(2h)11v|1^(2p−10)(01)^7 1^(2c−9)(01)^(3h+7)0v|2p+2c+60+40h|
|(101)^(2h+1)11v|1^(2p−6)(01)^(c+3h+9)0v|2p+4c+52+40h|

This is one all-repetition return statement, split into seven subtraction-free
parameter branches where needed. The first two rows split the even00 case
so that no h−1 repetition appears in the declarations.

### Exact compositions

Let A101^j denote j repetitions of its13-step kernel; C01^r and D10^r
are the previously proved left sweeps, taking2r and4r transitions. The
following compositions prove the table. All repetition counts are nonnegative
under the stated guards.

| Terminal, parity | Fixed kernels and sweeps in execution order |
|---|---|
|00, j=2h|A101^(2h); A00L; C6^h; K41short; C01^(c−5); K41short; C01^(p−6)|
|00, j=2h+1|A101^(2h+1); A00L; C6^h; Cpop; C01^c; K41short; C01^(p−6)|
|100, j=2h|A101^(2h); A100; C6^h; Cpop; C01^c; K41short; C01^(p−6)|
|100, j=2h+1|A101^(2h+1); A100; C6^(h+1); K41short; C01^(c−5); K41short; C01^(p−6)|
|11, j=2h|A101^(2h); A11; D10^3; D6^h; K22; C01^(c−3); K41short; C01^(p−6)|
|11, j=2h+1|A101^(2h+1); A11; D10^3; D6^h; J1K; D10^c; K22; C01^(p−4)|

For00 even, the C6 sweep leaves the right word `X^h1^9v`. K41short removes
its first three1s and writes its final0. For h=0 the following six1s join
one01 pair and leave five1s. For h≥1 the remaining word is
`010 X^(h−1)1^9v`, giving the explicit0010 in the second row. It cannot
be trimmed. The odd100 row has the same mechanism with `X^(h+1)1^7v`.

For the odd Cpop branches, the Cpop kernel followed by C01^c leaves a
leading run `1^(2c+1)` followed by010 and the periodic suffix. K41short
consumes four of those1s after the following01 join, leaving2c−3.

For11 even, D6 writes three10 pairs per pair of gaps. K22 and the following
C sweep give the remaining `(01)^(3h+7)0v`. For11 odd, J1K and D10^c
give the input to K22 with the first hole removed, yielding one alternating
block of width c+3h+9. These are word equalities between successive framed
endpoints, not fitted recurrences. Every kernel's next required bits occur
in the displayed scanner normal form or the preceding output. Guards p≥6,
c≥7 ensure the final K41 inputs and C sweep counts exist. At c=7 the relevant
leading run has five1s, enough for the short41-step kernel and its01 join.

Adding the path lengths in each row gives its stated polynomial. For example
00 even has

    26h+10+6h+41+2(c−5)+41+2(p−6)
      =2p+2c+70+32h.

The odd11 row has

    13(2h+1)+3+12+14h+10+4c+22+2(p−4)
      =2p+4c+52+40h.

No path reads v. If j is its number of101 tokens and t its terminal length,
all reads are contained in `[−B,3j+t−1]`. This bound includes the endpoint
head for simplicity; it is a safe containing interval, not a claim every
cell of it is read.

## 4. Back to the original C-section1101 branch

The preceding handoff established, for a,c≥1:

    Ccal(a;(10)^c1101w)
      → A(a−1,c;w),

in2a+2c+28 steps, A-head displacement2a+2c+4. The A left word has length
2a+2c+6. For a≥7,c≥7, apply any uniform return row with p=a−1.
The overall head displacement is therefore−2. The complete target words
are those in the table after substituting p=a−1.

Overall times from the original C entry are:

| w | Time |
|---|---:|
|00v|4a+4c+96|
|(101)^(2h+2)00v|4a+4c+128+32h|
|(101)^(2h+1)00v|4a+4c+82+32h|
|(101)^(2h)100v|4a+4c+78+32h|
|(101)^(2h+1)100v|4a+4c+124+32h|
|(101)^(2h)11v|4a+4c+86+40h|
|(101)^(2h+1)11v|4a+6c+78+40h|

These extend1101 from an A-entry lemma to an exact C-return theorem for
an unbounded family. A regular repeated block X^h compresses many gaps;
having many geometric layers does not force many independent counters in
this subfamily. It does not establish a finite counter system for all tails.

## 5. The precise next boundary

Take initial stack `[6,7,3]` and tokens01,101,01,101. The scanner gives
`[6,7,2,2,3]` in30 steps, displacement10. A00L then gives C at source
coordinate2 after40 total steps, with local window `[−5,0]:001010` and
right prefix1^9. The homogeneous C6 input010010 does not occur; Cpop and
the six-pair K41 input do not occur either. This is a concrete missing
width2 return case, not a counterexample to the guarded table.

A literal run of this one input with context001101 returns to a blank-left
C-section after166 steps, head−34. That finite result is in
`mixed-boundary.json`; no uniform mixed-width formula is inferred from it.
The analogous arbitrary mixed scanner can create widths2–5 and larger.
Their return rules remain the next task. The statement that all A exits
return, all stacks terminate, or all blank-orbit stack depth is bounded
remains open.

## 6. Validation and evidence boundary

The main campaign checks992 endpoints:625 guarded return inputs,56 direct
original-C1101 compositions,143 mixed scanner prefixes and168 arbitrary-
context kernel instances. Every endpoint agrees with the C++ raw interpreter
and the separate Python raw table;905 have identical full read traces.
The longest probe is4,542 raw steps, below the200,000 cap. The29 matched
translated controls pass O2,O0 andUBSan with identical complete outcomes.
All15 unit tests and20 planted in-memory mutations pass their decision gates.

The general statements rest on the finite framed paths and their induction/
composition, not on those finite counts. Same-author code paths are not
external replication. No new Lean proof, new blank-tape prefix or halting
decision is claimed. The initial exploratory63 probes use n=3,4,8, but the
uniform table deliberately fixes the final A run to3; its extension to other
run widths is not silently assumed. The96-token cap applies to arbitrary
mixed scanner probes; the separate homogeneous return sample uses h≤95,
so its largest j is192. These are two different test families.
