# L17: a scanner and uniform returns after arbitrarily many101 pushes

This is an additive follow-up to the halting package. No Lean file or current
GitHub status was changed or checked. Please build these statements against
the same upstream machine semantics as the previous work.

**Main advance:** the old1101 rule stopped at an A head with written left
gaps. We now have exact C returns for every prefix `(101)^j`, every j≥0,
and each terminal00/100/11. The return is linear in j and its endpoint is
compressed by one repetition counter. Mixed01/101 scanning is also exact,
but a general mixed-width return is still open.

The repetition count used in these return inductions is not a global affine
rank for the internal D/G system; the earlier L17k claims are unaffected.

## First add the short paths

All unshown tape contexts are arbitrary. Head coordinates are local.
`kernels.json` gives every read triple and also the reused kernels.

| Name | Input | Entry→exit | Time | Output |
|---|---|---|---:|---|
|A101|[−4,2]:1010101|A0→A3|13|0101010|
|A00L|[−7,1]:0(10)^3 00|A0→C−8|10|1^9|
|A100|[−4,2]:(10)^2 100|A0→C−5|19|1^7|
|Cpop|[−3,0]:0010|C0→C−4|4|1010|
|C6|[−5,0]:010010|C0→C−6|6|111010|
|D6|[−5,0]:010010|D0→D−6|14|101010|

Each path reads only inside its input interval. A101 is K7 plus three A
sweeps; A00L is A00 plus four C sweeps. A100 factors the earlier K60 into
19+41 steps. The literal Cpop/C6/D6 paths are in DERIVATION.md.

Induct on h to get C6 and D6 sweeps over `(010010)^h`, with times6h/14h,
the same displacement−6h, and outputs `(111010)^h`/`(101010)^h`.

## The scanner, including mixed tails

Let a left stack `[r0,…,rk]` denote `(10)^r0 0…0(10)^rk` before A.
The local actions are

    01:  […,n] → […,n+1], time2, shift2;
    101: […,n] → […,n−2,3], time13, shift3.

If the last width starts≥3, it stays≥3. Parse any finite right tape uniquely
into01/101 tokens until00,100 or11, using exterior zeros. This proves only
scanner termination, not return from every terminal stack.

Starting from `[p,c,3]`, `(101)^j` gives `[p,c,1,…,1,3]`, with j width1
runs. General blocks `(01)^z0 101 …101(01)^zj` give
`[p,c,1+z0,…,1+z(j−1),3+zj]`. This identifies the mixed-width boundary.

## Uniform homogeneous returns

Use

    A(p,c;w)=0∞(10)^p0(10)^c0(10)^3 A>w0∞,
    X=111010, p≥6,c≥7.

Every row ends at a blank-left C head at displacement `−2p−2c−8` from A.
The table gives its complete word. The right context v is arbitrary and unread.

| w | Complete target after C> | Time |
|---|---|---:|
|00v|1^(2p−10)(01)^7 1^(2c−13)(01)^7 1^5v|2p+2c+70|
|(101)^(2h+2)00v|1^(2p−10)(01)^7 1^(2c−13)(01)^6 0010 X^h1^9v|2p+2c+102+32h|
|(101)^(2h+1)00v|1^(2p−10)(01)^7 1^(2c−3)010 X^h1^9v|2p+2c+56+32h|
|(101)^(2h)100v|1^(2p−10)(01)^7 1^(2c−3)010 X^h1^7v|2p+2c+52+32h|
|(101)^(2h+1)100v|1^(2p−10)(01)^7 1^(2c−13)(01)^6 0010 X^h1^7v|2p+2c+98+32h|
|(101)^(2h)11v|1^(2p−10)(01)^7 1^(2c−9)(01)^(3h+7)0v|2p+2c+60+40h|
|(101)^(2h+1)11v|1^(2p−6)(01)^(c+3h+9)0v|2p+4c+52+40h|

To avoid natural subtraction in Lean, write p=u+6,c=v+7 (and rename the
right context). Leading exponents become2u+2 or2u+6; the middle exponents
become2v+1,2v+11 or2v+5. The positive-even00 row uses2h+2 so no h−1
appears. X is a six-bit repeated word, not another copy of01.

### Compositions for Lean

In this table j is the number of101 tokens; the first j=2h row includes h=0.

| Case | Kernels/sweeps, in execution order |
|---|---|
|00,j=2h|A101^(2h),A00L,C6^h,K41short,C01^(c−5),K41short,C01^(p−6)|
|00,j=2h+1|A101^(2h+1),A00L,C6^h,Cpop,C01^c,K41short,C01^(p−6)|
|100,j=2h|A101^(2h),A100,C6^h,Cpop,C01^c,K41short,C01^(p−6)|
|100,j=2h+1|A101^(2h+1),A100,C6^(h+1),K41short,C01^(c−5),K41short,C01^(p−6)|
|11,j=2h|A101^(2h),A11,D10^3,D6^h,K22,C01^(c−3),K41short,C01^(p−6)|
|11,j=2h+1|A101^(2h+1),A11,D10^3,D6^h,J1K,D10^c,K22,C01^(p−4)|

All reads lie within `[−2p−2c−8,3j+t−1]`, where t is terminal length.
Thus no v bit is read. Keep every internal zero, especially0010 in the
positive-even00 and odd100 endpoints.

## Original1101 C returns

Prepend your earlier

    Ccal(a;(10)^c1101w) → A(a−1,c;w),

time2a+2c+28, displacement2a+2c+4. With a≥7,c≥7, substitute p=a−1
above. Every overall displacement is−2. Overall times, in the seven table
rows' order, are:

    4a+4c+96;
    4a+4c+128+32h;
    4a+4c+82+32h;
    4a+4c+78+32h;
    4a+4c+124+32h;
    4a+4c+86+40h;
    4a+6c+78+40h.

These are exact guarded formulas for all parameters, derived from the fixed
paths; the finite comparator checks are cross-checks, not their proof.

## Next boundary and checks

The mixed tokens01,101,01,101 from `[6,7,3]` give `[6,7,2,2,3]` in30
steps, shift10. A00L then leaves C at coordinate2 after40 total steps,
with local six-bit input001010 and right1^9. It is not the C6 pattern010010,
Cpop input, or a six-pair K41 input. The literal example with context001101
returns to a C-section in166 steps at head−34, but no all-parameter width2
formula is supplied. Mixed widths2–5 are the next specific derivation task.

992 endpoints pass C++ and Python;905 complete read traces agree. The29
translated controls agree in O2/O0/UBSan.15 tests and20 planted mistakes
pass. All new statements remain unformalized in Lean. No blank reachability,
global stack bound, unrestricted A-return theorem or nonhalting is claimed.
