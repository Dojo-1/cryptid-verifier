# L17: the mixed width2 boundary now returns uniformly

No Lean file or GitHub status was changed here. This package supplies framed
paths and mathematical compositions ready for the same machine semantics.

## Main lemma to formalize first

Let S=01·101·01·101. For a≥5,c≥1 and any right context v:

    Ccal(a;(10)^c1101 S00v)
      reaches Ccal(0;1^(2a−8)(01)^(c+12)1^2 v).

Exact time **4a+6c+152**, head displacement **−2**, reads contained in
[−2,2a+2c+15]. No bit of v is read. This closes the saved mixed boundary,
including its a=7,c=7 specialization in222 original-C steps. The old A-state
example takes166 steps at p=6,c=7; its general A time is2p+4c+126.

The proof is: old1101 entry; scanner tokens01,101,01,101 (30 steps);
A00L (10 steps); new C2,s2 return. The last piece is

    C2B; B_to_D(5); D_pair1(c,6); K22; C01^(p−4),

with p=a−1. Its time is38+24+(4c+10)+22+2(p−4)=2p+4c+86.
It needs p≥4,c≥1, so no seven-pair guard is required for this particular
lemma. Sixteen separate lower-corner A/C checks cover p=4,5 and c=1,2.

## New finite paths

Both outside contexts are arbitrary and unchanged. `kernels.json` contains
all reads, including the reused J/K/sweep kernels.

| Kernel | Input | Entry→exit | Time | Output |
|---|---|---|---:|---|
|C2B|[−6,3]:1001010111|C0→B4|38|(01)^5|
|C3D|[−8,3]:100101010111|C0→D−9|33|(10)^6|
|C4|[−9,3]:0010101010111|C0→C−10|32|1011010101010|
|C5D|[−11,3]:001010101010111|C0→D−12|42|(01)^7 0|
|C5B|[−14,3]:(10)^2 0(10)^5 111|C0→B4|62|(01)^9|
|Dgap0|[−3,2]:100010|D0→A2|14|010100|

C2B consumes one pair of the preceding run; C5B needs two. The width1
previous-run case uses C5D then D1,E0,B0 instead. B4 is a rightward scan
exit, not a blank-left C endpoint. Keep these phases explicit.

## Nine framed variable transfers

These are named exactly as in claims.json and DERIVATION.md:

    C_large(r) = K41short; C01^(r−5).
    C_pair1(s) = Cpop; C01^s.
    C_pair4(s) = C4; C01^s.
    B_to_D(n) = B111; D10^(n−1).
    D_large(r,n) = K22; C01^(r−3).
    D_pair1(s,n) = J1K; D10^s.
    D_pair2(s,n) = J2K; C01^s.
    D_three_B(n) = J3K; B10^(n−1).
    D_zero_turn(c,n) = Dgap0; A01^n; A11; D10^(n+2).

D_zero_turn acts on `(10)^c00(10)^n111`, with D scanning the second gap0:
in6n+25 steps it writes `(10)^(c−1)0(10)^(n+3)` and exits at D−3.
The current gap type changes; this is not by itself a global descent rank.

## Thirteen complete returns

For p≥6,c≥7,s≥1, put C at the final0 in

    0∞(10)^p0(10)^c0(10)^s0(10)^r 1^m v0∞.

The source head is0. For r=2,3,4,5 and m≥9 every s is covered by the
table in DERIVATION.md. Some branches need only3 or6 right ones. All returns
end at the first cell of the bottom10 run with a blank left tape. Their
complete target words and times are in the13-row table and claims.json.
This is a four-run theorem, not a theorem for arbitrarily long mixed stacks.

For formalization define F_p=K41short;C01^(p−6) and
E_p=K22;C01^(p−4). Then:

| Row | Composition |
|---|---|
|C2,s1|C2B;B_to_D(5);D_zero_turn(c,6);D_large(c−1,9);F_p|
|C2,s2|C2B;B_to_D(5);D_pair1(c,6);E_p|
|C2,s3|C2B;B_to_D(5);D_pair2(c,6);F_p|
|C2,s4|C2B;B_to_D(5);D_three_B(6);B_to_D(12);D_large(c−2,13);F_p|
|C2,s≥5|C2B;B_to_D(5);D_large(s−1,6);C_large(c);F_p|
|C3|C3D;D10^(s−1);D_large(c,s+5);F_p|
|C4|C4;C01^s;C_large(c);F_p|
|C5,s1|C5D;D1,E0,B0;C01^c;F_p|
|C5,s2|C5B;B_to_D(9);D_zero_turn(c,10);D_large(c−1,13);F_p|
|C5,s3|C5B;B_to_D(9);D_pair1(c,10);E_p|
|C5,s4|C5B;B_to_D(9);D_pair2(c,10);F_p|
|C5,s5|C5B;B_to_D(9);D_three_B(10);B_to_D(16);D_large(c−2,17);F_p|
|C5,s≥6|C5B;B_to_D(9);D_large(s−2,10);C_large(c);F_p|

Use p=u+6,c=w+7 for the shared guards. The named C2,s2 proof can instead
use p=u+4,c=w+1. The right context should keep a different Lean name.
Do not trim a zero when an exponent2s−10 or2s−12 vanishes at its boundary.

## Evidence and next boundary

846 main endpoints agree in C++ and Python;840 have full matching traces.
The16 low-guard cases are additional.42 translated controls agree across
O2/O0/UBSan.16 tests and20 planted bugs pass. These are same-author checks,
not new Lean theorems or external independent replication.

The next entry is saved in next-boundary.json: width2/previous width2 with
only three right ones reaches B4 after38 steps, before reading any following
context. The six-one C2,s2 theorem cannot yet be applied. Branch on the actual
next bits rather than assuming a longer run of ones. Longer mixed stacks
also remain open. None of these generic sources is claimed blank-reachable.
