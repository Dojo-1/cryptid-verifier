# L17: arbitrary middle counts, the width39 return, and a3M continuation

The private repository still returns404 in this environment. I recovered the
new boundary from the archived2M endpoint instead. It is original rewrite
**2,059,835**, with the supplied **977,821-bit** A, A mod243=62, and width39.
The stronger recovered residue is **A mod729=548**. This matches your supplied
fingerprint; it is not a byte comparison with your private gzip file.

**Main result:** the width39 push returns to S after21 original rewrites,
including F1100 (20 after it). Its six D decisions are **1,1,1,2,2,0**.
Three more ordinary rewrites reach the reset section, explaining the runner's
24-rewrite reset return. The later guarded continuation reaches exactly
**3,000,000** rewrites, with no unsupported rule or three-layer event.
It stops at the registered budget, not at a mathematical obstruction.

## A uniform return covering that event

For t>=0, c>=11 and arbitrary finite suffix v, with two explicit input zeros:

    Ccal(729t+548; 1 (01)^c 100 v)
      -> Ccal(1000000t+740902; 1^(2c-22) (01)^7 111 v).

In the blank-suffix S notation this is

    S(729t+548,1,c,1) -> S(1000000t+740902,2c-22,7,3).

Time:

    659340308940 t² + 976981433088 t + 4c + 361912016145.

Head displacement: `-1998542t-1480699`.
Read bound: `[-1998542t-1480698, 1458t+2c+1099]`.
For c=39 the last time constant becomes361912016301 and the middle count56.

This uses F1100, then D1,D1,D1,D2,D2,D0. The successive q values are:

| r | q | k before | m before |
|---:|---|---:|---|
|1|486t+361|7|2c-13|
|1|1620t+1201|14|2c-16|
|1|5400t+4001|21|2c-19|
|2|18000t+13334|28|2c-22|
|2|60000t+44451|27|2c-22|
|0|200000t+148175|26|2c-22|

The c=11 endpoint has middle count0: retain the tape equality merging adjacent
pair blocks. It is covered; it must not be rejected or treated as a new gap.
The full time is above the raw horizon even at t=0. These are checked arithmetic
compositions, not enormous literal simulations or new Lean theorems.

## General D interface, including all m>=0

Use `L(l,s)=(01)^l1^s`, l>=1,s>=0, and arbitrary suffix v. Your D is
`D(N,k,m)=Ccal(0;1^N(01)^k1^m L(7,3))`. The broader notation below keeps
terminal-width changes visible:

    D(N,k,m;l,s) = Ccal(0;1^N(01)^k1^m L(l,s)v)
    G(N,k;l,s)   = Ccal(0;1^N(01)^k 0 L(l,s)v).

All rows, times and read bounds are in DERIVATION.md and the consumed JSON
specifications. The minimal Lean compositions are:

| Row | Guard beyond k>=1 | Composition / endpoint type |
|---|---|---|
|M0|m=0|literal pair-block join, no transitions|
|K0|k=0|literal ones-block join, no transitions|
|D0|N=3q,q>=1|entry,Q,normalize -> one-tail prefix|
|D1|N=3q+1,q>=1,m>=3|entry,Q,F111 -> D(10q-6,k+7,m-3;l,s)|
|D12|N=3q+1,q>=1,m=2|entry,Q,F111 -> **G(10q-6,k+6;l,s)**|
|D11|N=3q+1,q>=1,m=1|entry,Q -> Ccal(1+5q;(10)^k11 L(l,s)v)|
|D2|N=3q+2,q>=0|entry,Q if q>0,P,Z -> D(10q+15,k-1,m;l,s)|
|G0|N=3q,q>=1,k>=0|entry,Q,normalize if k>0,Z -> one-tail prefix, width l-1|
|G1|N=3q+1,q>=2,k>=0|entry,Q,F100 -> D(10q-10,7,2k+4;l-1,s)|
|G2|N=3q+2,q>=0,k>=1|entry,Q if q>0,P,Z -> G(10q+15,k-1;l,s)|
|G2k|N=3q+2,q>=0,k=0|entry,Q if q>0,P,Z -> Ccal(0;1^(10q+14)L(l,s)v)|

Width0 is a literal boundary: merge the adjacent ones. G1 does not preserve the
old fixed terminal T. Its output when l=7 has width6, not7.

## The m=1 join: no new kernel

For a>=7,c>=5,l>=1 and arbitrary v:

    Ccal(a;(10)^c 11 (01)^l 11 v)
      -> Ccal(0;1^(2a-12)(01)^7 1^(2c-9)(01)^(l+6) 0 v)

in `4a+4c+6l+80` transitions, displacement-2,
read bound `[-2,2a+2c+2l+3]`.

It composes the existing entry and A sweep, K11, A sweep c; then the existing
K7, A sweep(l+2), A11 path, D sweep(l+2), K22; then C sweep(c-4), K43, and the
final C sweep(a-7). All fixed kernels already appeared in the earlier handoffs.
DERIVATION.md gives the exact translated windows and intermediate words.

Thus, for q>=2,k>=5,l>=1,s>=3:

    D(3q+1,k,1;l,s)
      -> D(10q-10,7,2k-9;l+7,s-3)

in `15q²+32q+4k+6l+86` transitions, displacement `-7q-4`,
read bound `[-7q-4,3q+2k+2l+3]`.
For your T this changes the right terminal to **(01)^14**.

## Rank and the remaining obstruction

The ordinary D rows decrease `3k+8m` by exactly3 per internal D1/D2 move.
They therefore reach a one-tail prefix, G, or the explicit m=1 join boundary
within `floor((3k+8m)/3)+1` decisions. This applies to every m>=0.
It is **not** a universal return-to-S theorem.

The obstruction to simply reusing your induction is exact: D12 leaves the
interior zero before T, and D11join changes T into(01)^14. Neither output stays
in the fixed-T D domain. For example D(7,5,1) reaches
`Ccal(0;1^10(01)^7 1(01)^14)`, which is neither a fixed-T D state nor a one-tail
S. This does not refute an eventual return theorem in a larger state family.

I have not promoted the short join guards a=6 or c<5. The literal entrance D11
remains valid there, and the engine stops on unsupported continuations. They
are not needed by this blank-orbit extension. I have not derived the arbitrary
1101v family beyond the guarded join with its two required final ones.

## Checks and artifacts

- 601 distinct row probes against the C++ literal machine; full state, tape,
 time, head and read bound checked.
- 51 selected probes each with O0 and UBSan, in addition to the O2 campaign.
- 74 exterior-tape/window probes, including K7 and K22 with random tape on
 both sides of their complete read intervals.
- 11 planted faults killed, including dropping the interior zero, using the
 wrong terminal width/ones, and shrinking the join read window.
- 21 sampled endpoints replayed with the separate dense Python machine.
- 553 declarative old-rule compositions plus8 RET39 and15 RET729 arithmetic
 checks, including the actual huge source. No actor or Word imports there.
- The new million-rewrite extension is replayed from all273255 scalar choices,
 all81 exceptional primitive edges and26 sparse checkpoints, without importing
 the orbit actor or Word class. Exact3M endpoint: S(1,B,7,3), B has1424091 bits.

The Python/C++ code paths share authorship. Your independent stepper remains the
external witness for the earlier prefix and the supplied boundary fingerprint.
No PR status, Lean build, new blank-prefix certificate, global stack bound or
nonhalting result is claimed from this environment.

Suggested Lean order: generalize D0/D1/D2 to arbitrary m; add D12 retaining its
zero; add G rows; derive JOIN from K7/K22; instantiate the six-row RET729 family.
The finite-exit rank theorem is safe to add separately from a universal collapse
claim. The exact missing proof is a decreasing invariant covering the changed
right terminals and the still excluded join guards.
