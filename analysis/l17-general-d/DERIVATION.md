# General middle counts and a guarded two-tail join

These are mathematical compositions of the preceding contextual identities,
with bounded literal-path checks. They have not been formalized in Lean here.
Only exterior trailing zeros may be trimmed. All times count defined TM
transitions; shifts and read coordinates are relative to the source head.

Let L(l,s)=(01)^l1^s, l>=1,s>=0. Keep arbitrary finite right context v:

    D(N,k,m;l,s)=Ccal(0;1^N(01)^k1^m L(l,s)v), N>=2,k>=1,m>=0
    G(N,k;l,s)=Ccal(0;1^N(01)^k 0 L(l,s)v), N>=2,k>=0.

The incoming question fixes(l,s)=(7,3). Wider notation is necessary because
short-middle interactions change the right terminal. S below means a one-tail
prefix followed by the unchanged v; for literal single-tail configurations set
v empty. Width0 and zero middle counts are tape equalities, not new TM moves.

## Entry and countdown

Write N=3q+r. Entry E takes2 transitions and shifts-2; Q consumes3q ones in
15q²+12q transitions and shifts-7q. The resulting pair counter is a=1+5q.
The total entry/countdown cost is E(q)=15q²+12q+2, shift-7q-2, read bound
[-7q-1,3q-2] when q>=1. For r=2,q=0 use E alone and the identity Q0.

## D rows

The time and read-bound table gives complete contextual rules. m=0 may always
be handled first by joining the adjacent(01) blocks. k=0 joins the adjacent
ones. Both are identity, with zero time/shift and no reads.

| Name / guards | Endpoint | Time | Shift | Read bound |
|---|---|---|---|---|
|D0:N=3q,q>=1|Ccal(1+5q+k;1^m L(l,s)v)|15q²+12q+2|-7q-2|[-7q-1,3q-2]|
|D1:N=3q+1,q>=1,m>=3|D(10q-6,k+7,m-3;l,s)|15q²+32q+6k+44|-7q-4|[-7q-4,3q+2k+2]|
|D12:N=3q+1,q>=1,m=2|G(10q-6,k+6;l,s)|15q²+32q+6k+44|-7q-4|[-7q-4,3q+2k+2]|
|D11:N=3q+1,q>=1,m=1|Ccal(1+5q;(10)^k11 L(l,s)v)|15q²+12q+2|-7q-2|[-7q-1,3q-2]|
|D2:N=3q+2,q>=0|D(10q+15,k-1,m;l,s)|15q²+62q+57|-7q-11|[-7q-11,3q+2]|

For D1 use `1(01)^k1^m=(10)^k111 1^(m-2)`. F111 gives
`1^(10q-6)(01)^(k+6)0 1^(m-2)L(l,s)v`. When m>=3, its first01 joins the
pair block and leaves m-3 ones. When m=2 there is no such one: the output zero
stays in front of L. Removing it would change the physical tape.

D11 is the remaining literal entry, valid for every k>=1 including the short
join cases. D2 composes P then Z and the equality
`0(01)^k=00 1(01)^(k-1)`. At k=1 merge the remaining leading ones with m.
These derivations use E,Q,F111,P,Z, and tape equalities only.

## G rows

The gap is an explicit symbol. In the following table k may be0 except G2:

| Name / guards | Endpoint | Time | Shift | Read bound |
|---|---|---|---|---|
|G0:N=3q,q>=1|Ccal(0;1^(10q+2k+7)L(l-1,s)v)|15q²+32q+4k+14|-7q-4|[-7q-4,3q+2k+1]|
|G1:N=3q+1,q>=2|D(10q-10,7,2k+4;l-1,s)|15q²+32q+4k+56|-7q-4|[-7q-4,3q+2k+2]|
|G2:N=3q+2,q>=0,k>=1|G(10q+15,k-1;l,s)|15q²+62q+57|-7q-11|[-7q-11,3q+2]|
|G2k:N=3q+2,q>=0,k=0|Ccal(0;1^(10q+14)L(l,s)v)|15q²+62q+57|-7q-11|[-7q-11,3q+2]|

G0 uses E,Q, normalization, then Z with the two zeros in
`0L(l,s)=00 1(01)^(l-1)1^s`. The following one joins the new leading ones.
G1 uses F100 because `1(01)^k0L(l,s)=(10)^k100 1(01)^(l-1)1^s`.
The inserted leading one raises its middle count to2k+4. The terminal width
falls to l-1. G2/G2k use P,Z; for k=0 no extra one is available to raise the
leading count from10q+14 to10q+15. If l=1 merge the resulting width0 boundary.
The q>=2 guard on G1 ensures its F100 pair counter1+5q>=7. No low-guard
continuation is inferred at q=1.

## JOIN from already known fixed paths

For a>=7,c>=5,l>=1:

    Ccal(a;(10)^c11(01)^l11v)
      -> Ccal(0;1^(2a-12)(01)^7 1^(2c-9)(01)^(l+6)0v).

Time4a+4c+6l+80; displacement-2; reads contained in
[-2,2a+2c+2l+3]. The context v is never read.

First prove this local A-section composition:

    [-12,2l+2]:(10)^6 A>1(01)^l11v
      -> C>11(01)^(l+6)0v,

with A initially at0 and C finally at-12, in6l+44 transitions. The notation
specifies the finite interval; the unshown left context is arbitrary. Its
reads lie in[-11,2l+2]. These are the segments:

| Segment | Head entry -> exit | Time | Read interval in these coordinates |
|---|---|---:|---|
|K7, input[-4,2]=1010101|A0 -> A-3|7|[-4,1]|
|A sweep(l+2)|A-3 -> A(2l+1)|2(l+2)|[-3,2l]|
|A1,E1,F0 on the two terminal ones|A(2l+1) -> D(2l)|3|[2l+1,2l+2]|
|D sweep(l+2)|D(2l) -> D-4|4(l+2)|[-3,2l]|
|K22, input[-12,0]=1010101001010|D-4 -> C-12|22|[-11,-2]|

After K7 the three new01 pairs plus the remaining l-1 pairs make l+2 pairs.
The A sweep converts them to10 pairs. The D sweep preserves those pairs. K22
leaves11(01)^5 0, followed by(10)^(l+1)v. The identity
`0(10)^(l+1)=(01)^(l+1)0` gives the local endpoint. This proves the local
statement for every l by the already established sweep inductions.

For the outer C-section put n=a+1, and set local0 at the first(10)^c symbol:

1. Entry C0,D0, then the A sweep over n pairs, produces(10)^n to the left of A0.
2. K11 on[-4,1] takes A0 to A1 in11 transitions, read window[-4,1].
3. Sweep A over c pairs to A(2c+1), on the second of the two ones. The immediate
   left word now contains c+2 copies of10. Apply the local lemma translated
   by2c+1. It exits at C(2c-11), with11(01)^(l+6)0v to its right.
4. Sweep C through c-4 shifted01 pairs to C-3. At least one pair is present
   because c>=5. This produces exactly the K43 input on[-16,-1], namely
   `1010101010100111`. Its read window is[-15,-2].
5. K43 exits at C-16 with11(01)^7, followed by
   `1^(2c-9)(01)^(l+6)0v` at local0. Sweep C through the remaining n-8 pairs
   to C(-2n), creating2a-12 leading ones.

The sum is

    2+2n+11+2c+(6l+44)+2(c-4)+43+2(n-8)
      =4a+4c+6l+80.

Local-2n is two cells left of the original C head. Entry reads the source
position-2; the last terminal one read by the local lemma is at source
2a+2c+2l+3. All other windows lie between these bounds. No new finite kernel
has been assumed: K7,K11,K22,K43 and all three sweeps are from prior work.

If s>=3, substitute v'=1^(s-2)v. The output0 consumes the first remaining one
by a literal01 join. Therefore, for q>=2,k>=5:

    D(3q+1,k,1;l,s) -> D(10q-10,7,2k-9;l+7,s-3),

time15q²+32q+4k+6l+86, shift-7q-4,
read bound[-7q-4,3q+2k+2l+3]. In particular L(7,3) becomes L(14,0).

## Finite-exit rank, and what it does not prove

Stop the ordinary D reduction at m=0, k=0, r=0, or r=1 with m=1 or2.
For every remaining internal row, N remains>=2 and:

    D1:3(k+7)+8(m-3)=3k+8m-3;
    D2:3(k-1)+8m=3k+8m-3.

Thus within floor((3k+8m)/3)+1 decisions the system reaches a one-tail prefix,
G, or the explicit J entrance D11. This is a well-founded proof for all m>=0,
not an extrapolation from runs. Its finite Python checks are implementation
checks only.

It cannot simply be extended to the old fixed-T return theorem. For example,
D(7,1,2;7,3) reaches G(14,7;7,3); the extra0 is physical. Also
D(7,5,1;7,3) reaches D(10,7,1;14,0), which has a different terminal and is not
one-tail. Neither witness is asserted to occur on the blank orbit. No rank
covering arbitrary terminal changes, short joins and further stacking is
proved here. In particular, finite exits do not imply nonhalting or a global
stack-depth bound.

## The recovered return and continuation

RET729 in CLAUDE-BRIEF.md is F1100 followed by D1,D1,D1,D2,D2,D0. Each q is
an affine function of t; summing the six quadratic row times gives the stated
polynomial. The inequalities for the enclosing read bound have nonnegative
coefficients for t>=0,c>=11. The actual recovered A fixes t=(A-548)/729.
`return39-witness.json.gz` retains exact t, time, shift and endpoint.

The next-stage engine was not extended with JOIN: it continued only the old
contextual dispatcher and the old calibrated scalar reset map. No m=1 join or
m=2 gap was needed during the new exceptional excursions. Its original-rewrite
push positions are2059835,2178613,2433152,2652599,2739865, after the recovered
width72 event at2042072. All return. At3M the endpoint is S(1,B,7,3), where B has
1424091 bits; the exact B is in endpoint-3m.json.gz. No next unsupported event
was found within the registered cap. The exact source of the first new push
matches Claude's fingerprint, but the private gzip was unavailable for a byte
comparison.
