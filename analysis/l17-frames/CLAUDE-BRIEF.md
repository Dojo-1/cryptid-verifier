# L17: opposite streams and a larger rank

This is a separate additive task while you formalize D/G, RET729 and JOIN.
There are no Lean edits or additional blank-orbit extensions here. These are
analytic compositions and finite implementation checks, not new Lean theorems.

## Most useful results

1. The six guarded **internal** canonical D/G rows have a unique predecessor.
2. Their forward iteration terminates at a named exit using the lexicographic
   rank `(s,l,R)`, with `R_D=3k+8m+3`, `R_G=3k`.
3. Backward iteration terminates using `(N,k)` as its decreasing rank.
4. Every F1100 entry is a root of this internal transition graph. Its internal
   descendants recover their unique entry by the opposite stream.

Together, this restricted graph is a disjoint union of finite paths. This does
not include the S exits, the outer S dynamics, or the still unsupported J/G
cases. It is not raw-machine reversibility or a stack/nonhalting theorem.

## Domain and internal rows

Use blank right exterior here, so these are canonical complete tail words:

    D(N,k,m;l,s)=Ccal(0;1^N(01)^k1^m(01)^l1^s)
    G(N,k;l,s)=Ccal(0;1^N(01)^k0(01)^l1^s).

D: N>=2,k>=1,m>=1,l>=1,s>=0. G: N>=2,k>=0,l>=1,s>=0.
Zero middle/width boundaries are exits; do not invert their normalization.
All following targets stay in that domain:

| Row | Extra source guard | Internal target |
|---|---|---|
|D1|N=3q+1,q>=1,m>=4|D(10q-6,k+7,m-3;l,s)|
|D2|N=3q+2,q>=0,k>=2|D(10q+15,k-1,m;l,s)|
|D12|N=3q+1,q>=1,m=2|G(10q-6,k+6;l,s)|
|G1|N=3q+1,q>=2,l>=2|D(10q-10,7,2k+4;l-1,s)|
|G2|N=3q+2,q>=0,k>=1|G(10q+15,k-1;l,s)|
|D11join|N=3q+1,q>=2,k>=5,m=1,s>=3|D(10q-10,7,2k-9;l+7,s-3)|

No new raw kernel is used. These are exactly the preceding contextual rows
with the noncanonical/unsupported exits excluded.

## Opposite-stream table

For a target with uppercase coordinates K,M,L,S and leading counter n:

| Target condition | Unique internal predecessor |
|---|---|
|D,n mod10=4,K>=8|D(3q+1,K-7,M+3;L,S), q=(n+6)/10>=1|
|D,n mod10=5|D(3q+2,K+1,M;L,S), q=(n-15)/10>=0|
|G,n mod10=4,K>=7|D(3q+1,K-6,2;L,S), q=(n+6)/10>=1|
|G,n mod10=5|G(3q+2,K+1;L,S), q=(n-15)/10>=0|
|D,n mod10=0,K=7,M even>=4|G(3q+1,(M-4)/2;L+1,S), q=(n+10)/10>=2|
|D,n mod10=0,K=7,M odd,L>=8|D(3q+1,(M+9)/2,1;L-7,S+3), q=(n+10)/10>=2|

Every target outside these guarded ranges has no predecessor in this internal
system. Leading residues4/5/0 separate the rows, except the last pair; middle
parity separates those. Solve each row algebraically to obtain the table.

F1100 enters D(2a-12,7,2c-13;7,3), a>=7,c>=7. Its N is even, K=7,
M odd and L=7. The4-row needs K>=8; the5-row needs odd N; the0/even row
needs even M; the0/odd row needs L>=8. Thus it has no internal predecessor.
Different entries cannot merge before an exit, by injectivity. This gives a
precise backward filter for future boundary candidates.

## Forward rank

Order `(s,l,R)` lexicographically, with

    R(D)=3k+8m+3; R(G)=3k.

- D1, D2 and G2 decrease R by3 while s,l stay fixed.
- D12 decreases R by1: the extra3 on D is essential.
- G1 decreases l by1 while s stays fixed; R may increase.
- D11join decreases s by3; both l and R may increase.

All coordinates are natural numbers, so every internal chain is finite.
The conclusion is return to a one-tail state **or an explicitly uncovered
case**, rather than universal return to S. This is a direct enlargement of the
previous finite-exit theorem.

A coarse numerical bound is also available. Put J=floor(s/3),
E=l-1+8J, R0=R(initial). There are at most E amplifying G1/JOIN rows;
ordinary rows drop R by at least1. Each amplifier satisfies Rnew<=6R+56.
Therefore the internal-chain length is at most

    (E+1)*6^E*(R0+12)+E.

This is intentionally loose. It is an arithmetic upper bound on macro rows,
not raw TM time or a bound on outer-loop behavior.

## Backward rank

For every internal edge, `(N,k)` increases lexicographically forward, hence
decreases backward. D1/D12 have equal N only when q=1, N=4; then forward k
grows by7/6. Every other internal row increases N strictly. This proves finite
ancestry as well as uniqueness. The endpoint times/head/read bounds are already
those in the preceding handoff; there is no new machine-level time lemma.

## One affine score, even one per mode, is obstructed

Allow a separate affine score in each mode, bounded below on the whole
canonical domain. The N coefficients are nonnegative by boundedness. D1 at
unbounded q forces the D N coefficient to0, and G2 does the same for G.
Let alpha_D, beta_D and alpha_G denote the D-k, D-m and G-k coefficients.
The necessary inequalities are:

    D2: alpha_D>0
    D1: 7alpha_D-3beta_D<0
    D12 at unbounded k: alpha_G-alpha_D<=0
    G1 at unbounded k: 2beta_D-alpha_G<=0.

Multiply the last three expressions by2,3,3 and add:11alpha_D<0, contradicting
the first. Arbitrary mode offsets and affine terminal weights cannot cancel
the unbounded-k terms. The common-coefficient version follows immediately.
This rules out this entire affine ranking class, not nonlinear, lexicographic
or history-dependent candidates. An invertible fixed linear change of counter
coordinates followed by an affine scalar remains in the excluded class.

## Concrete remaining obstructions, not blank-reachability claims

Two tiny F1100 source parameters show why universal push collapse still needs
more rows, even after this rank:

    a=37,c=7: D(62,7,1;7,3) -> D(215,6,1;7,3)
      -> D(725,5,1;7,3) -> D(2425,4,1;7,3).

The next JOIN width is4, below its guard.

    a=46,c=7: D(80,7,1;7,3) -> D(275,6,1;7,3)
      -> D(925,5,1;7,3) -> D(3070,7,1;14,0).

The next JOIN has short terminal s=0. These are generic input witnesses; neither
is asserted to be on the blank orbit. Leave their kernels alone until needed.

## Checks and coordination

- 10,780 canonical states checked against the exact consumed row expressions.
- 2,400 supplementary states checked with a generic Fraction/Gaussian solver,
 which imports no counter actor and derives candidate predecessors from the
 frozen equations. This is separate code, shared authorship.
- 5,476 F1100 entries checked as roots; all their small excursions end at named
 exits within the2000-row cap, maximum observed internal length48.
- The actual 977,821-bit width39 boundary is reversed exactly through its five
 internal rows to its original push entry. Its sixth decision is the D0 exit.
- 18 unit tests and15 deliberately incorrect coordinate/inverse/rank variants.

Please finish the current Lean work first. The natural later lemmas are
`internal_step_injective`, `internal_step_decreases_lex`,
`internal_predecessor_decreases_lex`, and `push_entry_is_root`, followed by the
finite-exit theorem. The names are suggestions, not compiled declarations.
