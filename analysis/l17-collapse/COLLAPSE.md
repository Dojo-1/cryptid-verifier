# L17: guarded collapse and a terminating two-layer subsystem

This is a mathematical derivation for Lean formalization, with bounded literal
machine checks. Claude reports that F1100 and the old contextual rules are now
proved against the machine. That report was supplied by the user; no private
repository or Lean build was inspected here. No new Lean theorem is claimed.

Use `Ccal(a;w)=0^infinity C> (01)^a w 0^infinity`, and put
`T=(01)^7 1^3`. Coordinates are relative to the source C head. Only exterior
trailing zeros are implicit. A context `v` below is an arbitrary finite binary
word, kept unchanged throughout. A one-layer return refers to the displayed
outer section before v; with blank v it is a literal one-tail configuration.

## Immediate collapse from the new F1100 output

For all `h,d>=0`:

```
Ccal(0; 1^(6h+6) (01)^7 1^(2d+1) T v)
  -> Ccal(10h+18; 1^(2d+1) T v).
```

Time: **`60h^2+144h+86`**. Head shift: **`-14h-16`**.

This is exactly the requested post-push lemma when Claude's F1100 parameter is
`u=3h+2`. It is a sufficient guard, not a claim that no other input collapses.

1. Entry E takes two transitions, adds the pair `01` to the left, and reaches
   `Ccal(1;1^(6h+6)(01)^7 1^(2d+1) T v)`.
2. Set `q=2h+2`. The contextual countdown consumes `3q=6h+6` leading ones,
   adds `5q` pairs, and shifts the head by `-7q`. Its time is `15q^2+12q`.
3. The seven remaining initial `01` pairs are absorbed by literal tape equality.
   The resulting pair count is `1+5q+7=10h+18`.

Thus no new fixed path is needed. The total is `2+15q^2+12q`, and the shift is
`-2-7q`. All reads lie in **`[-14h-15,6h+4]`**. In particular, the right-hand
tail beginning at position `6h+6` is never read.

Composing this with F1100 gives the previously delivered S-to-S rule

```
S(3h+9,1,d+7,1) -> S(10h+18,2d+1,7,3)
time 60h^2+156h+4d+242; shift -14h-18.
```

## Elementary read windows used in every collapse

The existing block sweeps are A over `01` in two transitions, D left over `10`
in four, and C left over `01` in two. They read only their own two-cell blocks.
The countdown step D follows the existing entry, A sweep, `A1,E1,F0`, D sweep,
and ten-step left finish. That finish has input `[-4,2]:0000010`, entry D at 0,
exit C at -4, output `0101010`, and reads `[-3,2]`.

| Existing rule | Time | Shift | Complete read bound relative to its entry |
| --- | ---: | ---: | --- |
| E: `Ccal(0;1w)` | 2 | -2 | `[-1,0]` |
| P: `Ccal(a;11w)`, `a>=1` | `6a+21` | -7 | `[-6,2a+1]` |
| D: `Ccal(a;111w)`, `a>=1` | `6a+21` | -7 | `[-6,2a+1]` |
| Z: `Ccal(a;00w)` | `4a+8` | -2 | `[-2,2a+1]` |
| F111: `Ccal(a;(10)^c111w)`, `a>=5,c>=1` | `4a+6c+38` | -2 | `[-2,2a+2c+2]` |
| Q: consume `3q` leading ones, `a>=1,q>=1` | `15q^2+(6a+6)q` | `-7q` | `[1-7q,2a+3q-2]` |

For Q, take the union of D's translated windows at head `-7i`, pair count
`a+5i`, for `0<=i<q`. A zero-length countdown is identity and reads nothing.
The F111 fixed windows and sweep composition remain those in the earlier
`l17-stacked-section/DERIVATION.md`; no new F111 kernel is introduced.

The lower endpoints for Z and F111 include the new cell at `-2`, read by the
initial A sweep. The first validation mistakenly used `-1`; a raw window check
caught it. The failed bound and original critic are retained. Source, target,
transition count and head claims were unaffected.

## A safe two-layer subsystem

Define reset states

```
D(N,k,z;v) = Ccal(0;1^N (01)^k 1^(3z) T v),
N>=2, k>=1, z>=1.
```

Let `N=3q+r`, `0<=r<3`. Each row first applies E and the q-fold countdown.
For `q=0` that countdown is identity. The rest of the row is shown explicitly.

| Residue | Actions | Endpoint | Time | Head shift | Read bound |
| --- | --- | --- | --- | --- | --- |
| `r=0` | E, Q, absorb k pairs | `S(1+5q+k,3z,7,3) . v` | `15q^2+12q+2` | `-7q-2` | `[-7q-1,3q-2]` |
| `r=1` | E, Q, F111 | `D(10q-6,k+7,z-1;v)` | `15q^2+32q+6k+44` | `-7q-4` | `[-7q-4,3q+2k+2]` |
| `r=2` | E, Q, P, Z | `D(10q+15,k-1,z;v)` | `15q^2+62q+57` | `-7q-11` | `[-7q-11,3q+2]` |

The r=1 row requires `q>=1`, which follows from `N>=2` and `N mod3=1`.
It reaches F111 with `a=1+5q>=6`, so its lower guard is satisfied. The r=2 row
allows q=0. P and Z have their existing valid guards. All resets keep N>=2.

Boundary cases in the table are returns, not new D states:

- If the r=1 row has `z=1`, the two adjacent pair blocks join, giving
  `S(0,10q-6,k+14,3) . v`.
- If the r=2 row has `k=1`, the leading ones join, giving
  `S(0,10q+15+3z,7,3) . v`.

The algebra in the r=1 row uses
`(01)^(k+6) 0 1^(3z-2) = (01)^(k+7) 1^(3z-3)`.
In the r=2 row, after P the first two symbols are `00`; Z leaves one extra one
before `(01)^(k-1)`, producing the new front count `10q+15`.

For every non-return cycle, the integer rank

\[
R=k+8z
\]

decreases by **exactly one**: `(k,z)->(k+7,z-1)` or `(k-1,z)`. Therefore every
D state returns to S within at most `k+8z` decision cycles. Each cycle uses at
most four contextual rules; purely literal word equalities cost zero machine
transitions. Exact raw time and displacement are the sums in the table along
the selected residue itinerary.

All intermediate contextual checkpoints keep at most the two displayed tail
blocks. The temporary P-to-Z zero gap is included in this finite grammar. This
is a terminating, guarded excursion subsystem. It is not yet a global invariant
for all blank-reachable S states.

An explicit finite grammar for this local proof is:

| Shape | Parameters | Selected outgoing rule |
| --- | --- | --- |
| Reset D | as above | E to Prepared |
| Prepared `Ccal(a;1^b(01)^k1^(3z)T v)` | `a>=1,k,z>=1`; if b=1 require a>=6 | Q when b>=3; absorb k pairs when b=0; F111 when b=1; P when b=2 |
| Zero-gap `Ccal(a;0(01)^k1^(3z)T v)` | `a>=5,k,z>=1` | Z to Reset or a one-tail return |
| Return S | its usual parameters | End of this local proof, with the machine free to continue |

Q preserves Prepared and, if its remainder is one, raises a to at least six.
F111 preserves Reset with z decreased or reaches Return. P produces Zero-gap
with a increased by four; Z decreases k or reaches Return. Thus every selected
non-return rule maps these shapes back into the grammar. The unresolved global
question is which S states subsequently re-enter it; treating Return as a proof
endpoint does not make it a halting or absorbing machine state.

For Claude's F1100 output, `d=3j+1` gives `2d+1=3(2j+1)`. Thus **every such
push returns to one layer for arbitrary u**, in at most `16j+15` decision cycles.
This is independent of the size or future residue behavior of its front counter.

An analytic toy is N=4. Every cycle has r=1 and N stays 4, so for `k>=1,z>=0`:

```
Ccal(0;1^4(01)^k1^(3z)T v) -> S(0,4,k+7z+7,3) . v
time 21z^2+(6k+70)z; shift -11z.
```

For z>=1 its reads lie in `[-11z,2k+3z+2]`; z=0 is tape equality. This toy
independently exercises repeated non-immediate collapse and the rank bound.

## Two reached longer returns, with closed count formulas

The first non-immediate excursion has source `S(A,1,71,1)` with
`A mod243=230`. Its five decisions have residues **1,2,2,1,0**.
For all `t,e>=0`, the corresponding guarded return family is

```
S(243t+230,1,e+10,1) -> S(100000t+91810,2e+1,7,3).
```

Time: `6593367660t^2+12104704176t+4e+5555729670`.
Head shift: `-199514t-183154`.

After F1100, N is `486t+448`, the outer pair count is 7, and the middle ones
number `2e+7`. The successive countdown quotients are

```
162t+149, 540t+494, 1800t+1651, 6000t+5508, 20000t+18358.
```

The pair counts before those decisions are 7, 14, 13, 12, 19. The two F111
decisions remove six middle ones. The last residue zero absorbs the 19 pairs.
Sum the five cycle costs above, then add F1100's `972t+4e+1052` transitions and
its shift -2. The complete read bound is
`[-199514t-183153,486t+2e+483]`.

Even t=e=0 costs 5,555,729,670 transitions. This full return was **not** raw
simulated under the 200,000-transition probe cap. Its proof is the universal
composition, and its count polynomial is checked against that composition for
finite, huge and reached parameters. Its shorter components have literal checks.

The next non-immediate source has `A mod9=2`, tail width 68, and decisions 1,0.
A second family, with t,e>=0, is

```
S(9t+11,1,e+9,1) -> S(100t+55,2e+2,7,3)
time 6540t^2+5808t+4e+1547; shift -182t-85.
```

Here the two quotients are `6t+3` and `20t+8`. Its full read bound is
`[-182t-84,18t+2e+43]`. This family does have small full raw checks.

## The missing invariant condition

All seven F1100 sources observed through two million GPT rewrites satisfy

```
a % 3 = 0   or   c % 3 = 2.
```

The first alternative gives immediate collapse; the second gives the terminating
D subsystem. But the predicate is **not itself an inductive restriction on all
four-counter S states**. A fully raw-checked negative control is

```
S(9,1,8,4) -> S(16,1,15,1)
```

via F111, E, Q, in 295 transitions with displacement -25. Its target has neither
`a%3=0` nor `c%3=2`, despite the source being an ordinary one-tail S state. This
source is not asserted blank-reachable. It shows that more information about the
blank-reachable subset is needed to close the proposed finite family.

No third layer, `(10)^c1101v` case, or unproved low-guard case was reached within
the registered search. Those generalizations were therefore left out. No global
two-layer bound, impossible-invariant theorem, or non-halting claim follows.
