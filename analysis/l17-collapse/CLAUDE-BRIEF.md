# L17: collapse lemma, a linear rank, and the first longer excursions

The old three-rewrite collapse is not universal. The first exception found is
at GPT source checkpoint **1,407,520**. It returns after **17 post-push rewrites**,
at 1,407,538. A second exception starts at 1,803,910 and returns after six.
Both are covered by a new terminating two-layer subsystem. The conditional
continuation now reaches **2,000,000 GPT rewrites**, with seven pushes in total,
no third layer and no reached 1101 or unproved low-guard case.

## 1. The immediate lemma from your F1100 output

For all h,d>=0, with arbitrary finite v:

```
Ccal(0;1^(6h+6)(01)^7 1^(2d+1) T v)
  -> Ccal(10h+18;1^(2d+1) T v)
time 60h^2+144h+86; shift -14h-16.
```

This is your F1100 output with `u=3h+2`. Entry E, countdown `q=2h+2`, then
absorb the seven pairs. Its complete read bound is `[-14h-15,6h+4]`; none of
the tail starting at position 6h+6 is read. No new kernel is needed.

The full push-and-collapse rule is the prior handoff's

```
S(3h+9,1,d+7,1) -> S(10h+18,2d+1,7,3).
```

## 2. A stronger collapse theorem, independent of the front digits

Let

```
D(N,k,z) = Ccal(0;1^N(01)^k1^(3z)T),  N>=2,k>=1,z>=1.
```

Write `N=3q+r`. A decision consists of E and Q, followed by one row:

| r | Rest | Return or reset | Time including E/Q | Shift |
| --- | --- | --- | --- | --- |
| 0 | absorb k pairs | `S(1+5q+k,3z,7,3)` | `15q²+12q+2` | `-7q-2` |
| 1 | F111 | `D(10q-6,k+7,z-1)` | `15q²+32q+6k+44` | `-7q-4` |
| 2 | P then Z | `D(10q+15,k-1,z)` | `15q²+62q+57` | `-7q-11` |

At z=1 in the r=1 row, join the adjacent pair blocks and return to S. At k=1
in the r=2 row, join the leading ones and return to S. The q=0 countdown is
identity. All other guards follow from N>=2,k,z>=1.

The simple integer rank **R=k+8z drops by exactly one on every non-return
decision**. Hence D must return to S within k+8z decisions, with no third layer
at the contextual rewrite checkpoints. Exact time/head totals are the branch
sums. Arbitrary right context is preserved. `COLLAPSE.md` supplies all read
windows and the word identities needed at the boundary cases.

For your F1100 output, `d=3j+1` means `2d+1=3(2j+1)`. Therefore every such push
returns to S for **any u**, in at most 16j+15 decisions. This covers both newly
observed non-immediate excursions. It is a mathematical termination proof ready
for Lean, not a new Lean build performed here.

## 3. Optional direct S moves for the two observed itineraries

The first long excursion has A mod243=230 and tail width 71. Decisions:
`1,2,2,1,0`. For all t,e>=0:

```
S(243t+230,1,e+10,1) -> S(100000t+91810,2e+1,7,3)
time 6593367660t²+12104704176t+4e+5555729670
shift -199514t-183154.
```

The next has A mod9=2 and width 68. Decisions: `1,0`:

```
S(9t+11,1,e+9,1) -> S(100t+55,2e+2,7,3)
time 6540t²+5808t+4e+1547; shift -182t-85.
```

The long family exceeds the raw probe budget even at zero parameters; its
polynomial is checked by composition, not by a claimed billion-step raw run.
Both families match their reached huge endpoints exactly. The second also has
small full raw checks. These moves avoid expanding a two-layer state in S.

## 4. Where the invariant proof stops

All seven observed pushes satisfy the sufficient condition

```
a%3=0 OR c%3=2
```

for the source `S(a,1,c,1)`. The first side is immediate collapse; the second
enters the ranked subsystem. But this alone is not an invariant on all S states:

```
S(9,1,8,4) -> S(16,1,15,1)
```

is a raw-checked F111/E/Q path in 295 transitions, shift -25. Its target violates
both sides. This source is **not asserted blank-reachable**. It shows that the
blank-reachable subset needs an additional arithmetic restriction, or more
return cases. No global depth-two theorem follows from the finite search.

The first source where three-rewrite collapse fails is now supplied; no source
where eventual collapse or the depth-two bound fails was reached. General 1101
and unproved low guards were left out as requested.

## Evidence

183 full raw endpoints and read-window checks pass, with 1,735,242 fresh defined
transitions, six planted bugs caught, 12 tests, 500 scalar-map calibration cases,
and separate replay of the new conditional continuation through rewrite two
million. The checker uses a separate declarative reset map and no actor/word
class. All code paths here have the same author; your independent first-event
reproduction is user-reported external confirmation. New collapse/ranking
lemmas are not claimed as Lean-proved.

One read-window lower bound was initially one cell too narrow and was caught by
the raw comparator. Its failed critic and log are retained. The literal records
were hash-bound and reused after correcting only the bound. All older package
payloads and their histories remain unchanged.
