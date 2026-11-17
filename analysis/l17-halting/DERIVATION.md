# L17: bounded halt language and short-guard calculus

This is an additive mathematical derivation and bounded execution campaign.
There is no new Lean file or Lean build here. PR #9 and the pending `L17k`
status are supplied by the user; the private repository was not re-audited.
All general identities below follow by composition of the stated sweeps and
finite paths. Their numerical tests are cross-checks, not the universal proof.

The machine is `1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`.
An undefined transition performs no write, move, or counted transition.
The head is on the first symbol after `>`. Unshown exterior tape is zero.
Only exterior trailing zeros may be omitted.

Write Ccal(a;w) = `0∞ C> (01)^a w 0∞`,
T = `(01)^7 1^3`, and D(N,k,m;l,s) =
`Ccal(0;1^N(01)^k1^m(01)^l1^s)`.
In displays with an internal A/B/D head, the complete left word is shown;
these configurations must not be confused with blank-left C-sections.

## 1. Complete bounded backward set

Let H_d(q,x) mean that the first undefined transition is reached after at most
d **defined** transitions, with the initial head at coordinate0. Then
H_0(F,x)=x_0 and H_0(q,x)=false for q≠F. For a defined transition
q,b ↦ (w,δ,q'), the next relative tape is

    y_j = x_(j+δ), except y_(-δ)=w.

Consequently H_(d+1)(q,x) is the disjunction, over the two initial read bits,
of `x_0=b` and H_d(q',y); an undefined branch contributes true. Induction on
d proves completeness for every two-sided tape, finite or infinite. No
probabilistic assumption is involved. The serialized ordered Boolean diagram
implements precisely this recurrence.

`halt-bdd.json.gz` contains all six roots at every depth0…40. The current
depth40 roots use 460,141 nonterminal nodes; all saved snapshots together
use 2,112,639. Variables actually used across those snapshots range from
−40 to18. `verify_bdd.py` checks node ordering, reduction, uniqueness and all
480 recurrence branches by paired Shannon cofactors. It neither imports the
BDD constructor nor constructs the actor's substituted diagrams.

The initial explicit inverse search, anchored at the final halt head, completed
depth38 before its frontier cap. A cube inverse preserves all unoverwritten
bits and imposes the predecessor read bit at the overwritten cell, rejecting
a conflicting required output bit. It retained 4,597,310 exact first-halt-depth
path cylinders. These are not the minimal patterns of the union. The two
representations have different units and must not be compared as counts of
the same object.

### Complete minimal family, compressed rather than enumerated

For a ternary pattern p with entries0,1,free, define a circuit I(u,p) on each
saved diagram node u:

    I(0,p)=false; I(1,p)=true.
    I(node(v,lo,hi),p) = I(lo,p) if p_v=0;
                         I(hi,p) if p_v=1;
                         I(lo,p) AND I(hi,p) if p_v=free.

The complete inclusion-minimal family for state q is exactly

    I(root40[q],p) AND
    for every fixed v, NOT I(root40[q],p with v made free).

This is a finite, executable, factored description of the entire family.
Minimality follows because deleting any fixed literal enlarges the cylinder;
if deleting a larger subset still forced halting, deleting a single member of
that subset would also force it. No prime may specify an irrelevant coordinate
outside the saved variable support. `minimal-family.json` names the exact DAG
hash, roots and circuit; `minimal_query.py` implements membership and supplies
nonhalting completions after literal deletion.

**The full explicit list of minimal patterns was not enumerated.** That attempt
exceeded the node cap. The72 rows in `minimal-examples.json` are examples,
not a complete list; each includes a counterexample for deleting every literal.
The supplied circuit is the complete symbolic set, not a claim that this small
list is exhaustive. Early examples are F on1, E on11 with its head on the
right1, and D on111 with its head on the right1. C on `1110`, head on0,
halts after3 defined transitions. They illustrate why left context matters.

### Growth and the infinite question

Explicit path frontiers have30 cylinders at depth10,1,479 at20 and68,376
at30. The diagram node counts at those depths are302,5,342 and57,119.
The complete count series and counts by control state are retained in the two
result files. These are measured finite growth rates, not an asymptotic law.

One regular subfamily exists at arbitrarily large depths: start D on the last
cell of `111(10)^n`. Each D sweep preserves one10 pair and moves left in4
transitions. After4n transitions D is on the last1 of111; D1,E1 then reach
F1. Thus the exact first-halt time is4n+2. This proves that backward ancestors
do not die out and are not a finite total collection. It does not establish
regularity, nonregularity, or a cardinality growth law for the full unbounded
predecessor language.

## 2. Intersection: no meeting within this horizon

Restrict every negative variable of H_40(C) to0. The reduced root is false,
without imposing any condition on the right tape. Therefore no S,D or G
C-section can meet the depth40 halt language, including all counter/residue
values and all finite right contexts. This is stronger than the separate
regular-language product check. There is no list of special counter residues
to report: the intersection is empty at this depth, even for uncovered
C-section inputs.

A separate forward symbolic execution, with all initial nonnegative cells
free and every negative cell0, completes the same check through80 defined
transitions:397,335 symbolic states,50,368 terminal path cylinders, no halt.
This is a complete bounded computation, not a Lean theorem or an assertion of
arbitrary-time safety. It does not produce the unrestricted H80 language.

There is also an exact exclusion for **every intermediate state in a covered
C-to-C segment**, including all sweep iterations and all fixed kernels in
that segment, not just its counter-section endpoints. If R transitions remain
until its certified blank-left C endpoint, then:

* when R≥40, the certified segment itself excludes a halt during the next40;
* when R<40, it excludes a halt until that endpoint, and the C-root exclusion
  excludes one in the remaining40−R.

This argument requires the complete contextual C-to-C statement. A standalone
local kernel with arbitrary tape on both sides is not automatically a state
of the forward grammar. Local-cylinder overlaps after its endpoint do not
contradict a finite reachability lemma. The incoming brief's inference that
any overlap must start in an uncovered case would have been too strong.

For the new exit grammars, H40 restrictions also give no intersection:

    0∞ (10)^p 0(10)^c 0(10)^3 A> v, p≥0,c≥1;
    0∞ (10)^p (01)^(n−2)00(10)^3 A> v, p≥6,n≥10;
    0∞ (10)^p (01)^n B> v, p≥4,n≥10.

The right tape v is arbitrary. `guard_intersection.py` checks all parameter
classes exactly: pair lengths at least41 have identical suffixes in the
last40 cells, so41 represents the entire unbounded tail of a parameter.
This saturation argument is what turns the finite class enumeration into
an all-parameter restriction of the bounded predicate.

Thus the backward horizon does **not** prioritize1101 versus short JOIN versus
a third layer for eventual halting. The next rules are prioritized because of
the two explicit generic witnesses and the missing grammar, not because a
halt intersection was found. No such meeting point was found in the complete
bounded objects above. Finding the first meeting at a longer horizon remains
open.

## 3. Reflection and complement

Reflection sends coordinate x to−x and flips L/R. Complement exchanges the
two input branches and replaces every written bit b by1−b. It changes a
zero background to a one background. Either operation, or their combination,
is a global conjugacy to the corresponding **transformed** machine, preserving
the number of defined transitions and the halt convention. The full machine
strings and400 literal background-aware tests are in `symmetry-results.json`.

None is an automorphism of L17 obtained by a state relabeling. Reflection
changes the multiset of directions from3 R/8 L to8 R/3 L, which no state
permutation changes. Complement moves the sole undefined branch from read1
to read0, also impossible to repair by state permutation. The combined
operation has both obstructions. An exhaustive check of all720 relabelings
per transformation agrees. Identity has only the identity relabeling.

All D/G equations map to valid equations of the transformed machine: keep
their parameter values and times, reflect the head displacement and tape
coordinates if reflecting, and change01↔10 and1↔0 if complementing. Reflection
puts the written side on the other side of the head; complement puts the
exterior on1. These are transformed grammars, not extra rows of the original
zero-background C> grammar. No general exclusion of nonlinear/variable-length
conjugacies on a restricted grammar is claimed by a720-permutation test.

## 4. Five fixed paths and the short JOIN rows

All fixed paths below preserve every cell outside the specified input interval.
Arbitrary outside context is valid because the listed read windows stay within
that interval. `kernels.json` contains every literal read triple.

| Kernel | Input interval and word | Entry → exit | Steps | Output on that interval | Actual reads |
|---|---|---|---:|---|---|
|J1K|[−4,2]:0010010|D0→D−4|10|0101010|[−3,2]|
|J2K|[−7,2]:1001010010|D0→C−7|13|1101101010|[−6,2]|
|J3K|[−11,2]:10100101010010|D0→B3|39|(01)^7|[−11,2]|
|J4K|[−21,2]:(10)^6 0(10)^4 010|D0→C−21|65|11(01)^6 0(01)^4 0|[−20,2]|
|K41short|[−11,3]:(10)^6 111|C0→C−11|41|11(01)^6 0|[−10,3]|

K41short is the earlier41-step path with its unused right assumptions removed.
When followed by another1, its terminal01 joins into a seventh pair. It is
important to keep its final0 if no such1 follows. Its former7-one input was
stronger than the path's actual read requirement.

Put J_c(a,l;v)=Ccal(a;(10)^c11(01)^l11v). For a≥7,l≥1:

| Rule | Complete endpoint | Time | Head shift |
|---|---|---:|---:|
|J0 (a≥1 suffices)|Ccal(0;1^(2a+13)(01)^(l−1)11v)|10a+45|−9|
|J1|Ccal(a+l+6;0v)|6a+6l+55|−7|
|J2|Ccal(0;1^(2a−2)(01)1(01)^(l+4)0v)|4a+6l+50|−2|
|J4|Ccal(0;1^(2a−12)(01)^6 0(01)^(l+6)0v)|4a+6l+96|−2|
|J3B|0∞(10)^(a−3)(01)^(l+9) B>v0∞|2a+8l+86|2a+2l+10|

J0 is P followed by Z and a literal word equality. For c≥1, use the usual
C entry, A sweep(a+1), K11, A sweep(c), K7, A sweep(l+2), the3-step A11
finish, then D sweep(l+2). At that point D is at the second zero gap in

    0∞(10)^(a−1)0(10)^c D>0(10)^(l+2)10v0∞,

at source coordinate2a+2c−3, after2a+2c+6l+37 transitions. Now:

* c=1: J1K, D sweep(a−1), then the old10-step blank-left finish J10;
* c=2: J2K, C sweep(a−2);
* c=4: J4K, C sweep(a−7);
* c=3: J3K, B sweep(l+2), where `B1,A0` changes10→01 in2 steps.

These compositions prove the rows for all the stated parameters. No v cell
is read in any of them. Source-relative read bounds are respectively
J0:[−9,2a+2], J1:[−6,2a+2l+5], J2:[−2,2a+2l+7],
J4:[−2,2a+2l+11], J3B:[−2,2a+2l+9].

### The c=3 tail dispatcher

At J3B, consume any leading(10)^j of v with B1,A0, adding2j transitions.
Set p=a−3,n=l+9+j. For a≥9,l≥1,j≥0, the following rows cover four
disjoint prefix classes; w below is arbitrary:

| v at the original J3 entry | Endpoint | Total time from J3 source | Shift |
|---|---|---:|---:|
|(10)^j0w|Ccal(0;1^(2a−16)(01)^7 1^(2l+2j+15)w)|4a+10l+4j+128|−2|
|(10)^j111w|Ccal(0;1^(2a−12)(01)^(l+j+13)0w)|4a+12l+6j+134|−2|
|(10)^j1100w|Ccal(0;1^(2a−16)(01)^7 1^(2l+2j+1)T w)|4a+10l+4j+174|−2|
|(10)^j1101w|0∞(10)^(a−3)(01)^(l+j+7)00(10)^3 A>w0∞|2a+8l+2j+100|2a+2l+2j+14|

Every finite v, with its exterior zeros, eventually has one of these forms.
An infinite all10 right tape would remain in the B scan; that is not a finite
tail. All four rows read only through their displayed terminal prefix and
never into w. Their maximum read position is2a+2l+2j+9 plus its terminal
length (1,3,4,4), and their minimum is−2.

The compositions after the B scan are:

* 0: B0, C sweep(n), K41short, C sweep(p−6). The41-step path consumes
  four leading ones after the available final1 is joined; its tail has at
  least2n+1 ones before the path.
* 111: the8 fixed transitions B1,A1,E1,F0,D0,A1,E1,F0,
  D sweep(n−1), K22, C sweep(p−4).
* 1100: B1, K60, C sweep(n−7), K41short, C sweep(p−6).
* 1101: B1, K7, A sweep(3), giving the explicit two-zero gap.

The final row is an exact escape to an A grammar; no general C-return theorem
for that grammar is asserted. For a=7,8, J3B itself is valid, but the displayed
uniform return finishes are not claimed. The normal D11 input with q≥2 has
a=1+5q≥11 and meets the stronger a≥9 guard.

## 5. General1101 and short terminal guards

For a≥1,c≥1, any finite v:

    Ccal(a;(10)^c1101v)
      → 0∞(10)^(a−1)0(10)^c0(10)^3 A>v0∞.

Time2a+2c+28, head shift2a+2c+4, reads[−2,2a+2c+3].
Composition: C entry, A sweep(a+1), K11, A sweep(c), K7,
A sweep(3). The context v is not read. This is an all-parameter identity,
not a fitted return rule. Its endpoint records two zero holes and the full
left tape. Dropping them or silently replacing that A-state by a C-section
would change the machine.

More generally, define L=`(10)^(a−1)0(10)^c0(10)^(l+2)` and
H=2a+2c+2l+2. For a≥1,c,l≥1:

    Jentry: Ccal(a;(10)^c11(01)^l v) → 0∞L A>v0∞,

time2a+2c+2l+26, shift H, reads[−2,H−1]. This is the1101 row followed
by A sweep(l−1). It works for every terminal size, including0,1,2.
Two short fixed finishes supply exact kernels without further counter guards:

* v=00w: A0,B0 gives `0∞L C>11w0∞`, time Jentry+2, shift H;
* v=10w: A1,E0,B0 gives the same finite word L10w, with C at H−1,
  its head on the last0 of L, time Jentry+3.

These are `Jlow0` and `Jlow1` in the declarative file. They are **not**
blank-left C endpoints; their recorded target word starts at source−2.
They cover the local short terminal kernels universally, while leaving a
return to D/G/S as a separate obligation. For s=2, A1,E1,F0 followed by
the ordinary D sweep gives the c-specific finishes above, or the existing
JOIN when c≥5. In that case retain the output0; the s≥3 normalization
cannot be used at s=2.

Here are two longer finishes particularly useful for the known witnesses.
For a≥7,c≥7,l≥1 and arbitrary w:

    Ccal(a;(10)^c11(01)^l00w)
      → Ccal(0;1^(2a−12)(01)^7 1^(2c−13)(01)^7 1^(2l+3)w),

time4a+4c+4l+92, shift−2. Compose Jentry,A00,C sweep(l+3),
K41short,C sweep(c−5),K41short,C sweep(a−7).

For a≥7,c≥7,l≥7:

    Ccal(a;(10)^c11(01)^l100w)
      → Ccal(0;1^(2a−12)(01)^7 1^(2c−13)(01)^7 1^(2l−13)T w),

time4a+4c+4l+134, shift−2. Compose Jentry,K60,C sweep(l−5),
K41short,C sweep(c−5),K41short,C sweep(a−7).
Their read bounds are[−2,2a+2c+2l+3] and[−2,2a+2c+2l+4].
The stronger finish guards are explicit: no claim of return is being made
for c=5,6 or, in the second row, l≤6. The local Jentry/Jlow paths still apply
there. The remaining problem is closing their nonblank-left exit grammar.

### The two earlier generic witnesses

The a=37 push witness previously stopped at D(2425,4,1;7,3).
E,Q with q=808 gives J4(4041,7;1). J4 yields
G(8070,6;14,0). The existing G0 row then reaches
`Ccal(0;1^26919(01)^13)`, a one-tail state. Total from D2425 is
118,446,578 transitions, displacement−24,494. These counts are compositions
of the old row formulas; the long Q/G0 stretches were not literally replayed.

The a=46 push witness stopped at D(3070,7,1;14,0). E,Q with q=1023
followed by Jend0 reaches D(10220,7,1;7,31). Total15,730,853 transitions,
displacement−7,165. Again this is a generic-state continuation, not a new
blank-orbit prefix. The new J4/Jend0 portions themselves fit the raw-probe cap.

### A third layer really can be produced

Set q=2 in D11 and a=11,c=l=7 in Jend1. Then

    D(7,7,1;7,1)
      → Ccal(0;1^10(01)^7 1(01)^7 1(01)^7 1^3)

in320 defined transitions with head displacement−18. A complete literal
C++ and Python replay checks this same endpoint. It has three nonempty
alternating blocks, separated by genuine11 separators. Since it starts with1,
its initial pair prefix is0; it cannot be normalized into an S or a two-tail D
shape. Nor is it G: G has a00 gap, absent from this target. Thus universal
two-tail closure fails on the full D input grammar. **Reachability of this
source from the blank tape is not established.** Bounded stack on the blank
orbit is still open.

## Evidence and limits

The final endpoint campaign has1,071 rule probes, including exhaustive3-value
local guard grids and seeded larger inputs, all compared with the C++ literal
interpreter.969 have full Python/C++ read-trace comparison;160 additional
kernel checks randomize both outside contexts. There are569 predicate-witness
replays and400 exact transformed-background checks. All20 planted in-memory
mistakes are detected. Same-compiler O2/O0/UBSan builds are controlled replays,
not replication by another author or toolchain. Exact reports retain the counts.

P: no new formal proof claim. A: the displayed universal compositions and
symmetry obstructions. M: complete bounded diagrams/searches and execution
checks. H: arbitrary-time return for the new A/nonblank-C grammars and blank
stack bounds. R: any promotion from these finite exclusions to nonhalting,
from generic third-layer production to blank reachability, or from table
relabel tests to exclusion of arbitrary grammar conjugacy.

Spatial reflection preserves the direction of time. It is not reversal of
the raw step relation, whose noninjectivity is already recorded in the
preceding work. Restricted internal D/G inverse uniqueness does not turn that
raw backward tree into a single reverse orbit.

`CORRECTIONS.md` records resource failures and the explicit-enumeration limit.
No global halt/nonhalt decision is claimed.
