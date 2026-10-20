# L17: the two nonzero residues and the tail calculus

## Handoff to Claude

Claude owns the divisible-by-three branch and its Lean proof. This contribution
handles the other residues. For every natural number `j`, the proposed exact
raw-machine transitions are:

| Source | Complete finite word to the right of the target C-state head | Raw transitions | Head displacement |
| --- | --- | --- | --- |
| `C(3j+7,1)` | `1^(20j+15) (01)^6 1^3` | `60j^2+136j+135` | `-14j-13` |
| `C(3j+8,1)` | `1^(20j+4) (01)^14` | `60j^2+136j+215` | `-14j-13` |

Both exterior regions are zero. The head reads the first symbol immediately to
its right. These endpoints have empty left tapes; they are not merely selected
substrings of a larger unknown tape. The guards cover `a>=7, a mod 3=1` and
`a>=8, a mod 3=2`. Small `a` cases are not covered by these formulas.

The derivation below is mathematical, with checked fixed paths and finite full
tape comparisons. **No new Lean theorem or Lean build is claimed here.** Claude
reports that PR #6 proves the divisible-by-three rule and the blank entry to
`C(6575648756,1)`. Those files remain inaccessible to this environment and were
not independently inspected here. The incoming boundary is therefore supplied
context for this contribution.

The expanded handoff also covers every one-tail input
`C(x,b) . (01)^c 1^r` with `x>=7`, `c>=1`, `r>=0` and `b=0,1,2`.
One such input creates two tail layers. This disproves closure of that
single-tail shape, but does not prove unbounded stack growth on the blank orbit.

The two main proof obligations can be stated without subtraction:

```text
stacked_residue1 (j : Nat):
  C(3*j+7,1) reaches 0^inf C> 1^(20*j+15) (01)^6 1^3 0^inf

stacked_residue2 (j : Nat):
  C(3*j+8,1) reaches 0^inf C> 1^(20*j+4) (01)^14 0^inf
```

These are specifications for formalization, not compiled Lean syntax.

## Machine and section

```text
1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---
```

| State | Read 0 | Read 1 |
| --- | --- | --- |
| A | 1RB | 0RE |
| B | 1LC | 0RA |
| C | 0LD | 1LB |
| D | 1LA | 1LE |
| E | 0LB | 0LF |
| F | 1LD | halt |

Define the contextual section

\[
\mathcal C(a;w)=0^\infty\ C>\ (01)^a w\ 0^\infty,
\]

where `w` is any finite binary word and `a>=0`. Its representation need not be
unique: `Ccal(a;(01)^q w) = Ccal(a+q;w)` is literal tape equality with no
transitions. The old `C(a,b)` is `Ccal(a;1^b)`.

All transition counts below count defined raw TM transitions. An undefined
transition halts without writing or moving. Every displayed displacement is
relative to the source head, so the statement specifies the complete physical
tape endpoint, not just a normalized picture.

## Elementary rules with arbitrary right context

For every finite `w`:

| Name and guard | Transition | Steps | Head shift |
| --- | --- | ---: | ---: |
| E, no pair prefix | `Ccal(0;1w) -> Ccal(1;1w)` | `2` | `-2` |
| Z, `a>=0` | `Ccal(a;00w) -> Ccal(0;1^(2a+4) w)` | `4a+8` | `-2` |
| P, `a>=1` | `Ccal(a;11w) -> Ccal(a+4;0w)` | `6a+21` | `-7` |
| D, `a>=1` | `Ccal(a;111w) -> Ccal(a+5;w)` | `6a+21` | `-7` |

E is the path `C1,B0` into the exterior blank on the left. Z is the earlier
empty-suffix derivation with its two required zeros made explicit. P is the
earlier two-one branch with the formerly implicit output zero retained. D
follows from P because `(01)^(a+4) 01w = (01)^(a+5) w`.

These contextual statements are stronger than merely instantiating the old
blank-suffix theorems. Their proofs use the same local sweeps, whose paths never
read the untouched `w`. The context preservation must be included in the Lean
proof, rather than inferred from a bounded example.

For Z, use `C0,D0`, the A sweep over `n=a+1` pairs, `A0,B0` on the
two displayed zeros, then the C sweep over `n` shifted pairs. Nothing reads
`w`. For P, use the same entry and A sweep, `A1,E1,F0`, the D sweep over
`n` pairs, and the ten-transition left finish tabulated below. This gives
`(01)^(n+3)0w`. Again the suffix after the two required ones is untouched.

Iterating D `q` times, starting with `a>=1`, gives

\[
\mathcal C(a;1^{3q}w)\longrightarrow
\mathcal C(a+5q;w)
\]

in `15q^2+(6a+6)q` transitions, with displacement `-7q`. For `q=0` this is
identity. The sum is `sum(6(a+5i)+21, i=0..q-1)`.

## Local paths suitable for finite Lean proofs

The three repeatable block paths are:

| Entry | Path | Exit | Block effect |
| --- | --- | --- | --- |
| A at the left cell of `01` | `A0,B1` | A immediately right | `01 -> 10` |
| D at the right cell of `10` | `D0,A1,E1,F0` | D immediately left | `10 -> 10` |
| C at the right cell of `01` | `C1,B0` | C immediately left | `01 -> 11` |

Because each path reads only its own two-cell block and returns the same
control state at the next boundary, induction gives sweeps of `2n`, `4n`, and
`2n` transitions respectively. Both outside contexts are arbitrary.

The new fixed segments have the following complete finite effects. Positions
are local coordinates, independent of the source machine's absolute position.
Cells outside each listed input interval are untouched.

| Segment | Input interval and word | Entry | Exit | Output word | Actual read positions |
| --- | --- | --- | --- | --- | --- |
| K11 | `[-4,1]: 101010` | A at `0` | A at `1` | `010100` | `[-4,1]` |
| K43 | `[-16,-1]: 1010101010100111` | C at `-3` | C at `-16` | `1101010101010101` | `[-15,-2]` |
| K22 | `[-12,0]: 1010101001010` | D at `-4` | C at `-12` | `1101010101010` | `[-11,-2]` |

K11 takes 11 transitions, K43 takes 43, and K22 takes 22. The literal paths,
each read state, position and symbol, and their checked endpoints are retained
in `validation-results.json` under `kernel_witnesses`. That data also contains
the two-step `A00 -> C` path writing `11`, and the three-step `A11 -> D` path
writing `10`. These are small finite path goals; the variable-sized parts of
the proof are only the three sweep inductions and their composition.

## First new contextual lemma: F100

For `a>=7`, `c>=0` and arbitrary finite `v`:

\[
\boxed{\mathcal C(a;(10)^c100v)\longrightarrow
\mathcal C(0;1^{2a-12}(01)^7 1^{2c+3}v).}
\]

It takes `4a+4c+50` raw transitions and shifts the head by `-2`.

For a statement without natural-number subtraction, substitute `a=u+7`; the
new leading-one count is `2u+2` and the time is `4u+4c+78`.

Proof composition, putting `n=a+1>=8`:

1. The entry `C0,D0` prepends one `01` pair and reaches A two cells left.
2. Sweep A right across `(01)^n` in `2n` steps, producing `(10)^n`. Set local
   position `0` to the start of `(10)^c100v`. Thus the left word occupies
   `[-2n,-1]`.
3. Apply K11, ending at A at position `1`.
4. Sweep A across the next `c` copies of `01`. They include the first 1 of the
   terminal `100`. This ends at A at `2c+1`, on the first of its two zeros.
5. Execute `A0,B0` on those zeros. C is now at `2c+1`, with two newly written
   ones at `2c+1,2c+2`.
6. Sweep C left across `c+2` copies of `01`, ending at C at `-3`. The word on
   `[-16,-1]` is exactly K43's input. The right context from position `0` is
   `1^(2c+3) v`.
7. Apply K43. Its output is `11(01)^7`, and C is at `-16`. It does not read
   the right context at position `0` or beyond.
8. Sweep C left across the remaining `n-8` shifted `01` pairs. This turns the
   leading portion into `1^(2(n-8)+2)`, which is `1^(2a-12)`, and ends at
   local `-2n`, two cells left of the original source head.

The time sum is

```text
2 + 2n + 11 + 2c + 2 + 2(c+2) + 43 + 2(n-8)
= 4a + 4c + 50.
```

The case `c=0` is included: the first A sweep in step 4 is empty. The two
terminal zeros still supply the A00 path in step 5. In the original singleton
suffix, these are the first two exterior blank cells.

## Second new contextual lemma: F111

For `a>=5`, `c>=1` and arbitrary finite `v`:

\[
\boxed{\mathcal C(a;(10)^c111v)\longrightarrow
\mathcal C(0;1^{2a-8}(01)^{c+6}0v).}
\]

It takes `4a+6c+38` raw transitions and shifts the head by `-2`.

Without subtraction, write `a=u+5`, `c=d+1`: the target is
`Ccal(0;1^(2u+2) (01)^(d+7) 0v)` and the time is `4u+6d+64`.

Proof composition, putting `n=a+1>=6`:

1. As above, use the two-step C entry, the A sweep across `n` pairs, K11, and
   the A sweep across `c` pairs. A is at local `2c+1`, on the second of the
   three terminal ones.
2. The path `A1,E1,F0` writes `10` and leaves D at `2c`.
3. Sweep D left across `c+2` unchanged `10` pairs in `4(c+2)` steps. D is at
   `-4`; the finite word on `[-12,0]` is K22's input.
4. Apply K22. C ends at `-12`, and the word on `[-12,0]` is `11(01)^5 0`.
   The untouched right context from position `1` is `(10)^(c+1) v`.
5. Sweep C across the remaining `n-6` shifted `01` pairs on its left. The
   leading ones number `2(n-6)+2 = 2a-8`. Use the literal identity
   `0(10)^(c+1) = (01)^(c+1)0` to obtain the stated target. No extra machine
   transitions are required for this word equality.

The time sum is

```text
2 + 2n + 11 + 2c + 3 + 4(c+2) + 22 + 2(n-6)
= 4a + 6c + 38.
```

The bounds `a>=5,c>=1` are essential for these particular fixed contexts.
Inserting an arbitrary `v` after the three ones is safe because none of these
paths reads it.

## Third contextual lemma: F1100 creates a second layer

For `a>=7`, `c>=7` and any finite `v`:

\[
\boxed{\mathcal C(a;(10)^c1100v)\longrightarrow
\mathcal C(0;1^{2a-12}(01)^7 1^{2c-13}(01)^7 1^3v).}
\]

It takes `4a+4c+92` transitions and shifts the head by `-2`.
With `a=u+7,c=d+7`, the leading counts become `2u+2` and `2d+1`,
and the time is `4u+4d+148`; no natural-number subtraction is needed.

One additional fixed path suffices:

| Segment | Complete input interval | Entry | Exit | Complete output | Actual read positions |
| --- | --- | --- | --- | --- | --- |
| K60 | `[-16,2]: (10)^8 100` | A at `0` | C at `-16` | `11(01)^7 1^3` | `[-15,2]` |

The literal 60-transition path, including each read, is in
`tail-family-checks.json`. Its suffix after position `2` is arbitrary.

Put `n=a+1`. Use the C entry, the A sweep over `n` pairs, K11, and the
A sweep over `c` pairs exactly as for F111. A is at local `2c+1`, the
second terminal one. The input to K60, translated by `2c+1`, is now present:
its leftmost cell is `2c-15`, and its last two cells are the required zeros.
The bound `c>=7` keeps this window within the established right sweep.

K60 leaves C at `2c-15` with `11(01)^7 1^3v` to its right.
Sweep C left through `c-6` shifted pairs, ending at local `-3`.
The K43 window on `[-16,-1]` is present; the context starting at local `0`
is `1^(2c-13)(01)^7 1^3v`. Apply K43 and the remaining C sweep of
`n-8` pairs. This yields the displayed whole-tape target, without reading `v`.

```text
2 + 2n + 11 + 2c + 60 + 2(c-6) + 43 + 2(n-8)
= 4a + 4c + 92.
```

In particular, with `T=(01)^7 1^3`,

```text
C(7,1) . (01)^8 1  ->  C(0,2) . T . T
```

in exactly **152 transitions**, head shift `-2`. Both terminal zeros on the
left are supplied by the exterior blank. The entire target contains two
separated alternating blocks, so it cannot be written
`C(a,b) . (01)^c 1^r` for any nonnegative parameters. This is an explicit
counterexample to universal single-tail closure. It is not asserted reachable
from the blank start.

## Six short cases of the 1100 suffix

The following rules have source `Ccal(a;(10)^c1100v)`, with common guard
`a>=7`, arbitrary finite `v`, and `1<=c<=6`:

| `c` | Target | Transitions | Head shift |
| ---: | --- | ---: | ---: |
| 1 | `Ccal(0;1^(2a-2)(01)^2 1^6 v)` | `4a+36` | `-2` |
| 2 | `Ccal(0;1^(2a-10)(01)^10 v)` | `4a+110` | `-2` |
| 3 | `Ccal(a+7;1^3 v)` | `6a+75` | `-7` |
| 4 | `Ccal(0;1^(2a-2)(01)1(01)^5 1^3 v)` | `4a+70` | `-2` |
| 5 | `Ccal(0;1^(2a-12)(01)^14 v)` | `4a+154` | `-2` |
| 6 | `Ccal(0;1^(2a-12)(01)^6 0(01)^7 1^3 v)` | `4a+116` | `-2` |

For five rows, use the common C entry and A sweep over `n=a+1` pairs.
With local zero at the start of `(10)^c1100v`, the following fixed paths
apply. Their input is `(10)^m (10)^c1100` on `[-2m,2c+3]`, entry A at `0`,
exit C at `-2m`. The suffix `v` starts at `2c+4` and is never read.

| `c` | `m` | Kernel steps | Complete kernel output | Actual read interval |
| ---: | ---: | ---: | --- | --- |
| 1 | 3 | 36 | `11(01)^2 1^6` | `[-5,5]` |
| 2 | 7 | 118 | `11(01)^10` | `[-13,7]` |
| 4 | 3 | 70 | `11(01)1(01)^5 1^3` | `[-5,11]` |
| 5 | 8 | 164 | `11(01)^14` | `[-15,13]` |
| 6 | 8 | 126 | `11(01)^6 0(01)^7 1^3` | `[-15,15]` |

Finish with the C sweep over the remaining `n-m` shifted pairs. This adds
`2(n-m)` leading ones to the two already displayed, and gives total
`2+2n+K+2(n-m) = 4a + K + 6 - 2m`, proving the five table entries.
The final head is local `-2n`, hence the source displacement is `-2`.

For `c=3`, replace that kernel and final sweep by these paths:

| Segment | Complete input interval | Entry | Exit | Complete output | Actual reads |
| --- | --- | --- | --- | --- | --- |
| K65 | `[-4,9]: (10)^5 1100` | A at `0` | D at `-5` | `(10)^5 1^4` | `[-4,9]` |
| J10 | `[-4,2]: 0000010` | D at `0` | C at `-4` | `0101010` | `[-3,2]` |

After K65, the remaining left word is `(10)^(n-2)`. Sweep D across it in
`4(n-2)` steps. It reaches the exterior zero at local `-2n-1`, followed
by `(10)^(n+3)1^4`. Apply the translated J10. This gives
`(01)^(n+6)1^3v`, C at local `-2n-5`. Thus the target is
`Ccal(a+7;1^3v)`, the displacement is `-7`, and the time is
`2+2n+65+4(n-2)+10 = 6a+75`.

All seven literal path witnesses and read traces are in
`small-tail-checks.json`. The single common guard `a>=7` ensures `n>=m`
in every row; no assertion of minimal guards is needed.

## Direct rules for the proposed one-tail family

Write `W(c,r)=(01)^c1^r`, with `c>=1,r>=0`. The formulas below cover all
three requested branches for `x>=7` (some individually have weaker guards).
Every target is again a complete tape configuration with empty left exterior.

| Source | Target | Transitions | Head shift |
| --- | --- | ---: | ---: |
| `C(x,0) . W(c,r)` | `C(x+c,r)` | `0` | `0` |
| `C(x,2) . W(c,r)` | `C(0,2x+13) . W(c-1,r)` | `10x+45` | `-9` |
| `C(x,1) . W(c,0)` | `C(0,2x-12) . W(7,2c+3)` | `4x+4c+50` | `-2` |
| `C(x,1) . W(c,2)` | `C(0,2x-8) . W(c+6,0)` | `4x+6c+38` | `-2` |
| `C(x,1) . W(c,r)`, `r>=3` | `C(0,2x-8) . W(c+7,r-3)` | `4x+6c+38` | `-2` |
| `C(x,1) . W(c,1)`, `c>=7` | `C(0,2x-12) . (01)^7 1^(2c-13) T` | `4x+4c+92` | `-2` |

For `r=1,c=1..6`, use the six-row table above with `v` empty. These
additional rows complete the table at the common `x>=7` guard. For `c=0`,
the tape identity `C(x,b) . W(0,r)=C(x,b+r)` returns to the original section.

The b=0 rule is tape equality. For b=2, use P, rewrite
`0(01)^c=001(01)^(c-1)`, then use Z; the costs are
`6x+21 + 4(x+4)+8 = 10x+45`. For b=1 use the identities
`1(01)^c=(10)^c1`, followed by F100, F111 or F1100. With `r>=3`,
absorb the output `01` into the alternating block. With `r=1`, the two
zeros following its terminal `11` come from the blank exterior.

The arbitrary-context lemmas preserve an additional suffix whenever their
displayed prefixes hold. They do not yet cover all interactions between
multiple layers: in particular `(10)^c1101v`, which has only one separating
zero, is different from the required `(10)^c1100v`.

## Composing the two residue transitions

### Input `a=3j+7`

F100 with `c=0` yields

```text
Ccal(0; 1^(6j+2) (01)^7 1^3).
```

Apply E, then `2j` countdown steps D. The result is

```text
Ccal(10j+1; 11 (01)^7 1^3).
```

Apply P and rewrite `0(01)^7 = 00 1(01)^6`. Then apply Z. The result is

```text
Ccal(0; 1^(20j+15) (01)^6 1^3).
```

The total is

```text
(12j+78) + 2 + (60j^2+24j) + (60j+27) + (40j+28)
= 60j^2+136j+135.
```

The displacement is `-2-2-14j-7-2 = -14j-13`. This also covers `j=0` because
the countdown is then empty and all other guards hold.

### Input `a=3j+8`

F100 and E give

```text
Ccal(1; 1^(6j+4) (01)^7 1^3).
```

Apply `2j+1` countdown steps, obtaining

```text
Ccal(10j+6; 1 (01)^7 1^3)
= Ccal(10j+6; (10)^7 1^4).
```

F111 applies with `c=7`, `v=1`. Its output is

```text
Ccal(0; 1^(20j+4) (01)^13 01)
= Ccal(0; 1^(20j+4) (01)^14).
```

The total is

```text
(12j+82) + 2 + (60j^2+84j+27) + (40j+104)
= 60j^2+136j+215.
```

The displacement is `-2-2-7(2j+1)-2 = -14j-13`. At `j=0` the F111 pair count
is 6, so its `a>=5` guard is satisfied.

## The next boundary supplied by Claude

Claude's supplied next boundary is `C(6575648756,1)`. It has
`j=2191882916` in the second formula, giving the derived endpoint

```text
0^inf C> 1^43837658324 (01)^14 0^inf.
```

Its relative transition count is `288261043345255860151` and head displacement
is `-30686360837`. This large-time calculation is arithmetic using the derived
rules, not a raw simulation or a new Lean certificate.

For an additional bounded algebraic trace, `rules.trajectory` applies only the
guarded contextual rules above. Starting at that same source, after 26
rewrites, including literal zero-step normalization, it returns to the old
two-counter section at

```text
C(30066981019881,27)
```

with relative time `596059321589371091992405650` and head displacement
`-60120810742272`. The registered follow-up stop was 100 contextual rewrites;
at that stop the derived endpoint is `C(862312594128352370665051,0)`.
Every arithmetic checkpoint is in `validation-results.json`. These derived
prefixes require formalizing the contextual lemmas before they can become
machine-level Lean theorems. No infinite continuation or halting result is
inferred from reaching the stop budget.

After the explicit user request to continue, a separate prospective phase
raised only the symbolic rewrite budget to 2,000; it did not extend any raw
probe or overwrite the first trace. The same original guarded engine completes
all 2,000 rewrites, reaching the budget without an unsupported case or halt.
The final pair counter has 296 decimal digits and the final residual word is
`11(01)^7 1^3`; the exact counter, cumulative time and displacement are in
`symbolic-extension.json`. Of the 2,000 source shapes, 1,895 are single-tail
states and 105 are the intermediate zero-prefixed P-to-Z bridge. No extra
tail layer is observed in this finite prefix.

This extension does not invoke F1100 or the six short rules: they were derived
afterward and are supplied as separate lemmas. Thus the 2,000-step trace and
the earlier validation remain reproducible by the frozen rewrite engine.
Whether the blank orbit eventually needs an additional layer, a new prefix,
a small guard, or reaches a halt remains open. Single-tail closure fails in
general; neither reachable finite-family closure nor unbounded stack growth
has been established.

## Validation, controls and limits

- 76 residue inputs through `a=120`, both formulas, passed complete raw-TM tape,
  state, head and transition-count checks.
- 64 seeded larger/translated probes passed; these are input/translation
  checks, not 64 distinct parameter values.
- 512 arbitrary suffix contexts checked F100 and F111, including the guard
  boundaries, interior zeros, and several alternating-run lengths.
- Of 1,000 seeded random contextual inputs, 933 had an applicable guarded
  rewrite and passed; the other 67 remained explicitly unsupported.
- An independent fixed-block evaluator was compared with the dense raw
  interpreter on another 300 random complete states. Every rule endpoint was
  also checked with both block widths 2 and 6.
- All reference probes respected 200,000 raw transitions; the maximum for the
  residue/core probes was 195,911. Block evaluation used the recorded
  200,000-event cap, without horizon extensions.
- Fourteen unittest methods pass. They additionally cover exact word identities
  at enormous counts, the fixed paths' read boundaries, invalid guards, halting,
  event budgets and restart invariance.
- A separate grid supplies 1,680 one-tail endpoint checks, 256 arbitrary suffix
  checks of F1100 and 64 larger F1100 probes. A second phase covers all 48
  short-tail grid gaps with 684 `a=7..120,c=1..6` checks plus 64 larger
  arbitrary-suffix checks. The maxima in the two phases are 84,008 and 59,517
  raw transitions, both below the same 200,000 bound.
- In total, the three validators perform 4,333 rule endpoint probes and
  another 300 random interpreter controls. These are check counts, not a claim
  of 4,633 distinct inputs. Each rule endpoint is checked with the dense raw
  interpreter and both independent block widths, 2 and 6.

The dense and block interpreters are separate code paths by the same author;
they are not external independent replication. The block evaluator initially
dropped a leading zero block during input encoding. A random dense comparison
caught the misalignment, it was corrected, and a dedicated regression test is
included. The endpoint formulas did not change.

These are proof-ready derivations and bounded implementation checks. They do
not establish a complete closed reduction: low guards and stacked prefixes
such as `(10)^c1101v` still require analysis. The frozen rewrite engine also
leaves the later-derived F1100 family out of its dispatch. There is no new
cryptid discovery or halting/non-halting theorem here.

## Evidence ledger and next bounded task

| Tag | Result | Remaining obligation |
| --- | --- | --- |
| M | Complete finite endpoint comparisons and fixed path witnesses | External replication and formal interpreter correctness |
| A | Three general contextual lemmas, six short-tail rules and both residue formulas | Formalize their fixed windows and compose the sweep inductions in Lean |
| A | A one-tail input creates two layers | This is not a reachable-unbounded-stack theorem |
| A | Derived large-time checkpoints and a 2,000-rewrite prefix | Lean formalization and connection to the supplied incoming boundary |
| H | Complete stacked dynamics for L17 | Low guards and stacked prefixes such as `1101` |
| R | Treating finite matches or 2,000 successful rewrites as non-halting | No such inference is supported |

The next bounded proof task is to formalize F100 and F111 for arbitrary finite
right context, then derive the two residue lemmas. F1100 and the six short
cases can follow from the additional finite kernels and the same sweeps.
Stop on any kernel/context
mismatch; do not patch an unrestricted lemma by silently assuming a blank
suffix. Promotion requires actual Lean theorem statements and a passing build,
with raw time formalized separately from reachability if that remains the
project's convention.
