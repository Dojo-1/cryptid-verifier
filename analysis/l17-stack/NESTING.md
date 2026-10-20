# A context-preserving nesting identity for L17

This is a mathematical derivation with literal-path checks, **not a new Lean
theorem**. It concerns general inputs; it does not assert unbounded depth on the
blank-tape run.

Use the machine and head convention of the preceding contribution:

```
1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---
Ccal(a;w) = 0^infinity C> (01)^a w 0^infinity.
```

Only trailing exterior zeros are implicit. Define the two **17-cell** words

\[
U=(01)^8 1,\qquad T=(01)^7 1^3.
\]

For every integer `a>=7`, `n>=0`, and arbitrary finite right context `v`, the
derived rule is

\[
\boxed{\mathcal C(a;1U^n00v)\longrightarrow
\mathcal C(0;1^{2a-12}T^{n+1}v).}
\]

It takes **`4a+74n+50` defined transitions**, with head displacement **`-2`**.
The two displayed zeros before `v` are essential. For a blank suffix they are
supplied by the exterior zeros. Without subtraction, put `a=u+7`: the leading
ones number `2u+2`, and the time is `4u+74n+78`.

For example, `C(7,1) . U^2` reaches `C(0,2) . T^3` in **226** transitions.
The old two-layer example is `n=1`, with time 152. These are general input
witnesses; neither input is asserted to occur on the blank orbit.

## Fixed paths and their complete windows

Coordinates in this table are local to the input A head at zero, except K41,
whose entry C head is at `-5`. All positions outside the stated input interval
are preserved. Each path is tabulated with all literal reads in
`nesting-kernels-exploratory.json`, then independently checked by the C++ machine
with random exterior tape in `nesting-windows.jsonl.gz`.

| Path | Complete input interval and word | Entry | Exit | Complete output on that interval | Time | Read interval |
| --- | --- | --- | --- | --- | ---: | --- |
| K7 | `[-4,2]: 1010101` | A at 0 | A at -3 | `0(01)^3` | 7 | `[-4,1]` |
| K27 | `[-4,17]: 1010 1 U` | A at 0 | A at 17 | `0(10)^10 1` | 27 | `[-4,16]` |
| K41 | `[-16,2]: (10)^6 1^7` | C at -5 | C at -16 | `11 T` | 41 | `[-15,-2]` |
| K60 (existing) | `[-16,2]: (10)^8 100` | A at 0 | C at -16 | `11 T` | 60 | `[-15,2]` |

K7 is the literal path `A1,E0,B0,C0,D1,E0,B1`. It ends at A at -3.
K27 is K7 followed by the existing A sweep over ten `01` pairs. After K7 the
three new pairs occupy `[-3,2]`; the seven remaining pairs of the first U occupy
`[3,16]`. The final `1` at position 17 is not read. The A sweep converts the ten
pairs into `10` pairs and exits at A at 17. In particular, `[1,16]` now contains
exactly `(10)^8`.

The other sweep used below is the existing two-step path `C1,B0`: C at the
right cell of `01` converts it to `11` and moves two cells left. It preserves
arbitrary outside contexts.

## Induction at the A section

First prove the following local lemma, with arbitrary context on **both** sides:

```
input [-16,17n+2]: (10)^8 A> 1 U^n 00
    -> C> 11 T^(n+1)
```

The source A head is at 0; the target C head is at -16. The interval length is
`19+17n` on both sides. The time is `60+74n`, and no cell outside this interval
is read or written. More precisely all reads lie in `[-15,17n+2]`.

Base `n=0` is K60.

For `n+1`:

1. Apply K27. It reaches A at 17 in 27 transitions. Its last eight output `10`
   pairs are exactly `[1,16]`, so the induction hypothesis is available there,
   translated by 17. The unprocessed input is `1 U^n 00 v` starting at 17.
2. Apply the induction hypothesis. It exits at C at 1 with `11 T^(n+1) v`
   starting at 1. The outer cells below 1 remain as K27 left them.
3. Apply the C sweep to the three `01` pairs `[0,1]`, `[-2,-1]`, and `[-4,-3]`.
   This takes six transitions and exits at C at -5. Now `[-16,2]` is exactly
   `(10)^6 1^7`: the six old pairs below -4, six newly formed ones, and the
   second leading one of the inner endpoint at 2.
4. Apply K41. It exits at C at -16 with `11T` on `[-16,2]`. The untouched inner
   `T^(n+1)v` begins at 3, so the whole output is `11 T^(n+2) v`.

The time is `27+(60+74n)+6+41=60+74(n+1)`. The read intervals just given also
prove context preservation inductively. There is no experiment over an infinite
parameter hidden in this step: it is an induction on a finite word power.

## Return to the C section

From `Ccal(a;1U^n00v)`, execute the existing entry `C0,D0` (two transitions),
then the A sweep over `a+1` pairs (time `2(a+1)`). A reaches the initial displayed
one, with at least eight `10` pairs to its left because `a>=7`.

Apply the A-section lemma, then sweep C left through the remaining `a-7` shifted
`01` pairs. This final sweep contributes `2(a-7)` transitions and `2(a-7)`
leading ones. Its final head is two cells left of the original C head. The total
leading count is `2+2(a-7)=2a-12`, and

```
2 + 2(a+1) + (60+74n) + 2(a-7) = 4a+74n+50.
```

The suffix `v` is never read. This proves the displayed contextual identity as a
mathematical composition of the fixed paths, the two sweep inductions, and the
A-section induction.

## What this does and does not settle

This gives a uniform **one-layer push** for arbitrarily deep inputs of a
specified shape. A universal one-tail template is inadequate. The output powers
`T^n` still have a compact one-counter encoding; a large block-depth by itself
does not prove that every counter encoding needs an unbounded number of
counters.

It does not make the outputs iterable inputs to this same rule: U and T differ.
Therefore it proves neither unbounded depth along one fixed orbit nor unbounded
depth on the blank orbit. General interacting prefixes, such as `(10)^c1101v`
with unequal block widths, and the relevant low guards remain separate work.

For Claude, the short formalization path is: reuse the A and C sweep lemmas and
the existing 60-step segment; prove K7 and K41 with their read windows; induct on
`n` at the A section; compose with the C entry. `nesting-claims.json` is the exact
specification consumed by the new comparator campaign.
