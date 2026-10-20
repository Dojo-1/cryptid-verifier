# L17: a partial two-counter reduction

The candidate is

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

Write `C(a,b)` for the **entire** tape configuration

```text
0^infinity C> (01)^a 1^b 0^infinity
```

Here the head reads the symbol immediately to its right, `a,b >= 0`, and both
exterior regions are blank. The formulas include the head displacement, so they
are equalities of complete tape configurations up to the specified translation.
An undefined transition halts without a write or move; step counts count defined
transitions.

## Four branches and an explicit open boundary

| Guard | Target | Raw transitions | Head displacement |
| --- | --- | --- | --- |
| `b = 0` | `C(0, 2a+4)` | `4a+8` | `-2` |
| `a = 0, b >= 1` | `C(1,b)` | `2` | `-2` |
| `a >= 1, b = 2` | `C(a+4,0)` | `6a+21` | `-7` |
| `a >= 1, b >= 3` | `C(a+5,b-3)` | `6a+21` | `-7` |
| `a >= 1, b = 1` | **Unsupported** | — | — |

These formulas have the derivation below and 4,433 distinct raw-TM endpoint
checks. The derivation has not been formalized in Lean. This is a partial
reduction: nothing here proves that the unsupported branch returns to this
section, halts, or avoids halting. Endpoint checks alone are finite evidence.

## Derivation from local sweeps

Three fixed paths never read outside the indicated two-cell block:

| Entry | Path | Exit | Block effect |
| --- | --- | --- | --- |
| A at the left cell of `01` | `A0, B1` | A just right of the block | `01 -> 10` |
| D at the right cell of `10` | `D0, A1, E1, F0` | D just left of the block | `10 -> 10` |
| C at the right cell of `01` | `C1, B0` | C just left of the block | `01 -> 11` |

Each path leaves its entry state at the next block boundary. Induction on the
number of disjoint blocks therefore gives sweeps of lengths `2n`, `4n`, and
`2n`. `test_local_sweeps_never_read_outside_their_block` checks the local paths,
including their complete block output and head position. The induction and the
composition below are mathematical arguments, not an implemented proof kernel.

When the head at C reads 0, `C0, D0` move the head two cells left to A and prepend
one `01` pair. Thus `C(a,b) -> A(a+1,b)` in two transitions when `a>=1` or `b=0`.
When `a=0,b>=1`, `C1,B0` instead give `C(1,b)` in two transitions.

Put `n=a+1` after the first of these entry paths.

For `b=0`, sweep A right across `(01)^n`, converting it to `(10)^n`. Execute
`A0,B0` on the two blank cells at the right boundary. The tape word is now
`(10)^n11 = 1(01)^n1`, with C at the right cell of its last `01` pair. Sweep C
left across those `n` pairs, obtaining `1^(2n+2)` with C on its first symbol.
The total is `2 + 2n + 2 + 2n = 4a+8`, with head shift `-2`.

For `b>=2`, sweep A right across `(01)^n`, then execute `A1,E1,F0` on the first
two suffix ones. This leaves D on the rightmost cell of `(10)^n`, followed by
`10 1^(b-2)`. Sweep D left across all `n` unchanged `10` pairs in `4n` transitions.
The head is now at position `-1` relative to the A entry position, immediately
left of a `10` pair. The following fixed ten-transition path applies:

```text
D0, A0, B1, A1, E0, B0, C0, D1, E0, B0
```

It ends in C at position `-5`, adding ones at positions `-4` and `-2` while
preserving the `10` at positions `0,1`. It reads only positions `-4` through `1`,
so the rest of the tape is an untouched context. The resulting finite word is
`(01)^(n+3) 0 1^(b-2)`. For `b=2`, the final zero belongs to the exterior blank
region. For `b>=3`, absorb `01` from `0 1^(b-2)` into the pair count. This gives
the last two formulas in the table. The total is
`2 + 2n + 3 + 4n + 10 = 6a+21`, with head shift `-7`.

No path used in these four cases reads F on 1. This conclusion applies to the
given guards; it says nothing about the omitted `b=1,a>=1` branch.

## Collapsing a whole countdown

Starting from `C(0,n)` with `n>0`, first use the two-transition entry to `C(1,n)`.
Writing `n=3k+r`, summing the countdown costs and applying the terminal branches
gives:

| Residue | Endpoint | Raw transitions | Head displacement |
| --- | --- | --- | --- |
| `n=3k` | `C(0,10k+6)` | `15k^2+32k+14` | `-7k-4` |
| `n=3k+2` | `C(0,10k+14)` | `15k^2+62k+57` | `-7k-11` |
| `n=3k+1` | `C(5k+1,1)` — open boundary | `15k^2+12k+2` | `-7k-2` |

The sums use `sum(j, j=0..k-1)=k(k-1)/2`. All 80 cases `1<=n<=80` were also
checked directly against complete raw-tape endpoints; every test used fewer
than 200,000 transitions.

## The blank orbit and the next proof obligation

The blank start reaches `C(0,2)` after two transitions. Applying the collapsed
formulas gives suffix lengths

```text
2, 14, 54, 186, 626, 2094, 6986, 23294, 77654, 258854,
862854, 2876186, 9587294, 31957654.
```

The next endpoint is the open boundary

```text
C(53262756, 1)
```

at derived raw time `1870497627040360` and head position `-106525494`.
This is a **conditional arithmetic consequence of the derivation**, not a raw
simulation to that time and not a Lean-verified certificate. It was computed
after the bounded screen; it was not a registered experimental endpoint.
`derived_blank_frontier` records every arithmetic checkpoint in `l17-probes.json`.

The raw blank-prefix probe itself stopped at the fixed 200,000-transition
budget: its last complete supported macro endpoint was `C(471,344)` at time
199,382. The separate 5,000,000-transition raw scan is in `traces.jsonl`.

For synthetic open-boundary inputs `C(a,1)`, `1<=a<=64`, the fixed 200,000-step
first-return probes gave 39 returns to this section, 25 timeouts, and no halts.
Timeouts were not extended. The actual derived boundary value 53,262,756 was
not among these probes. A timeout does not prove divergence, and the sampled
returns do not establish a rule for arbitrary `a`.

The next concrete task is to formalize the three sweeps and four branches, then
analyze the reachable singleton-suffix branch with a richer tape encoding or a
different return section. Replacing that branch with an assumed return would
erase the halting question.
