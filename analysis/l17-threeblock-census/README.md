# L17 E58/E59: three-block census and two contextual return guards

## Objective and evidence floor

Find counterexamples to coverage of the existing exact L17 width-five mixed B returns. The
mathematical object is the **raw six-state machine**, not a synthetic state graph. Read
windows, clocks, head position, control state, *complete tape*, scanner parse and the
relationship between C checkpoint and B entry must all agree.

This package extends [the L17 lead](../leads/L17.md), but does **not** assert that a generic
three-block input occurs on the blank-tape orbit, that arbitrary token strings have a
three-block parse, or that L17 never halts.

The prior informal number **71 missing cases** lacked a recoverable census specification.
An earlier first reconstruction reported 81, but accidentally used `0 (10)^7` for the
`wide(0)` block; the Lean/source value is `0 (10)^6`. Those counts are retired.

## Preregistered finite experiment

- Grammar: exactly **three ReturnBlocks** in C processing order; each from
  `pair`, `double`, `bridge`, `wide(j)` for `j=0..3`,
  or `shortTwo(j)` for `j=0..3`.
- Require the first five A-scan tokens of the reversed block list to be `01` to match
  the five virtual pairs; for the `100` terminator require and remove the final
  implicit `101` token.
- Compare the returned fixed right-tape prefix with literal `WidthFourGuard.word`
  expressions parsed from `L17FiveRun.lean`. Do **not** infer guard membership
  from a clock match.
- Run the frozen six-state transitions until the first *blank-left C* configuration
  (finite cap 14,000 transitions); compare transition count and full tape.
- Use independent B and C starting frames with four (u,v,suffix,translation)
  configurations for every pre-E59 unmatched parse. The two normalized endpoint
  tapes must match, not only their clocks.
- Fixed-kernel tests randomize both exterior tapes and inspect the complete
  fixed-length endpoint and extremal read positions; flip every guard bit as a
  negative control.
- Stop and reject theorem promotion on any raw mismatch, Lean build failure,
  unexpected axiom, or semantic mismatch between source and test representation.

Run with:

```bash
python3 -m unittest discover -s analysis/l17-threeblock-census -p 'test_*.py' -v
python3 analysis/l17-interleaved/check.py --cpp analysis/l17-hardening/comparator-O2
```

(The second command requires the C++ comparator to have been built; CI builds it.)

## Finite census

| Classification | Cases |
|---|---:|
| Valid bounded three-block parses | 1,016 |
| Matched nine guards on main before E59 | 962 |
| Previously unclassified | 54 |
| Matched new `oneWideWide` | 14 |
| Matched new `threeWideWide` | 14 |
| Still unclassified after E59 | 26 |

All 1,016 return at `u=v=0` in the bounded literal run. The previously
unclassified 54 additionally passed 216 B/C frame-paired exact-tape tests,
split by observed parametric clock slopes: **44** with `(du,dv)=(2,2)`,
**10** with `(du,dv)=(2,4)`. These slopes remain *sampled* for the
26 unproved guard cases.

## E59 contextual kernels

Let `K=(10)^7`. The two guard words, in raw right-tape order, are:

```text
oneWideWide:   1101010101010101101010101010100   (31 bits)
threeWideWide: 111101010101010101101010101010100 (33 bits)
```

Their exact contextual kernels were discovered by independent raw replay:

| New guard | Fixed steps | Read window relative to checkpoint | Complete C return clock |
|---|---:|---|---|
| `oneWideWide` | 203 | `[-14,34]` | `252+2*u+2*v` |
| `threeWideWide` | 243 | `[-20,36]` | `286+2*u+2*v` |

The outputs are full, explicit fixed words followed by **the same arbitrary
right exterior**, not clipped counters or normalized summaries. They are
composed with `width4_c_finish`; the full B-entry theorem
`mixed_zero_head_widewide_exact` further requires:

1. A *supplied* parse of the actual scanner tokens into
   `[b, .wide 1, .wide (if outerThree then 2 else 1)]`.
2. `b.output (term.residue R) = push [0] S` for some explicit `S`.

This covers `b=double`, `bridge`, `wide 0`, and `shortTwo j`
where the stipulated output prefix and parse are present, including all
28 matching cases in the bounded census. The Lean theorem handles arbitrary
natural indices and tape suffixes **under its explicit hypotheses**.

CI adds 140 full B-entry differential cases to the previous 4,048-case
campaign, plus separate 140-context checks per fixed kernel and 64
single-bit mutations. Bit flips changing a fixed-length endpoint do not
prove that a guard is globally minimal.

## Evidence ledger / exclusions

- **P, conditional**: only precise `ReachesIn` statements that actually compile
  and pass the trust audit; no extra axioms beyond standard Lean axioms.
- **M**: the 1,016-case bounded grammar census, full-tape B/C comparisons,
  frame-shift and exterior invariance checks, exact first-return samples,
  and single-bit mutants.
- **H**: a finite, sound disjoint classification of *all* reachable stack
  configurations; universal return; any true non-halting conclusion.
- **R**: numerical coverage claims made without a fixed census domain,
  and the erroneous `wide(0)` transcription.

**Stop rule:** Do not infer global coverage from the relative proportion
classified, and do not invent a new geometric framework to account for the
26 remaining parses. Isolate their shortest read-dependent prefixes next.
