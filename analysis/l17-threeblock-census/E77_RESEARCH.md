# E77 — entire 88/126-step C-to-A prelude is first-return-safe

This PR is **stacked on E76 (#70)**. Both are machine-level
first-return safety refinements; neither is a proof of L17 nonhalting.

## Universal candidate statement

For each contextual source from E65, with arbitrary symbolic
binary `ListBlank` left exterior `L` and right exterior `R`:

```text
G1: for all t < 88 and every exact t-step configuration c,
    not E76BlankLeftC(c)

G3: for all t < 126 and every exact t-step configuration c,
    not E76BlankLeftC(c)
```

The control *does* revisit C during these preludes. The exact C visits
from independent raw transitions are:

| Family | C event times before the A endpoint | C left witness |
| --- | --- | --- |
| G1 | 0, 25, 42, 67, 80 | head-nearest 1 at each event |
| G3 | 0, 25, 68, 105, 118 | head-nearest 1 at each event |

At all other prelude timestamps the control is different from C.
The C left witnesses are within the fixed frame and are independent of
the arbitrary external tapes.

## Formal tactic design

- Reuse the E76 0..25 universal safety theorem.
- New E77 source file contains **62 G1 + 100 G3** exact symbolic
  `ReachesIn` paths for times 26..87 / 26..125, respectively.
- Each complete machine path is checked by `l17_exact_steps`
  against the frozen six-state transition table. Raw traces are only
  candidate endpoints, never an axiom.
- Divide the remaining times into bounded, disjoint windows
  (G1: 26–55, 56–87; G3: 26–55, 56–85, 86–115, 116–125)
  and discharge all cases with exact determinism.
- At C visits prove left-head bit is 1; at non-C visits, reject
  blank-left C by control-state inequality. Both predicates are
  over the complete `Cfg` and its symbolic half-tape exteriors.

The two public theorem names
`e77_one_full_prelude_noBlankLeftC` and
`e77_three_full_prelude_noBlankLeftC`
are registered in the standard-axiom trust inventory.

## Evidence governance and stop rule

**P prerequisites:** E65 88/126-step exact contextual C-to-A entry,
E71 exact returns, E74/E75 no-C variable middle interval.

**H until Lean link CI and trust audit:** both E76 and E77
new safety statements. E77 must not be considered proved until the
literal symbolic paths and every case split compile with only
standard axioms and no `sorryAx`. Very large generated proofs are
not independently reviewed mathematics solely because they compile;
the source-to-statement correspondence remains explicit.

**M:** the E72 complete-trace census (930 cases), plus a separate
literal state trace identifying the fixed family C visits and
read windows: G1 [-6,24], G3 [-9,26].

**Still open:** every nonterminal C visit in the 77/95-step fixed
bridges and the u/v-parametric final unwinds must retain a
nonblank left tape. Only after those proofs and exact temporal
composition can the first-return theorem for both positive-width
E60 families be promoted to P. Complete mixed grammar, blank orbit
reachability and universal L17 nonhalting are distinct goals.
