# E81 — exact G1 bridge safety for all preterminal times

The 77-step G1 contextual A-to-A bridge is already proved as an
exact endpoint in E67. E78 (merged PR #72) proves that its C visit
at raw time 71 has left prefix `0101`, with the **second** left
symbol equal to 1. A first-left-one-only invariant is therefore false.

## Universal proposed statement

For arbitrary `L,R : ListBlank (Fin 2)` and every `0<=t<77`,

```text
ReachesIn target t (A(W1 ++ L; 11 ++ R)) c ->
  not (E76BlankLeftC c).
```

Here `W1` is E67's exact 35-bit fixed bridge guard. The
source-to-frame equality is represented literally by the same
`Cfg.headRight` lists. The property concerns complete symbolic
machine states, not only control state or finite recorded traces.

## Independent literal candidate C visits

| raw step | left word nearest first | witness |
| ---: | --- | --- |
| 17 | `110010101010101010010101000101` | 1st left cell |
| 55 | `110101000101` | 1st left cell |
| 67 | `10000101` | 1st left cell |
| 71 | `0101` | **2nd** left cell (E78) |

All other raw steps 0..76 have a state different from C.
The fixed read window is [-34,1], so arbitrary exterior L/R
remains uninterpreted during this bridge.

## Lean design

- 77 symbolic full-state `ReachesIn` certificates at times 0..76.
- The first exact state is `ReachesIn.zero`; every later state
  follows an exact **one-step** `l17_exact_steps` transition
  and a `ReachesIn.trans` composition.
- The 77 times are partitioned into four exhaustive, bounded
  windows: [0,20), [20,40), [40,60), [60,77).
- Every non-C timestamp discharges the safety predicate by
  control-state inequality; three C timestamps have nearest-left
  1, while t=71 invokes the already-certified E78 deeper witness.

**H until six pinned CI jobs, Lean kernel and trust audit pass.**
No `sorry` or fresh axiom is authorized. The 77 candidates were
independently transcribed from the frozen six-state transition table,
but that finite transcription is not a substitute for proving their
complete symbolic endpoints.

This branch neither covers the G3 95-step preterminal bridge nor
the parametric final unwind. Even a passing E81 does not prove
E60 first-return minimality, unrestricted scanner grammar,
blank-orbit reachability or universal L17 nonhalting.

If the chained Lean proofs hit recursion/heartbeat limits, repair
the proof budget or factor certificates into short chunks; do not
weaken the quantified theorem.
