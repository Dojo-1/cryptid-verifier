# E72 — Sparse C-event schedules and first-return minimality

## Authority floor (as of 2026-11-22)

E71 (merged PR #64, `59bfc5a`) proves **exact** `ReachesIn` from the
original E60 `widthFourCutSource` to its complete blank-left C tape for
every `M>=1`, `u,v : Nat`, arbitrary exterior `R : ListBlank (Fin 2)`.
The clock is `T1=214+6*M+2*u+4*v` for G1 and
`T3=268+6*M+2*u+2*v` for G3.

E71 does **not** prove that the endpoint is the first blank-left C visit.

## New conjecture: the complete sparse C-state schedule

Let `CVisit(t)` mean that after exactly `t` raw transitions, L17
has control state C, irrespective of left-tape content. The independent
literal raw-machine harness `test_e72.py` suggests **all** C-state
times between the E60 source and terminal E71 endpoint are exactly:

```text
S1(M,u,v) =
  [0,25,42,67,80,
   105+6M,143+6M,155+6M,159+6M,
   194+6M+4v,206+6M+4v]
  ++ [210+6M+4v+2j | 0 <= j <= u+2]

S3(M,u,v) =
  [0,25,68,105,118,143+6M,205+6M,217+6M]
  ++ [221+6M+2j | 0 <= j <= v+3]
  ++ [252+6M+2v,264+6M+2v]
  ++ [268+6M+2v+2j | 0 <= j <= u]
```

The final entries equal the respective E71 clocks. Their predicted
total C-state visit counts (including `t=0` and the terminal visit)
are `14+u` for G1 and `15+u+v` for G3. Notably **M changes C-visit
times, not counts**.

**Separate left-witness conjecture:** At every entry in `S1/S3`
except the final one, some tape cell strictly left of the head contains
`1`. At the final entry the left tape is blank and the complete
terminal configuration is E71's proved output.

Together, these two statements would establish **first-return
minimality** for the E60 guards. The C-visit schedule alone is
insufficient: the initial source is already in state C with nonblank
left tape.

## Evidence and checks

- **P:** E71's two exact-return theorems (earlier merge, standard axioms).
- **M:** 440 randomized + 490 adversarial-exterior complete raw trajectories, varying M=1..300 (selected
  positive widths), u/v, exterior suffix and origin translations;
  every C time, left witness, endpoint state, head, sparse tape and
  predicted visit count matched. `python3 -m unittest discover -s
  analysis/l17-threeblock-census -p 'test_e72.py' -v`.
- **H:** universal C-schedule completeness and universal
  nonterminal left-witness property.
- **R:** the false affine extrapolation to E60 M=0 (222/256 steps
  at u=v=0, not the positive-width formulas).

The control-state-only negative test and M=0 guard are retained.
This harness is neither an independent research review nor a formal
proof. It *replays* a separate translation of the raw transition table.

## Next Lean proof, scoped to the real obstruction

Define `FirstBlankLeftC s T out` as E71's exact `ReachesIn` plus

```text
forall t < T, forall (Z : ListBlank (Fin 2)),
  not (ReachesIn target t s (Cfg.headRight C default Z))
```

where the fixed L17 machine determinism and the precise meaning of
`ReachesIn` must be checked.

1. Instrument **the already-certified transition proof**, not a
   second oracle. Prove the finite 88/126-step preludes' exact C visits
   and persistent left witnesses for arbitrary symbolic exteriors.
2. Prove the parameterized A-scanner and E66 `4n`-sweep phases
   contain **no state C**, using local 2-step/4-step control paths
   and induction. This explains why M does not affect C-visit counts.
3. Prove the 77/95-step bridge schedules with arbitrary exteriors.
4. Strengthen E68 final-unwind lemmas with C visits and left-witness
   positions, by induction on u/v. Keep the G1 and G3 slopes separate.
5. Compose schedules through E69, restore sources with E70,
   normalize endpoints with E71, and then prove
   `FirstBlankLeftC` for both families.

**Stop rule:** A positive finite census cannot promote H to P. A
Lean proof of the event schedule without the left-witness condition
cannot promote first-return minimality. Neither result implies
blank-orbit reachability, an unrestricted scanner grammar, or
universal L17 nonhalting.


## Phase-local decomposition (candidate — stronger than the aggregate count)

The existing **P** exact steps give meaningful phase boundaries:

| Phase | G1 | G3 |
| --- | --- | --- |
| Fixed C-to-A prelude | [0,88) | [0,126) |
| A scanner plus 4M pair sweep | [88,88+6M) | [126,126+6M) |
| Fixed contextual bridge | [88+6M,165+6M) | [126+6M,221+6M) |
| Final unwind (includes endpoint) | [165+6M,T1] | [221+6M,T3] |

The independent raw transitions suggest the *entire* per-phase C-time
partition is:

- G1 prelude: `[0,25,42,67,80]` (5 visits).
- G1 A scanner/sweep: no C visits, for every tested positive M.
- G1 bridge (relative to `88+6M`): `[17,55,67,71]` (4 visits).
- G1 unwind (relative to `165+6M`):
  `[29+4v,41+4v] ++ [45+4v+2j | 0<=j<=u+2]` (u+5 visits).
- G3 prelude: `[0,25,68,105,118]` (5 visits).
- G3 A scanner/sweep: no C visits.
- G3 bridge (relative to `126+6M`): `[17,79,91]` (3 visits).
- G3 unwind (relative to `221+6M`):
  `[2j | 0<=j<=v+3] ++ [31+2v,43+2v] ++ [47+2v+2j | 0<=j<=u]`
  (u+v+7 visits).

This partition was checked against the randomized 440-case census; the additional 490 exterior attacks also matched the complete schedules
and makes the next **smallest formal lemma** the C-free A-scan/pair-sweep,
whose two-step and four-step state cycles can be inspected directly.
The C-witness proof then concentrates on the fixed preludes, fixed bridges,
and parameterized final unwind. No claim is promoted to P without a
machine-level Lean proof.