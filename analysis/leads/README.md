# Triage of the 25 Appendix C follow-up leads (exploratory)

Input: the 25 machines in GPT's `results/candidate-inventory.json` that are neither in the paper's results
table nor have a machine module in `google-deepmind/cryptids` (commit a0c1f56). Tools: `sim.py` (raw simulation,
tape compression into repeated blocks at head-boundary events, most frequent shape) and `races.py` (splits the
shape's exponent sequence into runs of constant increment, "races", and tries exact affine fits for the
transitions between them, "resets", per residue class).

**Status refresh: see `gpt-2026-10-20/report.md`** (GPT, against the bbchallenge holdout lists and annotation
sheet). In short: L02/L09/L10 belong to the documented Racheline2024 family; L25 is reported resolved
(verification pending); L13 already has public analysis; the 25 tables form 19 families when the start state is ignored.
L17 is followed up in `L17.md`.

## Results (3 000 000 raw steps per machine)

- **None of the 25 halts** within 3·10⁶ raw steps. That is consistent with holdout status but proves nothing.
- **15 show the countdown motif** of the known Cryptids: one dominant compressed tape shape whose exponents move
  in long races of constant increment, e.g. (2, −4), (4, −3), (−3, 4), (0, −2, 0, 6).
- **Too few resets to fit.** Races grow, so 3·10⁶ steps contain only 2–11 resets per machine. Exact affine reset
  fits exist for 4 leads, but on 4–7 samples each, which is not evidence of a closed rule system. A faster
  simulator, or acceleration of the races themselves, is needed for the next step.
- **7 leads show no stable shape** at this scale (top shape seen 1–2 times), and **3 have a shape without a clear
  race** (one race seen twice, a 41-block shape, a shape with no repeated increment). These 10 need a different tape
  encoding or return section, the representation question raised in the audit.

## Equivalence candidate

`1RB1LE_1RC0RF_0LD---_1RF1LE_0LF1LC_1LD0RA` and `1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA` produce
**identical** compressed-shape exponent sequences over all 819 occurrences in 3·10⁶ steps. They are not
state relabelings of each other (checked over all permutations of B–F), so the agreement is at the macro level.
This is a candidate pair for "one problem, two machines".

**Why (exact, from the transition tables).** Rename the states of the first machine M1 by A→A, B→B, C→D, D→E,
E→C, F→F. Then M1 and the second machine M2 agree on 11 of 12 transitions. The only difference is B reading 0:

- M2: B0 → write 1, move left, go to C.
- M1: B0 → write 1, move right, go to D′ (its C). D′ reads the right neighbour: on 0 it writes 0, moves left, goes
  to E′; E′ reads the 1 just written and moves left to C. Net: write 1, move left, state C, in 3 steps instead of 1.
  On 1, M1 halts.

So M1 is M2 with step dilation plus **one extra halting trigger**: a B0 event whose right neighbour is 1. As long as
that never happens the runs are identical up to time. Consequences:

- If M1 never halts, M2 never halts (proving M1 settles both).
- If M2 halts, M1 halts no later (in its own time).
- M1 halts ⟺ M2 halts, or a B0 event with a 1 on its right occurs first.

Evidence on the trigger: in 5·10⁶ steps of M2 there are only 15 B0 events, all with blank cells on the right
(context (1, 0, 0) every time), which suggests B0 happens only at the right edge of the written tape. Proving
that would make the pair exactly equivalent. Not yet proved.

## Per-lead output

| Machine | Races (increment: count) and reset-fit status |
|---|---|
| `1RB---_1RC0LC_0RD0LE_1LE1RF_0LB0RC_0RE1RA` | top shape too rare/irregular (count 2) |
| `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---` | races {(0, -3, 4): 2}  resets: no exact affine fit (n=1) |
| `1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_---0RC` | races {(3, 1, -1): 3}  resets: no exact affine fit (n=2) |
| `1RB1LC_1LA0RD_0LB1LF_1RE1LC_1LC0RB_0LA---` | races {(2, -4): 4}  resets: no exact affine fit (n=4) |
| `1RB---_1LC1RE_1LD0LC_1LE1LC_1RF0RE_1RA0RB` | top shape too rare/irregular (count 2) |
| `1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB` | races {(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 3): 1}  resets: no exact affine fit (n=0) |
| `1RB0RE_0LC---_1RE1LD_0LE1LB_1LC0RF_1RA1LD` | races {(2, -4): 6}  resets: no exact affine fit (n=6) |
| `1RB1LE_1RC0RF_0LD---_1RF1LE_0LF1LC_1LD0RA` | races {(2, -4): 7}  resets 5/7 fit exactly mod 2: (0, 0):['(0,-1/2,6)', '(3,5/2,-8)'] |
| `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` | races {(4, -3): 5}  resets 5/5 fit exactly mod 1: (0, 0):['(0,0,4)', '(2,3,-1)'] |
| `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---` | races {(-3, 4): 4}  resets: no exact affine fit (n=5) |
| `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD0RF_1RA---` | top shape too rare/irregular (count 1) |
| `1RB0RF_1LC---_1RD0LC_0RE0RD_1LF1LC_1LE1RA` | races {(0, -2, 0, 6): 4}  resets: no exact affine fit (n=4) |
| `1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---` | races {(0, -2, 0, 6): 4}  resets: no exact affine fit (n=3) |
| `1RB1RC_0LA1RF_1RD0LE_1LC0RB_0RA0LC_0RD---` | top shape too rare/irregular (count 1) |
| `1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_1RD---` | top shape too rare/irregular (count 2) |
| `1RB1LC_1LC0RF_0LF1LD_0LE---_1RF1LC_1LE0RA` | races {(2, -4): 7}  resets 5/7 fit exactly mod 2: (0, 0):['(0,-1/2,6)', '(3,5/2,-8)'] |
| `1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---` | races {(5, -3): 5}  resets 4/4 fit exactly mod 1: (0, 0):['(0,0,4)', '(2,2,8)'] |
| `1RB1RA_1LC0RE_1LE0LD_0LB1LB_1RA0LF_1LD---` | races {}  resets: no exact affine fit (n=52) |
| `1RB1LF_1LC0RD_---1LA_0LA0RE_1LA1RA_1LB0LD` | races {(0, 1, -3): 5}  resets: no exact affine fit (n=11) |
| `1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA` | races {(-1, 1, 2): 4}  resets: no exact affine fit (n=3) |
| `1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC` | races {(1, 1, -4, 0, 0, 0): 3, (2, 1, 0, -1, 0, 0): 2}  resets: no exact affine fit (n=2) |
| `1RB0LC_1LA1RF_1LD1RF_1LE0LA_0RB---_0RA1RE` | races {(-4, 2): 6}  resets: no exact affine fit (n=6) |
| `1RB0LF_1LC0RB_0LD1LA_0RA1LE_0LA0RA_1LA---` | races {(0, 3, -2, 1, 0): 4}  resets: no exact affine fit (n=3) |
| `1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LA---` | top shape too rare/irregular (count 1) |
| `1RB2LA0RB1LB---_1LA3RA1RA4LB0RB` | top shape too rare/irregular (count 2) |
