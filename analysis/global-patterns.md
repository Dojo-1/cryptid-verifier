# Global halting patterns across the 12 Cryptids (exploratory, not proved)

Rule systems: the simplified (merged) systems of Appendix A of arXiv:2610.22603, transcribed in
`scripts/machines.py`, plus Antihydra. Every system ran 3M rule steps (or until counters reached ~2^4000)
without halting or getting stuck, which is a sanity check on the transcription.

## 1. One halting motif, two flavours (exact, read off the rules)

| Machine | Halting configuration | What must coincide |
|---|---|---|
| Antihydra | A(0, odd) | running total a crosses 0 (**barrier**) |
| A.1 | A(0, b, 0, b+2) | cascade remainder d − b − 2 = 0 |
| A.2, A.5 | D(0, even, 0) | drained counter w ends exactly at 0 with a = 0 |
| A.3 | C(2,2,f), C(2,4,f) | Euclid step difference m − k ∈ {0,1} |
| A.4 | C(a, 2) | cascade from C(m,1) lands on 2 ⟺ m = 2^(s+2) − 4 − s (proved: `a4_halts_iff`) |
| A.6 | J(1, v, 1) | race start with w = 2u − 1 |
| A.7 | E(a, 1, 1) | race ends with k = 1 while c = 1 |
| A.8 | k − a ∈ {4,5} (even b) / a − k ∈ {0,1} (odd b) | difference in a 2-element window |
| A.9 | C(a, 0, 0) | race starts with b − c ∈ {0,1} (proved: `a9_halts_iff`) |
| A.10 | E(a, 0, 3) | race start with c = 2b + 3 |
| A.11 | C(0, odd, 0, 3), C(0, even, 1, 3) | small counters coincide at a reset |

**Motif.** In all 11 new machines the dynamics is a sequence of *countdowns* — a **race** (two counters
decremented in lockstep) or a **doubling cascade** (one counter doubles while another is consumed) — and the
machine halts only if, at the end of a countdown, the leftover lands **exactly** in a window of 1–2 values.
Antihydra is the odd one out: it halts when a cumulative total crosses a **barrier** (a ≥ 0), not by an exact
coincidence.

## 2. The common heuristic law

If the leftover at a countdown of size L is spread over ~L values, the chance of halting there is ≈ |W|/L.
Counters grow (geometrically per round for A.3, A.4, A.7, A.8, A.9, A.11, Antihydra; more slowly in A.1, A.2,
A.5, A.6, A.10 whose inner loops are long), so the expected number of future halts is a convergent, small sum.
Measured in the runs: no countdown ever ended in its window; expected-halt sums over the observed countdowns are
O(1) (e.g. A.3 0.6, A.8 0.9, A.9 0.6, A.10 3.0).

**Consequence.** Every one of these halting questions is the same type of problem: a *shrinking-target
problem* — does one specific orbit ever hit a target whose relative size goes to 0? Antihydra is the
*barrier* (large-deviation) version; the 11 new machines are the *window* (exact-coincidence) version. Known
results (Borel–Cantelli, Furstenberg-type rigidity, Baker bounds) control *almost all* orbits or orbits with
extra symmetry, not one given orbit — which is why none is settled.

## 3. Leads tested

- **Residue obstructions** (window never hit modulo some M, i.e. a finite-state proof): none for A.3, A.4,
  A.6, A.8 (M ≤ 200–400). Apparent obstructions for A.1, A.9, A.10 came from small or highly structured
  samples. For A.1 the "never 0 mod 4" pattern of 40 samples **failed** on a longer run (39 of 3000 decision
  states have d − b − 2 ≡ 0 mod 4).
- **A.1 cascade structure** (derived, not yet in Lean): every outer cycle starts at (2,0,0,D) with D ≡ 2 (mod 4)
  in all 63 observed cycles; the main cascade then has remainders rⱼ = (D − 4) − 15(2ʲ − 1) + 4j, which are
  never 0 when D ≡ 2 (mod 4). So, if D ≡ 2 (mod 4) holds at every cycle start, A.1 can only halt through its
  side branches (b ≥ d − 1 and d ∈ {b+3, b+4} exits), not through the main cascade.
- **Abstract interpretation** (counters as exact-small or residue-mod-M): too coarse for A.1 — halting stays
  abstractly reachable for M ∈ {4, 8, 12, 16, 24}.
