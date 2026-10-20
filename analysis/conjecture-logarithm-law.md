# Conjecture: a logarithm law for Cryptid orbits

**Status:** conjecture, pre-registered below. Not proved. If true for a machine, together with that machine's
finite simulated prefix it implies the machine never halts.

## Setting

Each Cryptid orbit lives in the S-adic solenoid ℝ × ℚ₂ × ℚ₃ (mod ℤ[1/6]): future parities in the ℚ₂ fibre
(`pv_surj`), past parities in ℚ₃ (`pv_past3`), size in ℝ (`antihydra_floor`). The halting set is a *cusp*
of this space:

- **barrier cusp** (Antihydra): the counter walk aₜ (+2 on even, −1 on odd) dropping below 0;
- **window cusp** (A.1–A.11): a countdown leftover rᵢ landing exactly in a finite window W.

Define the **excursion depth** toward the cusp:

- Antihydra: the maximal drawdown DD(t) = max_{s ≤ u ≤ t} (aₛ − aᵤ);
- window machines: at the i-th countdown of scale Lᵢ, depthᵢ = log₂(Lᵢ / max(dist(rᵢ, W), 1)), with depth = ∞ at a halt.

## Conjecture (logarithm law)

For every Cryptid orbit the deepest excursion into the halting cusp grows only logarithmically:

  **Antihydra:** aₜ/t → 1/2, and limsup_{t→∞} DD(t) / ln t = 1 / ln φ (φ the golden ratio).

  **Window machines:** limsup_{i→∞} depthᵢ / log₂ i = 1.

Halting needs depth comparable to t (barrier: DD ≥ peak height ≈ t/2) or infinite depth (window: dist = 0). A
logarithmic bound leaves the halting cusp out of reach at all large times. The conjecture is asymptotic, so it
yields non-halting only together with an effective version of the bounds, checked against the simulated prefix.

## Where the constants come from

- **1/ln φ.** For a fair parity stream, the counter walk falls x levels below a running peak with probability
  φ^(−x). That is the harmonic function φ^(−a) of the walk, i.e. the real tilt ε = −ln φ at which the
  transfer operator of the parity-window graph has Perron root (e^{2ε} + e^{−ε})/2 = 1 at every window depth
  (`analysis/scripts`, infinitesimal round). The maximum of t such excursions is ≈ log_φ t, the Erdős–Rényi law.
- **1 (in log₂).** If the leftover is spread over its range, P(depth ≥ x) ≈ 2^(−x) per countdown, so the record
  after i countdowns is ≈ log₂ i.
- The spectral side matches: the frustration of the depth-k connection Laplacian, 9/(2(k+1))·ε², is the
  fluctuation variance seen through a window of k+1 bits; the logarithm law is its large-deviation counterpart.

## Evidence (exploratory runs, `analysis/scripts/loglaw.py`)

| Orbit | Horizon | Deepest excursion | Logarithmic prediction | Needed to halt |
|---|---|---|---|---|
| Antihydra | t = 10⁶ macro steps | DD = 29 | log_φ 10⁶ = 28.7 | DD ≥ aₜ = 498 503 |
| A.3 | 9 820 countdowns | depth 13.05 | log₂ 9 820 = 13.3 | ∞ (dist = 0); scales reach 2^2679 |
| A.8 | 9 794 countdowns | depth 11.99 | log₂ 9 794 = 13.3 | ∞; scales reach 2^2798 |

Record-to-prediction ratios are 1.06 (Antihydra), 0.98 (A.3) and 0.90 (A.8).

## Known analogues (why it is plausible, and why it is open)

Erdős–Rényi (1970, longest runs), Sullivan's logarithm law for geodesic cusp excursions (1982) and
Kleinbock–Margulis (1999) prove laws of this form for *almost every* point. The Cryptid version asks it for one
explicit orbit, which is the same gap as normality of a specific number. New here are the unified
barrier/window form and the constant read off our connection-Laplacian computations.


## Past, present, future: what the past can and cannot tell the halting question

### Exact facts (Antihydra)
- **The past is compressed into the present.** aₜ = 3·(number of even steps so far) − t (`walk_count`), and the
  last j parities are b mod 3ʲ (`pv_past3`). The machine is deterministic and Markov in (a, b): the past can
  influence halting only through the present.
- **Residue-level independence is exact.** The next k parities are b mod 2ᵏ (`pv_mod`, `pv_inj`, `pv_surj`). Checked
  exhaustively for (j,k) ∈ {(2,2), (3,3), (4,3), (3,5)}: every pair (past j-pattern, future k-pattern) is realised
  by **exactly one** residue class of reachable b modulo 2ᵏ·3ʲ, consistent with the Chinese remainder theorem.
  In words, the ℚ₃ coordinate (past) and the ℚ₂ coordinate (future) of the present state are independent
  factors. No information flows from past to future at the level of residues. Any memory that matters for
  halting has to live in the **real** coordinate (the size of b, i.e. ξ), the one place where 2 and 3 meet.
  (Lean proof pending; it would combine `pv_surj`, `pv_past3` and the CRT.)

### Measured along the actual orbit (`scripts/pastfuture.py`, 10⁶ steps)
- χ² independence of (past j bits, future k bits): z = −0.5, 2.1, 2.2, 0.2, −0.05, −0.05 for
  (j,k) = (1,1), (3,3), (4,4), (6,6), (8,4), (4,8). Overlapping windows inflate the variance, so |z| ≈ 2 is the
  noise level; the (3,3) value falls from 2.4 to 1.4 between the two halves of the run.
- Correlation of past and future drift (the quantity the drawdown depends on): −0.003, −0.001, −0.008 over windows
  of 5, 20 and 100 steps, all inside noise.

### Window machines: a genuine past→present coupling that does not reach the halting window
A.9's invariant a ≡ 2 (mod 3) (`a9_mod3`) is 3-adic memory. With a = 2k + p it forces k ≡ 1 + p (mod 3), so every
race starts with b ≢ 0 (mod 3), an exact constraint inherited from the past. But c is not constrained:
over 13 006 race starts, b − c is uniform mod 3 and mod 9, and min |b − c| = 28 after the first ten. The past
narrows the present without narrowing the halting window {0, 1}.

### Refined conjecture (two strata)
1. **Sufficiency / independence.** Along each Cryptid orbit, past windows (ℚ₃ digits) and future windows (ℚ₂
   digits) of length up to (1 − ε)·log₂ t are asymptotically independent. Equivalently, the present residues carry
   all of the predictive information, and the parity process is Bernoulli(½) at logarithmic window lengths.
2. **Logarithm law** (above). It follows from stratum 1 by the Erdős–Rényi argument, with constant 1/ln φ.

Stratum 1 is the sharper and more testable form. Stratum 2 is its consequence for halting.

**P4 (pre-registered).** For Antihydra at t = 10⁷ the χ² z-score of (past j, future k) independence stays
within ±4 for every j + k ≤ 16. *Refuted if* any z > 6, which would mean the real place leaks predictive structure.

## Self-review (what to trust)
- **Proved (Lean, CI):** the reductions (`run_eq`, `a4_halts_iff`, `a9_halts_iff`, `antihydra_floor`), the residue
  dichotomy (`pv_mod`/`pv_inj`/`pv_surj`, `pv_past3`) and the bounded raw-TM linkage.
- **Exact but only machine-checked numerically:** the CRT factorisation above.
- **Heuristic:** the logarithm law and its constants; its evidence is a handful of record values per machine.
- **Refuted along the way:** A.1's "never 0 mod 4" (an artifact of a small sample); Gemini's A.4 halting set;
  the ℤ/k, Möbius and infinitesimal rounds produced no invariant (each was explained, not hidden).
- **Main risk:** the geometric language (cusp, solenoid, tilt) organises the picture but proves nothing by itself.
  Every claim above is labelled by which of the three categories it belongs to.

## Pre-registration (φ₄)

Predictions, each with a stop condition:

1. **P1.** Antihydra: DD(t) / log_φ t ∈ [0.8, 1.25] at every record time in t ∈ [10⁶, 10⁷].
   *Refuted if* a record with ratio > 1.5 appears.
2. **P2.** For A.3, A.4, A.8 and A.9: record depth / log₂ i ∈ [0.7, 1.3] at every record with i ∈ [10⁴, 10⁵].
   *Refuted if* any record has ratio > 2.
3. **P3.** In Antihydra, aₜ / t stays within 1/2 ± 3·√(ln t / t) for t ∈ [10⁶, 10⁷] (law-of-iterated-logarithm scale).

**Stop condition for the programme.** If P1 or P2 is refuted, the orbit has a deterministic structure biased
toward its cusp. That is worth more than the conjecture: it is the place to look for a halting mechanism or for
a hidden invariant.
