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
