# Conjecture: a logarithm law for Cryptid orbits

> **Status: unproved conjecture; interpretations corrected 2026-10-23.**
> The finite measurements below are exploratory evidence. CRT coding does not prove
> statistical independence on a chosen orbit, and an asymptotic law alone does not
> exclude an earlier halt. See the [independent finite-evidence audit](independent-audit.md).
> The original prediction bands and alert thresholds are preserved below; Git history
> retains the earlier wording. P2/window-law results were not reproduced by that audit.

Only effective bounds with explicit constants and onset, a checked finite prefix,
and the exact raw-machine bridge could establish non-halting by this programme.

## Setting

The proposed S-adic viewpoint uses ℝ × ℚ₂ × ℚ₃ (mod ℤ[1/6]) as organizing language.
For Antihydra there are exact coding results for future parities (`pv_surj`), past
parities (`pv_past3`) and real growth (`antihydra_floor`). An explicit common
measure-preserving geometric model for all eleven machines is not proved here.
The *cusp* terminology describes the following candidate halting mechanisms:

- **barrier cusp** (Antihydra): the counter walk aₜ (+2 on even, −1 on odd) dropping below 0;
- **window cusp** (A.1–A.11): a countdown leftover rᵢ landing exactly in a finite window W.

Define the **excursion depth** toward the cusp:

- Antihydra: the maximal drawdown DD(t) = max_{s ≤ u ≤ t} (aₛ − aᵤ);
- window machines: at the i-th countdown of scale Lᵢ, depthᵢ = log₂(Lᵢ / max(dist(rᵢ, W), 1)), with depth = ∞ at a halt.

## Conjecture (logarithm law)

The targets concern the **designated blank-tape orbit of each specified machine**.
Antihydra starts at A(0,4); A.4 at C(0,3); A.9 at C(5,2,0). For any other window
machine, its paper-defined start, leftover and halting window must be specified
before instantiating the target. This is not a claim about arbitrary starts:
A(0,1) halts immediately, and `halts_neg3` supplies a family of other halting starts.

For those designated orbits, conjecture logarithmic deepest excursions:

  **Antihydra:** aₜ/t → 1/2, and limsup_{t→∞} DD(t) / ln t = 1 / ln φ (φ the golden ratio).

  **Window machines:** limsup_{i→∞} depthᵢ / log₂ i = 1.

Under the proposed drift, a late barrier halt would require drawdown comparable
to the previous peak; a window hit is assigned infinite depth. A numerical limsup
fit on observed continuing trajectories does not prove either event impossible.
An effective tail bound must apply without assuming the desired non-halting
conclusion, and every time before its explicit onset must be covered separately.

## Where the constants come from

- **1/ln φ.** For a fair parity stream, the counter walk falls x levels below a running peak with probability
  φ^(−x). That is the harmonic function φ^(−a) of the walk, i.e. the real tilt ε = −ln φ at which the
  transfer operator of the parity-window graph has Perron root (e^{2ε} + e^{−ε})/2 = 1 at every window depth
  (`analysis/scripts`, infinitesimal round). The maximum of t such excursions is ≈ log_φ t, the Erdős–Rényi law.
- **1 (in log₂).** If the leftover is spread over its range, P(depth ≥ x) ≈ 2^(−x) per countdown, so the record
  after i countdowns is ≈ log₂ i.
- Exploratory connection-Laplacian calculations suggested the coefficient
  9/(2(k+1))·ε². Relating it rigorously to fluctuations and rare events on the
  specified deterministic orbit remains a separate unproved bridge.

## Evidence (exploratory runs, `analysis/scripts/loglaw.py`)

| Orbit | Horizon | Deepest excursion | Logarithmic prediction | Needed to halt |
|---|---|---|---|---|
| Antihydra | t = 10⁶ macro steps | DD = 29 | log_φ 10⁶ = 28.7 | DD ≥ aₜ = 498 503 |
| A.3 | 9 820 countdowns | depth 13.05 | log₂ 9 820 = 13.3 | ∞ (dist = 0); scales reach 2^2679 |
| A.8 | 9 794 countdowns | depth 11.99 | log₂ 9 794 = 13.3 | ∞; scales reach 2^2798 |

The displayed endpoint ratios are about 1.01 (Antihydra), 0.98 (A.3) and 0.90 (A.8).

## Known analogues (why it is plausible, and why it is open)

Erdős–Rényi (1970, longest runs), Sullivan's logarithm law for geodesic cusp excursions (1982) and
Kleinbock–Margulis (1999) prove laws of this form for *almost every* point. The Cryptid version asks it for one
explicit orbit, an analogous obstacle to proving normality of a specified number.
The barrier/window organization and suggested constants are proposals in this note;
no priority claim or theorem for the specified orbits follows from those analogues.


## Past, present, future: what the past can and cannot tell the halting question

### Exact facts (Antihydra)
- **The past is compressed into the present.** aₜ = 3·(number of even steps so far) − t (`walk_count`), and the
  last j parities are b mod 3ʲ (`pv_past3`). The machine is deterministic and Markov in (a, b): the past can
  influence halting only through the present.
- **Residue coding is exact; orbit independence is not established.** The next k
  parities are determined bijectively by b mod 2ᵏ (`pv_mod`, `pv_inj`, `pv_surj`);
  `pv_past3` supplies the corresponding past-coding statement. The exploratory
  CRT enumeration for (j,k) ∈ {(2,2), (3,3), (4,3), (3,5)} concerns static residue
  classes, not empirical frequencies of the orbit starting at b = 4. Product
  residue counts under a specified uniform ensemble do not show that this one
  trajectory samples that ensemble uniformly. In particular, the earlier claims
  that no predictive information can pass between the residue coordinates and
  that all relevant memory must reside in the real coordinate are retired.
  A formal CRT coding result would still leave the orbit-measure/mixing problem open.

### Measured along the actual orbit (`analysis/scripts/pastfuture.py`, 10⁶ steps)
- χ² independence of (past j bits, future k bits): z = −0.5, 2.1, 2.2, 0.2, −0.05, −0.05 for
  (j,k) = (1,1), (3,3), (4,4), (6,6), (8,4), (4,8). These are descriptive transforms:
  overlapping windows and related tests require a matched family-level null before
  significance is assigned. The (3,3) value falls from 2.4 to 1.4 between run halves.
- Correlation of past and future drift (the quantity the drawdown depends on): −0.003, −0.001, −0.008 over windows
  of 5, 20 and 100 steps. These finite values do not establish asymptotic independence.

### Window machines: a genuine past→present coupling that does not reach the halting window
A.9's invariant a ≡ 2 (mod 3) (`a9_mod3`) is 3-adic memory. With a = 2k + p it forces k ≡ 1 + p (mod 3), so every
generated race starts with b ≢ 0 (mod 3), an exact constraint inherited from the past.
The recorded sample of 13 006 race starts has roughly uniform b − c residues mod 3
and mod 9, and min |b − c| = 28 after the first ten. This observation neither
proves uniformity nor excludes a further constraint on c or a later halting-window hit.

### Refined conjecture (two strata)
1. **Independence target.** For the designated Antihydra orbit, test asymptotic
   independence of the specified past/future windows up to (1 − ε)·log₂ t.
   Any extension to other machines requires its own coding and empirical measure.
2. **Logarithm-law target** (above). Passing such window tests is not equivalent
   to being a Bernoulli process and does not itself prove the extreme-value law.
   A quantitative rare-event/mixing argument with effective bounds is still needed.

These are separate unproved targets; neither one is promoted by the finite tests below.

**P4 (recorded prediction).** For Antihydra at t = 10⁷ the descriptive χ² z-transform
stays within ±4 for every j + k ≤ 16. The original separate alert threshold was
any z > 6. An alert requires investigation and matched calibration; it does not
by itself identify a deterministic cause or a special role for the real coordinate.

## Results of the recorded tests (t = 10⁷, `analysis/scripts/antihydra_fast.py` + `predictions_p1_p3_p4.py`)
Parities generated in chunks of 4096 via b mod 2ᵏ (`pv_mod`), with b advanced exactly by 2ᵏ·b' = 3ᵏ·b + Sₖ
(`real_bridge`); checked against direct simulation for 50 000 steps. The original
GMP run reported 17 s; the independent Python run used a different environment,
so these records do not support a matched speed comparison.

| Prediction | Result | Verdict |
|---|---|---|
| P1: DD/log_φ t ∈ [0.8, 1.25] at record times in [10⁶, 10⁷] | new records only at t = 7 325 962–4: DD = 30, 31, 32, ratios 0.91, 0.94, 0.97; DD(10⁷) = 32 against log_φ 10⁷ = 33.5 | observed records within band |
| P3: \|aₜ/t − ½\| ≤ 3√(ln t / t) | max of the ratio to the band = 0.28 | within the stated concentration band |
| P4: \|z\| ≤ 4 for all 120 (j,k) with j + k ≤ 16 | z ∈ [−1.78, 2.52] | descriptive values within band; not a significance result |

By-product: the counter never drops below 12 for t ≥ 15 within the checked horizon, so Antihydra does not halt within 10⁷ macro steps
(a known fact; the community has simulated further).

## Self-review (what to trust)
- **Proved (Lean, CI):** the reductions (`run_eq`, `a4_halts_iff`, `a9_halts_iff`, `antihydra_floor`), the residue
  dichotomy (`pv_mod`/`pv_inj`/`pv_surj`, `pv_past3`) and the bounded raw-TM linkage.
- **Exact but only machine-checked numerically:** the CRT factorisation above.
- **Heuristic:** the logarithm law and its constants; its evidence is a handful of record values per machine.
- **Refuted along the way:** A.1's "never 0 mod 4" (an artifact of a small sample); Gemini's A.4 halting set;
  the ℤ/k, Möbius and infinitesimal rounds produced no invariant (each was explained, not hidden).
- **Main risk:** the geometric language (cusp, solenoid, tilt) organises the picture but proves nothing by itself.
  Formal results, finite observations and conjectures must remain separate.

## Original prediction record (φ₄)

The following numerical bands and separate alert thresholds retain the original
targets. A band failure must be reported even if it does not reach the alert
threshold. Their presence in this document is not independent authentication of
registration timing; the archive-based audit could not establish that timing.

Predictions, each with a stop condition:

1. **P1.** Antihydra: DD(t) / log_φ t ∈ [0.8, 1.25] at every record time in t ∈ [10⁶, 10⁷].
   *Refuted if* a record with ratio > 1.5 appears.
2. **P2.** For A.3, A.4, A.8 and A.9: record depth / log₂ i ∈ [0.7, 1.3] at every record with i ∈ [10⁴, 10⁵].
   *Refuted if* any record has ratio > 2.
3. **P3.** In Antihydra, aₜ / t stays within 1/2 ± 3·√(ln t / t) for t ∈ [10⁶, 10⁷].
   This is the recorded concentration band, not an LIL normalization, which involves ln ln t.

**Stop condition for the programme.** If P1 or P2 is refuted, stop promoting that
finite prediction and preserve the failed run. Check the specification, comparator
and null model before proposing a replacement. A failure alone does not prove a
deterministic bias toward halting, a hidden invariant or a geometric mechanism.

## Correction record (2026-10-23)

- Restricted the target from an ambiguous all-orbit reading to specified blank-tape starts.
- Retired CRT-to-single-orbit-independence and real-coordinate-only-memory inferences.
- Separated window independence, Bernoulli behavior, extreme-value laws and effective non-halting bounds.
- Reclassified overlapping-window z values as descriptive until matched calibration.
- Corrected the P3 LIL label and the finite-prefix indexing; retained the numerical targets and observations.
- Kept the geometric viewpoint as an organizing proposal, with no theorem or priority claim attached.
