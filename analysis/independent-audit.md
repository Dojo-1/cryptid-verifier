# Independent finite-evidence audit and reproducibility contribution

Date: 2026-10-20. Input: the uploaded cryptid-verifier-main.zip, SHA-256
b414234e7597bcc5d9693bf4545b75954e9eecaf9e99fa36d91a8870b6904a32.
The snapshot contains no Git history. The claimed registration commits edc08a5 and d0ef9c5
cannot be authenticated from this archive; registration timing is user-supplied context.

## Verdict

The finite Antihydra results reproduce: at 10,000,000 autonomous b-steps, the counter is
4,990,580, its maximum drawdown is 32, the P3 band ratio is 0.2809734663, and the 120
descriptive P4 transforms range from -1.7793761440 to 2.5224700326. The acceleration agrees
with a separate direct-arithmetic implementation for 50,000 steps and with extensive bounded
and representation checks. This is measured finite evidence, not a proof of mixing,
a logarithm law, or non-halting. The material does not justify a general impossibility
claim for semilinear invariants. No new cryptid is claimed.

## Claim and evidence ledger

| Claim | Before | Artifact | Audit result | After |
|---|---|---|---|---|
| Chunked parity generator computes the intended finite orbit | H | antihydra_fast.py; test_reproducibility.py | Exact endpoint and parity agreement on bounded reference cases, including 50,000 direct steps | M |
| Stated 10-million-step P1/P3/P4 numerical results | M, reported | results/predictions-10m.json | Independently rerun arithmetic; matches the reported values | M |
| P4 z transforms have iid chi-square significance | H if so interpreted | original overlapping-window monitor | Overlap and the 120 related tests require a matched null; raw z values are descriptive | R |
| Supplied affine-invariant no-go theorems exclude all semilinear invariants | H in conversation | Basic.lean, invariant_needs_dvd3 and its corollaries | Those quantifiers exclude a + c*t for all parity walks; they do not quantify over every invariant involving b, phase, inequalities or disjunctions | R |
| Static CRT factorization proves independence along the orbit starting at b=4 | H if so interpreted | pv_mod, pv_past3; conjecture document | Algebraic coding does not specify the orbit's empirical probability measure | R |
| Effective logarithm-law bounds establish non-halting | H, conditional | proposed theorem target | Needs explicit constants/onset, prefix coverage, and a sound connection to the exact machine | A |
| Particular orbit has Bernoulli extreme-value behavior | H | finite records and null model | Still open | H |

Tags: P proved; A conditional; M measured; H hypothesis; S design language; R retired interpretation.
No Lean theorem is promoted to newly verified P status here.

## Strongest surviving result

The same 10-million-step parity stream is regenerated with Python exact integers. Its
SHA-256 (one byte per parity) is
3d2d5bdb241a7d9c043a021676efc6ab8955a426d38ab03a1e68b51c0f4ee651.
The final b has 5,849,628 bits. Generation took 162.73 seconds in this environment;
this is not a matched performance comparison with the reported 17-second GMP run.

New drawdown records in the registered record-time interval [10^6,10^7]:

| t | DD(t) | DD(t) / log_phi(t) |
|---|---|---|
| 7,325,962 | 30 | 0.9132924706 |
| 7,325,963 | 31 | 0.9437355449 |
| 7,325,964 | 32 | 0.9741786185 |

The counter remains nonnegative in the checked horizon and is at least 12 for t >= 15.
This reproduces a known bounded non-halting observation, not a new non-halting result.

## Load-bearing obstruction

The unproved bridge is from finite residue coding / a stochastic null model to quantitative
rare-event control on one specified deterministic orbit. The finite observations do not
provide that bridge. Calling the state a cusp or a solenoid does not discharge it.

The conjecture's broad phrase "every Cryptid orbit" also needs a fixed domain of machines
and specified starts. A cryptid is a research classification, not a class already proved to
share a measure-preserving dynamical model. In particular, the Antihydra coding theorems
are not automatically encodings for A.1--A.11.

## Specification -> implementation -> test audit

- The original generator executed at import and wrote to an assumed /tmp/zk/p1 directory.
  The replacement is importable, has explicit CLI paths, and creates output parents.
- A chunk uses exactly k low bits to determine k parities. It checks exact divisibility of
  3^k*b+S by 2^k instead of silently shifting away a remainder.
- The generator evolves autonomous b even if the associated counter has already crossed
  below zero. The monitor now reports the first negative counter time explicitly.
- Drawdown includes the initial peak a_0=0. A deliberately all-odd test catches that edge.
- P1 reports the original record-time target, not a stronger all-times target. Absence of
  new records is marked inconclusive, rather than treated as a successful observation.
- Prediction-band limits and separate alert thresholds are distinct fields. Failure of
  a band does not by itself prove a deterministic bias toward halting.
- Degenerate P4 tables no longer manufacture an all-clear result.
- The original conjecture file is retained unchanged as a historical record.

P2 and the window-machine logarithm laws are not reproduced by this contribution.

## Direction, type, and metric audit

1. **The no-go theorem is narrower than the conversation's conclusion.**
   invariant_needs_dvd3 quantifies over affine counter-time expressions a+c*t and
   arbitrary parity walks. Failure of a>=0 to be closed on the whole state space does
   not exclude a smaller inductive subset containing the chosen start. A general
   Presburger impossibility theorem would require a separate argument.
2. **P3 is not a law-of-the-iterated-logarithm band.**
   The monitored deviation is 3*sqrt(ln(t)/t). The classical LIL normalization involves
   ln(ln(t)). This correction does not change the numerical P3 result.
3. **CRT is algebraic, independence is measure-dependent.**
   Product residue classes can be counted under a uniform ensemble. A particular
   deterministic trajectory need not sample that ensemble uniformly. The statement
   that predictive memory must live only in the real coordinate is therefore not
   established by CRT. It remains an interpretation requiring a specified model.
4. **Normality is weaker than the needed extreme-value control.**
   Fixed finite-word frequencies alone do not impose a logarithmic longest-run law.
   Sparse inserted blocks of zero density can preserve normality while producing
   abnormally long runs. A stratum implying the logarithm law needs quantitative
   uniformity / dependence bounds for the growing rare-event windows.
5. **An unknown asymptotic onset cannot be covered by an arbitrary finite prefix.**
   Eventual positive drift permits an earlier finite barrier crossing. An effective
   non-halting certificate must cover every time: a verified prefix up to an explicit
   N, and valid tail bounds from that N onward. Continuing the free b-orbit after a
   counter halt must not erase that event.
6. **The golden-ratio null constant is exact for the chosen random walk.**
   The nontrivial positive root r<1 of (r^2+r^(-1))/2=1 is r=1/phi.
   The weighted transfer matrix has constant row sum, so its Perron root follows
   directly from that sum at every window depth. This validates the null model;
   it does not prove the deterministic orbit follows it. Relating this transfer
   operator rigorously to the Hermitian connection-Laplacian coefficient is a
   further operator-level bridge, not a consequence of using the same edge labels.

## Controls and resource parity

P4 now optionally calibrates the maximum absolute z across the whole family, using iid
Bernoulli(1/2) controls of exactly the same length, overlapping extraction, and window pairs.

A bounded calibration used the first 100,000 exact orbit parities, all 120 pairs with j+k<=16,
99 controls, and seed 20261020. The observed maximum absolute descriptive z was
1.8460618203; 83 controls were at least as large. The Monte Carlo upper-tail rank is 0.84,
with resolution 0.01. This is a finite check under that null, not evidence proving exact
independence. No 10-million-step Monte Carlo calibration was performed.

An alternating stream is the negative control: its strong dependence is detected by the
same procedure. Constant streams are handled as degenerate rather than passing P4.

## Independent-witness status

- The direct reference uses b <- floor((3*b+4)/2), not the chunk bridge.
- A naive Counter-based implementation independently checks the vectorized contingency
  table calculation.
- Both new implementations were authored in this review. This is independent code-path
  agreement, not an external author/model replication.
- The original raw-TM smoke check passes: Antihydra 12, A.4 44, A.9 275 decoded configurations
  in 300,000 raw steps each.
- Sixteen new unittest methods pass, including exhaustive small parity bijections, random
  starts, low-bit shifts, chunk concatenation, partial chunks, fixed-point shadows,
  import safety, invalid inputs, and matched-null reproducibility.
- Lean/lake are unavailable in this environment. No Lean rebuild or new kernel certification
  is claimed. All 10 supplied .lean files are byte-identical to the uploaded snapshot.

## Round-trip coherence

Requirement: support discovery of additional small machines without promoting empirical
patterns to proofs. The contribution provides reproducible finite evidence and explicitly
typed outcomes; it does not treat passing tests as a universal macro-rule theorem. The
remaining gap is universal reachability/closure and the chosen orbit's asymptotic behavior.

## Corrections and retirements

The historical conjecture text is not rewritten. This addendum narrows the no-go,
independence, LIL, and effective-tail interpretations above. The README also corrects an
outdated source statement: the PDF contains a hyperlink to google-deepmind/cryptids.
The original upstream proof library is neither imported nor rebuilt here.

## A concrete queue for finding more cryptids

results/candidate-inventory.json extracts all 52 Appendix C candidates and compares
literal machine encodings with Table 1 and machine-module names in
google-deepmind/cryptids at commit a0c1f56af53a76e985a656032b48015f7e48921b.

- 26 candidates appear in the paper's completed-results table.
- 25 candidates have an exact machine-module name in that upstream snapshot.
- 25 are outside both checks: 24 BB(6), one BB(2,5).

These are follow-up leads, not 25 new cryptids. Missing a literal module does not exclude
an equivalent machine, analysis elsewhere, or a later resolution. Refresh against the
latest holdouts and community equivalences before spending proof effort.

For those leads, the specific search extension worth testing is **jointly choosing the
tape representation and the return section**. The paper's default repeated blocks have
length at most eight; its first pass favors the top 100 frequent patterns. Longer/nested
blocks and a small graph of several return sections can reveal a short exact counter map
that a single frequent tape skeleton hides. This is a proposed mechanism, not a measured gain.

## Next bounded experiment

- **Object:** a frozen, status-refreshed set of up to 25 leads above.
- **Prediction:** alternative encodings and multiple return sections produce additional
  closed macro systems for at least one lead that the matched baseline misses.
- **Primary metric:** number of behaviorally distinct, universally checked blank-tape
  halting reductions; record discovery cost separately.
- **Controls:** the same machine set, simulator data, compute budget, conjecturing budget
  and proof budget; baseline uses the paper's default length-eight block parser and
  frequent-pattern selection.
- **Representation attacks:** reflection, state relabeling, alternate block boundaries,
  and composing/splitting macro steps. Do not count a renamed known map as novelty.
- **Kill condition:** no extra certified reduction within the frozen budget; retire the
  measured advantage claim, preserving any finite observations.
- **Stop condition:** one full budget per lead; do not expand the grammar after seeing
  a failure without recording a new experiment.
- **Promotion rule:** sampled fit -> universal macro-step proofs with positive progress,
  blank-start entry and complete reachable branch coverage -> novelty/equivalence check ->
  provisional cryptid only if halting remains unresolved. A bounded raw trace is insufficient.

## Integration

GitHub returned 404 for Dojo-1/cryptid-verifier through the connected account, so this is
a reviewable snapshot contribution, not a pushed branch or pull request. Claude can apply
the accompanying patch to the matching baseline. Concurrent changes should be reconciled
rather than replacing the live repository wholesale.
