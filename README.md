# cryptid-verifier

**Lean proofs that turn machine-level halting questions into explicit arithmetic criteria.**

For Antihydra, A.4 and A.9, this repository proves exact conditions equivalent to
halting of the raw Turing machine from the blank tape. For example, **A.4 halts iff
its macro orbit reaches C(m,1) with m + s + 4 = 2^(s+2) for some natural numbers
m and s**. The remaining question is whether that particular orbit ever meets the
condition. Non-halting remains open.

L17, an Appendix C lead, has a different frontier: certified reachability to a
counter around 2·10^295, guarded return lemmas and termination of a restricted
internal graph. Its uncovered cases are recorded alongside the proofs.

This is a Lean 4 companion to *At the Limits of Computability: Steps Towards
Autonomous AI Discovery on the Busy Beaver Frontier* (Dos Santos et al.,
arXiv:2610.22603). The authors' pinned
[google-deepmind/cryptids](https://github.com/google-deepmind/cryptids/tree/a0c1f56af53a76e985a656032b48015f7e48921b)
proofs supply the raw-machine accelerations. This repository connects them to its
arithmetic criteria, adds bounded transcription checks and develops the L17 results
listed below. The core reductions use no Mathlib; the other projects retain their
separately pinned dependencies.

## Current evidence boundary

| Status | Scope |
|---|---|
| **Proved in Lean** | Exact machine-level halting criteria for Antihydra, A.4 and A.9; the L17 reachability and restricted internal-graph results listed below. |
| **Finite evidence** | Numerical orbits, literal-machine comparisons and mutation checks. They do not establish asymptotic laws. |
| **Open** | Non-halting of the three Cryptids, the logarithm-law programme, universal L17 collapse and a bound on stack depth on the blank orbit. |

The logarithm-law targets concern specified **blank-tape starts**, not all possible
initial counter states. See the corrected [conjecture note](analysis/conjecture-logarithm-law.md)
and [finite-evidence audit](analysis/independent-audit.md). For example, the Antihydra
macro state A(0,1) halts immediately; its designated blank-tape start is A(0,4).

## Build and trust checks

Install [elan](https://github.com/leanprover/elan) and Python 3.10+; ensure `lake` is
on PATH. From a clean checkout, one command builds and audits all three projects:

```sh
python3 scripts/verify.py
```

`make verify` is an optional alias. On Windows, use PowerShell with Python and elan
on PATH:

```powershell
py -3 scripts/verify.py
```

The runner selects each pinned toolchain, fetches dependency caches, regenerates
the bulk L17 proof sources, copies upstream data into the paths its elaborators
expect, and builds and audits core → Mathlib → machine links. It cleans our local
build products for fresh axiom output, retains dependency caches and stops on any
failure. Logs remain in `build.log`, `mathlib/build.log` and `link/build.log`.
For one project, append `--project core`, `--project mathlib` or `--project link`.
No manual symlinks or Bash pipelines are required. Tooling tests run on Linux and
Windows in CI; the full Lean builds currently run on Linux.

| Project | Lean pin | Dependency boundary |
|---|---|---|
| core (`.`) | v4.24.0 | No Mathlib |
| real-number proofs (`mathlib/`) | v4.24.0 | Mathlib v4.24.0 and the local core |
| machine links (`link/`) | v4.35.0-rc4 | Cryptids commit `a0c1f56` and the local core |

The separate Lake projects retain these compatibility boundaries. The runner
handles their working directories and relative dependencies. The five generated
orbit chains are [hash-checked build inputs](link/CryptidLink/Generated/README.md);
their endpoint remains tracked and CI uploads the regenerated sources and build log.
For direct manual `lake build` commands, prepare the generated sources first as
documented there; the verification runner also prepares upstream's data paths.

CI runs all three builds and the numerical evidence suite. Numerical tests need
NumPy; the literal-comparator regression also needs a C++17 compiler. These are
separate from the standard-library-only verification runner. See
[`scripts/README.md`](scripts/README.md) for maintained tooling and test commands.

The source policy rejects `axiom` declarations with
modifiers, `sorry`, `admit`, `native_decide` and direct `sorryAx` identifiers outside
comments and string literals. The gate requires both the live `#print axioms`
commands in [the explicit inventory](scripts/trust_inventory.json) and their matching
build-log output; every output record must use only `propext`, `Quot.sound` and
`Classical.choice`. The `TMLink` kernel checks use no axioms.

An absent inventoried output is a failure. The verification runner cleans local
build outputs before building so cached local results cannot omit required messages.
When adding a public theorem to this audit set, add its print command and update
the inventory together. The inventory is explicit; it does not enumerate every
intermediate lemma. This lexical/log check complements Lean's kernel and is not a
sandbox for hostile metaprograms or a proof of the surrounding prose.

## What is proved

### Antihydra (`AntihydraOuroboros/Basic.lean`)
| Theorem | Plain meaning |
|---|---|
| `run_eq` | n macro-steps = the b-tape evolving on its own under T, plus a +2/−1 walk on its parities; halt ⟺ walk goes below 0 |
| `pv_mod`, `pv_inj`, `pv_surj` | the next k parities ⟷ b mod 2^k, one-to-one and onto (every parity pattern occurs) |
| `antihydra_survives_iff` | the halting question from A(0,4) as a walk question |
| `halts_neg3`, `survives_neg4`, `halts_of_near_neg3` | 2-adically near −3 ⇒ quick halt; near −4 ⇒ survival |
| `antihydra_halt_time_mod3`, `walk_count` | a + t = a₀ + 3·(#even steps); halting only after a multiple of 3 macro-steps |
| `no_dyadic_invariant`, `no_invariant_mod9`, `no_invariant_prime_pow`, `no_integer_invariant` | no conserved quantity a + c·t modulo 2^k, 4^k, 8^k, 9, p^k (p ≠ 3), or over ℤ |
| `pv_past3` | b mod 3^j records the last j parities (3-adic memory) |
| `real_bridge` | 2ⁿ·bₙ = 3ⁿ·b₀ + Sₙ: the link to ⌊ξ(3/2)ⁿ⌋ (Mahler 3/2 setting) |

### Link to the raw Turing machines (`AntihydraOuroboros/TMLink.lean`)
Each machine is given by its standard bbchallenge string, parsed in Lean and run from the blank tape.
Every raw configuration with exactly the shape of a macro configuration is decoded, and the kernel checks
(`decide +kernel`, no `native_decide`) that the decoded sequence equals the macro run of our step functions:

| Theorem | Plain meaning |
|---|---|
| `antihydra_link` | `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`: the first 8 macro configurations (raw steps 11 … 10 933) are exactly `step`'s run from A(0,4) |
| `a4_link` | `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`: the first 25 (raw steps 7 … 8 936) are exactly `step4`'s run from C(0,3) (the tape also shows C(0,2a+4) between C(a,1) and C(2,2a+2); `step4_through_zero` checks that this is the expansion rule) |
| `a9_link` | `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`: the first 40 (raw steps 100 … 9 738) are exactly `step9`'s run from C(5,2,0) |

This is a bounded check; the general statement is in the next section. A Python version (`analysis/scripts/smoke.py`, run in CI) extends it to 300 000
raw steps: 12 / 44 / 275 macro configurations, all in agreement.

### Machine level, via the authors' proofs (`link/`, Lean v4.35.0-rc4 + Mathlib, checked in CI)
Upstream proves `IsHalt target ↔ CollatzHalts next start` for each machine, with its own finer macro system.
`CryptidLink/Sim.lean` proves a general simulation lemma (each of our steps is one or more of theirs, through an
encoding φ and an invariant), and each machine file instantiates it.

| Theorem | Plain meaning |
|---|---|
| `Antihydra.machine_halts_iff_walk` | the Antihydra TM halts ⟺ the +2/−1 walk on the parities of the T-orbit of 4 goes below 0 |
| `A4.machine_halts_iff_cascade` | the A.4 TM halts ⟺ some reachable C(m,1) has m + s + 4 = 2^(s+2) |
| `A9.machine_halts_iff_race` | the A.9 TM halts ⟺ some reachable C(a,b,c) has b ≥ 1 and (b = c or b = c + 1) |

### L17: current formal frontier (`link/CryptidLink/L17*.lean`)

L17 (`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`) is an Appendix C lead,
not one of the paper's eleven Cryptids. The work now extends beyond the original
C(53262756,1) boundary through contextual rules and an explicit finite orbit proof:

| Theorem / files | Exact scope |
|---|---|
| `L17.Orbit.blank_reaches_trace_end` | From blank, the raw machine reaches a state with a counter about 2·10^295, through 1,251 formal macro steps. |
| `D_returns`, `push_returns` (`L17g`) | Return to a one-tail section for the stated guarded two-layer subsystem. |
| General D/G rows, `RET729`, `JOIN`, `Dg11J` (`L17h/i`) | Contextual machine reachability under their explicit guards. |
| `IStep.sound`, `internal_terminates` (`L17j`) | The six internal D/G rows are sound; every internal path reaches an exit or an uncovered guard. This is not universal return to S. |
| `internal_acyclic`, `internal_unique_root`, `push_entries_disjoint` (`L17k`) | Acyclicity and unique ancestry inside that restricted graph. |
| `raw_not_injective`, `no_affine_rank` (`L17k`) | The raw machine is not reversible; no per-mode integer affine score in (k,m,l,s), independent of N, decreases on every internal row. Other ranking classes remain possible. |

Generic pushes `(a,c) = (37,7)` and `(46,7)` reach uncovered JOIN guards. Neither
is claimed reachable from blank, and neither proves that eventual collapse is false.
Universal collapse and a blank-orbit stack-depth bound remain open.
See [the L17 record](analysis/leads/L17.md) for the derivations and finite checks.

For Antihydra, A.4 and A.9, these machine-level equivalences are general theorems;
their validity is not limited to a simulated prefix. They use the authors' upstream
acceleration proofs. Lean checks the pinned dependencies, the lexical policy scans
our local sources, and the inventoried endpoint axiom outputs contain only the
permitted standard axioms. These are distinct checks with the boundaries described above.

### Antihydra as one real number (`mathlib/CryptidReal/Antihydra.lean`, Mathlib, checked in CI)
| Theorem | Plain meaning |
|---|---|
| `exists_even_after`, `exists_odd_after` (core, `AntihydraOuroboros/Escape.lean`) | within b + 4 steps every orbit shows both an even and an odd value (it never sits on −3 or −4) |
| `S_bounds` (core, `Escape.lean`) | 3(3ⁿ − 2ⁿ) ≤ Sₙ ≤ 4(3ⁿ − 2ⁿ) |
| `antihydra_floor` | **bₙ = ⌊ξ·(3/2)ⁿ⌋ − 3 for every n**, with ξ = 4 + Σₖ qₖ(2/3)ᵏ/3, qₖ = 4 − (bₖ mod 2) (ξ ≈ 7.86417726205661897…) |
| `antihydra_parity` | Antihydra's parities are those of ⌊ξ·(3/2)ⁿ⌋ − 3: its halting question is a question about the integer parts of ξ·(3/2)ⁿ (Mahler 3/2 setting) |
| `ξ_floor` | ⌊ξ⌋ = 7 |

The floor representation is an exact bridge to a specific explicit number. It does
not establish a distribution law for that number's orbit. A route to non-halting
through this representation still needs a suitable property of this particular
deterministic orbit and a proved implication to the halting criterion.

### A.4 (`AntihydraOuroboros/A4.lean`)
| Theorem | Plain meaning |
|---|---|
| `con_even_out`, `con_odd_out` | contraction steps only produce b ∈ {1, 3}, never the halting value 2 |
| `expand_closed` | closed form of the expansion cascade from C(2, B) |
| `cascade_hits_two` | the cascade from C(m,1) hits b = 2 after s steps ⟺ m + s + 4 = 2^(s+2), i.e. m ∈ {0, 3, 10, 25, 56, 119, 246, …} |
| `a4_halts_iff` | **A.4 halts from C(0,3) ⟺ it visits some C(m,1) with m + s + 4 = 2^(s+2)** (full rule system; invariant `J` also shows b = 0 is never reached) |

### A.9 (`AntihydraOuroboros/A9.lean`)
| Theorem | Plain meaning |
|---|---|
| `step9_enc` | the merged rules on C(a,b,c) are exactly the paper's two-family (C₀, C₁) rules, read through C₀(a,b,c) = C(2a,b,c), C₁(a,b,c) = C(2a+1,b,c) |
| `drain`, `sweep_le`, `sweep_gt` | the unary sweep compresses: C(a,b,c) ↠ C(a+6b, 0, c−b) if b ≤ c, and ↠ C(a+6c+3, 0, b−c−1) if b > c |
| `section_branch1` | on the section S(a,c) = C(a,0,c), with a = 2k+p: if c ≥ k+5 then S(2k+p, c) ↠ S(6k+20+3p, c−k−5) |
| `section_branch2` | if 2 ≤ c < k+5 then S(2k+p, c) ↠ S(6c−7+3p, k+4−c) |
| `a9_mod3` | along the orbit from C(5,2,0), a ≡ 2 (mod 3) always (true, but it cannot block halting) |
| `step9_halt_iff` | the only halting configurations are C(a,0,0) |
| `a9_halts_iff` | **A.9 halts from C(5,2,0) ⟺ it reaches some C(a,b,c) with b ≥ 1 and (b = c or b = c + 1)**: a draining race that ends in a tie or a lead of one |

## What remains open

- Whether Antihydra, A.4 or A.9 ever halts from the blank tape. Each question now has an explicit arithmetic criterion.
- A logarithm law, mixing or Bernoulli behavior on the designated deterministic orbits.
- Universal L17 return to S and bounded stack depth on its blank orbit. The raw transition map is not injective; the precise proved statement is in `L17k` above.

A halting witness beyond a verified finite prefix remains compatible with these
results. A longer certified run extends that prefix; settling non-halting requires
an argument covering the entire designated orbit.

## What would move the frontier

The next useful result should make the open problem more precise or discharge a
specific proof obligation. These are research targets, with no probability or
completion claim attached:

| Target | Concrete advance | Remaining obligation |
|---|---|---|
| L17 return-or-exception theorem | For every push in a stated domain, prove return to the chosen section or membership in an explicit residual family. | Determine whether the blank orbit reaches the residual cases and what happens there. |
| Conditional bounds with explicit constants | State the exact hypotheses, onset, bounds and finite-prefix coverage; prove what they imply for the machine. | Establish the hypotheses for the designated deterministic orbit. |
| Longer certified reach | Extend L17's blank-tape reachability theorem beyond the current endpoint, with every bridge and side condition checked in Lean. | Convert finite reach into a structural argument if the goal is non-halting. |

A.4 and A.9 illustrate the aim: expose the arithmetic condition that decides the
machine's fate, prove the equivalence, and leave the unresolved orbit question
visible. Useful contributions include sharper hypotheses, missing cases, checked
counterexamples and simpler verification paths. Every claim should point to its
theorem or reproducible finite test and state the gap that remains.

## Scripts and finite evidence

Maintained verification tooling is indexed in [`scripts/`](scripts/README.md).
The numerical evidence and literal-machine regression suites live under `analysis/`
and run separately in CI. Their scope is finite evidence.

The original one-off spectral, residue, stream and A.4/A.9 probes are preserved in
[`analysis/experiments/`](analysis/experiments/README.md), with their dependencies,
environment assumptions and current claim status documented. They have no dedicated
regression tests and are excluded from the supported verification path.

## Corrections log
- A.4 halting set: an external suggestion gave m ∈ {2, 7, 19, 41, 88, …} (m = 3(2^s − 1) − s). That is wrong;
  the correct set, proved here and confirmed by brute force, is m = 2^(s+2) − 4 − s ∈ {0, 3, 10, 25, 56, …}.
- A.9 branch 2: the formula k − c + 4 must be read as k + 4 − c in ℕ (truncated subtraction makes them differ).
- The 2026-10-23 audit found that the old trust scanner missed modified axiom declarations and direct `sorryAx`, and accepted incomplete axiom-output coverage. The gate now rejects those forms and requires the explicit theorem inventory; regression fixtures preserve the failures.
- CRT residue coding does not establish statistical independence on the chosen orbit. The conjecture note records this correction, the designated-start restriction and the distinction between concentration bands and LIL scaling.

## Reproducible numerical checks

The finite-evidence audit is in [`analysis/independent-audit.md`](analysis/independent-audit.md).
It adds importable exact parity generation, explicit paths, JSON results, and optional matched
Monte Carlo calibration of the overlapping-window P4 statistic. Python 3 and NumPy are sufficient;
`gmpy2` is an optional speedup. These checks do not establish a logarithm law or non-halting.

```bash
python -m unittest discover -s analysis/scripts -p 'test_*.py' -v
python analysis/scripts/antihydra_fast.py 10000000 --output analysis/results/parities-10m.npy
python analysis/scripts/predictions_p1_p3_p4.py analysis/results/parities-10m.npy --output analysis/results/predictions-10m.json
```

For a bounded calibration run (99 equally long iid controls, same overlapping windows):

```bash
python analysis/scripts/antihydra_fast.py 100000 --output analysis/results/parities-100k.npy
python analysis/scripts/predictions_p1_p3_p4.py analysis/results/parities-100k.npy --lo 10000 --null-replicates 99 --output analysis/results/calibration-100k.json
```

The conjecture note preserves the exploratory measurements and records the later corrections.
The audit distinguishes its recorded record-time P1 target from stronger all-time readings,
and prediction bands from separate alert thresholds. Git history retains the original wording.

To run the hardening harness tests with the absolute-position regression enabled:

```bash
g++ -std=c++17 -O2 analysis/l17-hardening/raw_comparator.cpp -o analysis/l17-hardening/comparator-O2
python3 -m unittest discover -s analysis/l17-hardening -p 'test_hardening.py' -v
```

CI builds this comparator before running the suite. The full archived hardening campaign is
separate finite evidence; a passing unit-test suite does not replay that whole campaign.

## Licence, citation and provenance

Original code and documentation are licensed under [Apache-2.0](LICENSE).
[CITATION.cff](CITATION.cff) identifies this repository and the upstream paper;
[NOTICE](NOTICE) records provenance and AI assistance. Imported dependencies retain
their own copyright and licences. The authors of `google-deepmind/cryptids` supply
the original raw-machine acceleration proofs. This repository's separate checks
and reductions should be credited for their stated scope, without counting shared
authorship or repeated model review as independent replication.
