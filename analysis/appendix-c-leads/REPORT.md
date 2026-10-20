# Twenty-five leads: status refresh and bounded discovery

**Result:** 25 starts were screened, with no newly certified cryptid. The screen
produced a sourced census, explicit transition-table witnesses and a partial
two-counter reduction for L17 with a concrete remaining boundary case.

This work covers the discovery track. Claude's separate task connects the
project's existing rules to the upstream machine-level Lean proofs. No existing
project or Lean file is changed by this contribution.

## Status and equivalence, as checked on 2026-10-20

The census uses the [663 BB(6) representative holdouts](https://wiki.bbchallenge.org/w/images/6/69/BB6_holdouts_663.txt),
the [37 BB(2,5) holdouts](https://wiki.bbchallenge.org/w/images/9/9b/Bb2x5_informalLast37.txt),
the complete public [1,534-row BB6 annotation sheet](https://docs.google.com/spreadsheets/d/1mMp8bAcTFT91j7azn72liX8NSTwc2E_ozKnOGTfRCfw/edit?gid=1330361301),
machine pages and the 53 BB(6) module names in the
[pinned upstream repository](https://github.com/google-deepmind/cryptids/tree/a0c1f56af53a76e985a656032b48015f7e48921b).
Input hashes and exact source rows are retained in `census.json`.

- **L02, L09 and L10 belong to an already documented cryptid family.** Their
  tables are conjugate to
  `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`, with their starts mapped to C, D
  and E respectively. The wiki redirects all three to the
  [Racheline2024 family page](https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA).
  This does not identify their individual blank-tape orbits with one another.
- **L25 is reported resolved with moderate rigor.** The
  [BB(2,5) wiki](https://wiki.bbchallenge.org/wiki/BB(2,5)) lists the exact code
  among 22 Lean-proof reports whose independent verification is pending. The
  specific proof and its halting/non-halting conclusion were not rebuilt here.
- **L13 already has a public analysis and simulator.** It appears on
  [Machines at the Edge](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Machines_at_the_Edge)
  and in [Laturas's simulator](https://github.com/Laturas/mildly_upsetting_tm_simulator).
  This is an existing lead, not a fresh discovery.
- **L22 has a related-machine analysis noted in the annotation sheet.** That
  note does not establish behavioral equivalence to the exact L22 table.

Of the 24 BB(6) starts, 16 occur literally in the 663 representative list and
eight do not. All 24 have rows in the annotation sheet. The eight literal
absences are **L03, L05, L07, L08, L14, L15, L22 and L24**. The sheet does not
mark these eight resolved. Absence from a representative list is not a solution
certificate or a complete status determination.

The 25 inputs occupy **19 transition-table families when the initial state is
ignored**, under state renaming and tape reflection. The nonsingleton groups
are:

| Lead IDs | Relation checked |
| --- | --- |
| L02, L09, L10 | One documented table family, distinct initial-state variants |
| L04, L16 | One table family, distinct initial-state variants |
| L07, L08, L22 | One table family, distinct initial-state variants |
| L14, L24 | One table family, distinct initial-state variants |

Every witness checks every transition, preserves blank symbol 0, and records
where initial state A maps. None of these within-queue matches preserves the
initial state. Thus 19 is a count of table families, **not** a reduction of the
25 blank-tape halting questions to 19. Whether some starts eventually coalesce
or have equivalent future behavior remains a separate proof obligation.

No lead matched an upstream module by the literal table conjugacies implemented
here, including when the start state was ignored. This search does not cover
block encodings, symbol complementation, general tape transducers, or arbitrary
behavioral equivalence. It does not establish novelty.

## Fixed-budget raw screen

`protocol.json` was recorded locally before these simulations. Its budget was
5,000,000 raw transitions per lead, 16 reservoir samples per section, seed
20261020, and maximum recorded support span 8,192. Sections distinguish state,
previous movement, reversal and position relative to the nonzero support.

All 25 machines completed their horizon without an observed halt: **125,000,000
raw transitions** total. The run retained **3,740 exact configurations**, with
no width-filter exclusions. This is a modest finite horizon, not evidence that
the community has not simulated further and not a non-halting proof.

Reservoir snapshots are not consecutive return events. No transition formula is
inferred by joining consecutive rows in a reservoir. Formulas are checked by
restarting exact raw-TM execution on their proposed complete input tapes.

### Representation comparison

Both parsers receive the identical saved configurations and scan each tape side
from the outer boundary toward the head. The baseline implements Appendix D's
block score and boundary lookahead with maximum block length eight; the variant
uses 32. A primitive-word optimization is checked against a literal independent
implementation of the paper's pseudocode. Expansion reconstructs each tape side
exactly.

| Diagnostic over the same 3,740 snapshots | Max block 8 | Max block 32 |
| --- | ---: | ---: |
| Mean blocks per complete finite configuration | 12.569786 | 11.875936 |
| Distinct state/block-word families, summed over machines | 2,157 | 2,166 |
| Families represented by at least three snapshots | 313 | 311 |
| Additional complete universally checked reductions | 0 | 0 |

The smaller mean block count is a representation diagnostic. There is no
demonstrated discovery-rate benefit. Both parsers use the same stratified
sections, so this comparison does not isolate an effect of choosing different
sections. It is not a replication of the paper's full learning pipeline.

## L17: the concrete handoff

L17 is

```text
1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---
```

Its annotation is Bell-like; the exact machine also appears as undecided on
[bbchallenge](https://bbchallenge.org/1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---).
The census does not certify its novelty or cryptid status.

On the section `C(a,b) = 0^infinity C> (01)^a 1^b 0^infinity`, four branches
reduce to linear counter updates with exact raw step counts. The remaining
branch is `a>=1,b=1`. See [the full derivation](l17-reduction.md).

The proposed endpoint formulas passed **4,433 distinct raw checks**, including
the 65-by-65 guarded grid, 256 seeded larger inputs, and 16 saved section inputs.
The collapsed countdown formulas passed 80 additional raw checks. Three fixed
local sweeps are checked to read only their own blocks; the universal induction
and composition are supplied as a mathematical derivation, not a Lean proof.

For `C(a,1)`, `1<=a<=64`, a fixed 200,000-step first-return probe per input found
39 returns, 25 timeouts and no halts. A timeout remained a timeout; no failed
horizon was extended.

Starting from the blank tape, the supported formulas predict the first open
boundary to be **C(53,262,756, 1)** at raw time **1,870,497,627,040,360**.
This is a conditional arithmetic derivation after the screen, not simulation
to that time. Its full checkpoint sequence, time sums and head shifts are in
`l17-probes.json`. The separately executed raw prefix probe stopped at its
200,000-step budget, with last complete endpoint C(471,344) at time 199,382.

The useful next proof obligation is therefore specific: formalize the four
supported branches and analyze the singleton-suffix boundary at that reachable
counter value. A closed reduction or a cryptid certificate is still missing.

## Validation and evidence ledger

**15 tests pass** under Python 3.12.14 and GCC 13.3.0. They compare the C++ scanner
with an independent sparse-tape Python interpreter on all 25 leads, three
answer cases and 100 seeded random tables, including every saved configuration
in the bounded validation runs. Parser tests cover all binary words of lengths
zero through nine, 500 additional structured/random words, both widths and the
paper's lookahead example. Conjugacy tests check random state renamings and
reflections and reject a changed transition. L17 tests cover raw endpoints,
section rejection, local sweep boundaries and budget handling.

Both implementations and the oracle were written by the same reviewing agent.
They are different code paths, not an external independent replication. No
Lean/lake toolchain was available, and no Lean build or proof is claimed.

| Tag | Claim | Evidence and remaining limit |
| --- | --- | --- |
| M | Exact public snapshot membership and annotations | Source bytes, URLs, hashes and 24 sheet rows; later status may change |
| M | Literal table witnesses | Every transition checked; does not preserve starts in the within-queue groups |
| M | No halt in the fixed raw screen | Exact run and differential checks; finite horizon only |
| M | Finite L17 endpoint agreement | 4,433 branch cases and 80 collapsed cases |
| A | Universal interpretation of the four branches and huge blank prefix | Supplied sweep derivation; awaits formal verification |
| H | A complete new cryptid reduction for L17 | Open singleton-suffix branch, closure and novelty checks remain |
| R | Claiming 25 new cryptids or a measured discovery-rate improvement | Neither is supported by this experiment |

The original local protocol's input-checksum field is not reproducible from the
delivered input files. It is preserved, disclosed in `protocol-check.json`, and
is not used as authentication evidence. The embedded 25-entry queue matches
the simulation input and trace rows exactly. The new integrity hashes are
post-run checks, not a retroactive preregistration.

The registered promotion condition was not met: no additional **complete,
universally checked** reduction was obtained within the bounded screen.
Accordingly this report claims no new certified cryptid and no discovery-rate
benefit from the wider block parser.
