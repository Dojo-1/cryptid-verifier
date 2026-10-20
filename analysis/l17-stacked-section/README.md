# L17 stacked-section handoff

Start with [DERIVATION.md](DERIVATION.md). It gives both nonzero-residue endpoint
formulas, three contextual sweep lemmas, six short-tail cases, exact finite
proof segments, guards, time sums and head shifts. Claude has reported the
divisible-by-three branch as proved. [CLAUDE-BRIEF.md](CLAUDE-BRIEF.md) is the
short handoff.

This folder contains no Lean file and claims no Lean build. Claude's reported
machine-level proof of the previous boundary is recorded as supplied context;
it has not been independently inspected here.

From the repository root:

```bash
python -m unittest discover -s analysis/l17-stacked-section -p 'test_stacked.py' -v
python analysis/l17-stacked-section/validate.py
python analysis/l17-stacked-section/validate_tail_family.py
python analysis/l17-stacked-section/validate_small_tails.py
python analysis/l17-stacked-section/trace_symbolic.py
```

Python 3.12, standard library only. No network, installation or compiler is
needed. Imports perform no simulations or writes. Running `validate.py`
rebuilds `validation-results.json`; its timestamp changes on rerun. The other
validators regenerate their named JSON outputs. `trace_symbolic.py` reproduces
the separately bounded 2,000-rewrite prefix and checks the exact frozen trace
without overwriting it. All reference probes remain below 200,000 raw
transitions.

| File | Purpose |
| --- | --- |
| `DERIVATION.md` | Main mathematical handoff and evidence boundaries |
| `rules.py` | Guarded formulas and original bounded rewrite engine; the new 1100 lemmas are separate functions |
| `words.py` | Exact finite periodic-word representation, with no huge expansion |
| `reference.py` | Independent dense raw interpreter |
| `block_sim.py` | Independent finite-block evaluator with repeatable sweeps |
| `validate.py`, `validation-results.json` | Finite cases, local paths and separate derived prefix |
| `validate_tail_family.py`, `tail-family-checks.json` | 1,680 one-tail cases, 320 additional F1100 cases, K60 and nonclosure witness |
| `validate_small_tails.py`, `small-tail-checks.json` | 684 short-tail cases, 64 larger contexts and seven finite kernels |
| `trace_symbolic.py`, `symbolic-extension.json` | Frozen derived 2,000-rewrite trace and exact reproduction |
| `probe_remaining.py`, `remaining-tail-probes.json` | The exploratory 64-case r=1 screen, separate from validation |
| `test_stacked.py`, `tests.log` | Fourteen passing regression/property methods |
| `protocol.json`, `steering-and-predictions.json` | Original follow-up scope and later task split before validation |
| `*-protocol.json`, `*-predictions.json` | Explicitly separated later phases and their limits |
| `audit-manifest.json`, `integrity.json` | Claim map and post-run byte integrity |

The combined handoff ZIP also contains the original 28-file contribution at
`analysis/appendix-c-leads/`, including its `census.json`, C++ simulator and 15
tests. That directory preserves the earlier dated report and its historical
evidence labels. Its original protocol-checksum issue remains disclosed there;
it is not changed by this follow-up.

Both directories are additive. No existing project README, current Lean proof,
or Claude-owned notes are overwritten by the archive.

There are 4,333 rule endpoint checks and 300 random interpreter controls in
the three validators, in addition to the unit tests. Separate implementations
by the same author are not external independent replication. The original
protocol called its oracle sparse; this follow-up uses a dense bytearray
oracle instead, keeping its raw-transition budget. The earlier contribution
still contains its sparse oracle.

The one-tail shape is not closed: a checked 152-transition example creates
two copies of `T=(01)^7 1^3`. The supplied blank-orbit prefix has not needed
that extra layer. General stacked closure, bounded versus unbounded stack
depth on the blank orbit, and halting remain open. Nothing here is a new Lean
build or a new certified Cryptid.
