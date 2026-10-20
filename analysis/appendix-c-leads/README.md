# Appendix C lead screen

This additive contribution follows the 25 leads from the earlier audit. It
refreshes their public status, checks transition-table conjugacies, records a
bounded raw scan, and derives a partial counter reduction for L17.

**No new cryptid is certified.** The useful handoff is the status census plus
the exact L17 rules and their open boundary.

Read [REPORT.md](REPORT.md) for results and evidence limits, and
[l17-reduction.md](l17-reduction.md) for the reduction and proof obligations.
`leads.json` maps the stable IDs L01–L25 to literal machine codes.

## Integration

The archive adds only `analysis/appendix-c-leads/`. Copy that directory into the
current repository. It does not replace the project README, previous audit,
existing scripts, or Lean files. It can be reviewed alongside Claude's upstream
Lean bridge. Nothing is executed on import, and reproduction uses no network.

## Reproduction

From the repository root, with Python 3.12 and a C++17 compiler:

```bash
python -m unittest discover -s analysis/appendix-c-leads -p 'test_pipeline.py' -v
python analysis/appendix-c-leads/census.py
g++ -std=c++17 -O2 -Wall -Wextra -pedantic analysis/appendix-c-leads/scan.cpp -o /tmp/cryptid-lead-scan
/tmp/cryptid-lead-scan analysis/appendix-c-leads/leads.txt /tmp/cryptid-lead-traces.jsonl 5000000 20261020 16 8192
python analysis/appendix-c-leads/analyze.py /tmp/cryptid-lead-traces.jsonl /tmp/cryptid-lead-representations.json
python analysis/appendix-c-leads/probe_l17.py
```

`census.py` rebuilds from the bundled public source snapshots; it does not fetch
new status. Refresh the sources explicitly before using the census as current
information at a later date. Its generation timestamp changes on rerun.

The scanner writes only the requested output file. The other entry points write
their named JSON outputs in this directory. Tests compile into a temporary
directory. No compiled executable is bundled.

## Files

| File | Purpose |
| --- | --- |
| `protocol.json`, `protocol-check.json` | Original prospective local protocol and later integrity check |
| `census.json` | Per-lead source rows, literal membership, exact table witnesses, prior-analysis flags |
| `holdouts-663.txt`, `holdouts-2x5-37.txt`, `bb6-annotated.csv` | Public source snapshots, URLs and hashes in census |
| `upstream-inventory.json` | Pinned upstream machine-module names |
| `traces.jsonl`, `scan.log` | Exact reservoir snapshots and bounded raw-run summaries |
| `representations.json` | Both repeated-block encodings on the same snapshots |
| `l17-probes.json` | Finite rule checks, frontier probes, raw prefix and separate derived endpoints |
| `test_pipeline.py`, `validation.log` | Differential and adversarial validation |
| `audit-manifest.json`, `integrity.json` | Claim ledger, provenance and delivered-file hashes |

The local protocol predates this screen, but has no external authenticated
timestamp. Its original `input_sha256` does not reproduce from the delivered
input files; it is preserved and is not used as authentication evidence.
`protocol-check.json` checks the full embedded queue against the actual inputs
and trace rows, and records the correct file hashes after the run.
