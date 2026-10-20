# L17 comparator and ACAF hardening

The separate C++ comparator matches **6,381 complete raw-machine endpoints**:
the frozen 4,333 checks and 2,048 new ACAF cases. All 20 specified live-source
mutants are detected. No original L17 formula was changed.

Read [AUDIT.md](AUDIT.md) for the evidence boundary and correction history,
or [CLAUDE-BRIEF.md](CLAUDE-BRIEF.md) for the short formalization handoff.

From the repository root, with Python 3.12 and `g++` available:

```bash
python analysis/l17-hardening/run_hardening.py --actor-root analysis/l17-stacked-section
python -m unittest discover -s analysis/l17-hardening -p 'test_hardening.py' -v
python analysis/l17-hardening/export_cases.py
```

The runner builds the C++ comparator at O2, O0 and with undefined-behavior
sanitization. It writes its own results; the original handoff stays frozen.
No network, installed Python package, Lean build or external service is
needed. Modules do no work on import.

The comparator consumes `claims.json` directly. That file is a separate
transcription by the **same author**, not an independent human transcription.
The C++ backend imports no actor code and parses the literal transition table.
The exact consumed specification and serialized request digests are recorded.

| Files | Purpose |
| --- | --- |
| `claims.json`, `specification.py` | Separate declarative claims, exact arithmetic and periodic-word equality |
| `raw_comparator.cpp`, `backend.py` | Separate sparse raw interpreter and literal request/response transport |
| `actor_bridge.py` | Explicit boundary where frozen Python code is loaded |
| `corpus.py`, `case-queue.jsonl.gz` | ACAF generation and the exact 6,381-case queue |
| `controls.py`, `trace_critic.py` | Frame/representation controls and separate arithmetic-edge checking |
| `mutations.py`, `mutation-plan.json`, `mutation-results.json` | Twenty specified live-source defects, survivors and bounded shrinking |
| `regression-seeds.json`, `kernel-witnesses.json` | Twenty-one regression specifications and sixteen read-window witnesses |
| `PERIOD-COMPARATOR.md` | Self-contained justification of the exact huge-word comparison |
| `*-results.jsonl.gz`, `*.meta.json` | Full literal outputs and hash-bound metadata |
| `execution.json`, `raw-work-ledger.jsonl` | Actual source/specification provenance and executed-work accounting |
| `attempt-1/`, `attempt-2/`, `attempt-3/`, `completed-runs/` | Preserved operational, critic and harness corrections |
| `test_hardening.py`, `tests.log` | Ten passing tests of the new critic and harness |

Literal outputs may be reused only when the serialized requests, uncompressed
response and compiled binary hashes all match. Expected values and actor
comparisons are recomputed. A durable ledger charges fresh raw batches,
including work before a later harness failure. The fixed campaign allows at
most 200,000 transitions per request and 80 million cumulatively across these
recorded attempts. A new machine/compiler may need a fresh physical replay;
the supplied history leaves enough budget for one such replay. A later budget
exhaustion is an explicit stop, not permission to raise the horizon silently.

The archive preserves all 59 payloads of the previous handoff unchanged,
including the original census, simulators and 15 tests and the 14 stacked-tail
tests. This new directory adds ten tests. Earlier test logs are historical;
this phase's ten-test log and comparator results are new.

General stacked closure, reachable unbounded depth, and halting remain open.
No new Lean theorem or new certified Cryptid is claimed.
