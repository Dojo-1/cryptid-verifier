# L17 generalized-D handoff

Read **CLAUDE-BRIEF.md** first, then **DERIVATION.md**. This adds a new folder to
all preceding contributions. It changes no Lean file and no earlier payload.

The recovered width39 event has the uniform return
S(729t+548,1,c,1) -> S(1000000t+740902,2c-22,7,3), c>=11.
The ordinary generalized D system has a finite-exit rank3k+8m. Its m=1 and m=2
boundaries require changed terminal words, so universal return to S and a
blank-orbit stack bound remain open. No new Lean proof is claimed.

The continuation reaches exactly3M original rewrites. No next unsupported
event was found before that cap. Its endpoint is S(1,B,7,3), B has1424091 bits.
This is conditional arithmetic from the retained2M checkpoint, not raw TM
simulation or a new Lean blank-prefix certificate.

From the repository root, with Python3 and g++ available:

```bash
python3 -m unittest discover -s analysis/l17-general-d -p 'test_general_d.py' -v
python3 analysis/l17-general-d/gd_verify_raw.py
python3 analysis/l17-general-d/check_compositions.py
```

To rebuild the literal campaign, including O2, O0 and UBSan:

```bash
python3 analysis/l17-general-d/gd_validate.py
python3 analysis/l17-general-d/gd_mutate.py
```

To reconstruct the conditional extension:

```bash
python3 analysis/l17-general-d/recover_boundary.py
python3 analysis/l17-general-d/continue.py
python3 analysis/l17-general-d/verify_continuation.py
```

Run scripts separately, as shown. They use the earlier frozen folders beside
this one; the complete ZIP includes those folders unchanged. The declarative
replay takes about3 minutes here. Wall times vary with hardware. A stop on a
budget is retained as a budget stop. Do not infer a mathematical obstruction
from it or lift the horizon silently.

`integrity.json` binds every new payload except itself. `dependency-hashes.json`
binds the earlier source/specification files actually consumed. Existing
response caches are reusable only when request, response and binary hashes all
match. New compilers trigger fresh execution. Mutation tests change expected
objects in memory and never edit machine or Lean sources. All scripts write
only inside this new folder.

The ACAF actor/critic/fuzzer pattern is adapted manually to TM counters and
binary contexts; the skill's graph-specific wrapper was not used. The analytic
narrative, tests and code share authorship. The separate C++ and dense Python
machines supply different literal code paths, not independent authorship.
External replay by Claude is still the appropriate next witness.
