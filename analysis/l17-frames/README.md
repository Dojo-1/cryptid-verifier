# L17 alternate frames and opposite streams

Read CLAUDE-BRIEF.md for the useful mathematical results. FRAME-NOTES.md covers
the tape transformations. This folder is separate from Claude's current Lean
formalization; no earlier source or Lean file is changed.

The six internal canonical D/G rows admit a unique, terminating backward
stream. Forward iteration terminates at a named exit using(s,l,R), where
R_D=3k+8m+3 and R_G=3k. F1100 entries are roots. A global affine scalar ranking,
even affine by mode, is impossible for this guarded system. These are analytic
conditional results ready for formalization, not new Lean theorems.

Exits remain important: the current rows still leave short widths/terminals
and low guards unsupported. Generic input witnesses and precise guard failures
are included. No new blank-orbit prefix, universal S-return or nonhalting claim
is made.

The small ZIP is standalone for these experiments. It includes six exact,
unchanged dependencies from the preceding handoff, including the recovered
977821-bit boundary. Their hashes are in dependency-hashes.json. Extract at a
repository root, or into an empty folder. All scripts write in this new folder.

Run:

```bash
python3 -m unittest discover -s analysis/l17-frames -p 'test_frames.py' -v
python3 analysis/l17-frames/validate_streams.py
python3 analysis/l17-frames/verify_streams.py
python3 analysis/l17-frames/validate_frames.py
python3 analysis/l17-frames/verify_frames.py
python3 analysis/l17-frames/mutations.py
```

Python3 and g++ are sufficient; no new Python dependency is required.
The frame campaign compiles the frozen literal C++ machine and compares32
traces with the separate Python transition table. Eight reversible views agree
on103368 decoded snapshots of12921 aggregate logical steps. This is eight
views of the same prefixes, not a longer run or independent authorship.

The ACAF pattern is used manually for seeded counters, binary tapes, coordinate
maps and deliberately wrong predicates; its graph wrapper is not used. The
new generic counter critic solves the frozen row equations with exact Gaussian
elimination and imports no counter actor. Its comparison driver does import
the actor being checked, as expected. All paths share authorship.

No campaign endpoint or guard mismatch occurred. Supplementary verification
uses2400 separately seeded counter states after the registered4000-state main
sample; this additional check is labelled supplementary, not preregistered
exploration. It changes neither the derived claims nor a stop threshold.
