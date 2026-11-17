# L17 mixed-return continuation

The saved width2 example is now an all-parameter return lemma. For a≥5,c≥1,
the original C-section with suffix `(10)^c1101 (01·101·01·101)00v` returns
in4a+6c+152 defined transitions, head displacement−2, without reading v.

The package also gives six new finite paths, nine framed variable transfers,
and13 guarded full returns for four-run left tapes with small final widths2–5.
These extend the preceding homogeneous101 package. They do not prove universal
mixed-stack return, blank reachability, nonhalting or a global stack bound.
No Lean file or repository status was changed.

Read `CLAUDE-BRIEF.md` first; `DERIVATION.md` has complete words, times,
head positions, read bounds and compositions. The first Lean target is the
named mixed lemma via C2B,B_to_D(5),D_pair1(c,6),K22 and C01^(p−4).

Quick checks from the archive root:

```sh
python3 analysis/l17-mixed-return/verify_package.py
python3 -m unittest discover -s analysis/l17-mixed-return -p test_mixed_return.py -v
python3 analysis/l17-mixed-return/verify.py
python3 analysis/l17-mixed-return/mutations.py
```

Fresh C++ replay and controls:

```sh
python3 analysis/l17-mixed-return/campaign.py
python3 analysis/l17-mixed-return/controls.py
python3 analysis/l17-mixed-return/named_corners.py
```

Check integrity before regeneration: reports and cache fields may change.
Scripts write only in this new directory, have no network calls and edit no
Lean or old dependencies. C++17 is needed only for the fresh literal campaigns.
Compiled binaries are excluded. Four frozen code dependencies and three prior
explanatory documents are included for standalone use. When integrating,
add the new directory and preserve existing dependency versions if they differ.

The main846 endpoint count includes512 returns,150 transfers,144 arbitrary-
context kernel instances and40 named mixed compositions.16 lower-guard A/C
checks are supplementary.42 translated inputs are matched across three build
modes; they are not42 new discoveries.16 unit methods and20 mutation checks
pass. Same-author code paths are not external replication.

`next-boundary.json` records the remaining three-one B-mode entry. It is an
explicit unsupported guard of this table, not evidence of a nonreturning orbit.
