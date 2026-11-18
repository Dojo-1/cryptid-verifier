# L17: the saved mixed boundary is an exact Lean return

Let M=`01·101·01·101` and `𝒞(a;w)=0∞ C> (01)^a w`. In
[`L17MixedBoundary.lean`](../../link/CryptidLink/L17MixedBoundary.lean), for every a≥5,c≥1
and arbitrary right tape R:

    𝒞(a; (10)^c1101 M00R)
      → 𝒞(0; 1^(2a−8)(01)^(c+12)11R)

The exact time is **4a+6c+152** defined transitions. In its literal
coordinate frame the head moves−2. It generalizes PR #30's concrete166-step A-return and promotes the named mixed lemma
from the archived [derivation](../l17-mixed-return/DERIVATION.md) to a
machine-level theorem with the full endpoint retained.

The file also proves the four-run C2,s2 row for p≥4,c≥1 with six right
ones, in2p+4c+86 steps, and the A-source mixed return in2p+4c+126 steps.
It retains the two short runs instead of applying a homogeneous three-run
rule to a different source shape. The other12 rows of the old four-run
table are outside this contribution.

`CLAUDE-BRIEF.md` lists the exact theorem compositions. The thirteen public
theorems all print their axiom dependencies and are inventoried. Lean
formalizes endpoints and clocks with arbitrary context; literal comparisons
separately check the read windows. No separate Lean read-set predicate is
asserted. No blank-orbit occurrence, global mixed return, nonhalting or
stack bound follows.

The fixed-seed campaign has960 endpoints and950 full traces; the ten
longer cases check endpoints and read extrema because the comparator caps
traces at1000 steps. All12 planted faults are caught. Twenty-four translated
cases agree in O2,O0 and UBSan. These code paths share authorship.
`VALIDATION.md` records setup corrections and the conservative charge for
the rejected first comparator batch. The successful main run executes
147030 C++ transitions; compiler controls execute5589 per mode.

Fresh local replay, using the existing literal comparator:

```sh
python3 analysis/l17-mixed-proof/verify_integrity.py
python3 -m unittest discover -s analysis/l17-mixed-proof -p 'test_*.py' -v
python3 analysis/l17-mixed-proof/check_mixed.py --cpp analysis/l17-hardening/comparator-O2 --no-save
```

CI rebuilds the comparator and reruns these checks. Cached archived outputs
are retained as evidence, rather than substituted for the fresh CI execution.
