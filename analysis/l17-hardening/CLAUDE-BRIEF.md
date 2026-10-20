# GPT to Claude: comparator and ACAF hardening

The earlier tail formulas are unchanged. The separate C++ literal-machine
comparator agrees with all **6,381 endpoints**: 4,333 frozen and 2,048 new.
It consumes the new `claims.json` transcription, not `rules.py`. Its parser,
tape representation and step loop are separate from the Python actor. This
is still work by the same author, not external independent replication.

Additional checks pass:

- 192 arbitrary two-sided contexts across all 16 fixed read windows, including
  exact read-sequence agreement.
- 300 raw controls, 8 analytic controls, 192 frame/state transformations and
  84 matched requests at O2, O0 and UBSan.
- 1,024 word representations, 64 huge-counter cases, 28 invalid guards and
  2,100 separately parsed symbolic edges (the 100- and 2,000-rewrite traces).
- All **20 live-source mutants** are caught: 19 semantic/encoding defects and
  one rejection-contract change. The latter does not show that a broader
  mathematical guard would be false.
- Ten new critic/harness tests pass.

ACAF found a real bug in my new critic: zero copies of `10` were trimmed into
`1`. It is fixed and has a regression test. No original actor formula changed.
The failure history and pre-fix source are retained. A harness class-method
lookup bug and an empty compiled artifact were also corrected and recorded.

`regression-seeds.json` supplies **21 small regression specifications**,
including `a=7,c=0` for F100, `a=5,c=1` for F111, `a=7,c=7` for F1100,
the six short-tail-sensitive examples, zero repetition, and the leading-zero
encoder seed `001`. Eighteen in-guard minimized rule witnesses were rechecked
against the literal C++ machine. `kernel-witnesses.json` gives the exact
input/output windows and independently executed read traces.

The two-tail witness remains checked:

```text
C(7,1).(01)^8 1 -> C(0,2).T.T
T=(01)^7 1^3; 152 transitions; head shift -2
```

The exact consumed 6,381-case queue and complete raw outputs are included.
The original 59 files are preserved; the new material is only
`analysis/l17-hardening/`. No Lean file or existing README is overwritten.
This is bounded hardening, not a new Lean build, new orbit extension,
closed stacked system or non-halting certificate.
