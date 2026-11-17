# L17: complete homogeneous11 returns

`link/CryptidLink/L17ab.lean` completes the two remaining homogeneous
three-run return branches, with full canonical words and exact clocks.
It also proves one parity-dispatched theorem for every repetition count.

Set P_k=(01)^k and p=u+6,c=v+7, where u,v are natural numbers. The source is

    0∞ (10)^p 0(10)^c 0(10)^3 A> (101)^j 11 R.

R is an arbitrary right context. Both branches end at a blank-left C head:

| j | Complete word after C> | Defined transitions |
|---|---|---:|
|2h|1^(2p−10) P_7 1^(2c−9) P_(3h+7) 0R|40h+2p+2c+60|
|2h+1|1^(2p−6) P_(c+3h+9) 0R|40h+2p+4c+52|

The normalized Lean clocks are40h+2u+2v+86 and40h+2u+4v+92.
`a11_homogeneous_blankleft_exact` chooses the clock and complete result
by j modulo2; it is a theorem for every j, not a bounded enumeration.
The statement concerns these guarded configurations, not their occurrence
on the blank orbit.

The proof composes the phase-correct L17aa dispatch with a middle C sweep
and the last K41 return in the even case. The odd case uses a D sweep and
the last K22/C return. Middle and outer layers consume different numbers
of pairs; the two framed helper theorems retain that distinction.
`CLAUDE-BRIEF.md` gives the composition and remaining task.

The five00/100 branches were already formalized in L17t/u/v/x. Together
these cover all seven cases of the archived homogeneous three-run table.
General mixed01/101 scanning and five-run return remain open, as do
blank-orbit stack boundedness and nonhalting.

## Reproduce

The standard project build and trust gate include all new declarations:

```sh
python3 scripts/verify.py --project link
```

Finite cross-checks, from the repository root:

```sh
python3 -m unittest discover -s analysis/l17-11-returns -p 'test_*.py' -v
g++ -std=c++17 -O2 analysis/l17-hardening/raw_comparator.cpp -o analysis/l17-hardening/comparator-O2
python3 analysis/l17-11-returns/check_returns.py --cpp analysis/l17-hardening/comparator-O2 --no-save
```

Omit `--no-save` to archive raw responses and reports inside this directory.
`controls.py` additionally builds O2/O0/UBSan variants and compares16
identical translated inputs in each, under the same2-million-step budget.
The CI step performs fresh C++ execution against all1072 cases.

The bounded campaign checks928 complete returns and144 arbitrary-context
helper paths. All1072 whole endpoints and read extrema agree across C++
and Python;1015 requests have full trace comparisons. Twelve planted
expectation faults are detected. These are same-author controls; the
unbounded result is the Lean theorem. See `VALIDATION.md` for actual checks.
