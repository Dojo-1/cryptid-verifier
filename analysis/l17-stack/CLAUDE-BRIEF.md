# Handoff: a real conditional layer excursion and a short nesting induction

The remaining blank-stack question is still open, but there is now an explicit
conditional two-layer event on that orbit. The previous 2,000-rewrite prefix was
extended to 673,467 rewrites with guarded complete-word checks. F1100 fires at
source checkpoints 226,797; 344,264; and 366,708. Their targets have two layers;
all three collapse to one after three more rewrites. No three-layer state was
seen before the registered wall-budget stop.

The first source is `C(A,1).(01)^76 1`, where A has 107,633 bits and `A % 3=0`.
It reaches `Ccal(0;1^(2A-12)(01)^7 1^139 T)` in `4A+396` transitions, shift -2.
`replay-compact.json` carries A and the complete relative time/head totals in
hexadecimal. The two later sources have widths 57 and 59, also `A % 3=0`.
Their exact integers are in `deeper.json`. Those later continuations check states
only; raw counts were not accumulated. None is claimed as a new Lean theorem.

The easiest new formalization target is the following contextual identity.

Let `U=(01)^8 1`, `T=(01)^7 1^3`. For every `u,n : Nat` and arbitrary finite v:

```
Ccal(u+7; 1 U^n 00 v) reaches Ccal(0; 1^(2u+2) T^(n+1) v)
time 4u+74n+78, head shift -2.
```

It is an A-section induction using the existing K60 segment and your A/C sweeps,
plus two new fixed paths:

| Path | Input interval | Entry | Exit | Output | Steps | Reads |
| --- | --- | --- | --- | --- | ---: | --- |
| K7 | `[-4,2]:1010101` | A0 | A(-3) | `0(01)^3` | 7 | `[-4,1]` |
| K41 | `[-16,2]:(10)^6 1^7` | C(-5) | C(-16) | `11T` | 41 | `[-15,-2]` |

K7 followed by ten A-pairs takes 27 steps and enters the recursive A problem
17 cells right, with the required eight `10` pairs immediately to its left.
After recursion, sweep C over three `01` pairs and apply K41. The recurrence is
`R(0)=60`, `R(n+1)=27+R(n)+6+41`, hence `R(n)=60+74n`. The complete read-window
induction and return to the C section are in `NESTING.md`.

`C(7,1).U^2 -> C(0,2).T^3` takes 226 steps. This is a general-input witness,
not asserted blank-reachable. The identity does not iterate on its own output,
because U and T differ, and it does not prove unbounded growth on the blank run.

The new raw campaign passes 268 endpoints, 80 windows, two additional build
comparisons of 64 cases each, 12 ACAF mutations, 64 huge-counter checks, and 12
unit tests. All earlier ZIP payloads are unchanged. `verify_results.py` consumes
the declarative claims and delivered raw evidence without actor imports;
`verify_symbolic.py` separately replays the recorded conditional states.

The next mathematical target is a reachable-condition invariant, or the first
F1100 event whose new countdown does **not** immediately absorb the new outer
tail. General `(10)^c1101v` interactions with unequal widths and low guards remain
outside this nesting lemma. No global stack bound or non-halting claim is made.
