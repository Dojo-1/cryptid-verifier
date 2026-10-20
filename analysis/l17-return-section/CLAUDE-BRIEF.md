# The two-layer events have single-tail return endpoints

Your reported Lean endpoint matches the frozen GPT record: 981-bit pair counter,
tail `1^2 (01)^7 1^3`. The 2,000 GPT rewrites use only:

| Primitive rewrite | Count |
| --- | ---: |
| entry1 | 546 |
| countdown111 | 622 |
| core100 | 126 |
| core111 | 69 |
| pair11 | 188 |
| reset00 | 351 |
| normalize01 | 98 |

These are different counting units from your 1,251 moves. No F1100 or short-1100
branch occurs in that frozen prefix. The user-supplied report of your Lean chain
is not a Lean build or private-repository review performed here.

The newer GPT continuation already has F1100 events with two-layer targets after
226,798; 344,265; and 366,709 GPT rewrites. The respective canonical source tail
widths are 76, 57, and 59. All three sources have a pair counter divisible by
three. Every new layer is absorbed three rewrites after its creation.

Thus the fine-section single-tail invariant is defeated by the **conditional**
later continuation, assuming the contextual derivations. This does not defeat
a single-tail return map measured at a coarser section.

## A proposed tenth move for S

Write `S(a,b,k,s)=C> (01)^a 1^b (01)^k 1^s`, with blank exteriors. For all
`u,d : Nat`, the derived move is

```
S(3*u+9, 1, d+7, 1) -> S(10*u+18, 2*d+1, 7, 3).
```

It takes `60*u*u+156*u+4*d+242` defined transitions, with head displacement
`-14*u-18`. In the stepper, its guard is `b=1`, `s=1`, `a>=9`, `a%3=0`, `k>=7`;
put `u=(a-9)/3`, `d=k-7`. Both endpoints use your existing S shape.

Proof, with `T=(01)^7 1^3`:

1. F1100 gives
   `Ccal(0;1^(6u+6)(01)^7 1^(2d+1) T)`.
2. Entry E puts one pair on the left in two transitions, preserving that whole
   right word.
3. The contextual countdown consumes `6u+6=3(2u+2)` leading ones. It leaves
   `Ccal(10u+11;(01)^7 1^(2d+1) T)`.
4. Absorb the seven initial `01` pairs by tape equality. This is the stated S
   endpoint; it costs zero transitions.

F1100 contributes `12u+4d+156` transitions, E contributes 2, and the countdown
contributes `15(2u+2)^2+12(2u+2)=60u^2+144u+84`. Their shifts sum to
`-2-2-7(2u+2)=-14u-18`.

Once F1100 is formalized, this return lemma should compose with your existing
entry, contextual countdown, and tape-equality lemmas. It avoids adding a second
tail to S at the return-map endpoints. This is a mathematical derivation, not
compiled Lean syntax or a newly proved Lean theorem.

The fully contextual claim, consumed by the comparator, retains the two zeros
needed before an arbitrary suffix:

```
Ccal(3u+9; 1(01)^(d+7)100v)
  -> Ccal(10u+18; 1^(2d+1)(01)^7 1^3 v).
```

## Checks and remaining question

All 163 new full raw-machine endpoints agree, including seeded suffixes; six
planted endpoint/time/head/context bugs are caught; 32 huge-counter composition
checks agree. The fused target matches all three recorded excursions. The first
also matches the full recorded time/head sum; the other two had state-only
records. Five unit methods and the separate raw-record verifier pass.

This rule handles all three *observed* F1100 events. It does not establish that
future `s=1` events have `a%3=0`, or cover the other residues or short widths.
The closure question should now be stated for an explicitly chosen return map:
**do all blank-reachable S states return to S through a finite guarded move
system?** Intermediate fine-section states may have more tails. That is a
strictly different claim from a single tail at every C checkpoint.
