# E82 — entire 95-step G3 fixed bridge is preterminally safe

The existing E67 95-step G3 bridge returns to control C with left
tape **exactly L**. E78 proved that choosing arbitrary L=blank produces
a genuine blank-left C endpoint. E79 proves the actual structured
E60 exterior L3(u,v) retains a second-left-cell 1 at that endpoint.

The present theorem handles the complementary interval: **all raw
times t<95**, universally for arbitrary exterior left/right tapes.

## Exact theorem candidate

```text
forall (L R : ListBlank (Fin 2)) (t : Nat) (c : Cfg),
  t < 95 ->
  ReachesIn target t (A(W3 ++ L; 11 ++ R)) c ->
  not E76BlankLeftC(c)
```

`W3` is the exact fixed 43-bit G3 bridge word from E67.

## Raw-machine candidate events, verified symbolically by Lean if CI passes

| Step | Complete fixed left prefix at C | Witness |
| ---: | --- | --- |
| 17 | `11001010101010101010101010101001010101` | head-nearest 1 |
| 79 | `11010101` | head-nearest 1 |
| 91 | `1001` | head-nearest 1 |

At every other preterminal timestamp, the control state differs from
C. The machine reads only the fixed window [-42,1], so arbitrary
exterior tapes are retained as symbolic `ListBlank` arguments.

The Lean module constructs 95 exact full-configuration
`ReachesIn target t` certificates, t=0..94, using verified
one-step transitions and `ReachesIn.trans`. It then proves exhaustive
windowed time cases [0,20),[20,40),[40,60),[60,80),[80,95).
The public `e82_G3_bridge_noBlankLeftC_before95`
is registered in the trust inventory.

## Important distinction

The universal safety interval is **open at the right endpoint**:
t<95. The false statement t<=95 for arbitrary L is refuted by E78.
To cover t=95 for E60, use E79's *structured* left exterior.
Do not strengthen a theorem merely to simplify a final composition.

## Evidence status

- P prerequisite: E67 exact 95-step bridge and E78 deep witness
  / blank-exterior counterexample
- P on original branch, merge pending: E79 structured exterior
  endpoint theorem
- H: E82 until pinned Lean link and standard-axiom audit
- M: E72's 930 bounded full traces; local 95-step literal simulation

No claim of the parameterized final unwind, complete E60 first-return
minimality, blank-tape orbit reachability, arbitrary scanner grammar,
or universal L17 nonhalting follows yet.
