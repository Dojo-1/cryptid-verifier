# E86 — fixed width-four A finish: strict 25-step safety

**Proof source:** `link/CryptidLink/L17AFinishSafety.lean`
**Stack:** E84 #78 -> E85 #79 -> E86
**Evidence at creation:** H, pending Lean link and six jobs.

## Frozen object

The exact E68 G1 A-unwind proof factors the A finish as

```lean
Cfg.headRight A ([0,0,1,0,1,0,1,0,1] ++ L) ([1,1] ++ R)
 -- exactly 25 raw steps -->
Cfg.headRight C L ([1,1,0,1,0,1,0,1,0,1,0] ++ R)
```

All 26 symbolic endpoints (times 0..25) are certified using
one-step `l17_exact_steps` transitions and `ReachesIn.trans`.
Every stage retains arbitrary symbolic left/right exteriors.

## Adversarial strict-boundary census

An independent literal six-state stepper found control C precisely
at times 9, 21, 25 in the fixed 25-step path:

- t=9 left prefix nearest-first `11010101`: nonblank left.
- t=21 left prefix nearest-first `1001`: nonblank left.
- t=25 left prefix is the arbitrary `L`: it can be blank.

The Lean proof treats the first 25 states: for every `t < 25`,
the exact reachable state is non-C, except at t=9 or 21 when the
head-nearest left bit is a proven `1`. A separate theorem records
the genuine t=25 blank-exterior witness.

**Do not silently change `t < 25` to `t <= 25`.**

## Representation and independence

This kernel does not require the further left `L` to have a fixed
length or shape, or the right `R` to be blank. The chosen 9-bit
left guard and 2-bit right guard are exactly those in the merged
E68 width-four A-finish endpoint theorem.

A literal Python simulator generated a state census for independent
numeric exterior choices. It is a bounded/finite codepath, not the
universal Lean proof and not independent machine semantics.

## Next exact bridge

E83 covers the 4p C-free prefix. E86 covers the strict 25-step
fixed finish. E85 covers the final 2(u+2) C sweep *only with its
structural left sentinel*. Combine these using E80 along the
**existing** E68 exact intermediate full tape configurations, then
apply E84 to certify first-return for the E68 G1 final A unwind.

This is not yet a proof of the full canonical E60 G1/G3 first
return, scanner grammar, blank-orbit reachability or nonhalting.

## Gate

Promote only after pinned Lean link / trust / all six CI checks,
manual statement review, and a regression at t=25 with L blank.
Any proof failure or lost arbitrary exterior is a blocking defect.
