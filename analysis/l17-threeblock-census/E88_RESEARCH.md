# E88 — the positive-width G1 E60 first blank-left-C return

**Status H** until pinned Lean CI, all trust checks, and manual statement review.
Dependency graph: merged E84 #78; E77 preregistered fixed prelude #71;
E85 #79; E86 #80; E87 #81. This PR folds the E77 branch into the
E87 branch via a two-parent commit; no prior result is redefined.

## Exact theorem scope
For every m,u,v in Nat, and all binary full right exteriors R,
the original E60 G1 source at physical width M=m+1>=1 first reaches
blank-left control C at raw time T=214+6M+2u+4v.

"First" means no blank-left C at any strictly earlier raw clock
0 <= t < T, not simply no earlier visit to the control C.
The endpoint right tape is exactly E71's F1 output. This is a
machine-level conditional section family, not proof that the blank
initialization reaches any such source and not nonhalting.

## Four strict intervals
1. E77 full G1 fixed prelude, t in [0,88), arbitrary exteriors.
2. E74 A window, t in [88,88+6M), control never C.
3. E81 fixed G1 bridge, 77 timestamps, t=71 deep left witness.
4. E87 entire G1 final A unwind, duration 4(v+5)+29+2u,
   with a strict 25-step fixed finish and sentinel-dependent C01 tail.

Exact clock identity:
  88 + 6M + 77 + 4(v+5) + 29 + 2u
    = 214 + 6M + 2u + 4v.

## Full-configuration seam checks
- Prelude right exit `0 (10)^m 111 R` equals `(01)^(m+1) 11 R`.
- The E65/E64/E66 exact window endpoint matches the E67 bridge
  source through E69's original left-word rearrangement.
- The E67 bridge right exit `11100 (10)^16 (10)^M R`
  matches E87's guarded A source as `111 ++ (00 ++ (10)^16 ++ (10)^M R)`.
- The E70 widthFourCutSource is the contextual E65 C source after
  splitting `(10)^(m+1)` as `10 ++ (10)^m`.
- E71 supplies the exact terminal F1 word. E84 packages the endpoint
  and strict preterminal exclusion into local first-return minimality.

## Adversarial guards / kill cases
- `M=0` has no theorem and is the retired affine extrapolation.
- Do not extend this result to G3: its fixed 95-step bridge has a
  genuinely unsafe blank exterior at t=95 (E78), and a structured
  left witness only for actual E60 geometry (E79).
- `m,u,v` and `R` are fully quantified. Do not silently
  replace R by blank or shorten the physical left tape.
- This theorem does not certify an eventual sequence of return
  sources starting from blank, nor mixed scanner grammar closure,
  nor L17 nonhalting.
- Any Lean error, unexpected axiom, failed full-tape seam or
  trust inventory failure blocks promotion and merging.
