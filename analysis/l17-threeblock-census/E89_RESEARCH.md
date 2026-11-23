# E89 — G3 fixed bridge, strict safety through the structured endpoint

## Claim

In the actual E60 G3 structured left exterior,
the full 95-step A-to-C bridge avoids blank-left control C at
**every** t in [0,95], equivalently strict t<96.

All u,v : Nat and arbitrary right exteriors R : ListBlank (Fin 2)
are quantified. The 43-bit fixed bridge guard is precisely E67/E82.

## Mechanism

- E82: t<95 no blank-left C for arbitrary left/right exterior.
- E79: t=95 is nonblank-left C for the E60 structured left exterior:
  P^(v+2) ++ [0] ++ P^(u+6) ++ blank, whose second left bit is 1.
- E80: typed safety interval `E80NoBlankLeftCBefore source 96`.

No additional raw machine transitions, clock extrapolations, or
unproved recurrences. The case split is exact: t<95 or t=95.

## Negative control and prohibited promotion

E78 proves the same G3 fixed bridge with **blank** left exterior
*can* reach blank-left C at t=95. Consequently neither E82 nor
E89 may be stated with arbitrary left exterior through t=95.
An explicit structural left-witness is mandatory.

This is not a first return for G3 E60. The C-mode finishing trajectory
of length 2(p+1) + (41+2u), including its K41short core and C01
sweeps, still needs strict intermediate-state certificates.

## Evidence and gate

Status H until **new combined six-job CI**, exact `#print axioms`,
trust-inventory validation, and statement review succeed.
If complete, promote only the scoped E89 theorem to P.
The E60 M=0 extrapolation and claims of nonhalting remain retired/open,
respectively. The G1 E88 line remains independent.
