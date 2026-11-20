# E62 — exact double/pair/wide(2) C-return guard

## Frozen object

Three returned blocks in C processing order:
`[.double, .pair, .wide 2]`. The real mixed B scanner must satisfy
`(five virtual .a01 ++ ts) ++ term.extra = returnBlockTokens blocks`.
Both scanner stops are supported under that explicit equality.

The 25-bit right guard is `1111010101010101011010111`. This is exactly
`wide(2).output ++ pair.output ++ double.output`, followed by an
**arbitrary** right suffix. The fixed left context is 21 bits.

## Proof decomposition

- Local contextual kernel: **219 raw transitions**, C right-head to C
  right-head, left shift 21, entire exterior tapes preserved. Raw
  reads relative to the checkpoint head: `[-20,28]`.
- Local output word after the two leading ones:
  `010101010101011111111111111111101010101010101010` (48 bits).
- Existing `width4_c_finish u v`: **43 + 2u + 2v** transitions.
- Total exact checkpoint return: **262 + 2u + 2v** transitions.
- `mixed_three_pair_double_exact` composes the real mixed scanner,
  specified block parse, the guard and this checkpoint return.

The 25th guard bit is genuinely read. A 24-bit truncated guard with
arbitrary following bit produces different control/endpoint behavior in
the preregistered negative control. This is a finite contextual test,
**not a universal proof of minimality among all encodings**.

## Evidence and scope

- 200 independently coded raw full-return samples check exact state,
  head, entire tape, clock and read extrema (both scanner residues;
  arbitrary suffixes; varied u/v and origins).
- 80 additional Python/C++ differential mixed-entry full traces in CI.
- A Lean contextual theorem over **arbitrary** exterior ListBlanks, plus
  a conditional B-entry theorem over all natural u/v, only after
  green Lean link CI and the standard-axiom trust inventory.
- Re-run the exact frozen E59 census: 1016 valid cases; 990 matched at
  E59; 992 matched (24 unmatched) if and only if this guard is certified.

No universal three-block coverage, first-return minimality theorem,
blank-orbit source reachability, stack bound or L17 nonhalting follows.
Stop and reject any promotion if Lean, full tape or read-window tests fail.
