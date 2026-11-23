# E83 — reuse E73 to eliminate the variable G1 final A sweep

The exact G1 final unwind theorem E68 begins at

```text
A((01)^p 0 (01)^(u+6) blank ; 111 R)
```

and lasts `4p+29+2u` steps before reaching its complete
blank-left C output.

The existing **P** E73 theorem proves no C visit during the first
`4p` steps of

```text
A((01)^p L ; 11 R')
```

for arbitrary left/right tape exteriors. In the E68 source choose

```text
L = 0 (01)^(u+6) blank,
R' = 1 R.
```

The two complete A configurations are definitionally equal.
Consequently E73 itself certifies a C-free initial `4p` interval
for **every p,u and arbitrary R**, with no extra raw machine paths.

## Lean targets

- `e83_G1_unwind_A_prefix_C_free u p R`
  proves `E73NoCBefore` during `4p` steps.
- `e83_G1_unwind_A_prefix_noBlankLeftC u p R`
  derives the first-return safety predicate during that interval.

Both theorem statements have separate `#print axioms` entries
and are included in the link trust inventory. **H until pinned
Lean CI succeeds**; their mathematical proof relies exclusively
on the previously certified E73 safety theorem.

This is a genuine reduction of the variable-dependent part of
the G1 unwind. What remains after this sweep is a fixed 25-step
A finish followed by a `2(u+2)`-step C01 finishing sweep,
whose earlier C visits require nonblank-left witnesses.

The G3 C-mode finish has a different structure, with C visits
throughout its initial `2(p+1)` phase, and needs its own
safety invariant. Neither claim proves full E60 first-return,
blank-tape orbit reachability or universal L17 nonhalting.
