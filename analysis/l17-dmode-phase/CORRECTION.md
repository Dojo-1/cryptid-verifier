# L17 D-mode: corrected order of the exact 11 return kernels

Status: **phase mismatch in earlier proposed factorization (R); corrected
candidate ordering (M), submitted to Lean for proof (P only after CI).**

## Correction to `analysis/l17-a-stream/DERIVATION.md`

The published decomposition listed (for both even and odd `101` counts):

```
A101^j ; A11 ; D10^3 ; D6^h ; (K22 | J1K)
```

This order has a phase error when `h > 0`. The transition-compatible
decomposition is:

```
A101^j ; A11 ; D10^2 ; D6^h ; D10 ; (K22 | J1K)
```

The aggregate duration of the D-mode prelude is still `12 + 14*h`.
The reordering matters because the D6 kernel reads the full
head-inclusive tape interval `010010`. The change is **not** a
commutation theorem for D10 and D6; those operations cannot generally
be permuted.

## Smallest hostile witness

Take the guarded source `p=6, c=7, j=2`, where the A-left physical tape
is `(10)^6 0 (10)^7 0 (10)^3`, and the right input starts with
`(101)^2 11`. Coordinates are relative to the original A head.

| Absolute raw step | Current mode/head | Event |
|---|---|---|
| 29 | D at +5 | `A101^2; A11` completed |
| 37 | D at +1 | two D10 kernels completed; **D6 input applies** |
| 51 | D at -5 | one exact 14-step D6 kernel completed |
| 55 | D at -7 | final 4-step D10 completed; K22 input applies |
| 77 | C at -15 | 22-step K22 completed |

If one instead performs **three** D10 kernels before D6, the
configuration at raw step 41 is D at -1 and its head-inclusive
leftward six-bit word is `001001`, not the `010010` required by D6.
Thus the earlier `D10^3;D6` factorization does not compose from that
particular raw state, even though the complete return clock remains
consistent with the sampled seven-row table.

Additional raw-trace entry checks:

| j | h | D6 phase begins at step | Final D10 begins at step | K22/J1K entry step |
|---:|---:|---:|---:|---:|
| 0 | 0 | no D6 | 11 | K22 at 15 |
| 1 | 0 | no D6 | 24 | J1K at 28 |
| 2 | 1 | 37 | 51 | K22 at 55 |
| 3 | 1 | 50 | 64 | J1K at 68 |
| 4 | 2 | 63 | 91 | K22 at 95 |
| 5 | 2 | 76 | 104 | J1K at 108 |

The underlying checks used the raw six-state transition table
`1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---` with explicit
sparse tape, control-state and head updates. This is a bounded
same-author trace audit, not an independent proof, and the correctness
of the mathematical source/endpoint theorem is adjudicated separately
by the Lean build.

## Formal obligations

`link/CryptidLink/L17z.lean` carries:

1. `a101_11_d10_twice_exact`: exact `13*j+11` prefix through two D10
   kernels for every j, including the framed residual word.
2. `a101_11_even_dmode_exact`: `40*h+15` steps to the K22-entry
   D head (with arbitrary exterior L,R).
3. `a101_11_odd_dmode_exact`: `40*h+28` steps to the J1K-entry
   residual D head (with arbitrary exterior L,R).

**Limit:** These do not yet prove a blank-left C section return or any
claim concerning halting/non-halting. After they compile, compose
them with K22 or J1K and the remaining C01/D10 bottom layers.
