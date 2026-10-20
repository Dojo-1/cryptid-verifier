# cryptid-verifier

Lean 4 (core, no Mathlib) companion to *At the Limits of Computability: Steps Towards
Autonomous AI Discovery on the Busy Beaver Frontier* (Dos Santos et al., arXiv:2610.22603).
The macro-rules are transcribed by hand from the paper (Sec. 2.2 for Antihydra, Appendix A.4);
they are **not yet linked** to the authors' Turing-machine-level Lean proofs.

Build: `lake build` (Lean `v4.24.0`). Zero `sorry`; `#print axioms` shows only
`propext`, `Quot.sound`, `Classical.choice`.

## What is proved

### Antihydra (`AntihydraOuroboros/Basic.lean`)
| Theorem | Plain meaning |
|---|---|
| `run_eq` | n macro-steps = the b-tape evolving on its own under T, plus a +2/−1 walk on its parities; halt ⟺ walk goes below 0 |
| `pv_mod`, `pv_inj`, `pv_surj` | the next k parities ⟷ b mod 2^k, one-to-one and onto (every parity pattern occurs) |
| `antihydra_survives_iff` | the halting question from A(0,4) as a walk question |
| `halts_neg3`, `survives_neg4`, `halts_of_near_neg3` | 2-adically near −3 ⇒ quick halt; near −4 ⇒ survival |
| `antihydra_halt_time_mod3`, `walk_count` | a + t = a₀ + 3·(#even steps); halting only after a multiple of 3 macro-steps |
| `no_dyadic_invariant`, `no_invariant_mod9`, `no_invariant_prime_pow`, `no_integer_invariant` | no conserved quantity a + c·t modulo 2^k, 4^k, 8^k, 9, p^k (p ≠ 3), or over ℤ |
| `pv_past3` | b mod 3^j records the last j parities (3-adic memory) |
| `real_bridge` | 2ⁿ·bₙ = 3ⁿ·b₀ + Sₙ: the link to ⌊ξ(3/2)ⁿ⌋ (Mahler 3/2 setting) |

### A.4 (`AntihydraOuroboros/A4.lean`)
| Theorem | Plain meaning |
|---|---|
| `con_even_out`, `con_odd_out` | contraction steps only produce b ∈ {1, 3}, never the halting value 2 |
| `expand_closed` | closed form of the expansion cascade from C(2, B) |
| `cascade_hits_two` | the cascade from C(m,1) hits b = 2 after s steps ⟺ m + s + 4 = 2^(s+2), i.e. m ∈ {0, 3, 10, 25, 56, 119, 246, …} |
| `a4_halts_iff` | **A.4 halts from C(0,3) ⟺ it visits some C(m,1) with m + s + 4 = 2^(s+2)** (full rule system; invariant `J` also shows b = 0 is never reached) |

## What is NOT proved
- That Antihydra or A.4 never halts (both open).
- The real-number (Mathlib) form of the Mahler reduction.

## Scripts (`scripts/`, evidence only)
Numerical experiments: connection-Laplacian frustration, 2-adic survival densities, stream monitor,
A.4 orbit (3M rule steps: 2789 visits to C(m,1), none in the halting set; no modular obstruction for moduli < 400).
