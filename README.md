# cryptid-verifier

Lean 4 (core, no Mathlib) companion to *At the Limits of Computability: Steps Towards
Autonomous AI Discovery on the Busy Beaver Frontier* (Dos Santos et al., arXiv:2610.22603).
The macro-rules are transcribed by hand from the paper (Sec. 2.2 for Antihydra, Appendix A.4);
they are **not yet linked** to the authors' Turing-machine-level Lean proofs.

Build: `lake build` (Lean `v4.24.0`, core only). The Mathlib part lives in `mathlib/` (`cd mathlib && lake exe cache get && lake build`). CI runs the build plus `scripts/audit_trust.py`, which fails on any
`sorry`/`admit`/`native_decide`/`axiom` in the sources and on any non-standard axiom in the `#print axioms` output. Zero `sorry`; `#print axioms` shows only
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

### Antihydra as one real number (`mathlib/CryptidReal/Antihydra.lean`, Mathlib, checked in CI)
| Theorem | Plain meaning |
|---|---|
| `exists_even_after`, `exists_odd_after` (core) | within b + 4 steps every orbit shows both an even and an odd value (it never sits on −3 or −4) |
| `S_bounds` (core) | 3(3ⁿ − 2ⁿ) ≤ Sₙ ≤ 4(3ⁿ − 2ⁿ) |
| `antihydra_floor` | **bₙ = ⌊ξ·(3/2)ⁿ⌋ − 3 for every n**, with ξ = 4 + Σₖ qₖ(2/3)ᵏ/3, qₖ = 4 − (bₖ mod 2) (ξ ≈ 7.86417726205661897…) |
| `antihydra_parity` | Antihydra's parities are those of ⌊ξ·(3/2)ⁿ⌋ − 3: its halting question is a question about the integer parts of ξ·(3/2)ⁿ (Mahler 3/2 setting) |
| `ξ_floor` | ⌊ξ⌋ = 7 |

### A.4 (`AntihydraOuroboros/A4.lean`)
| Theorem | Plain meaning |
|---|---|
| `con_even_out`, `con_odd_out` | contraction steps only produce b ∈ {1, 3}, never the halting value 2 |
| `expand_closed` | closed form of the expansion cascade from C(2, B) |
| `cascade_hits_two` | the cascade from C(m,1) hits b = 2 after s steps ⟺ m + s + 4 = 2^(s+2), i.e. m ∈ {0, 3, 10, 25, 56, 119, 246, …} |
| `a4_halts_iff` | **A.4 halts from C(0,3) ⟺ it visits some C(m,1) with m + s + 4 = 2^(s+2)** (full rule system; invariant `J` also shows b = 0 is never reached) |

### A.9 (`AntihydraOuroboros/A9.lean`)
| Theorem | Plain meaning |
|---|---|
| `step9_enc` | the merged rules on C(a,b,c) are exactly the paper's two-family (C₀, C₁) rules, read through C₀(a,b,c) = C(2a,b,c), C₁(a,b,c) = C(2a+1,b,c) |
| `drain`, `sweep_le`, `sweep_gt` | the unary sweep compresses: C(a,b,c) ↠ C(a+6b, 0, c−b) if b ≤ c, and ↠ C(a+6c+3, 0, b−c−1) if b > c |
| `section_branch1` | on the section S(a,c) = C(a,0,c), with a = 2k+p: if c ≥ k+5 then S(2k+p, c) ↠ S(6k+20+3p, c−k−5) |
| `section_branch2` | if 2 ≤ c < k+5 then S(2k+p, c) ↠ S(6c−7+3p, k+4−c) |
| `a9_mod3` | along the orbit from C(5,2,0), a ≡ 2 (mod 3) always (true, but it cannot block halting) |
| `step9_halt_iff` | the only halting configurations are C(a,0,0) |
| `a9_halts_iff` | **A.9 halts from C(5,2,0) ⟺ it reaches some C(a,b,c) with b ≥ 1 and b − c ∈ {0, 1}**: a draining race that ends exactly in a tie |

## What is NOT proved
- That Antihydra, A.4 or A.9 never halts (all open; each is now reduced to an explicit arithmetic condition).

## Scripts (`scripts/`, evidence only)
Numerical experiments: connection-Laplacian frustration, 2-adic survival densities, stream monitor,
A.4 orbit (3M rule steps: 2789 visits to C(m,1), none in the halting set; no modular obstruction for moduli < 400).

## Corrections log
- A.4 halting set: an external suggestion gave m ∈ {2, 7, 19, 41, 88, …} (m = 3(2^s − 1) − s). That is wrong;
  the correct set, proved here and confirmed by brute force, is m = 2^(s+2) − 4 − s ∈ {0, 3, 10, 25, 56, …}.
- A.9 branch 2: the formula k − c + 4 must be read as k + 4 − c in ℕ (truncated subtraction makes them differ).
