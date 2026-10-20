# cryptid-verifier

Lean 4 (core, no Mathlib) companion to *At the Limits of Computability: Steps Towards
Autonomous AI Discovery on the Busy Beaver Frontier* (Dos Santos et al., arXiv:2610.22603).
The macro-rules are transcribed from the paper (Sec. 2.2 for Antihydra, Appendices A.4 and A.9) and checked
against the raw Turing machines for their first macro steps (`TMLink.lean`); they are not linked to the
authors' own Lean proofs, whose repository the paper does not name.

Build: `lake build` (Lean `v4.24.0`, core only). The Mathlib part lives in `mathlib/` (`cd mathlib && lake exe cache get && lake build`). CI runs the build plus `scripts/audit_trust.py`, which fails on any
`sorry`/`admit`/`native_decide`/`axiom` in the sources and on any non-standard axiom in the `#print axioms` output. Zero `sorry`; `#print axioms` shows only
`propext`, `Quot.sound`, `Classical.choice` (the `TMLink` checks use no axioms at all).

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

### Link to the raw Turing machines (`AntihydraOuroboros/TMLink.lean`)
Each machine is given by its standard bbchallenge string, parsed in Lean and run from the blank tape.
Every raw configuration with exactly the shape of a macro configuration is decoded, and the kernel checks
(`decide +kernel`, no `native_decide`) that the decoded sequence equals the macro run of our step functions:

| Theorem | Plain meaning |
|---|---|
| `antihydra_link` | `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`: the first 8 macro configurations (raw steps 11 … 10 933) are exactly `step`'s run from A(0,4) |
| `a4_link` | `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`: the first 25 (raw steps 7 … 8 936) are exactly `step4`'s run from C(0,3) (the tape also shows C(0,2a+4) between C(a,1) and C(2,2a+2); `step4_through_zero` checks that this is the expansion rule) |
| `a9_link` | `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`: the first 40 (raw steps 100 … 9 738) are exactly `step9`'s run from C(5,2,0) |

This is a bounded check (the authors' Lean proofs establish the rules for all parameters; their repository
is not linked from the paper). A Python version (`analysis/scripts/smoke.py`, run in CI) extends it to 300 000
raw steps: 12 / 44 / 275 macro configurations, all in agreement.

### Antihydra as one real number (`mathlib/CryptidReal/Antihydra.lean`, Mathlib, checked in CI)
| Theorem | Plain meaning |
|---|---|
| `exists_even_after`, `exists_odd_after` (core, `AntihydraOuroboros/Escape.lean`) | within b + 4 steps every orbit shows both an even and an odd value (it never sits on −3 or −4) |
| `S_bounds` (core, `Escape.lean`) | 3(3ⁿ − 2ⁿ) ≤ Sₙ ≤ 4(3ⁿ − 2ⁿ) |
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
- That the macro rules hold for **all** parameters at the Turing-machine level: `TMLink` checks the first 8 / 25 / 40
  macro steps against the raw machines; the general statement is the authors' result, not re-proved here.

## Scripts (`analysis/scripts/`, evidence only; `smoke.py` runs in CI)
Numerical experiments: connection-Laplacian frustration, 2-adic survival densities, stream monitor,
A.4 orbit (3M rule steps: 2789 visits to C(m,1), none in the halting set; no modular obstruction for moduli < 400).

## Corrections log
- A.4 halting set: an external suggestion gave m ∈ {2, 7, 19, 41, 88, …} (m = 3(2^s − 1) − s). That is wrong;
  the correct set, proved here and confirmed by brute force, is m = 2^(s+2) − 4 − s ∈ {0, 3, 10, 25, 56, …}.
- A.9 branch 2: the formula k − c + 4 must be read as k + 4 − c in ℕ (truncated subtraction makes them differ).
