# Invariant search (lambda-sat), fuzzing and merging — all 12 machines

## 1. Invariant search, certified with lambda-sat (`scripts/engine.py`)

**Domain.** Each coordinate is exact if < K, otherwise its residue mod M; each pair of large coordinates also
carries its difference, exact in [−D, D] and clipped beyond. Abstract edges are read off every concrete state in
a box ([0,120]², [0,40]³, [0,18]⁴).

**Encoding.** An invariant is a set I of abstract states with: the start in I; I closed under the edges; no
halting-capable state in I; no unsampled state in I. These are unit and binary clauses (Horn 2-CNF). lambda-sat's
coupled frame (`frame_solve_coupled`: unit propagation + 2-SAT + parity) decides them soundly.

**Result.** All 60 instances (12 machines × (K,M,D) ∈ {(4,2,2), (6,4,4), (6,6,6), (8,12,8), (8,24,12)}) are
**UNSAT, refuted by lambda-sat**: no invariant of this kind exists for any of the 12 machines. With lambda-sat at
`dd391db` the default router (`frame_solve_scouted`) refutes all 60 directly in its 2-SAT frame. The negative result
is sound even though the box sampling is not complete: sampling can only *miss* edges, and halting is already
reachable with the sampled ones.

**Scope (correction).** This rules out invariants built from small values, residues and clipped pairwise
differences, and the Lean no-go theorems rule out affine counter–time laws. Neither excludes general
**semilinear** invariants: linear inequalities mixing coordinates (b included), disjunctions over phases, or
congruences on combinations. That search is still open, for Antihydra too. An earlier remark of mine that it was
"provably impossible" for Antihydra was too strong. (Point raised in the GPT-6.1 audit.)

**Feedback for lambda-sat** (found while wiring it in; **fixed upstream in `dd391db`**, PR #34 — unit/empty
clauses folded into the 2-SAT check and the scout gate made exact):
- `frame_solve_scouted` returns `CDCL_NEEDED` on trivially refutable Horn chains (unit, x₁→x₂→…→xₙ, ¬xₙ, any n),
  which `frame_solve_coupled` refutes. The scout appears to prune the frame that owns the instance.
- `check_binary_clauses` ignores unit clauses, so it reports such formulas as "consistent". This is sound as a
  partial check but misses free refutations.

## 2. Fuzzing the start (`scripts/fuzz.py`, `scripts/merge.py`)

From 20 states on each orbit, each coordinate was perturbed by δ ∈ [−12, 12] \ {0} and the perturbed state run
for up to 40 000 steps.

| Machine | Perturbed starts | Halt | Merge back into the real orbit | Halting configurations hit |
|---|---|---|---|---|
| A.1 | 1 672 | 3 | 81 | (0,69,0,71), (0,250,0,252) |
| A.2 | 1 406 | 3 | 270 | (0,360,0), (0,544,0), (0,780,0) |
| A.3 | 821 | 0 | 0 | — |
| A.4 | 951 | 1 | 20 | one C(·,2) |
| A.5 | 1 422 | 1 | 2 | (0,1272,0) |
| **A.6** | 1 429 | **49** | 64 | **(1,888,1) × 48**, (1,656,1) |
| A.7 | 1 440 | 1 | 0 | (128986,1,1) |
| A.9 | 1 440 | 0 | 0 | — |
| A.10 | 1 428 | 1 | 341 | (129,0,3) |
| A.11 | 1 728 | 10 | 14 | (0,2265,0,3), (0,2271,0,3), … |

Antihydra and A.8 are absent: their counters pass 600 bits before the sampling window.

**Reading.**
- The slow machines (A.1, A.2, A.6, A.10) *contract*: many nearby starts merge exactly into the real orbit.
- **A.6 has a halting trunk.** 48 of its 49 halting perturbations, started from different orbit states and
  coordinates, end in the **same** configuration (1, 888, 1). Nearby states therefore flow into one tree that ends
  in a single halt, and the real orbit avoids that tree. So A.6's halting question is "does the real trunk ever
  join the trunk of (1,888,1)?" That is a concrete, finite object to study: the backward tree of (1,888,1).
- The fast machines (A.3, A.9) neither merge nor halt under perturbation, as expected for expanding dynamics.

## 3. Conjugacy (partial)

A.2 and A.5 differ in two transitions and have parallel rule systems, but their orbits are not related by a
simple coordinate shift, and they merge very differently (270 against 2). There is no conjugacy evidence yet;
a full normal-form classification was not done.

## What this changes

- **Simple invariants are ruled out.** Residue, difference and small-value invariants don't exist for any of the
  12, now with lambda-sat certificates, so any proof must use non-local structure.
- **A.6 is the new priority.** Its contraction plus a dominant halting trunk is structure that expanding machines
  lack. The next step is to describe the backward tree of (1,888,1) and the real trunk in the outer-seed
  coordinates; the outer seeds advance in runs of constant increments of +28 and +72.
