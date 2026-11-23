# E84 — integrated exact-return safety, conditional first-return criterion

Snapshot: `main` at `d3fdf22761a1496335944ed44dfbc79b8ae0af20` (E79).

## Scope and status

This integration carries the independently CI-green PR branches #74 (E80),
#75 (E81), #76 (E82), and #77 (E83), preserving their exact contents and
their separate research notes. The only new theorem is E84's **conditional**
logical criterion: exact endpoint + preterminal safety imply a first
blank-left-C visit at that clock. It does **not** prove the premise for G1/G3.

At integration creation, the combined build is **H until its own six CI
jobs and trust audit pass**. Previous individual six-job CI successes
do not establish that the combined import graph and inventory succeed.

## Formal dependencies

- **E80**: safety on `[0,m)` and `[0,n)` composes along an exact
  intermediate configuration; a C-free phase implies blank-left-C safety.
- **E81**: the G1 fixed bridge is safe for all `t<77` with arbitrary
  exteriors. Its C visit at `t=71` needs the E78 *second-left-cell* witness.
- **E82**: the G3 fixed bridge is safe for all `t<95` with arbitrary
  exteriors. The endpoint is **not** safe with arbitrary left exterior:
  E78 gives an explicit blank-exterior counterexample. E79 separately
  establishes that the *structured E60* endpoint is nonblank-left.
- **E83**: the parameterized `4p` G1 final A-sweep is C-free by reuse
  of E73. Its fixed 25-step finish and remaining `2(u+2)` C sweep
  are not covered.
- **E84**: a separate, small first-return criterion with no new machine
  transitions, recurrence axioms or guessed witness schedule.

## Open obligations — do not promote to first-return or nonhalting

1. Entire positive-width G1/G3 fixed preludes beyond the first 26
   certified steps, including every relevant C left-tape witness.
2. Exact alignment of the certified variable scanner/middle phase,
   fixed bridges, structured G3 boundary and terminal A/C unwinds
   with the complete E60 full-tape configurations and arithmetic clocks.
3. G1 25-step final A finish and `2(u+2)` C sweep; G3 final C-mode finish.
4. Composition over all `M=m+1`, `u,v`, arbitrary `R`, including
   **strictly earlier** timestamps in the eventual first-return theorem.
5. Mixed scanner grammar, blank-orbit reachability and global L17
   nonhalting remain separate open questions.

## Adversarial controls

- Boundary attack: do not replace `t<95` with `t<=95`.
- Representation attack: compare definitionally equal `11 ++ (1::R)`
  with `111 ++ R` in E83; no new transition is assumed.
- Proof-vs-runtime: a pinned Lean kernel/trust check certifies theorem
  declarations, not that a later global statement has been proved.
- Negative control: the discarded `M=0` affine extension remains retired.

## Promotion gate

Promote E80–E84 to **P for exactly their statements** only after all six
integration checks, the standard-axiom trust inventory, and manual statement
review. Do not upgrade the first-return theorem until the missing final-phase
and full-source alignment obligations are discharged.
