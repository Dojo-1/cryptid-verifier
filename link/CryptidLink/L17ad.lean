import CryptidLink.L17ac
/-!
# L17: local transport kernels behind the mixed width-two return

The formerly isolated 166-step mixed [6,7,2,2,3] witness can be
decomposed into smaller contextual machine paths. These preserve the
full tape and directional head frame, not merely the control state:

* 112 steps: from A with last run (10)^3 and right prefix
  01·101·01·101·00 to D scanning the first cell left of that run;
* 6 steps: a local D-to-C conversion at a zero separator;
* 16 steps: a C-mode conversion of the first four outer pairs,
  moving the head 8 cells left and writing four 10 pairs.

All exterior tapes L and R are arbitrary. None of these lemmas alone
proves the parametric width-two return. The next step is to compose
the 112-step prelude, D10^c, the 6-step bridge, the 16-step outer
kernel, and C01^(p-4) under the explicit guard p>=4.

For the pinned raw L17 transition relation, no symbolic context is
read outside the displayed windows. This is a raw machine theorem,
not a claim of blank-tape reachability, termination or non-halting.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- The fixed mixed scanner+inner return, exact 112 defined steps.
    With the initial A head at position 0, the D head exits at -8.
    Its 19-bit right word is (10)^8 111, entirely explicit. -/
theorem mixed112_prelude_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 112
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0] L)
        (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0] R))
      (Cfg.headLeft D L
        (ListBlank.append
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] R)) := by
  set_option maxRecDepth 16384 in
    l17_exact_steps

/-- Six steps on the zero separator, with one zero immediately to
    its left and right prefix 10, change D to C at the *same head*
    coordinate. The former left zero becomes one. -/
theorem mixed6_D_to_C_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 6
      (Cfg.headLeft D (ListBlank.append [0, 0] L)
        (ListBlank.append [1, 0] R))
      (Cfg.headLeft C (ListBlank.append [0, 1] L)
        (ListBlank.append [1, 0] R)) := by
  l17_exact_steps

/-- Sixteen defined steps consume a local C boundary plus the first
    four outer 10 pairs; the C head moves left by exactly eight cells.
    The untouched left L will contain additional 10 pairs in the
    parameterized outer-run induction. -/
theorem mixed16_C_outer_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 16
      (Cfg.headLeft C
        (ListBlank.append [0, 1, 1, 0, 1, 0, 1, 0, 1] L)
        R)
      (Cfg.headLeft C (ListBlank.append [1] L)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

end CryptidLink.L17

#print axioms CryptidLink.L17.mixed112_prelude_exact
#print axioms CryptidLink.L17.mixed6_D_to_C_exact
#print axioms CryptidLink.L17.mixed16_C_outer_exact
