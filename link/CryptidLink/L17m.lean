import CryptidLink.L17l
/-!
# L17: finite A-scanner and C/D return primitives

These are exactly timed, arbitrarily framed raw-machine paths. All outside
tape on both sides is a symbolic \`ListBlank\`. They promote the six literal
kernels recorded in \`analysis/l17-a-stream/kernels.json\` to machine-checked
statements. The accompanying parameterized return tables are *not* proved
by these finite lemmas alone.

All spatial words in this file use Lean's head-nearest-first left tape.
The equivalent spatial left-to-right input/output windows are documented
in the original kernel JSON and in \`analysis/l17-a-stream/DERIVATION.md\`.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- 01 scanner token: A0; B1. Reads x=0,1, exits A at x=2. -/
theorem a01_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 2
      (Cfg.headRight A L (ListBlank.append [0, 1] R))
      (Cfg.headRight A (ListBlank.append [0, 1] L) R) := by
  l17_exact_steps

/-- 101 scanner token on local [-4,2]: 1010101 -> 0101010.
    Thirteen defined steps, exits A at x=3. -/
theorem a101_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 13
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1] L)
        (ListBlank.append [1, 0, 1] R))
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0] L) R) := by
  l17_exact_steps

/-- Terminal 00 after a last run of three 10 pairs, on [-7,1].
    Ten defined steps, exits C at x=-8. -/
theorem a00l_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 10
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1, 0, 1, 0] L)
        (ListBlank.append [0, 0] R))
      (Cfg.headLeft C L (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  l17_exact_steps

/-- Terminal 100 on [-4,2]: 1010100 -> 1111111.
    Nineteen defined steps, exits C at x=-5. -/
theorem a100_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 19
      (Cfg.headRight A (ListBlank.append [0, 1, 0, 1] L)
        (ListBlank.append [1, 0, 0] R))
      (Cfg.headLeft C L (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R)) := by
  l17_exact_steps

/-- Cpop on [-3,0]: 0010 -> 1010.
    Four defined steps, exits C at x=-4. -/
theorem cpop_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 4
      (Cfg.headRight C (ListBlank.append [1, 0, 0] L)
        (ListBlank.append [0] R))
      (Cfg.headLeft C L (ListBlank.append [1, 0, 1, 0] R)) := by
  l17_exact_steps

/-- C6 on [-5,0]: 010010 -> 111010.
    Six defined steps, exits C at x=-6. -/
theorem c6_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 6
      (Cfg.headRight C (ListBlank.append [1, 0, 0, 1, 0] L)
        (ListBlank.append [0] R))
      (Cfg.headLeft C L (ListBlank.append [1, 1, 1, 0, 1, 0] R)) := by
  l17_exact_steps

/-- D6 on [-5,0]: 010010 -> 101010.
    Fourteen defined steps, exits D at x=-6. -/
theorem d6_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 14
      (Cfg.headRight D (ListBlank.append [1, 0, 0, 1, 0] L)
        (ListBlank.append [0] R))
      (Cfg.headLeft D L (ListBlank.append [1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

end CryptidLink.L17

#print axioms CryptidLink.L17.a01_exact
#print axioms CryptidLink.L17.a101_exact
#print axioms CryptidLink.L17.a00l_exact
#print axioms CryptidLink.L17.a100_exact
#print axioms CryptidLink.L17.cpop_exact
#print axioms CryptidLink.L17.c6_exact
#print axioms CryptidLink.L17.d6_exact
