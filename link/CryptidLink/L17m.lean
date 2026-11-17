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

/-! ## Guarded parametric scanner moves

These are not tests at a finite list of widths. The power parameter is
arbitrary; the exact conclusion follows from the local machine kernel
and a framed tape-word identity.
-/

/-- For every n, token 01 extends the last 10 run by one pair in exactly 2 steps. -/
theorem a01_run_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target 2
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) L)
        (ListBlank.append [0, 1] R))
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 1)) L)
        R) := by
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) n L]
  exact a01_exact _ _

/-- For every n, token 101 splits a final run of width n+2 into widths n and 3,
    inserting a genuine zero gap, in exactly 13 steps. The left context is arbitrary. -/
theorem a101_split_run_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target 13
      (Cfg.headRight A
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 2)) L)
        (ListBlank.append [1, 0, 1] R))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) L))
        R) := by
  rw [show n + 2 = 2 + n by omega,
    ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 n L]
  exact a101_exact _ _

/-- The formerly typed B1101 exit actually returns to C if followed by 00.
    This is the exact *local* 24-step B-to-C transfer, not yet a global C-section
    return. The zero immediately left of the exit C remains explicit in L. -/
theorem b110100_local_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 24
      (Cfg.headRight B (ListBlank.append [1, 0, 1, 0] L)
        (ListBlank.append [1, 1, 0, 1, 0, 0] R))
      (Cfg.headLeft C (ListBlank.append [0] L)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  have h1 := short_B1101_exact L (ListBlank.append [0, 0] R)
  have h2 := a00l_exact (ListBlank.append [0] L) R
  exact h1.trans h2

end CryptidLink.L17

#print axioms CryptidLink.L17.a01_exact
#print axioms CryptidLink.L17.a101_exact
#print axioms CryptidLink.L17.a00l_exact
#print axioms CryptidLink.L17.a100_exact
#print axioms CryptidLink.L17.cpop_exact
#print axioms CryptidLink.L17.c6_exact
#print axioms CryptidLink.L17.d6_exact
#print axioms CryptidLink.L17.a01_run_exact
#print axioms CryptidLink.L17.a101_split_run_exact
#print axioms CryptidLink.L17.b110100_local_exact
