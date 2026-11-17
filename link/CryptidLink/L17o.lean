import CryptidLink.L17n
/-!
# L17: exact terminal exits after arbitrarily many homogeneous 101 scans

Local endpoint dispatcher for the three terminal prefixes 00, 100 and 11
following (101)^j. Each theorem below records the complete framed machine
configuration and its exact defined-transition count, with *arbitrary*
unread exterior tapes L and R. Left tape lists are head-nearest-first.

The base 00 case is already \`a00l_exact\` (ten transitions); the positive
case is separate because one leading 001 block is consumed at the last
C exit, leaving a nontrivial left residual. The C and D endpoints below
are local machine exits. None is a claim of return to a blank-left C section,
blank-tape reachability, or halting/non-halting.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Terminal 11 after a leading left zero: three raw defined steps,
    exit D at x=-1. The left tape past that cell is unchanged. -/
theorem a11_terminal_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 3
      (Cfg.headRight A
        (ListBlank.append [0] L)
        (ListBlank.append [1, 1] R))
      (Cfg.headRight D L
        (ListBlank.append [0, 1, 0] R)) := by
  l17_exact_steps

/-- All j: (101)^j 100 gives a local C exit in 13*j+19
    defined transitions, preserving the complete left residual. -/
theorem a101_100_terminal_exact (j : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (13 * j + 19)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ j)
          (ListBlank.append [1, 0, 0] R)))
      (Cfg.headLeft C
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [0] L)))
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R)) := by
  have h1 := a101_repeat_exact j L (ListBlank.append [1, 0, 0] R)
  have h2 := a100_exact
    (ListBlank.append [0, 1]
      (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
        (ListBlank.append [0] L))) R
  exact h1.trans h2

/-- All j: (101)^j 11 gives a local D exit in 13*j+3
    defined transitions. Unlike the C rows, the head is at -1
    from the terminal's initial head and still has a left residual. -/
theorem a101_11_terminal_exact (j : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (13 * j + 3)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ j)
          (ListBlank.append [1, 1] R)))
      (Cfg.headRight D
        (ListBlank.append [1, 0, 1, 0, 1]
          (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [0] L)))
        (ListBlank.append [0, 1, 0] R)) := by
  have h1 := a101_repeat_exact j L (ListBlank.append [1, 1] R)
  have h2 := a11_terminal_exact
    (ListBlank.append [1, 0, 1, 0, 1]
      (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
        (ListBlank.append [0] L))) R
  exact h1.trans h2

/-- Positive repetition counts: (101)^(j+1) 00 gives a local C exit
    in 13*(j+1)+10 defined transitions. The leading 001 block
    contributes an untouched 01 at the left of the C head.

    For zero repetitions use the already-proved a00l_exact. -/
theorem a101_00_positive_terminal_exact (j : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (13 * (j + 1) + 10)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (j + 1))
          (ListBlank.append [0, 0] R)))
      (Cfg.headLeft C
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [0] L)))
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)) := by
  have h1 := a101_repeat_exact (j + 1) L (ListBlank.append [0, 0] R)
  have h2 := a00l_exact
    (ListBlank.append [0, 1]
      (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
        (ListBlank.append [0] L))) R
  rw [ListBlank.append_pow_succ ([0, 0, 1] : List (Fin 2)) j
    (ListBlank.append [0] L)] at h1
  exact h1.trans h2

end CryptidLink.L17

#print axioms CryptidLink.L17.a11_terminal_exact
#print axioms CryptidLink.L17.a101_100_terminal_exact
#print axioms CryptidLink.L17.a101_11_terminal_exact
#print axioms CryptidLink.L17.a101_00_positive_terminal_exact
