import CryptidLink.L17p
/-!
# L17: phase transport from homogeneous 101 terminals into C6 return sweeps

Two consecutive scanner-created 001 blocks become a 010010 block when
transported into the left-moving C head frame. The word equalities
below track this rotation exactly and *do not* identify distinct tape
configurations merely because they have the same block count.

The two composed return-phase lemmas are machine-level statements for
every h, with arbitrary external tapes. They end in a framed C exit,
not necessarily a blank-left C-section. They do not claim that these
source tapes occur on the blank orbit.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Phase-correct word identity for an even count of inserted 001 blocks.
    This is literal tape equality, not a new machine transition. -/
theorem c6_phase_even (h : ℕ) (L : ListBlank (Fin 2)) :
    ListBlank.append [0, 1]
      (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ (2 * h))
        (ListBlank.append [0] L)) =
    ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [0, 1, 0] L) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [show 2 * (h + 1) = 2 + 2 * h by omega,
      ListBlank.append_pow_add ([0, 0, 1] : List (Fin 2)) 2 (2 * h)
        (ListBlank.append [0] L),
      ListBlank.append_pow_succ ([0, 1, 0, 0, 1, 0] : List (Fin 2)) h
        (ListBlank.append [0, 1, 0] L)]
    exact congrArg (ListBlank.append ([0, 1, 0, 0, 1, 0] : List (Fin 2))) ih

/-- An odd count of inserted blocks exactly fills h+1 C6 input blocks. -/
theorem c6_phase_odd (h : ℕ) (L : ListBlank (Fin 2)) :
    ListBlank.append [0, 1]
      (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
        (ListBlank.append [0] L)) =
    ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ (h + 1)) L := by
  rw [← ListBlank.append_pow_succ' ([0, 0, 1] : List (Fin 2)) (2 * h)
      (ListBlank.append [0] L),
    ← ListBlank.append_pow_succ' ([0, 1, 0, 0, 1, 0] : List (Fin 2)) h L]
  exact c6_phase_even h (ListBlank.append [0, 1, 0] L)

/-- The even-positive 00 terminal subfamily reaches the bottom of its
    periodic C6 return phase in exactly 13*(2h+2)+10+6*(h+1) steps.
    The external left tape L may be nonblank. -/
theorem a101_00_even_c6_exact (h : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (13 * (2 * h + 2) + 10 + 6 * (h + 1))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 2))
          (ListBlank.append [0, 0] R)))
      (Cfg.headLeft C L
        (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ (h + 1))
          (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R))) := by
  have h1 := a101_00_positive_terminal_exact (2 * h + 1) L R
  rw [c6_phase_odd h L] at h1
  have h2 := c6_sweep_exact (h + 1) L (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)
  convert h1.trans h2 using 1 <;> omega

/-- The odd-100 terminal subfamily reaches the bottom of its periodic C6
    return phase with the same left head frame, but a seven-one suffix.
    The clock and suffix differ from the even-positive 00 family. -/
theorem a101_100_odd_c6_exact (h : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (13 * (2 * h + 1) + 19 + 6 * (h + 1))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
          (ListBlank.append [1, 0, 0] R)))
      (Cfg.headLeft C L
        (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ (h + 1))
          (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R))) := by
  have h1 := a101_100_terminal_exact (2 * h + 1) L R
  rw [c6_phase_odd h L] at h1
  have h2 := c6_sweep_exact (h + 1) L (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R)
  exact h1.trans h2

end CryptidLink.L17

#print axioms CryptidLink.L17.c6_phase_even
#print axioms CryptidLink.L17.c6_phase_odd
#print axioms CryptidLink.L17.a101_00_even_c6_exact
#print axioms CryptidLink.L17.a101_100_odd_c6_exact
