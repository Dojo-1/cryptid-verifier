import CryptidLink.L17v
/-!
# L17: phase-correct Cpop after homogeneous scanner returns

The positive-odd 00 and even 100 terminal families share a C-phase
obstruction that does not occur in the even-positive 00 / odd 100 rows:
an explicit zero-separator causes Cpop (four defined steps) before
the C01 sweep. The tape orientation matters. In head-nearest-first
notation, a left-directed C head with left [0,1,0,0] L is exactly the
right-directed C head on local [-3,0]: 0010 needed by cpop_exact.

This file proves the four-step framed conversion and the corresponding
all-h homogeneous scanner + C6 + Cpop compositions, with exact clocks.
Neither composite has a blank-left C endpoint: its residual L is
arbitrary, and the remaining C01 and K41 bottom operations are not
included. All inputs are arbitrary framed machine configurations,
not claimed to occur on the designated blank-tape orbit.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Local Cpop from the headLeft representation: local left word
    0,1,0,0 is consumed, the output written to the right is 1,0,1,0,
    and the C head moves four cells to the left, in four defined steps. -/
theorem cpop_headLeft_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 4
      (Cfg.headLeft C (ListBlank.append [0, 1, 0, 0] L) R)
      (Cfg.headLeft C L (ListBlank.append [1, 0, 1, 0] R)) := by
  have he :
      Cfg.headLeft C (ListBlank.append [0, 1, 0, 0] L) R =
      Cfg.headRight C (ListBlank.append [1, 0, 0] L)
        (ListBlank.append [0] R) :=
    Cfg.headLeft_cons C (0 : Fin 2)
      (ListBlank.append [1, 0, 0] L) R
  rw [he]
  exact cpop_exact L R

/-- Positive-odd 00 terminal after h periodic C6 blocks and one Cpop:
    exact 32h+27-step defined execution, with complete residual left
    context L and right output 1010 (111010)^h 1^9 R. The additional
    zero on the source left is the Cpop guard; it is not optional. -/
theorem a101_00_odd_cpop_exact (h : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (32 * h + 27)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0] (ListBlank.append [0] L)))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
          (ListBlank.append [0, 0] R)))
      (Cfg.headLeft C L
        (ListBlank.append [1, 0, 1, 0]
          (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
            (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)))) := by
  let Nine := ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R
  let Rest : ListBlank (Fin 2) :=
    ListBlank.append [0, 1, 0] (ListBlank.append [0] L)
  have h1 := a101_00_positive_terminal_exact (2 * h)
    (ListBlank.append [0] L) R
  rw [c6_phase_even h (ListBlank.append [0] L)] at h1
  have h2 := c6_sweep_exact h Rest Nine
  have h3 := cpop_headLeft_exact L
    (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h) Nine)
  convert (h1.trans h2).trans h3 using 1 <;> omega

/-- Even 100 terminal after h periodic C6 blocks and one Cpop:
    exact 32h+23-step defined execution, with complete residual left
    context L and right output 1010 (111010)^h 1^7 R. -/
theorem a101_100_even_cpop_exact (h : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (32 * h + 23)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0] (ListBlank.append [0] L)))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h))
          (ListBlank.append [1, 0, 0] R)))
      (Cfg.headLeft C L
        (ListBlank.append [1, 0, 1, 0]
          (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
            (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R)))) := by
  let Seven := ListBlank.append [1, 1, 1, 1, 1, 1, 1] R
  let Rest : ListBlank (Fin 2) :=
    ListBlank.append [0, 1, 0] (ListBlank.append [0] L)
  have h1 := a101_100_terminal_exact (2 * h)
    (ListBlank.append [0] L) R
  rw [c6_phase_even h (ListBlank.append [0] L)] at h1
  have h2 := c6_sweep_exact h Rest Seven
  have h3 := cpop_headLeft_exact L
    (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h) Seven)
  convert (h1.trans h2).trans h3 using 1 <;> omega

end CryptidLink.L17

#print axioms CryptidLink.L17.cpop_headLeft_exact
#print axioms CryptidLink.L17.a101_00_odd_cpop_exact
#print axioms CryptidLink.L17.a101_100_even_cpop_exact
