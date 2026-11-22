import CryptidLink.L17Window

/-!
# E65: exact C-to-A moving-window preludes

Two fixed-step C preludes expose precisely the A scanner inputs from E64.
Both input/output configurations retain arbitrary ListBlank exteriors.
The composite paths are exact for all natural m. This is an exact
pre-seam result, not the unproved E60 C first-return recurrence.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))

private abbrev e65_one_X : List (Fin 2) := [1, 0, 1, 0, 0, 1]
private abbrev e65_one_W : List (Fin 2) := [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev e65_one_Y : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0]

/-- The 88-step C-to-A one prelude: fixed read window [-6, 24], with arbitrary
left/right exteriors. The last head cell is zero and is retained. -/
theorem e65_one_prelude_exact (L R : Bits) :
    ReachesIn target 88
      (Cfg.headRight C (push e65_one_X L) (push e65_one_W R))
      (Cfg.headRight A (push e65_one_Y L) (push [0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

private abbrev e65_three_X : List (Fin 2) := [1, 0, 1, 0, 0, 1, 0, 0, 1]
private abbrev e65_three_W : List (Fin 2) := [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev e65_three_Y : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- The 126-step C-to-A three prelude: fixed read window [-9, 26], with arbitrary
left/right exteriors. The last head cell is zero and is retained. -/
theorem e65_three_prelude_exact (L R : Bits) :
    ReachesIn target 126
      (Cfg.headRight C (push e65_three_X L) (push e65_three_W R))
      (Cfg.headRight A (push e65_three_Y L) (push [0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- One spatial zero followed by m physical 10 pairs is m physical
01 pairs followed by a zero, with arbitrary right exterior. -/
private theorem e65_rotate_short (m : ℕ) (R : Bits) :
    push [0] (push (Q ^ m) (push [1, 1, 1] R)) =
      push (P ^ m) (push [0, 1, 1, 1] R) := by
  simpa only [P, Q, ListBlank.append_append, List.cons_append, List.nil_append] using
    (rotLB0 m (push [1, 1, 1] R))

private theorem e65_rotate_long (m : ℕ) (R : Bits) :
    push [0] (push (Q ^ m) (push [1, 0, 1, 1, 1] R)) =
      push (P ^ m) (push [0, 1, 0, 1, 1, 1] R) := by
  simpa only [P, Q, ListBlank.append_append, List.cons_append, List.nil_append] using
    (rotLB0 m (push [1, 0, 1, 1, 1] R))

/-- Exact C-to-A pair of moving-window branches for all m and arbitrary
left/right exteriors. The long branch's six additional steps are
locally certified; no later blank-left C return is claimed. -/
theorem e65_one_C_A_window_diamond_exact (m : ℕ) (L R : Bits) :
    ReachesIn target (88 + (2 * m + 2))
      (Cfg.headRight C (push e65_one_X L)
        (push e65_one_W (push (Q ^ m) (push [1, 1, 1] R))))
      (Cfg.headRight A
        (push [0, 1] (push (P ^ m) (push e65_one_Y L)))
        (push [1, 1] R)) ∧
    ReachesIn target (88 + (2 * m + 8))
      (Cfg.headRight C (push e65_one_X L)
        (push e65_one_W (push (Q ^ m) (push [1, 0, 1, 1, 1] R))))
      (Cfg.headRight A
        (push [0, 1] (push (P ^ m) (push e65_one_Y L)))
        (push [1, 1, 1, 0] R)) := by
  constructor
  · have hpre := e65_one_prelude_exact L (push (Q ^ m) (push [1, 1, 1] R))
    rw [e65_rotate_short m R] at hpre
    exact hpre.trans (e64_A_scan_window_diamond_exact m (push e65_one_Y L) R).1
  · have hpre := e65_one_prelude_exact L (push (Q ^ m) (push [1, 0, 1, 1, 1] R))
    rw [e65_rotate_long m R] at hpre
    exact hpre.trans (e64_A_scan_window_diamond_exact m (push e65_one_Y L) R).2

/-- Exact C-to-A pair of moving-window branches for all m and arbitrary
left/right exteriors. The long branch's six additional steps are
locally certified; no later blank-left C return is claimed. -/
theorem e65_three_C_A_window_diamond_exact (m : ℕ) (L R : Bits) :
    ReachesIn target (126 + (2 * m + 2))
      (Cfg.headRight C (push e65_three_X L)
        (push e65_three_W (push (Q ^ m) (push [1, 1, 1] R))))
      (Cfg.headRight A
        (push [0, 1] (push (P ^ m) (push e65_three_Y L)))
        (push [1, 1] R)) ∧
    ReachesIn target (126 + (2 * m + 8))
      (Cfg.headRight C (push e65_three_X L)
        (push e65_three_W (push (Q ^ m) (push [1, 0, 1, 1, 1] R))))
      (Cfg.headRight A
        (push [0, 1] (push (P ^ m) (push e65_three_Y L)))
        (push [1, 1, 1, 0] R)) := by
  constructor
  · have hpre := e65_three_prelude_exact L (push (Q ^ m) (push [1, 1, 1] R))
    rw [e65_rotate_short m R] at hpre
    exact hpre.trans (e64_A_scan_window_diamond_exact m (push e65_three_Y L) R).1
  · have hpre := e65_three_prelude_exact L (push (Q ^ m) (push [1, 0, 1, 1, 1] R))
    rw [e65_rotate_long m R] at hpre
    exact hpre.trans (e64_A_scan_window_diamond_exact m (push e65_three_Y L) R).2

end CryptidLink.L17

#print axioms CryptidLink.L17.e65_one_prelude_exact
#print axioms CryptidLink.L17.e65_three_prelude_exact
#print axioms CryptidLink.L17.e65_one_C_A_window_diamond_exact
#print axioms CryptidLink.L17.e65_three_C_A_window_diamond_exact
