import CryptidLink.L17FiveRun

/-!
# E64: parameterized A-window insertion diamond

The already-certified A01 scanner and E61 window diamond compose for
*every* natural number of 01 tokens and arbitrary exterior ListBlanks.
This is an exact local A-state theorem, not the global E60 C-checkpoint
recurrence: no theorem here asserts that an arbitrary C checkpoint
enters this A frame or that the return phase avoids the inserted cells.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))

/-- An arbitrary 01 scanner prefix can be followed by either branch of the
E61 insertion diamond. Both preserve arbitrary exteriors and finish at the
same A head with the same accumulated left prefix. The longer branch adds
exactly six defined transitions and leaves a different four-bit residue. -/
theorem e64_A_scan_window_diamond_exact (m : ℕ) (L R : Bits) :
    ReachesIn target (2 * m + 2)
      (Cfg.headRight A L (push (P ^ m) (push [0, 1, 1, 1] R)))
      (Cfg.headRight A (push [0, 1] (push (P ^ m) L)) (push [1, 1] R)) ∧
    ReachesIn target (2 * m + 8)
      (Cfg.headRight A L (push (P ^ m) (push [0, 1, 0, 1, 1, 1] R)))
      (Cfg.headRight A (push [0, 1] (push (P ^ m) L))
        (push [1, 1, 1, 0] R)) := by
  constructor
  · have hscan := a01_sweep_exact m L (push [0, 1, 1, 1] R)
    have hshort := (e61_A_window_insertion_diamond_exact (push (P ^ m) L) R).1
    exact hscan.trans hshort
  · have hscan := a01_sweep_exact m L (push [0, 1, 0, 1, 1, 1] R)
    have hlong := (e61_A_window_insertion_diamond_exact (push (P ^ m) L) R).2
    exact hscan.trans hlong

end CryptidLink.L17

#print axioms CryptidLink.L17.e64_A_scan_window_diamond_exact
