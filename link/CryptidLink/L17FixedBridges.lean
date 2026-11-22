import CryptidLink.L17Window

/-!
# E67 — exact A-to-A and A-to-C fixed bridges

Two fixed contextual machine paths close the gap between the parameterized
A sweep and the previously proved final unwind. All left and right exterior
ListBlanks are arbitrary. A separate lemma must still align these bridge
inputs with actual E60 checkpoint words, then compose the return.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))

/-- 77 exact raw steps, arbitrary exterior tapes; the observed read window
is [-34,1] relative to the entry A head. This returns in A mode and
leaves the right-hand "11100" prefix before sixteen 10 pairs. -/
theorem e67_one_contextual_bridge_exact (L R : Bits) :
    ReachesIn target 77
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight A L (push [1, 1, 1, 0, 0] (push (Q ^ 16) R))) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- 95 exact raw steps, arbitrary exterior tapes; the observed read window
is [-42,1] relative to the entry A head. This returns in C mode and
leaves a right-hand "11", 21 01 pairs and a 0 before the exterior. -/
theorem e67_three_contextual_bridge_exact (L R : Bits) :
    ReachesIn target 95
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight C L (push [1, 1] (push (P ^ 21) (push [0] R)))) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

end CryptidLink.L17

#print axioms CryptidLink.L17.e67_one_contextual_bridge_exact
#print axioms CryptidLink.L17.e67_three_contextual_bridge_exact
