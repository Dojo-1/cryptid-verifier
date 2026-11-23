import CryptidLink.L17G3BridgeSafe
import CryptidLink.L17FirstReturnSafety

/-!
E89 — complete through-endpoint safety for the structured G3 fixed bridge.

E82 certifies all timestamps t < 95 for arbitrary exterior half-tapes.
At t = 95, E78 rules out unrestricted exterior claims by exhibiting
a blank-left C counterexample. E79 certifies precisely the E60
structured left exterior, which has a nonzero second-left bit.
Their union proves safety on the strict time interval t < 96.

This is a local interval theorem, not a G3 first-return theorem.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev E89Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev E89P := ([0, 1] : List (Fin 2))
private abbrev E89W3 : List (Fin 2) :=
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
   1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]

private abbrev e89_left (u v : ℕ) : E89Bits :=
  push (E89P ^ (v + 2))
    (push [0] (push (E89P ^ (u + 6)) default))

/-- The actual structured G3 fixed bridge has no blank-left C at
any of its 96 states, including the C endpoint at raw t = 95.
The arbitrary R is unchanged. This does NOT hold for arbitrary
left exteriors. -/
theorem e89_G3_structured_bridge_noBlankLeftC_through95
    (u v : ℕ) (R : E89Bits) :
    E80NoBlankLeftCBefore
      (Cfg.headRight A
        (push E89W3 (e89_left u v)) (push [1, 1] R))
      96 := by
  intro t ht c hc
  by_cases hbefore : t < 95
  · exact e82_G3_bridge_noBlankLeftC_before95
      (e89_left u v) R t hbefore c hc
  · have heq : t = 95 := by omega
    subst t
    exact e79_three_bridge_C95_nonblank_in_E60_context u v R c hc

end CryptidLink.L17

#print axioms CryptidLink.L17.e89_G3_structured_bridge_noBlankLeftC_through95
