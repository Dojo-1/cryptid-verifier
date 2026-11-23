import CryptidLink.L17FirstReturnSafety

/-!
E84 — conditional first-blank-left-C criterion.

An exact return is not necessarily its first return. The criterion
requires (i) a complete exact full-configuration endpoint and (ii)
a safety proof for every strictly earlier timestamp. No claim is made
here that the canonical E60 families already satisfy (ii).
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

/-- A first return is a conjunction of the exact terminal witness and
the absence of any blank-left C state at earlier times. This theorem
only packages the independent reachability and safety obligations. -/
theorem e84_first_blankLeftC_criterion
    {source final : Cfg (Fin 2) (Fin 6)} {clock : ℕ}
    (hpath : ReachesIn target clock source final)
    (hfinal : E76BlankLeftC final)
    (hsafe : E80NoBlankLeftCBefore source clock) :
    (∃ Z : ListBlank (Fin 2),
      ReachesIn target clock source (Cfg.headRight C default Z)) ∧
    (∀ t : ℕ, t < clock →
      ∀ Z : ListBlank (Fin 2),
        ¬ ReachesIn target t source (Cfg.headRight C default Z)) := by
  rcases hfinal with ⟨Z, hZ⟩
  constructor
  · refine ⟨Z, ?_⟩
    rw [hZ] at hpath
    exact hpath
  · intro t ht Z hreach
    exact (hsafe t ht _ hreach) ⟨Z, rfl⟩

end CryptidLink.L17
#print axioms CryptidLink.L17.e84_first_blankLeftC_criterion
