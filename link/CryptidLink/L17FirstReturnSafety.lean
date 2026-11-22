import CryptidLink.L17NoCMiddle
import CryptidLink.L17First26CGuard

/-!
# E80 — exact temporal composition of blank-left-C safety

E71 proves exact return. E76/E77/E78/E79 and the final unwind certify
that *no earlier* C visit has a blank left tape. This module supplies
the general deterministic algebra to compose those interval claims
without assuming any new machine paths.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

/-- A safety condition on every intermediate exact machine state,
not just the endpoint or a bounded raw trace. -/
def E80NoBlankLeftCBefore
    (source : Cfg (Fin 2) (Fin 6)) (clock : ℕ) : Prop :=
  ∀ t : ℕ, t < clock →
    ∀ c : Cfg (Fin 2) (Fin 6),
      ReachesIn target t source c → ¬ E76BlankLeftC c

/-- Every C-free interval is automatically blank-left-C-free. The
converse is false, since C may occur with a nonblank left tape. -/
theorem e80_safe_of_C_free
    {source : Cfg (Fin 2) (Fin 6)} {n : ℕ}
    (h : E73NoCBefore source n) :
    E80NoBlankLeftCBefore source n := by
  intro t ht c hc
  have hnot : c.q ≠ some C := h t ht c hc
  rintro ⟨Z, hz⟩
  apply hnot
  rw [hz]
  rfl

/-- Composition along an **exact** machine trajectory preserves
first-return safety. Determinism, not reachability-graph intuition,
provides the crucial identification of the intermediate machine state. -/
theorem e80_safe_trans
    {source mid : Cfg (Fin 2) (Fin 6)} {m n : ℕ}
    (hpath : ReachesIn target m source mid)
    (hfirst : E80NoBlankLeftCBefore source m)
    (hsecond : E80NoBlankLeftCBefore mid n) :
    E80NoBlankLeftCBefore source (m + n) := by
  intro t ht c hc
  by_cases hleft : t < m
  · exact hfirst t hleft c hc
  · have hclock : t = m + (t - m) := by omega
    change multiStep target source m = some mid at hpath
    change multiStep target source t = some c at hc
    rw [hclock, multiStep_add, hpath, Option.bind_some] at hc
    exact hsecond (t - m) (by omega) c hc

/-- Convenient mixed form for composing a prelude with an A phase
that has the stronger C-free property. -/
theorem e80_safe_then_C_free
    {source mid : Cfg (Fin 2) (Fin 6)} {m n : ℕ}
    (hpath : ReachesIn target m source mid)
    (hprelude : E80NoBlankLeftCBefore source m)
    (hwindow : E73NoCBefore mid n) :
    E80NoBlankLeftCBefore source (m + n) :=
  e80_safe_trans hpath hprelude (e80_safe_of_C_free hwindow)

end CryptidLink.L17

#print axioms CryptidLink.L17.e80_safe_of_C_free
#print axioms CryptidLink.L17.e80_safe_trans
#print axioms CryptidLink.L17.e80_safe_then_C_free
