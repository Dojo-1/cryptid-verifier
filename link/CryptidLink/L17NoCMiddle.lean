import CryptidLink.L17NoCScan
import CryptidLink.L17WindowPrelude

/-!
# E75 — locate the C-free moving window inside both real E60 C checkpoints

E73 and E74 prove safety starting in A. Here the already-certified
88/126-step contextual C-to-A preludes are used to transport that
safety back to a C checkpoint with its complete tape. Only the
specified middle clock interval is certified: the fixed prelude and
post-window return still need separate left-witness proofs.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))

private abbrev oneX : List (Fin 2) :=
  [1, 0, 1, 0, 0, 1]
private abbrev oneW : List (Fin 2) :=
  [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev oneY : List (Fin 2) :=
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0]
private abbrev threeX : List (Fin 2) :=
  [1, 0, 1, 0, 0, 1, 0, 0, 1]
private abbrev threeW : List (Fin 2) :=
  [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev threeY : List (Fin 2) :=
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- A generic deterministic interval transport. It needs an exact
entry path, not a claimed global simulation or insertion conjugacy. -/
theorem e75_C_free_window_after_exact
    {source mid : Cfg (Fin 2) (Fin 6)} {a b : ℕ}
    (hentry : ReachesIn target a source mid)
    (hnoc : E73NoCBefore mid b) :
    ∀ t : ℕ, a ≤ t → t < a + b →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t source c → c.q ≠ some C := by
  intro t hlow hhigh c hc
  have hs : t = a + (t - a) := by omega
  change multiStep target source a = some mid at hentry
  change multiStep target source t = some c at hc
  rw [hs, multiStep_add, hentry, Option.bind_some] at hc
  exact hnoc (t - a) (by omega) c hc

/-- The 0(10)^m111 prelude remainder is precisely
(01)^(m+1)11, including arbitrary right exterior. -/
private theorem e75_repack (m : ℕ) (R : Bits) :
    push [0] (push (Q ^ m) (push [1, 1, 1] R)) =
      push (P ^ (m + 1)) (push [1, 1] R) := by
  calc
    _ = push (P ^ m) (push [0] (push [1, 1, 1] R)) :=
      rotLB0 m (push [1, 1, 1] R)
    _ = push (P ^ m) (push P (push [1, 1] R)) := by rfl
    _ = push (P ^ (m + 1)) (push [1, 1] R) := by
      rw [ListBlank.append_pow_succ' P m (push [1, 1] R)]

/-- All 6*(m+1) steps beginning at time 88 on the one-headed E65 C
source have non-C control, even with arbitrary exterior tape. -/
theorem e75_one_middle_C_free (m : ℕ) (L R : Bits) :
    ∀ t : ℕ, 88 ≤ t → t < 88 + 6 * (m + 1) →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight C (push oneX L)
            (push oneW (push (Q ^ m) (push [1, 1, 1] R)))) c →
          c.q ≠ some C := by
  have hpre := e65_one_prelude_exact L (push (Q ^ m) (push [1, 1, 1] R))
  change ReachesIn target 88
    (Cfg.headRight C (push oneX L)
      (push oneW (push (Q ^ m) (push [1, 1, 1] R))))
    (Cfg.headRight A (push oneY L)
      (push [0] (push (Q ^ m) (push [1, 1, 1] R)))) at hpre
  rw [e75_repack m R] at hpre
  exact e75_C_free_window_after_exact hpre
    (e74_variable_A_window_C_free (m + 1) (push oneY L) R)

/-- All 6*(m+1) steps beginning at time 126 on the three-headed E65
C source have non-C control, retaining arbitrary exterior tapes. -/
theorem e75_three_middle_C_free (m : ℕ) (L R : Bits) :
    ∀ t : ℕ, 126 ≤ t → t < 126 + 6 * (m + 1) →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight C (push threeX L)
            (push threeW (push (Q ^ m) (push [1, 1, 1] R)))) c →
          c.q ≠ some C := by
  have hpre := e65_three_prelude_exact L (push (Q ^ m) (push [1, 1, 1] R))
  change ReachesIn target 126
    (Cfg.headRight C (push threeX L)
      (push threeW (push (Q ^ m) (push [1, 1, 1] R))))
    (Cfg.headRight A (push threeY L)
      (push [0] (push (Q ^ m) (push [1, 1, 1] R)))) at hpre
  rw [e75_repack m R] at hpre
  exact e75_C_free_window_after_exact hpre
    (e74_variable_A_window_C_free (m + 1) (push threeY L) R)

end CryptidLink.L17

#print axioms CryptidLink.L17.e75_C_free_window_after_exact
#print axioms CryptidLink.L17.e75_one_middle_C_free
#print axioms CryptidLink.L17.e75_three_middle_C_free
