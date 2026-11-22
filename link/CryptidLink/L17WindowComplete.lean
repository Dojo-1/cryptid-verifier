import CryptidLink.L17WindowPrelude
import CryptidLink.L17PairSweep
import CryptidLink.L17FixedBridges
import CryptidLink.L17FiveRun

/-!
# E69 — candidate composition of the guarded C checkpoint returns

This module assembles separately proved exact trajectories. Its declarations
are proof targets until Lean CI checks them; no statement about the first
return, completeness of the scanner grammar, or blank-orbit nonhalting follows.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))
private abbrev I := ([1] : List (Fin 2))

private abbrev oneX : List (Fin 2) := [1, 0, 1, 0, 0, 1]
private abbrev oneW : List (Fin 2) := [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev oneY : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0]
private abbrev threeX : List (Fin 2) := [1, 0, 1, 0, 0, 1, 0, 0, 1]
private abbrev threeW : List (Fin 2) := [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev threeY : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
private abbrev oneBridge : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]
private abbrev threeBridge : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]

private abbrev oneLeft (u v : ℕ) : Bits :=
  push [0] (push (P ^ (v + 7)) (push [0] (push (P ^ (u + 6)) default)))
private abbrev threeLeft (u v : ℕ) : Bits :=
  push (P ^ (v + 6)) (push [0] (push (P ^ (u + 6)) default))
private abbrev oneTail (u v : ℕ) : Bits :=
  push (P ^ (v + 5)) (push [0] (push (P ^ (u + 6)) default))
private abbrev threeTail (u v : ℕ) : Bits :=
  push (P ^ (v + 2)) (push [0] (push (P ^ (u + 6)) default))

private theorem one_bridge_frame (u v : ℕ) :
    push oneY (oneLeft u v) = push oneBridge (oneTail u v) := by
  change push oneY (push [0] (push (P ^ (v + 7)) (push [0] (push (P ^ (u + 6)) default)))) =
    push oneBridge (push (P ^ (v + 5)) (push [0] (push (P ^ (u + 6)) default)))
  rw [show v + 7 = 2 + (v + 5) by omega, ListBlank.append_pow_add]
  rfl

private theorem three_bridge_frame (u v : ℕ) :
    push threeY (threeLeft u v) = push threeBridge (threeTail u v) := by
  change push threeY (push (P ^ (v + 6)) (push [0] (push (P ^ (u + 6)) default))) =
    push threeBridge (push (P ^ (v + 2)) (push [0] (push (P ^ (u + 6)) default)))
  rw [show v + 6 = 4 + (v + 2) by omega, ListBlank.append_pow_add]
  rfl

/-- Exact C-to-blank-left-C return in the G1 E65 frame, for every m/u/v.
    The global E60 source and output equality are separate obligations. -/
theorem e69_one_from_contextual_C_exact (m u v : ℕ) (R : Bits) :
    ReachesIn target (214 + 6 * (m + 1) + 2 * u + 4 * v)
      (Cfg.headRight C (push oneX (oneLeft u v))
        (push oneW (push (Q ^ m) (push [1, 1, 1] R))))
      (Cfg.headRight C default
        (push (I ^ (2 * u + 6))
          (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
            (push (P ^ (v + 5))
              (push [0, 0] (push (Q ^ 16) (push (Q ^ (m + 1)) R))))))) := by
  have h65 := (e65_one_C_A_window_diamond_exact m (oneLeft u v) R).1
  have h66 := e66_A_two_ones_sweep_exact (m + 1)
    (push oneY (oneLeft u v)) R
  rw [ListBlank.append_pow_succ P m (push oneY (oneLeft u v))] at h66
  have hbridge := e67_one_contextual_bridge_exact (oneTail u v)
    (push (Q ^ (m + 1)) R)
  rw [← one_bridge_frame u v] at hbridge
  let Rlast : Bits := push [0, 0] (push (Q ^ 16) (push (Q ^ (m + 1)) R))
  have hfinal := e68_a_unwind_exact u (v + 5) Rlast
  have hr : push [1, 1, 1] Rlast =
      push [1, 1, 1, 0, 0] (push (Q ^ 16) (push (Q ^ (m + 1)) R)) := by
    rfl
  rw [hr] at hfinal
  have h := ((h65.trans h66).trans hbridge).trans hfinal
  convert h using 1 <;> omega

/-- Exact C-to-blank-left-C return in the G3 E65 frame, for every m/u/v. -/
theorem e69_three_from_contextual_C_exact (m u v : ℕ) (R : Bits) :
    ReachesIn target (268 + 6 * (m + 1) + 2 * u + 2 * v)
      (Cfg.headRight C (push threeX (threeLeft u v))
        (push threeW (push (Q ^ m) (push [1, 1, 1] R))))
      (Cfg.headRight C default
        (five_run_bottom_result u
          (push (I ^ (2 * (v + 2)))
            (push (P ^ 21) (push [0] (push (Q ^ (m + 1)) R)))))) := by
  have h65 := (e65_three_C_A_window_diamond_exact m (threeLeft u v) R).1
  have h66 := e66_A_two_ones_sweep_exact (m + 1)
    (push threeY (threeLeft u v)) R
  rw [ListBlank.append_pow_succ P m (push threeY (threeLeft u v))] at h66
  have hbridge := e67_three_contextual_bridge_exact (threeTail u v)
    (push (Q ^ (m + 1)) R)
  rw [← three_bridge_frame u v] at hbridge
  have hfinal := e68_c_finish_exact u (v + 2)
    (push (P ^ 21) (push [0] (push (Q ^ (m + 1)) R)))
  have h := ((h65.trans h66).trans hbridge).trans hfinal
  convert h using 1 <;> omega

end CryptidLink.L17

#print axioms CryptidLink.L17.e69_one_from_contextual_C_exact
#print axioms CryptidLink.L17.e69_three_from_contextual_C_exact
