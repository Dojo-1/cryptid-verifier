import CryptidLink.L17AFinishSafety
import CryptidLink.L17CSweepSentinelSafety
import CryptidLink.L17UnwindPrefixSafe

/-!
E87 — first blank-left C for the exact E68 G1 final A unwind.

This is a *local* theorem about a guarded A source, not a first-return
claim for either full E60 C checkpoint. It reuses:
E83 (4p C-free A prefix), E86 (fixed 25-step A finish safety),
E85 (sentinel-dependent final 2(u+2) C sweep), and E68 exact return.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))

/-- Every exact intermediate state of the E68 G1 A unwind, strictly
before its full 4p+29+2u clock, avoids blank-left C.
The right exterior R is symbolic; all three seam tapes match exactly. -/
theorem e87_G1_A_unwind_noBlankLeftC_before
    (u p : ℕ) (R : Bits) :
    E80NoBlankLeftCBefore
      (Cfg.headRight A
        (push (P ^ p) (push [0] (push (P ^ (u + 6)) default)))
        (push [1, 1, 1] R))
      (4 * p + 29 + 2 * u) := by
  let L : Bits := push (P ^ (u + 2)) default
  let W : Bits := push (P ^ p) R
  let T : Bits := push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] (push [1] W)
  have hL :
      push [0, 0, 1, 0, 1, 0, 1, 0, 1] L =
      push [0] (push (P ^ (u + 6)) default) := by
    change push [0] (push (P ^ 4) (push (P ^ (u + 2)) default)) = _
    rw [← ListBlank.append_pow_add,
      show 4 + (u + 2) = u + 6 by omega]
  have hR : push (Q ^ p) (push [1] R) = push [1] W := by
    change push (Q ^ p) (push [1] R) =
      push [1] (push (P ^ p) R)
    exact (rotLB p R).symm

  -- 4p exact A-mode pairs: E66 endpoints and E83 safety coincide.
  have hPair := e66_A_two_ones_sweep_exact p
    (push [0] (push (P ^ (u + 6)) default)) (push [1] R)
  rw [hR] at hPair
  change ReachesIn target (4 * p)
    (Cfg.headRight A
      (push (P ^ p) (push [0] (push (P ^ (u + 6)) default)))
      (push [1, 1, 1] R))
    (Cfg.headRight A
      (push [0] (push (P ^ (u + 6)) default))
      (push [1, 1, 1] W)) at hPair
  have hPairSafe :
      E80NoBlankLeftCBefore
        (Cfg.headRight A
          (push (P ^ p) (push [0] (push (P ^ (u + 6)) default)))
          (push [1, 1, 1] R))
        (4 * p) :=
    e83_G1_unwind_A_prefix_noBlankLeftC u p R

  -- 25 exact fixed transitions: use the E86 proof that excludes all
  -- strictly earlier blank-left C visits, including the deep witnesses.
  have hFixed := e86_width4_A_finish_exact L (push [1] W)
  change ReachesIn target 25
    (Cfg.headRight A
      (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1] W))
    (Cfg.headRight C L (push [1] T)) at hFixed
  rw [hL] at hFixed
  have hFixedSafe := e86_width4_A_finish_noBlankLeftC_before25
    L (push [1] W)
  change E80NoBlankLeftCBefore
    (Cfg.headRight A
      (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L)
      (push [1, 1, 1] W)) 25 at hFixedSafe
  rw [hL] at hFixedSafe

  -- The actual final C-mode endpoint has a structural left sentinel
  -- and is exactly the symbolic source of the E85 sweep.
  have hFrame :
      Cfg.headRight C L (push [1] T) =
      Cfg.headLeft C
        (push (Q ^ (u + 2)) (push [1] (default : Bits))) T := by
    calc
      _ = Cfg.headLeft C (push [1] L) T :=
        Cfg.headRight_cons C (1 : Fin 2) L T
      _ = _ := by
        dsimp only [L]
        rw [rotLB]
  rw [hFrame] at hFixed
  have hSweepSafe := e85_G1_final_C_sweep_safe u T

  have hAfterPair := e80_safe_trans hFixed hFixedSafe hSweepSafe
  have hComplete := e80_safe_trans hPair hPairSafe hAfterPair
  have hClock :
      4 * p + (25 + 2 * (u + 2)) = 4 * p + 29 + 2 * u := by
    omega
  rw [hClock] at hComplete
  exact hComplete

/-- The first blank-left C reached from the E68 guarded G1 A source
occurs at exactly 4p+29+2u steps, for all u,p and arbitrary R.
This is not the first return from the earlier E60 C checkpoint. -/
theorem e87_G1_A_unwind_first_blankLeftC
    (u p : ℕ) (R : Bits) :
    (∃ Z : Bits,
      ReachesIn target (4 * p + 29 + 2 * u)
        (Cfg.headRight A
          (push (P ^ p) (push [0] (push (P ^ (u + 6)) default)))
          (push [1, 1, 1] R))
        (Cfg.headRight C default Z)) ∧
    (∀ t : ℕ, t < 4 * p + 29 + 2 * u →
      ∀ Z : Bits,
        ¬ ReachesIn target t
          (Cfg.headRight A
            (push (P ^ p) (push [0] (push (P ^ (u + 6)) default)))
            (push [1, 1, 1] R))
          (Cfg.headRight C default Z)) := by
  exact e84_first_blankLeftC_criterion
    (e68_a_unwind_exact u p R)
    ⟨_, rfl⟩
    (e87_G1_A_unwind_noBlankLeftC_before u p R)

end CryptidLink.L17

#print axioms CryptidLink.L17.e87_G1_A_unwind_noBlankLeftC_before
#print axioms CryptidLink.L17.e87_G1_A_unwind_first_blankLeftC
