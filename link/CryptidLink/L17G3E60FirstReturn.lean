import CryptidLink.L17G3CFinishFirstReturn
import CryptidLink.L17PreludeFullCGuard
import CryptidLink.L17G3StructuredBridgeSafety
import CryptidLink.L17WindowFinal
import CryptidLink.L17NoCMiddle

/-!
E94 — whole canonical positive-width G3 E60 first blank-left C.

For physical M=m+1 >= 1, exact machine trajectory:
126-step fixed G3 prelude (E77);
6M-step moving A window (E74);
95-step fixed bridge including structured t=95 witness (E89);
2(v+3)+(41+2u)-step guarded G3 C finish (E93).
Full left/right seam equalities from E69/E70 are reconstructed
in this module. E71 certifies the exact F3 terminal tape.

This is a theorem candidate, not a blank-tape orbit statement.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev E94Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev E94P := ([0, 1] : List (Fin 2))
private abbrev E94Q := ([1, 0] : List (Fin 2))

private abbrev e94_threeX : List (Fin 2) :=
  [1, 0, 1, 0, 0, 1, 0, 0, 1]
private abbrev e94_threeW : List (Fin 2) :=
  [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev e94_threeY : List (Fin 2) :=
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
   1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
private abbrev e94_threeBridge : List (Fin 2) :=
  [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
   0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]
private abbrev e94_threeLeft (u v : ℕ) : E94Bits :=
  push (E94P ^ (v + 6))
    (push [0] (push (E94P ^ (u + 6)) default))
private abbrev e94_threeTail (u v : ℕ) : E94Bits :=
  push (E94P ^ (v + 2))
    (push [0] (push (E94P ^ (u + 6)) default))

/-- Repack the prelude's right word without ever trimming the symbolic
right exterior: 0 (10)^m 111 R = (01)^(m+1) 11 R. -/
private theorem e94_repack (m : ℕ) (R : E94Bits) :
    push [0] (push (E94Q ^ m) (push [1, 1, 1] R)) =
      push (E94P ^ (m + 1)) (push [1, 1] R) := by
  calc
    _ = push (E94P ^ m) (push [0] (push [1, 1, 1] R)) :=
      rotLB0 m (push [1, 1, 1] R)
    _ = push (E94P ^ m) (push E94P (push [1, 1] R)) := by rfl
    _ = push (E94P ^ (m + 1)) (push [1, 1] R) := by
      rw [ListBlank.append_pow_succ' E94P m (push [1, 1] R)]

/-- Full left-tape bridge source identity (the G3 E69 frame). -/
private theorem e94_three_bridge_frame (u v : ℕ) :
    push e94_threeY (e94_threeLeft u v) =
      push e94_threeBridge (e94_threeTail u v) := by
  change push e94_threeY
    (push (E94P ^ (v + 6))
      (push [0] (push (E94P ^ (u + 6)) default))) =
    push e94_threeBridge
      (push (E94P ^ (v + 2))
        (push [0] (push (E94P ^ (u + 6)) default)))
  rw [show v + 6 = 4 + (v + 2) by omega,
    ListBlank.append_pow_add]
  rfl

/-- All strictly earlier times of the E65 contextual G3 C source
exclude blank-left C for every m,u,v,R and M=m+1>=1. -/
theorem e94_G3_contextual_noBlankLeftC_before
    (m u v : ℕ) (R : E94Bits) :
    E80NoBlankLeftCBefore
      (Cfg.headRight C
        (push e94_threeX (e94_threeLeft u v))
        (push e94_threeW
          (push (E94Q ^ m) (push [1, 1, 1] R))))
      (268 + 6 * (m + 1) + 2 * u + 2 * v) := by
  -- Exact 126-step prelude and its strict E77 safety.
  have hpre := e65_three_prelude_exact (e94_threeLeft u v)
    (push (E94Q ^ m) (push [1, 1, 1] R))
  rw [e94_repack m R] at hpre
  have hpreSafe :
      E80NoBlankLeftCBefore
        (Cfg.headRight C
          (push e94_threeX (e94_threeLeft u v))
          (push e94_threeW
            (push (E94Q ^ m) (push [1, 1, 1] R)))) 126 :=
    e77_three_full_prelude_noBlankLeftC
      (e94_threeLeft u v)
      (push (E94Q ^ m) (push [1, 1, 1] R))
  -- Middle 6M A-window never enters control C.
  have hmidSafe := e80_safe_then_C_free hpre hpreSafe
    (e74_variable_A_window_C_free (m + 1)
      (push e94_threeY (e94_threeLeft u v)) R)
  have h65 := (e65_three_C_A_window_diamond_exact m
    (e94_threeLeft u v) R).1
  have h66 := e66_A_two_ones_sweep_exact (m + 1)
    (push e94_threeY (e94_threeLeft u v)) R
  rw [ListBlank.append_pow_succ E94P m
    (push e94_threeY (e94_threeLeft u v))] at h66
  have hwin := h65.trans h66
  have hclockWin :
      126 + (2 * m + 2) + 4 * (m + 1) =
        126 + 6 * (m + 1) := by omega
  rw [hclockWin] at hwin

  -- The fixed 95-step G3 bridge and *structured* endpoint witness.
  let middleRight : E94Bits := push (E94Q ^ (m + 1)) R
  have hbridge := e67_three_contextual_bridge_exact
    (e94_threeTail u v) middleRight
  rw [← e94_three_bridge_frame u v] at hbridge
  have hbridgeThrough := e89_G3_structured_bridge_noBlankLeftC_through95
    u v middleRight
  change E80NoBlankLeftCBefore
    (Cfg.headRight A
      (push e94_threeBridge (e94_threeTail u v))
      (push [1, 1] middleRight)) 96 at hbridgeThrough
  have hbridgeSafe :
      E80NoBlankLeftCBefore
        (Cfg.headRight A
          (push e94_threeBridge (e94_threeTail u v))
          (push [1, 1] middleRight)) 95 := by
    intro t ht c hc
    exact hbridgeThrough t (by omega) c hc
  rw [← e94_three_bridge_frame u v] at hbridgeSafe

  -- Exact bridge C exit equals the guarded E93 G3 C finishing source.
  let lastRight : E94Bits :=
    push (E94P ^ 21) (push [0] middleRight)
  have hlastSafe := e93_G3_C_finish_noBlankLeftC_before
    u (v + 2) lastRight
  change E80NoBlankLeftCBefore
    (Cfg.headRight C (e94_threeTail u v) (push [1, 1] lastRight))
      (2 * ((v + 2) + 1) + (41 + 2 * u)) at hlastSafe
  have hafterBridge :=
    e80_safe_trans hbridge hbridgeSafe hlastSafe
  have hfull := e80_safe_trans hwin hmidSafe hafterBridge
  have hclock :
      (126 + 6 * (m + 1)) +
        (95 + (2 * ((v + 2) + 1) + (41 + 2 * u))) =
      268 + 6 * (m + 1) + 2 * u + 2 * v := by omega
  rw [hclock] at hfull
  exact hfull

/-- This is the original positive-width G3 E60 checkpoint, not a
different contextual surrogate: source equality preserves full tape. -/
private theorem e94_G3_source_frame
    (m u v : ℕ) (R : E94Bits) :
    widthFourCutSource u v
      (push [1, 1, 1] (push (E94Q ^ 7) (push [1, 1, 0, 1]
        (push (E94Q ^ (m + 1)) (push [1, 1, 1] R))))) =
    Cfg.headRight C
      (push e94_threeX (e94_threeLeft u v))
      (push e94_threeW
        (push (E94Q ^ m) (push [1, 1, 1] R))) := by
  unfold widthFourCutSource
  rw [ListBlank.append_pow_succ E94Q m (push [1, 1, 1] R)]
  change Cfg.headRight C
      (push (E94Q ^ 2)
        (push [0, 1, 0]
          (push (E94P ^ (v + 7))
            (push [0] (push (E94P ^ (u + 6)) default)))))
      _ = _
  rw [show v + 7 = 1 + (v + 6) by omega,
    ListBlank.append_pow_add E94P 1 (v + 6)
      (push [0] (push (E94P ^ (u + 6)) default))]
  rfl

/-- Strict first-return safety for the complete original E60 G3
C checkpoint, with symbolic full right exterior. -/
theorem e94_G3_E60_noBlankLeftC_before
    (m u v : ℕ) (R : E94Bits) :
    E80NoBlankLeftCBefore
      (widthFourCutSource u v
        (push [1, 1, 1] (push (E94Q ^ 7) (push [1, 1, 0, 1]
          (push (E94Q ^ (m + 1)) (push [1, 1, 1] R))))))
      (268 + 6 * (m + 1) + 2 * u + 2 * v) := by
  rw [e94_G3_source_frame m u v R]
  exact e94_G3_contextual_noBlankLeftC_before m u v R

/-- Exact first blank-left C of the full canonical positive-width
G3 E60 checkpoint: T=268+6M+2u+2v. Does not establish global
blank-tape orbit reachability or L17 nonhalting. -/
theorem e94_G3_E60_first_blankLeftC
    (m u v : ℕ) (R : E94Bits) :
    (∃ Z : E94Bits,
      ReachesIn target
        (268 + 6 * (m + 1) + 2 * u + 2 * v)
        (widthFourCutSource u v
          (push [1, 1, 1] (push (E94Q ^ 7) (push [1, 1, 0, 1]
            (push (E94Q ^ (m + 1)) (push [1, 1, 1] R))))))
        (Cfg.headRight C default Z)) ∧
    (∀ t : ℕ,
      t < 268 + 6 * (m + 1) + 2 * u + 2 * v →
      ∀ Z : E94Bits,
        ¬ ReachesIn target t
          (widthFourCutSource u v
            (push [1, 1, 1] (push (E94Q ^ 7) (push [1, 1, 0, 1]
              (push (E94Q ^ (m + 1)) (push [1, 1, 1] R))))))
          (Cfg.headRight C default Z)) := by
  exact e84_first_blankLeftC_criterion
    (e71_three_full_E60_exact m u v R)
    ⟨_, rfl⟩
    (e94_G3_E60_noBlankLeftC_before m u v R)

end CryptidLink.L17

#print axioms CryptidLink.L17.e94_G3_contextual_noBlankLeftC_before
#print axioms CryptidLink.L17.e94_G3_E60_noBlankLeftC_before
#print axioms CryptidLink.L17.e94_G3_E60_first_blankLeftC
