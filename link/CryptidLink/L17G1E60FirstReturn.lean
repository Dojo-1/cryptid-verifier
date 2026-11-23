import CryptidLink.L17G1AUnwindFirstReturn
import CryptidLink.L17PreludeFullCGuard
import CryptidLink.L17G1BridgeSafe
import CryptidLink.L17WindowFinal

/-!
E88 — first blank-left C from the canonical positive-width G1 E60
width-four checkpoint.

This composes four strict safety intervals using exact full tapes:
E77 prelude 88; E74 variable A window 6*(m+1); E81 fixed G1
bridge 77; E87 final A unwind 4*(v+5)+29+2*u.
At every seam we use the existing machine-exact endpoint certificates.
No result for M=0, the G3 family, or global nonhalting is claimed.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))

private abbrev oneX : List (Fin 2) := [1, 0, 1, 0, 0, 1]
private abbrev oneW : List (Fin 2) := [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
private abbrev oneY : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0]
private abbrev oneBridge : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]

private abbrev oneLeft (u v : ℕ) : Bits :=
  push [0] (push (P ^ (v + 7))
    (push [0] (push (P ^ (u + 6)) default)))
private abbrev oneTail (u v : ℕ) : Bits :=
  push (P ^ (v + 5)) (push [0] (push (P ^ (u + 6)) default))

/-- This is the same full-tape left frame equality used in E69,
with no machine steps or arbitrary insertion hypothesis. -/
private theorem e88_one_bridge_frame (u v : ℕ) :
    push oneY (oneLeft u v) =
      push oneBridge (oneTail u v) := by
  change push oneY
    (push [0] (push (P ^ (v + 7))
      (push [0] (push (P ^ (u + 6)) default)))) =
    push oneBridge
      (push (P ^ (v + 5))
        (push [0] (push (P ^ (u + 6)) default)))
  rw [show v + 7 = 2 + (v + 5) by omega, ListBlank.append_pow_add]
  rfl

/-- Exactly the rotating right tape identity used in E75:
0 (10)^m 111 = (01)^(m+1) 11, with arbitrary suffix R. -/
private theorem e88_repack (m : ℕ) (R : Bits) :
    push [0] (push (Q ^ m) (push [1, 1, 1] R)) =
      push (P ^ (m + 1)) (push [1, 1] R) := by
  calc
    _ = push (P ^ m) (push [0] (push [1, 1, 1] R)) :=
      rotLB0 m (push [1, 1, 1] R)
    _ = push (P ^ m) (push P (push [1, 1] R)) := by rfl
    _ = push (P ^ (m + 1)) (push [1, 1] R) := by
      rw [ListBlank.append_pow_succ' P m (push [1, 1] R)]

/-- Strict first-return safety for the E65 G1 contextual C-source.
This statement is independent of the E60 width-four spelling. -/
theorem e88_G1_contextual_noBlankLeftC_before
    (m u v : ℕ) (R : Bits) :
    E80NoBlankLeftCBefore
      (Cfg.headRight C (push oneX (oneLeft u v))
        (push oneW (push (Q ^ m) (push [1, 1, 1] R))))
      (214 + 6 * (m + 1) + 2 * u + 4 * v) := by

  -- First 88 steps: nonblank-left C at every intermediate C visit.
  have hpre := e65_one_prelude_exact (oneLeft u v)
    (push (Q ^ m) (push [1, 1, 1] R))
  rw [e88_repack m R] at hpre
  have hpreSafe :
      E80NoBlankLeftCBefore
        (Cfg.headRight C (push oneX (oneLeft u v))
          (push oneW (push (Q ^ m) (push [1, 1, 1] R))))
        88 :=
    e77_one_full_prelude_noBlankLeftC
      (oneLeft u v) (push (Q ^ m) (push [1, 1, 1] R))

  -- The A window contains no C at all; source and endpoint tapes are
  -- certified by E65, E64 and E66, not inferred from the clock alone.
  have hmidSafe := e80_safe_then_C_free hpre hpreSafe
    (e74_variable_A_window_C_free (m + 1)
      (push oneY (oneLeft u v)) R)
  have h65 := (e65_one_C_A_window_diamond_exact m (oneLeft u v) R).1
  have h66 := e66_A_two_ones_sweep_exact (m + 1)
    (push oneY (oneLeft u v)) R
  rw [ListBlank.append_pow_succ P m (push oneY (oneLeft u v))] at h66
  have hwin := h65.trans h66
  have hclockWin :
      88 + (2 * m + 2) + 4 * (m + 1) =
        88 + 6 * (m + 1) := by omega
  rw [hclockWin] at hwin

  -- The 77-step fixed bridge may revisit C, but never with blank left.
  let midRight : Bits := push (Q ^ (m + 1)) R
  have hbridge := e67_one_contextual_bridge_exact
    (oneTail u v) midRight
  rw [← e88_one_bridge_frame u v] at hbridge
  have hbridgeSafe := e81_G1_bridge_noBlankLeftC_before77
    (oneTail u v) midRight
  change E80NoBlankLeftCBefore
    (Cfg.headRight A (push oneBridge (oneTail u v))
      (push [1, 1] midRight)) 77 at hbridgeSafe
  rw [← e88_one_bridge_frame u v] at hbridgeSafe

  -- The exact bridge exit is the E68 guarded A source, including
  -- the untouched right suffix 00 (10)^16 (10)^(m+1) R.
  let lastRight : Bits := push [0, 0] (push (Q ^ 16) midRight)
  have hlastSafe := e87_G1_A_unwind_noBlankLeftC_before
    u (v + 5) lastRight
  change E80NoBlankLeftCBefore
    (Cfg.headRight A (oneTail u v)
      (push [1, 1, 1, 0, 0] (push (Q ^ 16) midRight)))
    (4 * (v + 5) + 29 + 2 * u) at hlastSafe

  have hafterBridge := e80_safe_trans hbridge hbridgeSafe hlastSafe
  have hfull := e80_safe_trans hwin hmidSafe hafterBridge
  have hclock :
      (88 + 6 * (m + 1)) +
        (77 + (4 * (v + 5) + 29 + 2 * u)) =
      214 + 6 * (m + 1) + 2 * u + 4 * v := by omega
  rw [hclock] at hfull
  exact hfull

/-- The original positive-width G1 E60 C checkpoint is definitionally
the contextual E65 source after the exact M=m+1 word split. -/
private theorem e88_one_source_frame (m u v : ℕ) (R : Bits) :
    widthFourCutSource u v
        (push [1]
          (push (Q ^ 7) (push [1, 1, 0, 1]
            (push (Q ^ (m + 1)) (push [1, 1, 1] R))))) =
    Cfg.headRight C (push oneX (oneLeft u v))
      (push oneW (push (Q ^ m) (push [1, 1, 1] R))) := by
  unfold widthFourCutSource
  rw [ListBlank.append_pow_succ Q m (push [1, 1, 1] R)]
  rfl

/-- First-return SAFETY from the full canonical E60 G1 C checkpoint,
for all physical widths M=m+1>=1, and arbitrary u,v,R. -/
theorem e88_G1_E60_noBlankLeftC_before
    (m u v : ℕ) (R : Bits) :
    E80NoBlankLeftCBefore
      (widthFourCutSource u v
        (push [1] (push (Q ^ 7) (push [1, 1, 0, 1]
          (push (Q ^ (m + 1)) (push [1, 1, 1] R))))))
      (214 + 6 * (m + 1) + 2 * u + 4 * v) := by
  rw [e88_one_source_frame m u v R]
  exact e88_G1_contextual_noBlankLeftC_before m u v R

/-- The E71 exact endpoint is now its first blank-left C endpoint:
an exact universal positive-width G1 C-to-C first-return theorem.
This remains a local machine section, NOT a blank-orbit nonhalting result. -/
theorem e88_G1_E60_first_blankLeftC
    (m u v : ℕ) (R : Bits) :
    (∃ Z : Bits,
      ReachesIn target (214 + 6 * (m + 1) + 2 * u + 4 * v)
        (widthFourCutSource u v
          (push [1] (push (Q ^ 7) (push [1, 1, 0, 1]
            (push (Q ^ (m + 1)) (push [1, 1, 1] R))))))
        (Cfg.headRight C default Z)) ∧
    (∀ t : ℕ, t < 214 + 6 * (m + 1) + 2 * u + 4 * v →
      ∀ Z : Bits,
        ¬ ReachesIn target t
          (widthFourCutSource u v
            (push [1] (push (Q ^ 7) (push [1, 1, 0, 1]
              (push (Q ^ (m + 1)) (push [1, 1, 1] R))))))
          (Cfg.headRight C default Z)) := by
  have hret := e71_one_full_E60_exact m u v R
  exact e84_first_blankLeftC_criterion hret ⟨_, rfl⟩
    (e88_G1_E60_noBlankLeftC_before m u v R)

end CryptidLink.L17

#print axioms CryptidLink.L17.e88_G1_contextual_noBlankLeftC_before
#print axioms CryptidLink.L17.e88_G1_E60_noBlankLeftC_before
#print axioms CryptidLink.L17.e88_G1_E60_first_blankLeftC
