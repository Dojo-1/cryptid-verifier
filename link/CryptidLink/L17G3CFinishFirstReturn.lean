import CryptidLink.L17G3K41TailFirstReturn
import CryptidLink.L17G3C01MiddleSafety
import CryptidLink.L17FiveRun
import CryptidLink.L17ab

/-!
E93 — local G3 C-finish first return at 2(p+1)+41+2u.

The exact E68 G3 finishing C-mode path splits into:
(1) E90: 2(p+1) C01-middle steps, strictly safe;
(2) E92: 41+2u K41/C01-tail steps, strictly safe.
The shared full C configuration matches by a power-of-ones
rewrite already used in the existing E68 exact proof.
E80/E84 promote these to a first blank-left-C *within this
finishing segment*. No E60 full-checkpoint claim is made.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev E93Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev E93P := ([0, 1] : List (Fin 2))
private abbrev E93I := ([1] : List (Fin 2))
private abbrev E93D := ([1, 1] : List (Fin 2))

private abbrev e93Source (u p : ℕ) (R : E93Bits) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (push (E93P ^ p)
      (push [0] (push (E93P ^ (u + 6)) default)))
    (push [1, 1] R)

/-- The C01 middle's exact right tape has three leading ones,
then precisely 2p more ones: the K41 source frame. -/
private theorem e93_middle_right_seam (p : ℕ) (R : E93Bits) :
    push (E93D ^ (p + 1)) (push [1] R) =
      push [1, 1, 1] (push (E93I ^ (2 * p)) R) := by
  rw [one_pow_two_mul,
    show 2 * (p + 1) = 3 + 2 * p - 1 by omega]
  change push (E93I ^ (3 + 2 * p - 1))
    (push (E93I ^ 1) R) = _
  rw [← ListBlank.append_pow_add,
    show 3 + 2 * p - 1 + 1 = 3 + 2 * p by omega,
    ListBlank.append_pow_add E93I 3 (2 * p)]
  rfl

/-- All strictly earlier times of the complete G3 finishing
C-mode sequence avoid blank-left C. This statement keeps u,p,R
fully symbolic, and preserves the complete seam configuration. -/
theorem e93_G3_C_finish_noBlankLeftC_before
    (u p : ℕ) (R : E93Bits) :
    E80NoBlankLeftCBefore (e93Source u p R)
      (2 * (p + 1) + (41 + 2 * u)) := by
  have hMiddle := c01_middle_headRight_exact p
    (push (E93P ^ (u + 6)) (default : E93Bits))
    (push [1] R)
  have hSeam := e93_middle_right_seam p R
  rw [hSeam] at hMiddle
  have hMiddleSafe :
      E80NoBlankLeftCBefore (e93Source u p R)
        (2 * (p + 1)) :=
    e90_G3_C_finish_C01_middle_noBlankLeftC_before u p R
  have hTailSafe := e92_G3_K41_tail_noBlankLeftC_before
    u (push (E93I ^ (2 * p)) R)
  have hFull := e80_safe_trans hMiddle hMiddleSafe hTailSafe
  exact hFull

/-- At exactly 2(p+1)+41+2u raw steps the E68 G3 finishing source
first reaches a blank-left C configuration. This is local to the
guarded finishing configuration, not the full E60 source. -/
theorem e93_G3_C_finish_first_blankLeftC
    (u p : ℕ) (R : E93Bits) :
    (∃ Z : E93Bits, ReachesIn target
      (2 * (p + 1) + (41 + 2 * u))
      (e93Source u p R) (Cfg.headRight C default Z)) ∧
    (∀ t : ℕ, t < 2 * (p + 1) + (41 + 2 * u) →
      ∀ Z : E93Bits,
        ¬ ReachesIn target t (e93Source u p R)
          (Cfg.headRight C default Z)) := by
  exact e84_first_blankLeftC_criterion
    (e68_c_finish_exact u p R)
    ⟨_, rfl⟩
    (e93_G3_C_finish_noBlankLeftC_before u p R)

end CryptidLink.L17

#print axioms CryptidLink.L17.e93_G3_C_finish_noBlankLeftC_before
#print axioms CryptidLink.L17.e93_G3_C_finish_first_blankLeftC
