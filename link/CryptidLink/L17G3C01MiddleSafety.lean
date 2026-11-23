import CryptidLink.L17G3StructuredBridgeSafety
import CryptidLink.L17CSweepSentinelSafety

/-!
E90 — G3 C-mode middle: no early blank-left C for an arbitrary
number of C01 pairs, provided the residual left tape has a 1
in its second cell. The actual E68 G3 finishing geometry supplies
that witness: (01)^(u+6) ++ blank.

The theorem excludes all strictly preterminal times of the
2(p+1)-step middle. The later fixed K41short 41-step core and
final 2u C sweep are NOT yet covered.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev E90Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev E90P := ([0, 1] : List (Fin 2))
private abbrev E90Q := ([1, 0] : List (Fin 2))

/-- A final two-step C/B/C pair is preterminally safe if the
farther-left residual tape has a 1 in its second cell.
For this case, inspecting only its first cell would be insufficient. -/
private theorem e90_last_pair_two_deep (L R : E90Bits)
    (hL : L.tail.head = (1 : Fin 2)) :
    E80NoBlankLeftCBefore
      (Cfg.headLeft C (push E90Q L) R) 2 := by
  let s : Cfg (Fin 2) (Fin 6) :=
    Cfg.headLeft C (push E90Q L) R
  have h0 : ReachesIn target 0 s s := ReachesIn.zero target s
  have h1 : ReachesIn target 1 s
      (Cfg.headLeft B (push [0] L) (push [1] R)) := by
    dsimp only [s, E90Q]
    l17_exact_steps
  intro t ht c hc
  change ReachesIn target t s c at hc
  rcases (show t = 0 ∨ t = 1 by omega) with hzero | hone
  · subst t
    have heq : c = s := Option.some.inj (hc.symm.trans h0)
    subst c
    rintro ⟨Z, hz⟩
    have hframe : s =
        Cfg.headRight C (push [0] L) (push [1] R) := by
      dsimp only [s, E90Q]
      exact Cfg.headLeft_cons C (1 : Fin 2) (push [0] L) R
    have hw : s.tape.left.tail.tail.head = (1 : Fin 2) := by
      rw [hframe]
      simpa only [Cfg.headRight, ListBlank.append,
        ListBlank.tail_cons, ListBlank.head_cons] using hL
    have hz0 :
        (Cfg.headRight C (default : E90Bits) Z).tape.left.tail.tail.head =
        (0 : Fin 2) := by rfl
    have heqLeft := congrArg
      (fun cfg : Cfg (Fin 2) (Fin 6) =>
        cfg.tape.left.tail.tail.head) hz
    exact (by decide : (1 : Fin 2) ≠ 0)
      (hw.symm.trans (heqLeft.trans hz0))
  · subst t
    have heq :
        c = Cfg.headLeft B (push [0] L) (push [1] R) :=
      Option.some.inj (hc.symm.trans h1)
    subst c
    rintro ⟨Z, hz⟩
    have hq := congrArg
      (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.q) hz
    change (some B : Option (Fin 6)) = some C at hq
    exact (by decide : (some B : Option (Fin 6)) ≠ some C) hq

/-- The entire C01 middle interval is strictly first-return safe
whenever the untouched left remainder has a one in its second cell.
The right exterior is arbitrary. This is NOT a no-C statement:
control C occurs at even intermediate clocks. -/
theorem e90_C01_middle_twoDeep_safe
    (p : ℕ) (L R : E90Bits)
    (hL : L.tail.head = (1 : Fin 2)) :
    E80NoBlankLeftCBefore
      (Cfg.headRight C
        (push (E90P ^ p) (push [0] L)) (push [1] R))
      (2 * (p + 1)) := by
  have hframe :
      Cfg.headRight C
        (push (E90P ^ p) (push [0] L)) (push [1] R) =
      Cfg.headLeft C (push (E90Q ^ (p + 1)) L) R := by
    have hrot :
        push [1] (push (E90P ^ p) (push [0] L)) =
        push (E90Q ^ (p + 1)) L := by
      rw [rotLB, ← ListBlank.append_pow_succ' E90Q p L]
      rfl
    calc
      _ = Cfg.headLeft C
          (push [1] (push (E90P ^ p) (push [0] L))) R :=
        Cfg.headRight_cons C (1 : Fin 2) _ R
      _ = _ := by rw [hrot]
  have hpower :
      push (E90Q ^ (p + 1)) L =
      push (E90Q ^ p) (push E90Q L) := by
    rw [ListBlank.append_pow_succ' E90Q p L]
  have hfirst :
      E80NoBlankLeftCBefore
        (Cfg.headLeft C
          (push (E90Q ^ p) (push E90Q L)) R) (2 * p) :=
    e85_C01_sweep_sentinel_safe p (push E90Q L) R
      (by simp only [E90Q, ListBlank.append, ListBlank.head_cons])
  have hpath := c01_sweep_exact p (push E90Q L) R
  have hlast := e90_last_pair_two_deep L
    (push (([1, 1] : List (Fin 2)) ^ p) R) hL
  have htotal := e80_safe_trans hpath hfirst hlast
  rw [hframe, hpower]
  convert htotal using 1 <;> omega

/-- Every (01)^(u+6) stack retains a one in its second left cell. -/
private theorem e90_G3_residual_witness (u : ℕ) :
    (push (E90P ^ (u + 6)) (default : E90Bits)).tail.head =
      (1 : Fin 2) := by
  have hsplit :
      push (E90P ^ (u + 6)) (default : E90Bits) =
      push E90P (push (E90P ^ (u + 5)) default) := by
    rw [show u + 6 = 1 + (u + 5) by omega,
      ListBlank.append_pow_add E90P 1 (u + 5) (default : E90Bits)]
    rfl
  rw [hsplit]
  simp only [E90P, ListBlank.append,
    ListBlank.tail_cons, ListBlank.head_cons]

/-- Exact safety of the 2(p+1)-step C01 middle at the start of
the canonical E68 G3 C finish, for any p,u and full right exterior. -/
theorem e90_G3_C_finish_C01_middle_noBlankLeftC_before
    (u p : ℕ) (R : E90Bits) :
    E80NoBlankLeftCBefore
      (Cfg.headRight C
        (push (E90P ^ p)
          (push [0] (push (E90P ^ (u + 6)) default)))
        (push [1] (push [1] R)))
      (2 * (p + 1)) := by
  exact e90_C01_middle_twoDeep_safe p
    (push (E90P ^ (u + 6)) default)
    (push [1] R)
    (e90_G3_residual_witness u)

end CryptidLink.L17

#print axioms CryptidLink.L17.e90_C01_middle_twoDeep_safe
#print axioms CryptidLink.L17.e90_G3_C_finish_C01_middle_noBlankLeftC_before
