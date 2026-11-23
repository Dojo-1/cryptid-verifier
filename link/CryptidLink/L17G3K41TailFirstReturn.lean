import CryptidLink.L17K41shortSafety
import CryptidLink.L17CSweepSentinelSafety
import CryptidLink.L17s

/-!
E92 — complete 41+2u K41/C01 tail of the G3 finishing path.

K41short has no blank-left C at t<41 (E91), although the
t=41 endpoint has arbitrary left exterior. In the actual E68
outermost G3 finish, this exterior is (01)^u ++ blank:
  * for u=0 it is blank and the clock 41 is terminal;
  * for u>0 it is nonblank and C01 consumes u alternating pairs
    against the invariant nonzero sentinel [1] before blank.

Exact K41 path + strict safety + exact C01 path + E85 strict
safety + E80/E84 yield first blank-left C at 41+2u.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev E92Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev E92P := ([0, 1] : List (Fin 2))
private abbrev E92Q := ([1, 0] : List (Fin 2))
private abbrev E92I := ([1, 1] : List (Fin 2))
private abbrev E92tail : List (Fin 2) :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

private abbrev e92Source (u : ℕ) (R : E92Bits) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C (push (E92P ^ (u + 6)) default) (push [1, 1, 1] R)

/-- A literal K41short full-config source rewrite: the headLeft C
on the rightmost zero of (01)^(u+6) is the fixed K41 C source. -/
private theorem e92_source_frame (u : ℕ) (R : E92Bits) :
    e92Source u R =
    Cfg.headRight C
      (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
        (push (E92P ^ u) (default : E92Bits)))
      (push [0, 1, 1, 1] R) := by
  unfold e92Source
  rw [show u + 6 = 6 + u by omega,
    ListBlank.append_pow_add E92P 6 u (default : E92Bits)]
  exact Cfg.headLeft_cons C (0 : Fin 2) _ _

/-- Exact 41-step K41 transfer into a left-directed C01 sweep,
with both boundary tapes retained. -/
private theorem e92_K41_frame_exact (u : ℕ) (R : E92Bits) :
    ReachesIn target 41 (e92Source u R)
      (Cfg.headLeft C
        (push (E92Q ^ u) (push [1] (default : E92Bits)))
        (push E92tail R)) := by
  let X : E92Bits := push (E92P ^ u) (default : E92Bits)
  have hK := e91_K41short_exact X R
  have hs := e92_source_frame u R
  change e92Source u R = Cfg.headRight C
    (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] X)
    (push [0, 1, 1, 1] R) at hs
  rw [← hs] at hK
  have hrot : push [1] X =
      push (E92Q ^ u) (push [1] (default : E92Bits)) :=
    rotLB u (default : E92Bits)
  have hf :
      Cfg.headRight C X
        (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R) =
      Cfg.headLeft C
        (push (E92Q ^ u) (push [1] (default : E92Bits)))
        (push E92tail R) := by
    rw [← hrot]
    exact Cfg.headRight_cons C (1 : Fin 2) X (push E92tail R)
  rw [hf] at hK
  exact hK

/-- E91 strict safety transported across the exact source frame. -/
private theorem e92_K41_frame_safe (u : ℕ) (R : E92Bits) :
    E80NoBlankLeftCBefore (e92Source u R) 41 := by
  have h := e91_K41short_noBlankLeftC_before41
    (push (E92P ^ u) (default : E92Bits)) R
  rw [e92_source_frame u R]
  exact h

/-- The full G3 tail, including arbitrary u=0, has no earlier
blank-left C before raw clock 41+2u. -/
theorem e92_G3_K41_tail_noBlankLeftC_before
    (u : ℕ) (R : E92Bits) :
    E80NoBlankLeftCBefore (e92Source u R) (41 + 2 * u) := by
  have hK := e92_K41_frame_exact u R
  have hKsafe := e92_K41_frame_safe u R
  have hSweepSafe := e85_C01_sweep_sentinel_safe u
    (push [1] (default : E92Bits)) (push E92tail R)
    (by rfl)
  exact e80_safe_trans hK hKsafe hSweepSafe

/-- The exact terminal C state is blank-left and its clock is the
first such visit for this G3 K41/C01 tail. This is a local result,
not a full E60 first return. -/
theorem e92_G3_K41_tail_first_blankLeftC
    (u : ℕ) (R : E92Bits) :
    (∃ Z : E92Bits, ReachesIn target (41 + 2 * u)
      (e92Source u R) (Cfg.headRight C default Z)) ∧
    (∀ t : ℕ, t < 41 + 2 * u →
      ∀ Z : E92Bits,
        ¬ ReachesIn target t (e92Source u R)
          (Cfg.headRight C default Z)) := by
  have hK := e92_K41_frame_exact u R
  have hSweep := c01_sweep_exact u
    (push [1] (default : E92Bits)) (push E92tail R)
  have hret := hK.trans hSweep
  have hframe :
      Cfg.headLeft C (push [1] (default : E92Bits))
        (push (E92I ^ u) (push E92tail R)) =
      Cfg.headRight C default
        (push [1] (push (E92I ^ u) (push E92tail R))) :=
    Cfg.headLeft_cons C (1 : Fin 2) default _
  rw [hframe] at hret
  exact e84_first_blankLeftC_criterion hret ⟨_, rfl⟩
    (e92_G3_K41_tail_noBlankLeftC_before u R)

end CryptidLink.L17

#print axioms CryptidLink.L17.e92_G3_K41_tail_noBlankLeftC_before
#print axioms CryptidLink.L17.e92_G3_K41_tail_first_blankLeftC
