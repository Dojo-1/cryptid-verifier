import CryptidLink.L17NoCWindow
import CryptidLink.L17First26CGuard

/-!
# E83 — the variable 4p sweep of the G1 final A unwind contains no C

The previously certified E73 sweep has right prefix 11. The actual
G1 final A unwind has 111. Its third bit belongs to the arbitrary
right exterior, so there is no new machine simulation obligation.
The fixed 25-step finish and the later 2(u+2)-step C sweep remain
separate first-return safety obligations.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))

private abbrev e83_left (u : ℕ) : Bits :=
  push [0] (push (P ^ (u + 6)) default)

/-- Every intermediate control state in the parameterized 4p prefix of
the G1 final unwind is not C. Both p and u are arbitrary naturals;
the right exterior is an arbitrary half-tape. -/
theorem e83_G1_unwind_A_prefix_C_free (u p : ℕ) (R : Bits) :
    E73NoCBefore
      (Cfg.headRight A (push (P ^ p) (e83_left u))
        (push [1, 1, 1] R))
      (4 * p) := by
  have h := e73_all_pair_sweeps_C_free p (e83_left u) (push [1] R)
  change E73NoCBefore
    (Cfg.headRight A (push (P ^ p) (e83_left u))
      (push [1, 1, 1] R)) (4 * p) at h
  exact h

/-- Hence no early blank-left C can occur in the variable 4p sweep;
the remaining 25+2(u+2) finish must be checked separately. -/
theorem e83_G1_unwind_A_prefix_noBlankLeftC (u p : ℕ) (R : Bits) :
    ∀ t : ℕ, t < 4 * p →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight A (push (P ^ p) (e83_left u))
            (push [1, 1, 1] R)) c →
        ¬ E76BlankLeftC c := by
  intro t ht c hc
  have hnot := (e83_G1_unwind_A_prefix_C_free u p R) t ht c hc
  rintro ⟨Z, hz⟩
  apply hnot
  rw [hz]
  rfl

end CryptidLink.L17

#print axioms CryptidLink.L17.e83_G1_unwind_A_prefix_C_free
#print axioms CryptidLink.L17.e83_G1_unwind_A_prefix_noBlankLeftC
