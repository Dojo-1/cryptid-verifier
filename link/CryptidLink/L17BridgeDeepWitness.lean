import CryptidLink.L17First26CGuard
import CryptidLink.L17FixedBridges

/-!
# E78 — fixed bridge safety needs a deeper left witness, not just head-one

The 77-step G1 bridge revisits C at step 71 with head-nearest left
word 0101. Its nearest-left bit is 0, but the *second* left bit is 1.
A C-free or head-one-only invariant would therefore be false.

The 95-step G3 bridge ends in C with precisely its arbitrary left
exterior L. Choosing L=default produces an actual blank-left C
endpoint at step 95. This is a formal counterexample to a theorem
claiming blank-left-C-free safety through the endpoint for *all* L.
The original E60 frame has a structured nonblank exterior, which
requires an additional proof at that boundary.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))

private theorem e78_noBlankLeft_of_second_one
    {c : Cfg (Fin 2) (Fin 6)}
    (hs : c.tape.left.tail.head = (1 : Fin 2)) :
    ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  have heq := congrArg
    (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.tail.head) hz
  have hz0 : (Cfg.headRight C (default : Bits) Z).tape.left.tail.head =
      (0 : Fin 2) := by rfl
  have absurdEq : (1 : Fin 2) = 0 := hs.symm.trans (heq.trans hz0)
  exact (by decide : (1 : Fin 2) ≠ 0) absurdEq

/-- G1's 71-step C revisit is NOT first-left-one, but is nonblank-left
because the *second* left tape symbol is 1. The arbitrary exterior
L,R is preserved in the exact full configuration. -/
theorem e78_one_bridge_C71_deep_witness (L R : Bits) :
    ∀ c : Cfg (Fin 2) (Fin 6),
      ReachesIn target 71
        (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1] L) (push [1, 1] R)) c →
      ¬ E76BlankLeftC c := by
  intro c hc
  have exact71 : ReachesIn target 71
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight C (push [0, 1, 0, 1] L)
        (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    set_option maxRecDepth 16384 in
      set_option maxHeartbeats 6000000 in
        l17_exact_steps
  have h : c = Cfg.headRight C (push [0, 1, 0, 1] L)
      (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R) :=
    Option.some.inj (hc.symm.trans exact71)
  subst c
  exact e78_noBlankLeft_of_second_one (by
    simp only [Cfg.headRight, ListBlank.append, ListBlank.tail_cons,
      ListBlank.head_cons])

/-- The G3 95-step bridge is NOT blank-left-C-free at its endpoint
over arbitrary exterior tapes. Specifically L=default is a real,
exact, machine-checked counterexample to that overstrong claim. -/
theorem e78_three_bridge_blankLeft_at95_if_left_exterior_blank (R : Bits) :
    ∃ c : Cfg (Fin 2) (Fin 6),
      ReachesIn target 95
        (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] (default : Bits))
          (push [1, 1] R)) c ∧
      E76BlankLeftC c := by
  let W : Bits := push [1, 1] (push (P ^ 21) (push [0] R))
  refine ⟨Cfg.headRight C default W, ?_, ?_⟩
  · exact e67_three_contextual_bridge_exact (default : Bits) R
  · exact ⟨W, rfl⟩

end CryptidLink.L17

#print axioms CryptidLink.L17.e78_one_bridge_C71_deep_witness
#print axioms CryptidLink.L17.e78_three_bridge_blankLeft_at95_if_left_exterior_blank
