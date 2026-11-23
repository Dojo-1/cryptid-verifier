import CryptidLink.L17BridgeBoundary

/-!
# E82 — universal no-blank-left C before the G3 fixed 95-step bridge exit

The G3 95-step exact bridge may reach a blank-left C endpoint when
L itself is blank (E78 counterexample). This theorem excludes such
returns only for the earlier range 0 <= t < 95, for arbitrary L/R.
The actual E60 structured boundary at t=95 is handled by E79.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev W3 : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1]

private theorem e82_transfer {source good actual : Cfg (Fin 2) (Fin 6)}
    {t : ℕ} (hg : ReachesIn target t source good)
    (hn : ¬ E76BlankLeftC good)
    (ha : ReachesIn target t source actual) :
    ¬ E76BlankLeftC actual := by
  have eq : actual = good := Option.some.inj (ha.symm.trans hg)
  simpa [eq] using hn

private theorem e82_noBlank_of_nonC {c : Cfg (Fin 2) (Fin 6)}
    (hn : c.q ≠ some C) : ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  apply hn
  rw [hz]
  rfl

private theorem e82_noBlank_of_leftOne {c : Cfg (Fin 2) (Fin 6)}
    (ho : c.tape.left.head = (1 : Fin 2)) :
    ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  have hzleft := congrArg
    (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.head) hz
  have hzero : (Cfg.headRight C (default : Bits) Z).tape.left.head =
      (0 : Fin 2) := by rfl
  exact (by decide : (1 : Fin 2) ≠ 0)
    (ho.symm.trans (hzleft.trans hzero))

private theorem e82_g3_at_0 (L R : Bits) :
    ReachesIn target 0
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R)) := by
  exact ReachesIn.zero target _

private theorem e82_g3_at_1 (L R : Bits) :
    ReachesIn target 1
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_0 L R).trans hstep

private theorem e82_g3_at_2 (L R : Bits) :
    ReachesIn target 2
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_1 L R).trans hstep

private theorem e82_g3_at_3 (L R : Bits) :
    ReachesIn target 3
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_2 L R).trans hstep

private theorem e82_g3_at_4 (L R : Bits) :
    ReachesIn target 4
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_3 L R).trans hstep

private theorem e82_g3_at_5 (L R : Bits) :
    ReachesIn target 5
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_4 L R).trans hstep

private theorem e82_g3_at_6 (L R : Bits) :
    ReachesIn target 6
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_5 L R).trans hstep

private theorem e82_g3_at_7 (L R : Bits) :
    ReachesIn target 7
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_6 L R).trans hstep

private theorem e82_g3_at_8 (L R : Bits) :
    ReachesIn target 8
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_7 L R).trans hstep

private theorem e82_g3_at_9 (L R : Bits) :
    ReachesIn target 9
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_8 L R).trans hstep

private theorem e82_g3_at_10 (L R : Bits) :
    ReachesIn target 10
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_9 L R).trans hstep

private theorem e82_g3_at_11 (L R : Bits) :
    ReachesIn target 11
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_10 L R).trans hstep

private theorem e82_g3_at_12 (L R : Bits) :
    ReachesIn target 12
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_11 L R).trans hstep

private theorem e82_g3_at_13 (L R : Bits) :
    ReachesIn target 13
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_12 L R).trans hstep

private theorem e82_g3_at_14 (L R : Bits) :
    ReachesIn target 14
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_13 L R).trans hstep

private theorem e82_g3_at_15 (L R : Bits) :
    ReachesIn target 15
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_14 L R).trans hstep

private theorem e82_g3_at_16 (L R : Bits) :
    ReachesIn target 16
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_15 L R).trans hstep

private theorem e82_g3_at_17 (L R : Bits) :
    ReachesIn target 17
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight C (push [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R))
      (Cfg.headRight C (push [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_16 L R).trans hstep

private theorem e82_g3_at_18 (L R : Bits) :
    ReachesIn target 18
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_17 L R).trans hstep

private theorem e82_g3_at_19 (L R : Bits) :
    ReachesIn target 19
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_18 L R).trans hstep

private theorem e82_g3_at_20 (L R : Bits) :
    ReachesIn target 20
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_19 L R).trans hstep

private theorem e82_g3_at_21 (L R : Bits) :
    ReachesIn target 21
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_20 L R).trans hstep

private theorem e82_g3_at_22 (L R : Bits) :
    ReachesIn target 22
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_21 L R).trans hstep

private theorem e82_g3_at_23 (L R : Bits) :
    ReachesIn target 23
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_22 L R).trans hstep

private theorem e82_g3_at_24 (L R : Bits) :
    ReachesIn target 24
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_23 L R).trans hstep

private theorem e82_g3_at_25 (L R : Bits) :
    ReachesIn target 25
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_24 L R).trans hstep

private theorem e82_g3_at_26 (L R : Bits) :
    ReachesIn target 26
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_25 L R).trans hstep

private theorem e82_g3_at_27 (L R : Bits) :
    ReachesIn target 27
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_26 L R).trans hstep

private theorem e82_g3_at_28 (L R : Bits) :
    ReachesIn target 28
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_27 L R).trans hstep

private theorem e82_g3_at_29 (L R : Bits) :
    ReachesIn target 29
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_28 L R).trans hstep

private theorem e82_g3_at_30 (L R : Bits) :
    ReachesIn target 30
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_29 L R).trans hstep

private theorem e82_g3_at_31 (L R : Bits) :
    ReachesIn target 31
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_30 L R).trans hstep

private theorem e82_g3_at_32 (L R : Bits) :
    ReachesIn target 32
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_31 L R).trans hstep

private theorem e82_g3_at_33 (L R : Bits) :
    ReachesIn target 33
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_32 L R).trans hstep

private theorem e82_g3_at_34 (L R : Bits) :
    ReachesIn target 34
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_33 L R).trans hstep

private theorem e82_g3_at_35 (L R : Bits) :
    ReachesIn target 35
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_34 L R).trans hstep

private theorem e82_g3_at_36 (L R : Bits) :
    ReachesIn target 36
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_35 L R).trans hstep

private theorem e82_g3_at_37 (L R : Bits) :
    ReachesIn target 37
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_36 L R).trans hstep

private theorem e82_g3_at_38 (L R : Bits) :
    ReachesIn target 38
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_37 L R).trans hstep

private theorem e82_g3_at_39 (L R : Bits) :
    ReachesIn target 39
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_38 L R).trans hstep

private theorem e82_g3_at_40 (L R : Bits) :
    ReachesIn target 40
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_39 L R).trans hstep

private theorem e82_g3_at_41 (L R : Bits) :
    ReachesIn target 41
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_40 L R).trans hstep

private theorem e82_g3_at_42 (L R : Bits) :
    ReachesIn target 42
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_41 L R).trans hstep

private theorem e82_g3_at_43 (L R : Bits) :
    ReachesIn target 43
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_42 L R).trans hstep

private theorem e82_g3_at_44 (L R : Bits) :
    ReachesIn target 44
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_43 L R).trans hstep

private theorem e82_g3_at_45 (L R : Bits) :
    ReachesIn target 45
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_44 L R).trans hstep

private theorem e82_g3_at_46 (L R : Bits) :
    ReachesIn target 46
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_45 L R).trans hstep

private theorem e82_g3_at_47 (L R : Bits) :
    ReachesIn target 47
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_46 L R).trans hstep

private theorem e82_g3_at_48 (L R : Bits) :
    ReachesIn target 48
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_47 L R).trans hstep

private theorem e82_g3_at_49 (L R : Bits) :
    ReachesIn target 49
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_48 L R).trans hstep

private theorem e82_g3_at_50 (L R : Bits) :
    ReachesIn target 50
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_49 L R).trans hstep

private theorem e82_g3_at_51 (L R : Bits) :
    ReachesIn target 51
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_50 L R).trans hstep

private theorem e82_g3_at_52 (L R : Bits) :
    ReachesIn target 52
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_51 L R).trans hstep

private theorem e82_g3_at_53 (L R : Bits) :
    ReachesIn target 53
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_52 L R).trans hstep

private theorem e82_g3_at_54 (L R : Bits) :
    ReachesIn target 54
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_53 L R).trans hstep

private theorem e82_g3_at_55 (L R : Bits) :
    ReachesIn target 55
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_54 L R).trans hstep

private theorem e82_g3_at_56 (L R : Bits) :
    ReachesIn target 56
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_55 L R).trans hstep

private theorem e82_g3_at_57 (L R : Bits) :
    ReachesIn target 57
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_56 L R).trans hstep

private theorem e82_g3_at_58 (L R : Bits) :
    ReachesIn target 58
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_57 L R).trans hstep

private theorem e82_g3_at_59 (L R : Bits) :
    ReachesIn target 59
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_58 L R).trans hstep

private theorem e82_g3_at_60 (L R : Bits) :
    ReachesIn target 60
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_59 L R).trans hstep

private theorem e82_g3_at_61 (L R : Bits) :
    ReachesIn target 61
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_60 L R).trans hstep

private theorem e82_g3_at_62 (L R : Bits) :
    ReachesIn target 62
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_61 L R).trans hstep

private theorem e82_g3_at_63 (L R : Bits) :
    ReachesIn target 63
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_62 L R).trans hstep

private theorem e82_g3_at_64 (L R : Bits) :
    ReachesIn target 64
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_63 L R).trans hstep

private theorem e82_g3_at_65 (L R : Bits) :
    ReachesIn target 65
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_64 L R).trans hstep

private theorem e82_g3_at_66 (L R : Bits) :
    ReachesIn target 66
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_65 L R).trans hstep

private theorem e82_g3_at_67 (L R : Bits) :
    ReachesIn target 67
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_66 L R).trans hstep

private theorem e82_g3_at_68 (L R : Bits) :
    ReachesIn target 68
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_67 L R).trans hstep

private theorem e82_g3_at_69 (L R : Bits) :
    ReachesIn target 69
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_68 L R).trans hstep

private theorem e82_g3_at_70 (L R : Bits) :
    ReachesIn target 70
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_69 L R).trans hstep

private theorem e82_g3_at_71 (L R : Bits) :
    ReachesIn target 71
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_70 L R).trans hstep

private theorem e82_g3_at_72 (L R : Bits) :
    ReachesIn target 72
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_71 L R).trans hstep

private theorem e82_g3_at_73 (L R : Bits) :
    ReachesIn target 73
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_72 L R).trans hstep

private theorem e82_g3_at_74 (L R : Bits) :
    ReachesIn target 74
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_73 L R).trans hstep

private theorem e82_g3_at_75 (L R : Bits) :
    ReachesIn target 75
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_74 L R).trans hstep

private theorem e82_g3_at_76 (L R : Bits) :
    ReachesIn target 76
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_75 L R).trans hstep

private theorem e82_g3_at_77 (L R : Bits) :
    ReachesIn target 77
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_76 L R).trans hstep

private theorem e82_g3_at_78 (L R : Bits) :
    ReachesIn target 78
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_77 L R).trans hstep

private theorem e82_g3_at_79 (L R : Bits) :
    ReachesIn target 79
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_78 L R).trans hstep

private theorem e82_g3_at_80 (L R : Bits) :
    ReachesIn target 80
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_79 L R).trans hstep

private theorem e82_g3_at_81 (L R : Bits) :
    ReachesIn target 81
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_80 L R).trans hstep

private theorem e82_g3_at_82 (L R : Bits) :
    ReachesIn target 82
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_81 L R).trans hstep

private theorem e82_g3_at_83 (L R : Bits) :
    ReachesIn target 83
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_82 L R).trans hstep

private theorem e82_g3_at_84 (L R : Bits) :
    ReachesIn target 84
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_83 L R).trans hstep

private theorem e82_g3_at_85 (L R : Bits) :
    ReachesIn target 85
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_84 L R).trans hstep

private theorem e82_g3_at_86 (L R : Bits) :
    ReachesIn target 86
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_85 L R).trans hstep

private theorem e82_g3_at_87 (L R : Bits) :
    ReachesIn target 87
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_86 L R).trans hstep

private theorem e82_g3_at_88 (L R : Bits) :
    ReachesIn target 88
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_87 L R).trans hstep

private theorem e82_g3_at_89 (L R : Bits) :
    ReachesIn target 89
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_88 L R).trans hstep

private theorem e82_g3_at_90 (L R : Bits) :
    ReachesIn target 90
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_89 L R).trans hstep

private theorem e82_g3_at_91 (L R : Bits) :
    ReachesIn target 91
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_90 L R).trans hstep

private theorem e82_g3_at_92 (L R : Bits) :
    ReachesIn target 92
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_91 L R).trans hstep

private theorem e82_g3_at_93 (L R : Bits) :
    ReachesIn target 93
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_92 L R).trans hstep

private theorem e82_g3_at_94 (L R : Bits) :
    ReachesIn target 94
      (Cfg.headRight A (push W3 L) (push [1, 1] R))
      (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e82_g3_at_93 L R).trans hstep

private theorem e82_safe_0_20 (L R : Bits) :
    ∀ t : ℕ, 0 ≤ t → t < 20 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight A (push W3 L) (push [1, 1] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · subst t
    exact e82_transfer (e82_g3_at_0 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_1 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_2 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_3 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_4 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_5 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_6 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_7 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_8 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_9 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_10 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_11 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_12 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_13 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_14 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_15 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_16 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_17 L R) (e82_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e82_transfer (e82_g3_at_18 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_19 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc

private theorem e82_safe_20_40 (L R : Bits) :
    ∀ t : ℕ, 20 ≤ t → t < 40 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight A (push W3 L) (push [1, 1] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 ∨ t = 31 ∨ t = 32 ∨ t = 33 ∨ t = 34 ∨ t = 35 ∨ t = 36 ∨ t = 37 ∨ t = 38 ∨ t = 39 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · subst t
    exact e82_transfer (e82_g3_at_20 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_21 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_22 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_23 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_24 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_25 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_26 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_27 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_28 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_29 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_30 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_31 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_32 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_33 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_34 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_35 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_36 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_37 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_38 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_39 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc

private theorem e82_safe_40_60 (L R : Bits) :
    ∀ t : ℕ, 40 ≤ t → t < 60 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight A (push W3 L) (push [1, 1] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 40 ∨ t = 41 ∨ t = 42 ∨ t = 43 ∨ t = 44 ∨ t = 45 ∨ t = 46 ∨ t = 47 ∨ t = 48 ∨ t = 49 ∨ t = 50 ∨ t = 51 ∨ t = 52 ∨ t = 53 ∨ t = 54 ∨ t = 55 ∨ t = 56 ∨ t = 57 ∨ t = 58 ∨ t = 59 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · subst t
    exact e82_transfer (e82_g3_at_40 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_41 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_42 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_43 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_44 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_45 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_46 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_47 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_48 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_49 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_50 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_51 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_52 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_53 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_54 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_55 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_56 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_57 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_58 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_59 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc

private theorem e82_safe_60_80 (L R : Bits) :
    ∀ t : ℕ, 60 ≤ t → t < 80 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight A (push W3 L) (push [1, 1] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 60 ∨ t = 61 ∨ t = 62 ∨ t = 63 ∨ t = 64 ∨ t = 65 ∨ t = 66 ∨ t = 67 ∨ t = 68 ∨ t = 69 ∨ t = 70 ∨ t = 71 ∨ t = 72 ∨ t = 73 ∨ t = 74 ∨ t = 75 ∨ t = 76 ∨ t = 77 ∨ t = 78 ∨ t = 79 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · subst t
    exact e82_transfer (e82_g3_at_60 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_61 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_62 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_63 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_64 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_65 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_66 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_67 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_68 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_69 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_70 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_71 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_72 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_73 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_74 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_75 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_76 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_77 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_78 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_79 L R) (e82_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc

private theorem e82_safe_80_95 (L R : Bits) :
    ∀ t : ℕ, 80 ≤ t → t < 95 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight A (push W3 L) (push [1, 1] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 80 ∨ t = 81 ∨ t = 82 ∨ t = 83 ∨ t = 84 ∨ t = 85 ∨ t = 86 ∨ t = 87 ∨ t = 88 ∨ t = 89 ∨ t = 90 ∨ t = 91 ∨ t = 92 ∨ t = 93 ∨ t = 94 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · subst t
    exact e82_transfer (e82_g3_at_80 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_81 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_82 L R) (e82_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_83 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_84 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_85 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_86 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_87 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_88 L R) (e82_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_89 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_90 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_91 L R) (e82_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e82_transfer (e82_g3_at_92 L R) (e82_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_93 L R) (e82_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e82_transfer (e82_g3_at_94 L R) (e82_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc

/-- Every G3 bridge timestamp before its 95-step C endpoint avoids
blank-left C, even with arbitrary left and right exterior tapes. -/
theorem e82_G3_bridge_noBlankLeftC_before95 (L R : Bits) :
    ∀ t : ℕ, t < 95 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t
          (Cfg.headRight A (push W3 L) (push [1, 1] R)) c →
        ¬ E76BlankLeftC c := by
  intro t ht c hc
  by_cases h0 : t < 20
  · exact e82_safe_0_20 L R t (by omega) h0 c hc
  · by_cases h1 : t < 40
    · exact e82_safe_20_40 L R t (by omega) h1 c hc
    · by_cases h2 : t < 60
      · exact e82_safe_40_60 L R t (by omega) h2 c hc
      · by_cases h3 : t < 80
        · exact e82_safe_60_80 L R t (by omega) h3 c hc
        · exact e82_safe_80_95 L R t (by omega) ht c hc

end CryptidLink.L17
#print axioms CryptidLink.L17.e82_G3_bridge_noBlankLeftC_before95
