import CryptidLink.L17G3C01MiddleSafety
import CryptidLink.L17FirstReturnSafety
import CryptidLink.L17r

/-!
E91 — every preterminal C visit of K41short retains a left-hand one.

The 41-step fixed K41 kernel reaches C with arbitrary left exterior L
at time 41. At times 0,25,37 it visits C with nearest-left bit 1;
all other preterminal control states are not C. Thus no blank-left C
occurs for t<41, while t=41 with blank L is a real counterexample to
inclusive or unrestricted endpoint-safety claims.

Each of the 42 exact full configurations is separately certified
by one-step L17 machine transitions. Arbitrary L,R remain symbolic.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev E91Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _

private theorem e91_transfer
    {source good actual : Cfg (Fin 2) (Fin 6)} {t : ℕ}
    (hg : ReachesIn target t source good)
    (hn : ¬ E76BlankLeftC good)
    (ha : ReachesIn target t source actual) :
    ¬ E76BlankLeftC actual := by
  have heq : actual = good := Option.some.inj (ha.symm.trans hg)
  simpa [heq] using hn

private theorem e91_noBlank_of_nonC {c : Cfg (Fin 2) (Fin 6)}
    (hn : c.q ≠ some C) : ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  apply hn
  rw [hz]
  rfl

private theorem e91_noBlank_of_leftOne {c : Cfg (Fin 2) (Fin 6)}
    (ho : c.tape.left.head = (1 : Fin 2)) :
    ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  have h := congrArg
    (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.head) hz
  have hz0 :
      (Cfg.headRight C (default : E91Bits) Z).tape.left.head =
      (0 : Fin 2) := by rfl
  exact (by decide : (1 : Fin 2) ≠ 0) (ho.symm.trans (h.trans hz0))

private theorem e91_at_0 (L R : E91Bits) :
    ReachesIn target 0 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) := by
  exact ReachesIn.zero target _

private theorem e91_at_1 (L R : E91Bits) :
    ReachesIn target 1 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_0 L R).trans hstep

private theorem e91_at_2 (L R : E91Bits) :
    ReachesIn target 2 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 1, 1] R)) (Cfg.headRight E (push [1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_1 L R).trans hstep

private theorem e91_at_3 (L R : E91Bits) :
    ReachesIn target 3 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 1, 1] R)) (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_2 L R).trans hstep

private theorem e91_at_4 (L R : E91Bits) :
    ReachesIn target 4 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_3 L R).trans hstep

private theorem e91_at_5 (L R : E91Bits) :
    ReachesIn target 5 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 1, 1] R)) (Cfg.headRight B (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_4 L R).trans hstep

private theorem e91_at_6 (L R : E91Bits) :
    ReachesIn target 6 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_5 L R).trans hstep

private theorem e91_at_7 (L R : E91Bits) :
    ReachesIn target 7 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_6 L R).trans hstep

private theorem e91_at_8 (L R : E91Bits) :
    ReachesIn target 8 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1] R)) (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_7 L R).trans hstep

private theorem e91_at_9 (L R : E91Bits) :
    ReachesIn target 9 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R)) (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_8 L R).trans hstep

private theorem e91_at_10 (L R : E91Bits) :
    ReachesIn target 10 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R)) (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_9 L R).trans hstep

private theorem e91_at_11 (L R : E91Bits) :
    ReachesIn target 11 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_10 L R).trans hstep

private theorem e91_at_12 (L R : E91Bits) :
    ReachesIn target 12 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_11 L R).trans hstep

private theorem e91_at_13 (L R : E91Bits) :
    ReachesIn target 13 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0] R)) (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_12 L R).trans hstep

private theorem e91_at_14 (L R : E91Bits) :
    ReachesIn target 14 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R)) (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_13 L R).trans hstep

private theorem e91_at_15 (L R : E91Bits) :
    ReachesIn target 15 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0] R)) (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_14 L R).trans hstep

private theorem e91_at_16 (L R : E91Bits) :
    ReachesIn target 16 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_15 L R).trans hstep

private theorem e91_at_17 (L R : E91Bits) :
    ReachesIn target 17 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 1, 0, 1, 0] R)) (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_16 L R).trans hstep

private theorem e91_at_18 (L R : E91Bits) :
    ReachesIn target 18 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R)) (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_17 L R).trans hstep

private theorem e91_at_19 (L R : E91Bits) :
    ReachesIn target 19 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_18 L R).trans hstep

private theorem e91_at_20 (L R : E91Bits) :
    ReachesIn target 20 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_19 L R).trans hstep

private theorem e91_at_21 (L R : E91Bits) :
    ReachesIn target 21 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_20 L R).trans hstep

private theorem e91_at_22 (L R : E91Bits) :
    ReachesIn target 22 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_21 L R).trans hstep

private theorem e91_at_23 (L R : E91Bits) :
    ReachesIn target 23 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R)) (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_22 L R).trans hstep

private theorem e91_at_24 (L R : E91Bits) :
    ReachesIn target 24 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0] R)) (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_23 L R).trans hstep

private theorem e91_at_25 (L R : E91Bits) :
    ReachesIn target 25 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_24 L R).trans hstep

private theorem e91_at_26 (L R : E91Bits) :
    ReachesIn target 26 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_25 L R).trans hstep

private theorem e91_at_27 (L R : E91Bits) :
    ReachesIn target 27 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_26 L R).trans hstep

private theorem e91_at_28 (L R : E91Bits) :
    ReachesIn target 28 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_27 L R).trans hstep

private theorem e91_at_29 (L R : E91Bits) :
    ReachesIn target 29 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_28 L R).trans hstep

private theorem e91_at_30 (L R : E91Bits) :
    ReachesIn target 30 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_29 L R).trans hstep

private theorem e91_at_31 (L R : E91Bits) :
    ReachesIn target 31 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_30 L R).trans hstep

private theorem e91_at_32 (L R : E91Bits) :
    ReachesIn target 32 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_31 L R).trans hstep

private theorem e91_at_33 (L R : E91Bits) :
    ReachesIn target 33 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_32 L R).trans hstep

private theorem e91_at_34 (L R : E91Bits) :
    ReachesIn target 34 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_33 L R).trans hstep

private theorem e91_at_35 (L R : E91Bits) :
    ReachesIn target 35 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_34 L R).trans hstep

private theorem e91_at_36 (L R : E91Bits) :
    ReachesIn target 36 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_35 L R).trans hstep

private theorem e91_at_37 (L R : E91Bits) :
    ReachesIn target 37 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_36 L R).trans hstep

private theorem e91_at_38 (L R : E91Bits) :
    ReachesIn target 38 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_37 L R).trans hstep

private theorem e91_at_39 (L R : E91Bits) :
    ReachesIn target 39 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_38 L R).trans hstep

private theorem e91_at_40 (L R : E91Bits) :
    ReachesIn target 40 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_39 L R).trans hstep

private theorem e91_at_41 (L R : E91Bits) :
    ReachesIn target 41 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e91_at_40 L R).trans hstep

/-- Exact full-configuration 41-step result, with unmodified
symbolic left and right exteriors. -/
theorem e91_K41short_exact (L R : E91Bits) :
    ReachesIn target 41 (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) :=
  e91_at_41 L R

/-- No configuration before the strict 41-step K41 endpoint can be
blank-left C, for any symbolic left and right exteriors. -/
theorem e91_K41short_noBlankLeftC_before41 (L R : E91Bits) :
    E80NoBlankLeftCBefore (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 1] R)) 41 := by
  intro t ht c hc
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 ∨ t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 ∨ t = 31 ∨ t = 32 ∨ t = 33 ∨ t = 34 ∨ t = 35 ∨ t = 36 ∨ t = 37 ∨ t = 38 ∨ t = 39 ∨ t = 40 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · subst t
    exact e91_transfer (e91_at_0 L R)
      (e91_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e91_transfer (e91_at_1 L R)
      (e91_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_2 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_3 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_4 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_5 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_6 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_7 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_8 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_9 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_10 L R)
      (e91_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_11 L R)
      (e91_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_12 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_13 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_14 L R)
      (e91_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_15 L R)
      (e91_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_16 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_17 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_18 L R)
      (e91_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_19 L R)
      (e91_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_20 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_21 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_22 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_23 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_24 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_25 L R)
      (e91_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e91_transfer (e91_at_26 L R)
      (e91_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_27 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_28 L R)
      (e91_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_29 L R)
      (e91_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_30 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_31 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_32 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_33 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_34 L R)
      (e91_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_35 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_36 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_37 L R)
      (e91_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e91_transfer (e91_at_38 L R)
      (e91_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_39 L R)
      (e91_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e91_transfer (e91_at_40 L R)
      (e91_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc

/-- The strict endpoint is sharp: with blank L, the 41-step
K41short endpoint itself is blank-left C, for any right context. -/
theorem e91_K41short_blank_exterior_C41 (R : E91Bits) :
    ∃ Z : E91Bits, ReachesIn target 41
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] (default : E91Bits)) (push [0, 1, 1, 1] R))
      (Cfg.headRight C default Z) := by
  exact ⟨(push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R), e91_K41short_exact default R⟩

end CryptidLink.L17

#print axioms CryptidLink.L17.e91_K41short_exact
#print axioms CryptidLink.L17.e91_K41short_noBlankLeftC_before41
#print axioms CryptidLink.L17.e91_K41short_blank_exterior_C41
