import CryptidLink.L17FirstReturnSafety
import CryptidLink.L17FiveRun

/-!
# E86 — all preterminal times of the fixed width-four A finish are safe

This 25-step A-to-C path is part of the canonical E68 G1 final unwind.
Every theorem carries arbitrary full ListBlank exteriors L and R.
The only preterminal C visits are t=9 and t=21, both with left head 1.
At t=25 a blank left exterior L *can* give blank-left C: strict
t < 25 is essential. This file does not imply E60 first return.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _

private theorem e86_transfer
    {source good actual : Cfg (Fin 2) (Fin 6)} {t : ℕ}
    (hg : ReachesIn target t source good)
    (hn : ¬ E76BlankLeftC good)
    (ha : ReachesIn target t source actual) :
    ¬ E76BlankLeftC actual := by
  have heq : actual = good := Option.some.inj (ha.symm.trans hg)
  simpa [heq] using hn

private theorem e86_noBlank_of_nonC {c : Cfg (Fin 2) (Fin 6)}
    (hn : c.q ≠ some C) : ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  apply hn
  rw [hz]
  rfl

private theorem e86_noBlank_of_leftOne {c : Cfg (Fin 2) (Fin 6)}
    (ho : c.tape.left.head = (1 : Fin 2)) :
    ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  have h := congrArg
    (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.head) hz
  have hz0 :
      (Cfg.headRight C (default : Bits) Z).tape.left.head =
      (0 : Fin 2) := by rfl
  exact (by decide : (1 : Fin 2) ≠ 0) (ho.symm.trans (h.trans hz0))

private theorem e86_at_0 (L R : Bits) :
    ReachesIn target 0
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R)) := by
  exact ReachesIn.zero target _

private theorem e86_at_1 (L R : Bits) :
    ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_0 L R).trans hstep

private theorem e86_at_2 (L R : Bits) :
    ReachesIn target 2
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1] R))
      (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_1 L R).trans hstep

private theorem e86_at_3 (L R : Bits) :
    ReachesIn target 3
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_2 L R).trans hstep

private theorem e86_at_4 (L R : Bits) :
    ReachesIn target 4
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R))
      (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_3 L R).trans hstep

private theorem e86_at_5 (L R : Bits) :
    ReachesIn target 5
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_4 L R).trans hstep

private theorem e86_at_6 (L R : Bits) :
    ReachesIn target 6
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_5 L R).trans hstep

private theorem e86_at_7 (L R : Bits) :
    ReachesIn target 7
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_6 L R).trans hstep

private theorem e86_at_8 (L R : Bits) :
    ReachesIn target 8
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0] R))
      (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_7 L R).trans hstep

private theorem e86_at_9 (L R : Bits) :
    ReachesIn target 9
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 0] R))
      (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_8 L R).trans hstep

private theorem e86_at_10 (L R : Bits) :
    ReachesIn target 10
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 1, 0, 1, 0, 1, 0, 1] L) (push [0, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_9 L R).trans hstep

private theorem e86_at_11 (L R : Bits) :
    ReachesIn target 11
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1] L) (push [1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_10 L R).trans hstep

private theorem e86_at_12 (L R : Bits) :
    ReachesIn target 12
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 1, 0, 1, 0, 1] L) (push [1, 1, 0, 1, 0] R))
      (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_11 L R).trans hstep

private theorem e86_at_13 (L R : Bits) :
    ReachesIn target 13
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight F (push [1, 0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_12 L R).trans hstep

private theorem e86_at_14 (L R : Bits) :
    ReachesIn target 14
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_13 L R).trans hstep

private theorem e86_at_15 (L R : Bits) :
    ReachesIn target 15
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [1, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_14 L R).trans hstep

private theorem e86_at_16 (L R : Bits) :
    ReachesIn target 16
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_15 L R).trans hstep

private theorem e86_at_17 (L R : Bits) :
    ReachesIn target 17
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_16 L R).trans hstep

private theorem e86_at_18 (L R : Bits) :
    ReachesIn target 18
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_17 L R).trans hstep

private theorem e86_at_19 (L R : Bits) :
    ReachesIn target 19
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_18 L R).trans hstep

private theorem e86_at_20 (L R : Bits) :
    ReachesIn target 20
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_19 L R).trans hstep

private theorem e86_at_21 (L R : Bits) :
    ReachesIn target 21
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_20 L R).trans hstep

private theorem e86_at_22 (L R : Bits) :
    ReachesIn target 22
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight C (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_21 L R).trans hstep

private theorem e86_at_23 (L R : Bits) :
    ReachesIn target 23
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight D (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_22 L R).trans hstep

private theorem e86_at_24 (L R : Bits) :
    ReachesIn target 24
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight E (push [0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_23 L R).trans hstep

private theorem e86_at_25 (L R : Bits) :
    ReachesIn target 25
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have hstep : ReachesIn target 1
      (Cfg.headRight B (push [1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
    l17_exact_steps
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      exact (e86_at_24 L R).trans hstep

/-- The same 25-step exact full-configuration endpoint as the
previously private width4_a_finish, now independently linked to the
per-time certificates. No assumption on either exterior is added. -/
theorem e86_width4_A_finish_exact (L R : Bits) :
    ReachesIn target 25
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R))
      (Cfg.headRight C L (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) :=
  e86_at_25 L R

/-- Exact safety at every earlier time of the fixed A finish. -/
theorem e86_width4_A_finish_noBlankLeftC_before25
    (L R : Bits) :
    E80NoBlankLeftCBefore
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1] L) (push [1, 1] R)) 25 := by
  intro t ht c hc
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 := by omega
  rcases hcases with heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq | heq
  · subst t
    exact e86_transfer (e86_at_0 L R)
      (e86_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_1 L R)
      (e86_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_2 L R)
      (e86_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_3 L R)
      (e86_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_4 L R)
      (e86_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_5 L R)
      (e86_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_6 L R)
      (e86_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_7 L R)
      (e86_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_8 L R)
      (e86_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_9 L R)
      (e86_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e86_transfer (e86_at_10 L R)
      (e86_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_11 L R)
      (e86_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_12 L R)
      (e86_noBlank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_13 L R)
      (e86_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_14 L R)
      (e86_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_15 L R)
      (e86_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_16 L R)
      (e86_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_17 L R)
      (e86_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_18 L R)
      (e86_noBlank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_19 L R)
      (e86_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_20 L R)
      (e86_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_21 L R)
      (e86_noBlank_of_leftOne (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e86_transfer (e86_at_22 L R)
      (e86_noBlank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_23 L R)
      (e86_noBlank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e86_transfer (e86_at_24 L R)
      (e86_noBlank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc

/-- The strict endpoint bound is necessary: a blank left exterior
permits a blank-left C exactly at the fixed 25-step endpoint. -/
theorem e86_width4_A_finish_blank_exterior_C25 (R : Bits) :
    ∃ Z : Bits,
      ReachesIn target 25
        (Cfg.headRight A
          (push [0, 0, 1, 0, 1, 0, 1, 0, 1] (default : Bits)) (push [1, 1] R))
        (Cfg.headRight C default Z) := by
  exact ⟨(push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R), e86_width4_A_finish_exact default R⟩

end CryptidLink.L17

#print axioms CryptidLink.L17.e86_width4_A_finish_exact
#print axioms CryptidLink.L17.e86_width4_A_finish_noBlankLeftC_before25
#print axioms CryptidLink.L17.e86_width4_A_finish_blank_exterior_C25
