import CryptidLink.L17First26CGuard

/-!
# E77 — all fixed-prelude steps avoid the blank-left C section

This formally extends E76 from [0,26) to [0,88) and [0,126)
for the two fixed C-to-A entry families. A raw six-state trace
produces the candidate full tape endpoints; each path is checked
symbolically using l17_exact_steps over arbitrary exterior tapes.

This is NOT a C-free theorem: the preludes contain valid C visits.
It certifies their left-tape witnesses when in C. Fixed bridges
and final unwinds remain separate first-return obligations.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _

private theorem e77_transfer_noBlankLeft
    {source good actual : Cfg (Fin 2) (Fin 6)} {t : ℕ}
    (hg : ReachesIn target t source good)
    (hn : ¬ E76BlankLeftC good)
    (ha : ReachesIn target t source actual) :
    ¬ E76BlankLeftC actual := by
  have h : actual = good := Option.some.inj (ha.symm.trans hg)
  simpa [h] using hn

private theorem e77_noBlankLeft_if_nonC
    {c : Cfg (Fin 2) (Fin 6)}
    (hn : c.q ≠ some C) : ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  apply hn
  rw [hz]
  rfl

private theorem e77_noBlankLeft_if_one
    {c : Cfg (Fin 2) (Fin 6)}
    (hone : c.tape.left.head = (1 : Fin 2)) :
    ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  have hs := congrArg
    (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.head) hz
  have hzero : (Cfg.headRight C (default : Bits) Z).tape.left.head =
      (0 : Fin 2) := by rfl
  have honezero : (1 : Fin 2) = 0 := hone.symm.trans (hs.trans hzero)
  exact (by decide : (1 : Fin 2) ≠ 0) honezero

/-- one C prelude at exact raw time 26 (symbolic exterior tapes). -/
private theorem e77_one_at_26 (L R : Bits) :
    ReachesIn target 26
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 27 (symbolic exterior tapes). -/
private theorem e77_one_at_27 (L R : Bits) :
    ReachesIn target 27
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 28 (symbolic exterior tapes). -/
private theorem e77_one_at_28 (L R : Bits) :
    ReachesIn target 28
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 29 (symbolic exterior tapes). -/
private theorem e77_one_at_29 (L R : Bits) :
    ReachesIn target 29
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 30 (symbolic exterior tapes). -/
private theorem e77_one_at_30 (L R : Bits) :
    ReachesIn target 30
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 31 (symbolic exterior tapes). -/
private theorem e77_one_at_31 (L R : Bits) :
    ReachesIn target 31
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 32 (symbolic exterior tapes). -/
private theorem e77_one_at_32 (L R : Bits) :
    ReachesIn target 32
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 33 (symbolic exterior tapes). -/
private theorem e77_one_at_33 (L R : Bits) :
    ReachesIn target 33
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 34 (symbolic exterior tapes). -/
private theorem e77_one_at_34 (L R : Bits) :
    ReachesIn target 34
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 35 (symbolic exterior tapes). -/
private theorem e77_one_at_35 (L R : Bits) :
    ReachesIn target 35
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 36 (symbolic exterior tapes). -/
private theorem e77_one_at_36 (L R : Bits) :
    ReachesIn target 36
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 37 (symbolic exterior tapes). -/
private theorem e77_one_at_37 (L R : Bits) :
    ReachesIn target 37
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 38 (symbolic exterior tapes). -/
private theorem e77_one_at_38 (L R : Bits) :
    ReachesIn target 38
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 39 (symbolic exterior tapes). -/
private theorem e77_one_at_39 (L R : Bits) :
    ReachesIn target 39
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 40 (symbolic exterior tapes). -/
private theorem e77_one_at_40 (L R : Bits) :
    ReachesIn target 40
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 41 (symbolic exterior tapes). -/
private theorem e77_one_at_41 (L R : Bits) :
    ReachesIn target 41
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 42 (symbolic exterior tapes). -/
private theorem e77_one_at_42 (L R : Bits) :
    ReachesIn target 42
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 43 (symbolic exterior tapes). -/
private theorem e77_one_at_43 (L R : Bits) :
    ReachesIn target 43
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 44 (symbolic exterior tapes). -/
private theorem e77_one_at_44 (L R : Bits) :
    ReachesIn target 44
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 45 (symbolic exterior tapes). -/
private theorem e77_one_at_45 (L R : Bits) :
    ReachesIn target 45
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 46 (symbolic exterior tapes). -/
private theorem e77_one_at_46 (L R : Bits) :
    ReachesIn target 46
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 47 (symbolic exterior tapes). -/
private theorem e77_one_at_47 (L R : Bits) :
    ReachesIn target 47
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 48 (symbolic exterior tapes). -/
private theorem e77_one_at_48 (L R : Bits) :
    ReachesIn target 48
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 49 (symbolic exterior tapes). -/
private theorem e77_one_at_49 (L R : Bits) :
    ReachesIn target 49
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 50 (symbolic exterior tapes). -/
private theorem e77_one_at_50 (L R : Bits) :
    ReachesIn target 50
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 51 (symbolic exterior tapes). -/
private theorem e77_one_at_51 (L R : Bits) :
    ReachesIn target 51
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 52 (symbolic exterior tapes). -/
private theorem e77_one_at_52 (L R : Bits) :
    ReachesIn target 52
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 53 (symbolic exterior tapes). -/
private theorem e77_one_at_53 (L R : Bits) :
    ReachesIn target 53
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 54 (symbolic exterior tapes). -/
private theorem e77_one_at_54 (L R : Bits) :
    ReachesIn target 54
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 55 (symbolic exterior tapes). -/
private theorem e77_one_at_55 (L R : Bits) :
    ReachesIn target 55
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 56 (symbolic exterior tapes). -/
private theorem e77_one_at_56 (L R : Bits) :
    ReachesIn target 56
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 57 (symbolic exterior tapes). -/
private theorem e77_one_at_57 (L R : Bits) :
    ReachesIn target 57
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 58 (symbolic exterior tapes). -/
private theorem e77_one_at_58 (L R : Bits) :
    ReachesIn target 58
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 59 (symbolic exterior tapes). -/
private theorem e77_one_at_59 (L R : Bits) :
    ReachesIn target 59
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 60 (symbolic exterior tapes). -/
private theorem e77_one_at_60 (L R : Bits) :
    ReachesIn target 60
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 61 (symbolic exterior tapes). -/
private theorem e77_one_at_61 (L R : Bits) :
    ReachesIn target 61
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 62 (symbolic exterior tapes). -/
private theorem e77_one_at_62 (L R : Bits) :
    ReachesIn target 62
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 63 (symbolic exterior tapes). -/
private theorem e77_one_at_63 (L R : Bits) :
    ReachesIn target 63
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 64 (symbolic exterior tapes). -/
private theorem e77_one_at_64 (L R : Bits) :
    ReachesIn target 64
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 65 (symbolic exterior tapes). -/
private theorem e77_one_at_65 (L R : Bits) :
    ReachesIn target 65
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 66 (symbolic exterior tapes). -/
private theorem e77_one_at_66 (L R : Bits) :
    ReachesIn target 66
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 67 (symbolic exterior tapes). -/
private theorem e77_one_at_67 (L R : Bits) :
    ReachesIn target 67
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 68 (symbolic exterior tapes). -/
private theorem e77_one_at_68 (L R : Bits) :
    ReachesIn target 68
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 69 (symbolic exterior tapes). -/
private theorem e77_one_at_69 (L R : Bits) :
    ReachesIn target 69
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 70 (symbolic exterior tapes). -/
private theorem e77_one_at_70 (L R : Bits) :
    ReachesIn target 70
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 71 (symbolic exterior tapes). -/
private theorem e77_one_at_71 (L R : Bits) :
    ReachesIn target 71
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 72 (symbolic exterior tapes). -/
private theorem e77_one_at_72 (L R : Bits) :
    ReachesIn target 72
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 73 (symbolic exterior tapes). -/
private theorem e77_one_at_73 (L R : Bits) :
    ReachesIn target 73
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 74 (symbolic exterior tapes). -/
private theorem e77_one_at_74 (L R : Bits) :
    ReachesIn target 74
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 75 (symbolic exterior tapes). -/
private theorem e77_one_at_75 (L R : Bits) :
    ReachesIn target 75
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 76 (symbolic exterior tapes). -/
private theorem e77_one_at_76 (L R : Bits) :
    ReachesIn target 76
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 77 (symbolic exterior tapes). -/
private theorem e77_one_at_77 (L R : Bits) :
    ReachesIn target 77
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 78 (symbolic exterior tapes). -/
private theorem e77_one_at_78 (L R : Bits) :
    ReachesIn target 78
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 79 (symbolic exterior tapes). -/
private theorem e77_one_at_79 (L R : Bits) :
    ReachesIn target 79
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 80 (symbolic exterior tapes). -/
private theorem e77_one_at_80 (L R : Bits) :
    ReachesIn target 80
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 81 (symbolic exterior tapes). -/
private theorem e77_one_at_81 (L R : Bits) :
    ReachesIn target 81
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 82 (symbolic exterior tapes). -/
private theorem e77_one_at_82 (L R : Bits) :
    ReachesIn target 82
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 83 (symbolic exterior tapes). -/
private theorem e77_one_at_83 (L R : Bits) :
    ReachesIn target 83
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 84 (symbolic exterior tapes). -/
private theorem e77_one_at_84 (L R : Bits) :
    ReachesIn target 84
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 85 (symbolic exterior tapes). -/
private theorem e77_one_at_85 (L R : Bits) :
    ReachesIn target 85
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 86 (symbolic exterior tapes). -/
private theorem e77_one_at_86 (L R : Bits) :
    ReachesIn target 86
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- one C prelude at exact raw time 87 (symbolic exterior tapes). -/
private theorem e77_one_at_87 (L R : Bits) :
    ReachesIn target 87
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- No blank-left C at any timestep in [26,56) of the one prelude. -/
private theorem e77_one_noBL_26_56 (L R : Bits) :
    ∀ t : ℕ, 26 ≤ t → t < 56 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 ∨ t = 31 ∨ t = 32 ∨ t = 33 ∨ t = 34 ∨ t = 35 ∨ t = 36 ∨ t = 37 ∨ t = 38 ∨ t = 39 ∨ t = 40 ∨ t = 41 ∨ t = 42 ∨ t = 43 ∨ t = 44 ∨ t = 45 ∨ t = 46 ∨ t = 47 ∨ t = 48 ∨ t = 49 ∨ t = 50 ∨ t = 51 ∨ t = 52 ∨ t = 53 ∨ t = 54 ∨ t = 55 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_26 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_27 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_28 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_29 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_30 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_31 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_32 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_33 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_34 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_35 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_36 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_37 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_38 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_39 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_40 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_41 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_42 L R)
      (e77_noBlankLeft_if_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_43 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_44 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_45 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_46 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_47 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_48 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_49 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_50 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_51 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_52 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_53 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_54 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_55 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc

/-- No blank-left C at any timestep in [56,88) of the one prelude. -/
private theorem e77_one_noBL_56_88 (L R : Bits) :
    ∀ t : ℕ, 56 ≤ t → t < 88 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 56 ∨ t = 57 ∨ t = 58 ∨ t = 59 ∨ t = 60 ∨ t = 61 ∨ t = 62 ∨ t = 63 ∨ t = 64 ∨ t = 65 ∨ t = 66 ∨ t = 67 ∨ t = 68 ∨ t = 69 ∨ t = 70 ∨ t = 71 ∨ t = 72 ∨ t = 73 ∨ t = 74 ∨ t = 75 ∨ t = 76 ∨ t = 77 ∨ t = 78 ∨ t = 79 ∨ t = 80 ∨ t = 81 ∨ t = 82 ∨ t = 83 ∨ t = 84 ∨ t = 85 ∨ t = 86 ∨ t = 87 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_56 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_57 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_58 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_59 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_60 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_61 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_62 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_63 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_64 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_65 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_66 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_67 L R)
      (e77_noBlankLeft_if_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_68 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_69 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_70 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_71 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_72 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_73 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_74 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_75 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_76 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_77 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_78 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_79 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_80 L R)
      (e77_noBlankLeft_if_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_81 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_82 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_83 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_84 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_85 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_86 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_one_at_87 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc

/-- The entire 88-step fixed one C-to-A prelude avoids a
blank-left C before its final A endpoint, for arbitrary exterior tapes. -/
theorem e77_one_full_prelude_noBlankLeftC (L R : Bits) :
    ∀ t : ℕ, t < 88 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t ht c hc
  by_cases hfirst : t < 26
  · exact e76_one_first26_noBlankLeftC L R t hfirst c hc
  · by_cases h0 : t < 56
    · exact e77_one_noBL_26_56 L R t (by omega) h0 c hc
    · exact e77_one_noBL_56_88 L R t (by omega) ht c hc

/-- three C prelude at exact raw time 26 (symbolic exterior tapes). -/
private theorem e77_three_at_26 (L R : Bits) :
    ReachesIn target 26
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 27 (symbolic exterior tapes). -/
private theorem e77_three_at_27 (L R : Bits) :
    ReachesIn target 27
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 28 (symbolic exterior tapes). -/
private theorem e77_three_at_28 (L R : Bits) :
    ReachesIn target 28
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 29 (symbolic exterior tapes). -/
private theorem e77_three_at_29 (L R : Bits) :
    ReachesIn target 29
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 30 (symbolic exterior tapes). -/
private theorem e77_three_at_30 (L R : Bits) :
    ReachesIn target 30
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 31 (symbolic exterior tapes). -/
private theorem e77_three_at_31 (L R : Bits) :
    ReachesIn target 31
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 32 (symbolic exterior tapes). -/
private theorem e77_three_at_32 (L R : Bits) :
    ReachesIn target 32
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 33 (symbolic exterior tapes). -/
private theorem e77_three_at_33 (L R : Bits) :
    ReachesIn target 33
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 34 (symbolic exterior tapes). -/
private theorem e77_three_at_34 (L R : Bits) :
    ReachesIn target 34
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 35 (symbolic exterior tapes). -/
private theorem e77_three_at_35 (L R : Bits) :
    ReachesIn target 35
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 36 (symbolic exterior tapes). -/
private theorem e77_three_at_36 (L R : Bits) :
    ReachesIn target 36
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 37 (symbolic exterior tapes). -/
private theorem e77_three_at_37 (L R : Bits) :
    ReachesIn target 37
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 38 (symbolic exterior tapes). -/
private theorem e77_three_at_38 (L R : Bits) :
    ReachesIn target 38
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 39 (symbolic exterior tapes). -/
private theorem e77_three_at_39 (L R : Bits) :
    ReachesIn target 39
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 40 (symbolic exterior tapes). -/
private theorem e77_three_at_40 (L R : Bits) :
    ReachesIn target 40
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 41 (symbolic exterior tapes). -/
private theorem e77_three_at_41 (L R : Bits) :
    ReachesIn target 41
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 42 (symbolic exterior tapes). -/
private theorem e77_three_at_42 (L R : Bits) :
    ReachesIn target 42
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 43 (symbolic exterior tapes). -/
private theorem e77_three_at_43 (L R : Bits) :
    ReachesIn target 43
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 44 (symbolic exterior tapes). -/
private theorem e77_three_at_44 (L R : Bits) :
    ReachesIn target 44
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 45 (symbolic exterior tapes). -/
private theorem e77_three_at_45 (L R : Bits) :
    ReachesIn target 45
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 46 (symbolic exterior tapes). -/
private theorem e77_three_at_46 (L R : Bits) :
    ReachesIn target 46
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 47 (symbolic exterior tapes). -/
private theorem e77_three_at_47 (L R : Bits) :
    ReachesIn target 47
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 48 (symbolic exterior tapes). -/
private theorem e77_three_at_48 (L R : Bits) :
    ReachesIn target 48
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 49 (symbolic exterior tapes). -/
private theorem e77_three_at_49 (L R : Bits) :
    ReachesIn target 49
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 50 (symbolic exterior tapes). -/
private theorem e77_three_at_50 (L R : Bits) :
    ReachesIn target 50
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 51 (symbolic exterior tapes). -/
private theorem e77_three_at_51 (L R : Bits) :
    ReachesIn target 51
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 52 (symbolic exterior tapes). -/
private theorem e77_three_at_52 (L R : Bits) :
    ReachesIn target 52
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 53 (symbolic exterior tapes). -/
private theorem e77_three_at_53 (L R : Bits) :
    ReachesIn target 53
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 54 (symbolic exterior tapes). -/
private theorem e77_three_at_54 (L R : Bits) :
    ReachesIn target 54
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 55 (symbolic exterior tapes). -/
private theorem e77_three_at_55 (L R : Bits) :
    ReachesIn target 55
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 56 (symbolic exterior tapes). -/
private theorem e77_three_at_56 (L R : Bits) :
    ReachesIn target 56
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 57 (symbolic exterior tapes). -/
private theorem e77_three_at_57 (L R : Bits) :
    ReachesIn target 57
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 58 (symbolic exterior tapes). -/
private theorem e77_three_at_58 (L R : Bits) :
    ReachesIn target 58
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 59 (symbolic exterior tapes). -/
private theorem e77_three_at_59 (L R : Bits) :
    ReachesIn target 59
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 60 (symbolic exterior tapes). -/
private theorem e77_three_at_60 (L R : Bits) :
    ReachesIn target 60
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 61 (symbolic exterior tapes). -/
private theorem e77_three_at_61 (L R : Bits) :
    ReachesIn target 61
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 62 (symbolic exterior tapes). -/
private theorem e77_three_at_62 (L R : Bits) :
    ReachesIn target 62
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 63 (symbolic exterior tapes). -/
private theorem e77_three_at_63 (L R : Bits) :
    ReachesIn target 63
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 64 (symbolic exterior tapes). -/
private theorem e77_three_at_64 (L R : Bits) :
    ReachesIn target 64
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 65 (symbolic exterior tapes). -/
private theorem e77_three_at_65 (L R : Bits) :
    ReachesIn target 65
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 66 (symbolic exterior tapes). -/
private theorem e77_three_at_66 (L R : Bits) :
    ReachesIn target 66
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 67 (symbolic exterior tapes). -/
private theorem e77_three_at_67 (L R : Bits) :
    ReachesIn target 67
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 68 (symbolic exterior tapes). -/
private theorem e77_three_at_68 (L R : Bits) :
    ReachesIn target 68
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 69 (symbolic exterior tapes). -/
private theorem e77_three_at_69 (L R : Bits) :
    ReachesIn target 69
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 70 (symbolic exterior tapes). -/
private theorem e77_three_at_70 (L R : Bits) :
    ReachesIn target 70
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 71 (symbolic exterior tapes). -/
private theorem e77_three_at_71 (L R : Bits) :
    ReachesIn target 71
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 72 (symbolic exterior tapes). -/
private theorem e77_three_at_72 (L R : Bits) :
    ReachesIn target 72
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 73 (symbolic exterior tapes). -/
private theorem e77_three_at_73 (L R : Bits) :
    ReachesIn target 73
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 74 (symbolic exterior tapes). -/
private theorem e77_three_at_74 (L R : Bits) :
    ReachesIn target 74
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 75 (symbolic exterior tapes). -/
private theorem e77_three_at_75 (L R : Bits) :
    ReachesIn target 75
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 76 (symbolic exterior tapes). -/
private theorem e77_three_at_76 (L R : Bits) :
    ReachesIn target 76
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 77 (symbolic exterior tapes). -/
private theorem e77_three_at_77 (L R : Bits) :
    ReachesIn target 77
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 78 (symbolic exterior tapes). -/
private theorem e77_three_at_78 (L R : Bits) :
    ReachesIn target 78
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 79 (symbolic exterior tapes). -/
private theorem e77_three_at_79 (L R : Bits) :
    ReachesIn target 79
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 80 (symbolic exterior tapes). -/
private theorem e77_three_at_80 (L R : Bits) :
    ReachesIn target 80
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 81 (symbolic exterior tapes). -/
private theorem e77_three_at_81 (L R : Bits) :
    ReachesIn target 81
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 82 (symbolic exterior tapes). -/
private theorem e77_three_at_82 (L R : Bits) :
    ReachesIn target 82
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 83 (symbolic exterior tapes). -/
private theorem e77_three_at_83 (L R : Bits) :
    ReachesIn target 83
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 84 (symbolic exterior tapes). -/
private theorem e77_three_at_84 (L R : Bits) :
    ReachesIn target 84
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 85 (symbolic exterior tapes). -/
private theorem e77_three_at_85 (L R : Bits) :
    ReachesIn target 85
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 86 (symbolic exterior tapes). -/
private theorem e77_three_at_86 (L R : Bits) :
    ReachesIn target 86
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 87 (symbolic exterior tapes). -/
private theorem e77_three_at_87 (L R : Bits) :
    ReachesIn target 87
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 88 (symbolic exterior tapes). -/
private theorem e77_three_at_88 (L R : Bits) :
    ReachesIn target 88
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 89 (symbolic exterior tapes). -/
private theorem e77_three_at_89 (L R : Bits) :
    ReachesIn target 89
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 90 (symbolic exterior tapes). -/
private theorem e77_three_at_90 (L R : Bits) :
    ReachesIn target 90
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 91 (symbolic exterior tapes). -/
private theorem e77_three_at_91 (L R : Bits) :
    ReachesIn target 91
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 92 (symbolic exterior tapes). -/
private theorem e77_three_at_92 (L R : Bits) :
    ReachesIn target 92
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 93 (symbolic exterior tapes). -/
private theorem e77_three_at_93 (L R : Bits) :
    ReachesIn target 93
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 94 (symbolic exterior tapes). -/
private theorem e77_three_at_94 (L R : Bits) :
    ReachesIn target 94
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 95 (symbolic exterior tapes). -/
private theorem e77_three_at_95 (L R : Bits) :
    ReachesIn target 95
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 96 (symbolic exterior tapes). -/
private theorem e77_three_at_96 (L R : Bits) :
    ReachesIn target 96
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 97 (symbolic exterior tapes). -/
private theorem e77_three_at_97 (L R : Bits) :
    ReachesIn target 97
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 98 (symbolic exterior tapes). -/
private theorem e77_three_at_98 (L R : Bits) :
    ReachesIn target 98
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 99 (symbolic exterior tapes). -/
private theorem e77_three_at_99 (L R : Bits) :
    ReachesIn target 99
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 100 (symbolic exterior tapes). -/
private theorem e77_three_at_100 (L R : Bits) :
    ReachesIn target 100
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 101 (symbolic exterior tapes). -/
private theorem e77_three_at_101 (L R : Bits) :
    ReachesIn target 101
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 102 (symbolic exterior tapes). -/
private theorem e77_three_at_102 (L R : Bits) :
    ReachesIn target 102
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 103 (symbolic exterior tapes). -/
private theorem e77_three_at_103 (L R : Bits) :
    ReachesIn target 103
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 104 (symbolic exterior tapes). -/
private theorem e77_three_at_104 (L R : Bits) :
    ReachesIn target 104
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 105 (symbolic exterior tapes). -/
private theorem e77_three_at_105 (L R : Bits) :
    ReachesIn target 105
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 106 (symbolic exterior tapes). -/
private theorem e77_three_at_106 (L R : Bits) :
    ReachesIn target 106
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 107 (symbolic exterior tapes). -/
private theorem e77_three_at_107 (L R : Bits) :
    ReachesIn target 107
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 108 (symbolic exterior tapes). -/
private theorem e77_three_at_108 (L R : Bits) :
    ReachesIn target 108
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 109 (symbolic exterior tapes). -/
private theorem e77_three_at_109 (L R : Bits) :
    ReachesIn target 109
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 110 (symbolic exterior tapes). -/
private theorem e77_three_at_110 (L R : Bits) :
    ReachesIn target 110
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 111 (symbolic exterior tapes). -/
private theorem e77_three_at_111 (L R : Bits) :
    ReachesIn target 111
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 112 (symbolic exterior tapes). -/
private theorem e77_three_at_112 (L R : Bits) :
    ReachesIn target 112
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 113 (symbolic exterior tapes). -/
private theorem e77_three_at_113 (L R : Bits) :
    ReachesIn target 113
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 114 (symbolic exterior tapes). -/
private theorem e77_three_at_114 (L R : Bits) :
    ReachesIn target 114
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 115 (symbolic exterior tapes). -/
private theorem e77_three_at_115 (L R : Bits) :
    ReachesIn target 115
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 116 (symbolic exterior tapes). -/
private theorem e77_three_at_116 (L R : Bits) :
    ReachesIn target 116
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 117 (symbolic exterior tapes). -/
private theorem e77_three_at_117 (L R : Bits) :
    ReachesIn target 117
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 118 (symbolic exterior tapes). -/
private theorem e77_three_at_118 (L R : Bits) :
    ReachesIn target 118
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 119 (symbolic exterior tapes). -/
private theorem e77_three_at_119 (L R : Bits) :
    ReachesIn target 119
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 120 (symbolic exterior tapes). -/
private theorem e77_three_at_120 (L R : Bits) :
    ReachesIn target 120
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 121 (symbolic exterior tapes). -/
private theorem e77_three_at_121 (L R : Bits) :
    ReachesIn target 121
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 122 (symbolic exterior tapes). -/
private theorem e77_three_at_122 (L R : Bits) :
    ReachesIn target 122
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 123 (symbolic exterior tapes). -/
private theorem e77_three_at_123 (L R : Bits) :
    ReachesIn target 123
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 124 (symbolic exterior tapes). -/
private theorem e77_three_at_124 (L R : Bits) :
    ReachesIn target 124
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [0, 1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- three C prelude at exact raw time 125 (symbolic exterior tapes). -/
private theorem e77_three_at_125 (L R : Bits) :
    ReachesIn target 125
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] L) (push [1, 0] R)) := by
  set_option maxRecDepth 16384 in
    set_option maxHeartbeats 6000000 in
      l17_exact_steps

/-- No blank-left C at any timestep in [26,56) of the three prelude. -/
private theorem e77_three_noBL_26_56 (L R : Bits) :
    ∀ t : ℕ, 26 ≤ t → t < 56 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 26 ∨ t = 27 ∨ t = 28 ∨ t = 29 ∨ t = 30 ∨ t = 31 ∨ t = 32 ∨ t = 33 ∨ t = 34 ∨ t = 35 ∨ t = 36 ∨ t = 37 ∨ t = 38 ∨ t = 39 ∨ t = 40 ∨ t = 41 ∨ t = 42 ∨ t = 43 ∨ t = 44 ∨ t = 45 ∨ t = 46 ∨ t = 47 ∨ t = 48 ∨ t = 49 ∨ t = 50 ∨ t = 51 ∨ t = 52 ∨ t = 53 ∨ t = 54 ∨ t = 55 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_26 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_27 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_28 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_29 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_30 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_31 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_32 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_33 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_34 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_35 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_36 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_37 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_38 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_39 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_40 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_41 L R)
      (e77_noBlankLeft_if_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_42 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_43 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_44 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_45 L R)
      (e77_noBlankLeft_if_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_46 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_47 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_48 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_49 L R)
      (e77_noBlankLeft_if_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_50 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_51 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_52 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_53 L R)
      (e77_noBlankLeft_if_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_54 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_55 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc

/-- No blank-left C at any timestep in [56,86) of the three prelude. -/
private theorem e77_three_noBL_56_86 (L R : Bits) :
    ∀ t : ℕ, 56 ≤ t → t < 86 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 56 ∨ t = 57 ∨ t = 58 ∨ t = 59 ∨ t = 60 ∨ t = 61 ∨ t = 62 ∨ t = 63 ∨ t = 64 ∨ t = 65 ∨ t = 66 ∨ t = 67 ∨ t = 68 ∨ t = 69 ∨ t = 70 ∨ t = 71 ∨ t = 72 ∨ t = 73 ∨ t = 74 ∨ t = 75 ∨ t = 76 ∨ t = 77 ∨ t = 78 ∨ t = 79 ∨ t = 80 ∨ t = 81 ∨ t = 82 ∨ t = 83 ∨ t = 84 ∨ t = 85 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_56 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_57 L R)
      (e77_noBlankLeft_if_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_58 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_59 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_60 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_61 L R)
      (e77_noBlankLeft_if_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_62 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_63 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_64 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_65 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_66 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_67 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_68 L R)
      (e77_noBlankLeft_if_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_69 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_70 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_71 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_72 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_73 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_74 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_75 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_76 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_77 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_78 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_79 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_80 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_81 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_82 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_83 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_84 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_85 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc

/-- No blank-left C at any timestep in [86,116) of the three prelude. -/
private theorem e77_three_noBL_86_116 (L R : Bits) :
    ∀ t : ℕ, 86 ≤ t → t < 116 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 86 ∨ t = 87 ∨ t = 88 ∨ t = 89 ∨ t = 90 ∨ t = 91 ∨ t = 92 ∨ t = 93 ∨ t = 94 ∨ t = 95 ∨ t = 96 ∨ t = 97 ∨ t = 98 ∨ t = 99 ∨ t = 100 ∨ t = 101 ∨ t = 102 ∨ t = 103 ∨ t = 104 ∨ t = 105 ∨ t = 106 ∨ t = 107 ∨ t = 108 ∨ t = 109 ∨ t = 110 ∨ t = 111 ∨ t = 112 ∨ t = 113 ∨ t = 114 ∨ t = 115 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_86 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_87 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_88 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_89 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_90 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_91 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_92 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_93 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_94 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_95 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_96 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_97 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_98 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_99 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_100 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_101 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_102 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_103 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_104 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_105 L R)
      (e77_noBlankLeft_if_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_106 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_107 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_108 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_109 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_110 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_111 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_112 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_113 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_114 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_115 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc

/-- No blank-left C at any timestep in [116,126) of the three prelude. -/
private theorem e77_three_noBL_116_126 (L R : Bits) :
    ∀ t : ℕ, 116 ≤ t → t < 126 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t hlo hhi c hc
  have hcases : t = 116 ∨ t = 117 ∨ t = 118 ∨ t = 119 ∨ t = 120 ∨ t = 121 ∨ t = 122 ∨ t = 123 ∨ t = 124 ∨ t = 125 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_116 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_117 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_118 L R)
      (e77_noBlankLeft_if_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_119 L R)
      (e77_noBlankLeft_if_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_120 L R)
      (e77_noBlankLeft_if_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_121 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_122 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_123 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_124 L R)
      (e77_noBlankLeft_if_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e77_transfer_noBlankLeft (e77_three_at_125 L R)
      (e77_noBlankLeft_if_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc

/-- The entire 126-step fixed three C-to-A prelude avoids a
blank-left C before its final A endpoint, for arbitrary exterior tapes. -/
theorem e77_three_full_prelude_noBlankLeftC (L R : Bits) :
    ∀ t : ℕ, t < 126 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t ht c hc
  by_cases hfirst : t < 26
  · exact e76_three_first26_noBlankLeftC L R t hfirst c hc
  · by_cases h0 : t < 56
    · exact e77_three_noBL_26_56 L R t (by omega) h0 c hc
  · by_cases h1 : t < 86
    · exact e77_three_noBL_56_86 L R t (by omega) h1 c hc
    · by_cases h2 : t < 116
    · exact e77_three_noBL_86_116 L R t (by omega) h2 c hc
            · exact e77_three_noBL_116_126 L R t (by omega) ht c hc

end CryptidLink.L17

#print axioms CryptidLink.L17.e77_one_full_prelude_noBlankLeftC
#print axioms CryptidLink.L17.e77_three_full_prelude_noBlankLeftC
