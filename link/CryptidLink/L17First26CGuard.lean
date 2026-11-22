import CryptidLink.L17WindowPrelude

/-!
# E76: finite 26-step exact C-guard certificate at both E60 C preludes

For each fixed family, 26 complete prefix configurations are checked by
the raw-machine exact-step tactic over arbitrary exterior ListBlanks.
Every time before t=26 either control is non-C, or state C has a 1
immediately to the left of its head. The C visits at t=0 and t=25 are
explicitly permitted; no earlier *blank-left* C occurs.

This is a universal Lean proof target over tape exteriors, not finite
numerical evidence. Later prelude events and phases remain separate.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _

/-- A qualifying blank-left C return, with arbitrary right half-tape. -/
def E76BlankLeftC (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ (Z : Bits), c = Cfg.headRight C default Z

/-- A blank-left C configuration always has head-nearest left bit zero. -/
private theorem e76_nonblank_of_one {c : Cfg (Fin 2) (Fin 6)}
    (hone : c.tape.left.head = (1 : Fin 2)) :
    ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  have heq := congrArg
    (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.head) hz
  have hzero : (Cfg.headRight C (default : Bits) Z).tape.left.head =
      (0 : Fin 2) := by rfl
  have absurdEq : (1 : Fin 2) = 0 := hone.symm.trans (heq.trans hzero)
  exact (by decide : (1 : Fin 2) ≠ 0) absurdEq

/-- Non-C machine states are not blank-left C, whatever the tape. -/
private theorem e76_nonblank_of_nonC {c : Cfg (Fin 2) (Fin 6)}
    (hnoc : c.q ≠ some C) : ¬ E76BlankLeftC c := by
  rintro ⟨Z, hz⟩
  apply hnoc
  rw [hz]
  rfl

/-- Exact-time determinism transfers a forbidden configuration predicate. -/
private theorem e76_transfer_nonblank
    {source good actual : Cfg (Fin 2) (Fin 6)} {t : ℕ}
    (hgood : ReachesIn target t source good)
    (hnot : ¬ E76BlankLeftC good)
    (hactual : ReachesIn target t source actual) :
    ¬ E76BlankLeftC actual := by
  have heq : actual = good := Option.some.inj (hactual.symm.trans hgood)
  subst actual
  exact hnot

/-- Exact one prelude trace at raw t=0; all exterior bits remain symbolic. -/
private theorem e76_one_at_0 (L R : Bits) :
    ReachesIn target 0
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  exact ReachesIn.zero target _

/-- Exact one prelude trace at raw t=1; all exterior bits remain symbolic. -/
private theorem e76_one_at_1 (L R : Bits) :
    ReachesIn target 1
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 0, 1] L) (push [1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=2; all exterior bits remain symbolic. -/
private theorem e76_one_at_2 (L R : Bits) :
    ReachesIn target 2
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 0, 1] L) (push [0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=3; all exterior bits remain symbolic. -/
private theorem e76_one_at_3 (L R : Bits) :
    ReachesIn target 3
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 0, 1] L) (push [1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=4; all exterior bits remain symbolic. -/
private theorem e76_one_at_4 (L R : Bits) :
    ReachesIn target 4
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 0, 1] L) (push [0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=5; all exterior bits remain symbolic. -/
private theorem e76_one_at_5 (L R : Bits) :
    ReachesIn target 5
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 0, 1] L) (push [1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=6; all exterior bits remain symbolic. -/
private theorem e76_one_at_6 (L R : Bits) :
    ReachesIn target 6
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=7; all exterior bits remain symbolic. -/
private theorem e76_one_at_7 (L R : Bits) :
    ReachesIn target 7
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=8; all exterior bits remain symbolic. -/
private theorem e76_one_at_8 (L R : Bits) :
    ReachesIn target 8
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=9; all exterior bits remain symbolic. -/
private theorem e76_one_at_9 (L R : Bits) :
    ReachesIn target 9
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=10; all exterior bits remain symbolic. -/
private theorem e76_one_at_10 (L R : Bits) :
    ReachesIn target 10
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 0, 1] L) (push [0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=11; all exterior bits remain symbolic. -/
private theorem e76_one_at_11 (L R : Bits) :
    ReachesIn target 11
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=12; all exterior bits remain symbolic. -/
private theorem e76_one_at_12 (L R : Bits) :
    ReachesIn target 12
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=13; all exterior bits remain symbolic. -/
private theorem e76_one_at_13 (L R : Bits) :
    ReachesIn target 13
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=14; all exterior bits remain symbolic. -/
private theorem e76_one_at_14 (L R : Bits) :
    ReachesIn target 14
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=15; all exterior bits remain symbolic. -/
private theorem e76_one_at_15 (L R : Bits) :
    ReachesIn target 15
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=16; all exterior bits remain symbolic. -/
private theorem e76_one_at_16 (L R : Bits) :
    ReachesIn target 16
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=17; all exterior bits remain symbolic. -/
private theorem e76_one_at_17 (L R : Bits) :
    ReachesIn target 17
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=18; all exterior bits remain symbolic. -/
private theorem e76_one_at_18 (L R : Bits) :
    ReachesIn target 18
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=19; all exterior bits remain symbolic. -/
private theorem e76_one_at_19 (L R : Bits) :
    ReachesIn target 19
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=20; all exterior bits remain symbolic. -/
private theorem e76_one_at_20 (L R : Bits) :
    ReachesIn target 20
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=21; all exterior bits remain symbolic. -/
private theorem e76_one_at_21 (L R : Bits) :
    ReachesIn target 21
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=22; all exterior bits remain symbolic. -/
private theorem e76_one_at_22 (L R : Bits) :
    ReachesIn target 22
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=23; all exterior bits remain symbolic. -/
private theorem e76_one_at_23 (L R : Bits) :
    ReachesIn target 23
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=24; all exterior bits remain symbolic. -/
private theorem e76_one_at_24 (L R : Bits) :
    ReachesIn target 24
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact one prelude trace at raw t=25; all exterior bits remain symbolic. -/
private theorem e76_one_at_25 (L R : Bits) :
    ReachesIn target 25
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- From the one fixed C prelude, no blank-left C can occur
in the first 26 raw configurations, regardless of exterior tape bits. -/
theorem e76_one_first26_noBlankLeftC (L R : Bits) :
    ∀ t : ℕ, t < 26 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t ht c hc
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e76_transfer_nonblank (e76_one_at_0 L R)
      (e76_nonblank_of_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_1 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_2 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_3 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_4 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_5 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_6 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_7 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_8 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_9 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_10 L R)
      (e76_nonblank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_11 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_12 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_13 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_14 L R)
      (e76_nonblank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_15 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_16 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_17 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_18 L R)
      (e76_nonblank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_19 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_20 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_21 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_22 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_23 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_24 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_one_at_25 L R)
      (e76_nonblank_of_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc

/-- Exact three prelude trace at raw t=0; all exterior bits remain symbolic. -/
private theorem e76_three_at_0 (L R : Bits) :
    ReachesIn target 0
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  exact ReachesIn.zero target _

/-- Exact three prelude trace at raw t=1; all exterior bits remain symbolic. -/
private theorem e76_three_at_1 (L R : Bits) :
    ReachesIn target 1
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 1, 0, 0, 1, 0, 0, 1] L) (push [1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=2; all exterior bits remain symbolic. -/
private theorem e76_three_at_2 (L R : Bits) :
    ReachesIn target 2
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=3; all exterior bits remain symbolic. -/
private theorem e76_three_at_3 (L R : Bits) :
    ReachesIn target 3
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=4; all exterior bits remain symbolic. -/
private theorem e76_three_at_4 (L R : Bits) :
    ReachesIn target 4
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=5; all exterior bits remain symbolic. -/
private theorem e76_three_at_5 (L R : Bits) :
    ReachesIn target 5
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 0, 0, 1, 0, 0, 1] L) (push [1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=6; all exterior bits remain symbolic. -/
private theorem e76_three_at_6 (L R : Bits) :
    ReachesIn target 6
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=7; all exterior bits remain symbolic. -/
private theorem e76_three_at_7 (L R : Bits) :
    ReachesIn target 7
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=8; all exterior bits remain symbolic. -/
private theorem e76_three_at_8 (L R : Bits) :
    ReachesIn target 8
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=9; all exterior bits remain symbolic. -/
private theorem e76_three_at_9 (L R : Bits) :
    ReachesIn target 9
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=10; all exterior bits remain symbolic. -/
private theorem e76_three_at_10 (L R : Bits) :
    ReachesIn target 10
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=11; all exterior bits remain symbolic. -/
private theorem e76_three_at_11 (L R : Bits) :
    ReachesIn target 11
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=12; all exterior bits remain symbolic. -/
private theorem e76_three_at_12 (L R : Bits) :
    ReachesIn target 12
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=13; all exterior bits remain symbolic. -/
private theorem e76_three_at_13 (L R : Bits) :
    ReachesIn target 13
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=14; all exterior bits remain symbolic. -/
private theorem e76_three_at_14 (L R : Bits) :
    ReachesIn target 14
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 1, 0, 0, 0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=15; all exterior bits remain symbolic. -/
private theorem e76_three_at_15 (L R : Bits) :
    ReachesIn target 15
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [1, 0, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=16; all exterior bits remain symbolic. -/
private theorem e76_three_at_16 (L R : Bits) :
    ReachesIn target 16
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 0, 0, 1, 0, 0, 1] L) (push [1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=17; all exterior bits remain symbolic. -/
private theorem e76_three_at_17 (L R : Bits) :
    ReachesIn target 17
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 0, 0, 1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=18; all exterior bits remain symbolic. -/
private theorem e76_three_at_18 (L R : Bits) :
    ReachesIn target 18
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight F (push [0, 0, 0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=19; all exterior bits remain symbolic. -/
private theorem e76_three_at_19 (L R : Bits) :
    ReachesIn target 19
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight D (push [0, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=20; all exterior bits remain symbolic. -/
private theorem e76_three_at_20 (L R : Bits) :
    ReachesIn target 20
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 0, 1] L) (push [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=21; all exterior bits remain symbolic. -/
private theorem e76_three_at_21 (L R : Bits) :
    ReachesIn target 21
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [1, 0, 1, 0, 0, 1] L) (push [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=22; all exterior bits remain symbolic. -/
private theorem e76_three_at_22 (L R : Bits) :
    ReachesIn target 22
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight A (push [0, 1, 0, 1, 0, 0, 1] L) (push [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=23; all exterior bits remain symbolic. -/
private theorem e76_three_at_23 (L R : Bits) :
    ReachesIn target 23
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight E (push [0, 0, 1, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=24; all exterior bits remain symbolic. -/
private theorem e76_three_at_24 (L R : Bits) :
    ReachesIn target 24
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight B (push [0, 1, 0, 1, 0, 0, 1] L) (push [0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- Exact three prelude trace at raw t=25; all exterior bits remain symbolic. -/
private theorem e76_three_at_25 (L R : Bits) :
    ReachesIn target 25
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R))
      (Cfg.headRight C (push [1, 0, 1, 0, 0, 1] L) (push [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) := by
  l17_exact_steps

/-- From the three fixed C prelude, no blank-left C can occur
in the first 26 raw configurations, regardless of exterior tape bits. -/
theorem e76_three_first26_noBlankLeftC (L R : Bits) :
    ∀ t : ℕ, t < 26 →
      ∀ c : Cfg (Fin 2) (Fin 6),
        ReachesIn target t (Cfg.headRight C (push [1, 0, 1, 0, 0, 1, 0, 0, 1] L) (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0] R)) c →
        ¬ E76BlankLeftC c := by
  intro t ht c hc
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 ∨ t = 25 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t
    exact e76_transfer_nonblank (e76_three_at_0 L R)
      (e76_nonblank_of_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_1 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_2 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_3 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_4 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_5 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_6 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_7 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_8 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_9 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_10 L R)
      (e76_nonblank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_11 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_12 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_13 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_14 L R)
      (e76_nonblank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_15 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_16 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_17 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_18 L R)
      (e76_nonblank_of_nonC (by change (some F : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_19 L R)
      (e76_nonblank_of_nonC (by change (some D : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_20 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_21 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_22 L R)
      (e76_nonblank_of_nonC (by change (some A : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_23 L R)
      (e76_nonblank_of_nonC (by change (some E : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_24 L R)
      (e76_nonblank_of_nonC (by change (some B : Option (Fin 6)) ≠ some C; decide)) hc
  · subst t
    exact e76_transfer_nonblank (e76_three_at_25 L R)
      (e76_nonblank_of_one (by simp only [Cfg.headRight, ListBlank.append, ListBlank.head_cons])) hc

end CryptidLink.L17

#print axioms CryptidLink.L17.e76_one_first26_noBlankLeftC
#print axioms CryptidLink.L17.e76_three_first26_noBlankLeftC
