import CryptidLink.L17FirstReturnCriterion
import CryptidLink.L17r

/-!
# E85 — a nonblank-left sentinel survives the exact C01 sweep

The parameterized G1 final unwind ends in a C-mode sweep of (10)^n
against the structural sentinel [1]. Its endpoint is blank-left C,
but each earlier even clock retains a left-hand one. Intermediate
odd clocks have control B, not C.

The generic theorem intentionally REQUIRES L.head = 1. Removing this
hypothesis makes the claim false: n=1, L=blank is blank-left C at t=0.
No claim about the preceding 25-step fixed A finish is made.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev Q := ([1, 0] : List (Fin 2))

/-- The head of a (10)^n stack is 1 when its suffix also begins in 1. -/
private theorem e85_power_head_one (n : ℕ) (L : Bits)
    (hL : L.head = (1 : Fin 2)) :
    (push (Q ^ n) L).head = (1 : Fin 2) := by
  cases n with
  | zero =>
      simpa only [list_pow_zero, ListBlank.append_nil] using hL
  | succ n =>
      rw [ListBlank.append_pow_succ Q n L]
      simp only [Q, ListBlank.append, ListBlank.head_cons]

/-- A two-step C/B/C transfer cannot visit blank-left C before its end
when the untouched farther-left suffix begins in 1. The C state at
time zero has a one in its SECOND left cell. -/
private theorem e85_pair_noBlankLeftC_before2 (L R : Bits)
    (hL : L.head = (1 : Fin 2)) :
    E80NoBlankLeftCBefore (Cfg.headLeft C (push Q L) R) 2 := by
  let s : Cfg (Fin 2) (Fin 6) := Cfg.headLeft C (push Q L) R
  have h0 : ReachesIn target 0 s s := ReachesIn.zero target s
  have h1 : ReachesIn target 1 s
      (Cfg.headLeft B (push [0] L) (push [1] R)) := by
    dsimp only [s, Q]
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
      dsimp only [s, Q]
      exact Cfg.headLeft_cons C (1 : Fin 2) (push [0] L) R
    have hw : s.tape.left.tail.head = (1 : Fin 2) := by
      rw [hframe]
      simpa only [Cfg.headRight, ListBlank.append,
        ListBlank.tail_cons, ListBlank.head_cons] using hL
    have hz0 :
        (Cfg.headRight C (default : Bits) Z).tape.left.tail.head =
        (0 : Fin 2) := by rfl
    have heqLeft := congrArg
      (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.tape.left.tail.head) hz
    have absurdEq : (1 : Fin 2) = 0 :=
      hw.symm.trans (heqLeft.trans hz0)
    exact (by decide : (1 : Fin 2) ≠ 0) absurdEq
  · subst t
    have heq : c = Cfg.headLeft B (push [0] L) (push [1] R) :=
      Option.some.inj (hc.symm.trans h1)
    subst c
    rintro ⟨Z, hz⟩
    have hq := congrArg
      (fun cfg : Cfg (Fin 2) (Fin 6) => cfg.q) hz
    change (some B : Option (Fin 6)) = some C at hq
    exact (by decide : (some B : Option (Fin 6)) ≠ some C) hq

/-- For every n and symbolic right exterior, (10)^n with a
left-suffix sentinel 1 has no blank-left C at strictly earlier times.
This is proved by induction on machine-exact two-step transfers. -/
theorem e85_C01_sweep_sentinel_safe
    (n : ℕ) (L R : Bits) (hL : L.head = (1 : Fin 2)) :
    E80NoBlankLeftCBefore
      (Cfg.headLeft C (push (Q ^ n) L) R) (2 * n) := by
  induction n generalizing R with
  | zero =>
      intro t ht c hc
      omega
  | succ n ih =>
      have hhead : (push (Q ^ n) L).head = (1 : Fin 2) :=
        e85_power_head_one n L hL
      have hpair := e85_pair_noBlankLeftC_before2
        (push (Q ^ n) L) R hhead
      have hstep : ReachesIn target 2
          (Cfg.headLeft C (push Q (push (Q ^ n) L)) R)
          (Cfg.headLeft C (push (Q ^ n) L) (push [1, 1] R)) := by
        have hf :
            Cfg.headLeft C (push Q (push (Q ^ n) L)) R =
            Cfg.headRight C (push [0] (push (Q ^ n) L))
              (push [1] R) := by
          exact Cfg.headLeft_cons C (1 : Fin 2)
            (push [0] (push (Q ^ n) L)) R
        rw [hf]
        exact c01_exact (push (Q ^ n) L) R
      have hcombined := e80_safe_trans hstep hpair
        (ih (push [1, 1] R))
      rw [ListBlank.append_pow_succ Q n L]
      convert hcombined using 1 <;> omega

/-- The actual G1 final C sweep has the required sentinel 1,
independently of u and the full right exterior. -/
theorem e85_G1_final_C_sweep_safe (u : ℕ) (R : Bits) :
    E80NoBlankLeftCBefore
      (Cfg.headLeft C
        (push (Q ^ (u + 2)) (push [1] (default : Bits))) R)
      (2 * (u + 2)) := by
  exact e85_C01_sweep_sentinel_safe (u + 2)
    (push [1] (default : Bits)) R (by rfl)

/-- Exactly this last C sweep has its first blank-left-C state at
the endpoint. This is LOCAL first-return minimality, not an E60
global first-return theorem. -/
theorem e85_G1_final_C_sweep_first_blankLeftC
    (u : ℕ) (R : Bits) :
    (∃ Z : Bits,
      ReachesIn target (2 * (u + 2))
        (Cfg.headLeft C
          (push (Q ^ (u + 2)) (push [1] (default : Bits))) R)
        (Cfg.headRight C default Z)) ∧
    (∀ t : ℕ, t < 2 * (u + 2) →
      ∀ Z : Bits,
        ¬ ReachesIn target t
          (Cfg.headLeft C
            (push (Q ^ (u + 2)) (push [1] (default : Bits))) R)
          (Cfg.headRight C default Z)) := by
  have hpath := c01_sweep_exact (u + 2)
    (push [1] (default : Bits)) R
  have hframe :
      Cfg.headLeft C (push [1] (default : Bits))
        (push (([1, 1] : List (Fin 2)) ^ (u + 2)) R) =
      Cfg.headRight C default
        (push [1] (push (([1, 1] : List (Fin 2)) ^ (u + 2)) R)) :=
    Cfg.headLeft_cons C (1 : Fin 2) default _
  rw [hframe] at hpath
  exact e84_first_blankLeftC_criterion hpath
    ⟨_, rfl⟩ (e85_G1_final_C_sweep_safe u R)

end CryptidLink.L17

#print axioms CryptidLink.L17.e85_C01_sweep_sentinel_safe
#print axioms CryptidLink.L17.e85_G1_final_C_sweep_safe
#print axioms CryptidLink.L17.e85_G1_final_C_sweep_first_blankLeftC
