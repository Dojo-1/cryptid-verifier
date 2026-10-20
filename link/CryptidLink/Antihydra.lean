import CryptidLink.Sim
import AntihydraOuroboros.Basic
import BusyBeaver.Machines.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA
/-!
# Antihydra: from the raw Turing machine to our walk

Upstream proves `IsHalt target ↔ CollatzHalts next start` with a finer system on
P(a, b, c) := 0^∞ 1^a 0 1^b F> 1 1^c 0^∞ that moves b two units at a time. Our A(a, B) corresponds to
P(a, B − 1, 1); each of our macro steps is j + 1 of their steps. Result:

    IsHalt target ↔ ∃ n, run n (0, 4) = none ↔ ∃ n, walk 0 (pv n 4) = none.
-/

open BusyBeaver CryptidLink

namespace CryptidLink.Antihydra

open BusyBeaver.M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA

def φ (s : ℕ × ℕ) : State := .P s.1 (s.2 - 1) 1

theorem loop (a r : ℕ) (hr : 1 ≤ r) : ∀ j c,
    It next j (some (.P a (2 * j + r) c)) = some (.P a r (c + 3 * j)) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  intro j
  induction j with
  | zero => intro c; rfl
  | succ j ih =>
    intro c
    rw [It_succ]
    have e : 2 * (j + 1) + (r + 1) = (2 * j + r) + 3 := by omega
    rw [e]
    show It next j (some (.P a ((2 * j + r) + 1) (c + 3))) = _
    rw [show (2 * j + r) + 1 = 2 * j + (r + 1) by omega, ih]
    congr 3; omega

theorem run_It : ∀ n s, run n s = It step n (some s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [It_succ]
    show (step s).bind (run n) = _
    cases h : step s with
    | none => exact (It_none step n).symm
    | some t => exact ih t

theorem sim : (∃ m, It next m (some (φ (0, 4))) = none) ↔ (∃ n, It step n (some (0, 4)) = none) := by
  refine sim_halts step next φ (fun s => 2 ≤ s.2) (0, 4) (by decide) ?_ ?_ ?_
  · rintro ⟨a, B⟩ ⟨a', B'⟩ hI h
    simp only [step] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
  · rintro ⟨a, B⟩ ⟨a', B'⟩ hI h
    simp only at hI
    simp only [step] at h
    split at h
    · rename_i hB
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨j, rfl⟩ : ∃ j, B = 2 * j + 2 := ⟨B / 2 - 1, by omega⟩
      refine ⟨j, ?_⟩
      rw [show j + 1 = 1 + j by omega, It_add]
      have hφ : φ (a, 2 * j + 2) = .P a (2 * j + 1) 1 := by simp [φ]
      rw [hφ, loop a 1 le_rfl j 1]
      simp only [It, Function.iterate_one, Option.bind_some, next, φ]
      congr 2 <;> omega
    · split at h
      · simp at h
      · rename_i hB ha
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨j, rfl⟩ : ∃ j, B = 2 * j + 3 := ⟨B / 2 - 1, by omega⟩
        obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        refine ⟨j, ?_⟩
        rw [show j + 1 = 1 + j by omega, It_add]
        have hφ : φ (a + 1, 2 * j + 3) = .P (a + 1) (2 * j + 2) 1 := by simp [φ]
        rw [hφ, loop (a + 1) 2 (by norm_num) j 1]
        simp only [It, Function.iterate_one, Option.bind_some, next, φ]
        congr 2 <;> omega
  · rintro ⟨a, B⟩ hI h
    simp only at hI
    simp only [step] at h
    split at h
    · simp at h
    · split at h
      · rename_i hB ha
        subst ha
        obtain ⟨j, rfl⟩ : ∃ j, B = 2 * j + 3 := ⟨B / 2 - 1, by omega⟩
        refine ⟨1 + j, ?_⟩
        rw [It_add]
        have hφ : φ (0, 2 * j + 3) = .P 0 (2 * j + 2) 1 := by simp [φ]
        rw [hφ, loop 0 2 (by norm_num) j 1]
        rfl
      · simp at h

/-- **Antihydra, machine level.** The Turing machine `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA`
    halts from the blank tape iff our macro system halts from A(0, 4). -/
theorem machine_halts_iff_run : IsHalt target ↔ ∃ n, run n (0, 4) = none := by
  rw [isHalt_iff_acceleration]
  have hs : start = φ (0, 4) := rfl
  unfold CollatzHalts
  rw [hs]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨n, hn⟩ := sim.mp ⟨m, Option.isNone_iff_eq_none.mp hm⟩
    exact ⟨n, by rw [run_It]; exact hn⟩
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := sim.mpr ⟨n, by rw [← run_It]; exact hn⟩
    exact ⟨m, Option.isNone_iff_eq_none.mpr hm⟩

/-- **Antihydra, machine level, walk form.** The Turing machine halts iff the +2/−1 walk driven by
    the parities of the T-orbit of 4 ever goes below zero. -/
theorem machine_halts_iff_walk : IsHalt target ↔ ∃ n, walk 0 (pv n 4) = none := by
  rw [machine_halts_iff_run]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [run_eq] at hn
    cases h : walk 0 (pv n 4) with
    | none => rfl
    | some x => rw [h] at hn; simp at hn
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [run_eq, hn]; rfl⟩

end CryptidLink.Antihydra

#print axioms CryptidLink.Antihydra.machine_halts_iff_run
#print axioms CryptidLink.Antihydra.machine_halts_iff_walk
