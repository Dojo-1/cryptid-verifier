import CryptidLink.Sim
import AntihydraOuroboros.A4
import BusyBeaver.Machines.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
/-!
# A.4: from the raw Turing machine to our `step4`

Upstream proves `IsHalt target ↔ CollatzHalts next start` with a finer system: `C a b` is our
C(a, b + 1), and a sweep phase `P k n p` peels one unit of `k` per step. One of our macro steps from
C(a, b) is one upstream step when b = 1, and a + 2 upstream steps (enter P, a sweep steps, exit)
when b ≥ 3. The sweep is computed in closed form by `phase`. Result:

    IsHalt target ↔ ∃ n, run4 n (0, 3) = none
                  ↔ the expansion cascade from some reachable C(m, 1) has m + s + 4 = 2^(s+2).
-/

open BusyBeaver CryptidLink

namespace CryptidLink.A4

open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

def φ (s : ℕ × ℕ) : State := .C s.1 (s.2 - 1)

/-- Where the sweep `P k n p` lands once `k` reaches 0, as the pair `(n, p)`. -/
def phase : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, n, p => (n, p)
  | k + 1, n, 0 => phase k (n + 1) 2
  | k + 1, n, 1 => phase k (n + 1) 0
  | k + 1, n, p + 2 => phase k (n + 2) p

theorem phase_s1 (k n : ℕ) : phase (k + 1) n 1 = phase k (n + 1) 0 := rfl
theorem phase_s2 (k n p : ℕ) : phase (k + 1) n (p + 2) = phase k (n + 2) p := rfl
theorem phase_s0 (k n : ℕ) : phase (k + 1) n 0 = phase k (n + 1) 2 := rfl
theorem phase_two (k n : ℕ) : phase (k + 1) n 2 = phase k (n + 2) 0 := rfl

theorem phase_It : ∀ k n p, It next k (some (.P k n p)) = some (.P 0 (phase k n p).1 (phase k n p).2) := by
  intro k
  induction k with
  | zero => intro n p; rfl
  | succ k ih =>
    intro n p
    rw [It_succ]
    rcases p with _ | _ | p
    · exact ih (n + 1) 2
    · exact ih (n + 1) 0
    · exact ih (n + 2) p

theorem phase_shift : ∀ q k n p, phase (q + k) n (2 * q + p) = phase k (n + 2 * q) p := by
  intro q
  induction q with
  | zero => intro k n p; simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]
  | succ q ih =>
    intro k n p
    rw [show q + 1 + k = (q + k) + 1 by omega, show 2 * (q + 1) + p = (2 * q + p) + 2 by omega,
      phase_s2, ih, show n + 2 + 2 * q = n + 2 * (q + 1) by omega]

theorem phase_ge (k n p : ℕ) : phase k n (2 * k + p) = (n + 2 * k, p) := by
  have h := phase_shift k 0 n p
  rw [Nat.add_zero] at h
  rw [h]; rfl

theorem phase_cycle : ∀ t K N, phase (2 * t + K) N 0 = phase K (N + 3 * t) 0 := by
  intro t
  induction t with
  | zero => intro K N; simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  | succ t ih =>
    intro K N
    rw [show 2 * (t + 1) + K = (2 * t + K + 1) + 1 by omega, phase_s0, phase_two, ih,
      show N + 1 + 2 + 3 * t = N + 3 * (t + 1) by omega]

theorem phase_even (t N : ℕ) : phase (2 * t) N 0 = (N + 3 * t, 0) := by
  have h := phase_cycle t 0 N
  rw [Nat.add_zero] at h
  rw [h]; rfl

theorem phase_odd (t N : ℕ) : phase (2 * t + 1) N 0 = (N + 3 * t + 1, 2) := by
  rw [phase_cycle]; rfl

/-! ## `step4` in the cases we need -/

theorem step4_one (a : ℕ) : step4 (a, 1) = some (2, 2 * a + 2) := by
  unfold step4; dsimp only; split_ifs <;> first | rfl | omega

theorem step4_two (a : ℕ) : step4 (a, 2) = none := by
  unfold step4; dsimp only; split_ifs <;> first | rfl | omega

theorem step4_exp (a b : ℕ) (h : 2 * a + 2 < b) : step4 (a, b) = some (2 * a + 2, b - (2 * a + 2)) := by
  unfold step4; dsimp only; split_ifs <;> first | rfl | omega

theorem step4_even (a b : ℕ) (h3 : 3 ≤ b) (h : b ≤ 2 * a + 2) (he : b % 2 = 0) :
    step4 (a, b) = some ((6 * a + b + 2) / 4, (6 * a + b + 2) % 4 + 1) := by
  unfold step4; dsimp only; split_ifs <;> first | rfl | omega

theorem step4_odd (a b : ℕ) (h3 : 3 ≤ b) (h : b ≤ 2 * a + 2) (ho : b % 2 = 1) :
    step4 (a, b) = some ((6 * a + (b - 1) + 6) / 4, (6 * a + (b - 1) + 6) % 4 + 1) := by
  unfold step4; dsimp only; split_ifs <;> first | rfl | omega

theorem step4_inv (a b : ℕ) (s' : ℕ × ℕ) (hb : 1 ≤ b) (h : step4 (a, b) = some s') : 1 ≤ s'.2 := by
  unfold step4 at h; dsimp only at h
  split_ifs at h <;> first | (obtain rfl := Option.some.inj h; dsimp only; omega) | simp at h

/-- For b ≥ 3: our step equals enter-P, sweep, exit. -/
theorem big (a b : ℕ) (h3 : 3 ≤ b) : ∃ s', step4 (a, b) = some s' ∧
    next (.P 0 (phase a 0 (b - 1)).1 (phase a 0 (b - 1)).2) = some (φ s') := by
  by_cases hE : 2 * a + 2 < b
  · refine ⟨_, step4_exp a b hE, ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, b = 2 * a + 3 + e := ⟨b - (2 * a + 3), by omega⟩
    rw [show 2 * a + 3 + e - 1 = 2 * a + (e + 2) by omega, phase_ge]
    dsimp only
    simp only [next, φ, Option.some.injEq, State.C.injEq] <;> omega
  · rcases Nat.even_or_odd' b with ⟨m, rfl | rfl⟩
    · obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k, a = q + k := ⟨a - q, by omega⟩
      refine ⟨_, step4_even (q + k) (2 * (q + 1)) (by omega) (by omega) (by omega), ?_⟩
      rw [show 2 * (q + 1) - 1 = 2 * q + 1 by omega, phase_shift]
      rcases k with _ | k
      · show next (.P 0 (0 + 2 * q) 1) = _
        simp only [next, φ, Option.some.injEq, State.C.injEq] <;> omega
      · rw [phase_s1]
        rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
        · rw [phase_even]; dsimp only
          simp only [next, φ, Option.some.injEq, State.C.injEq] <;> omega
        · rw [phase_odd]; dsimp only
          simp only [next, φ, Option.some.injEq, State.C.injEq] <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k, a = m + k := ⟨a - m, by omega⟩
      refine ⟨_, step4_odd (m + k) (2 * m + 1) (by omega) (by omega) (by omega), ?_⟩
      rw [show 2 * m + 1 - 1 = 2 * m + 0 by omega, phase_shift]
      rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
      · rw [phase_even]; dsimp only
        simp only [next, φ, Option.some.injEq, State.C.injEq] <;> omega
      · rw [phase_odd]; dsimp only
        simp only [next, φ, Option.some.injEq, State.C.injEq] <;> omega

theorem run4_It : ∀ n s, run4 n s = It step4 n (some s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [It_succ]
    show (step4 s).bind (run4 n) = _
    cases h : step4 s with
    | none => exact (It_none step4 n).symm
    | some t => exact ih t

theorem sim : (∃ m, It next m (some (φ (0, 3))) = none) ↔ (∃ n, It step4 n (some (0, 3)) = none) := by
  refine sim_halts step4 next φ (fun s => 1 ≤ s.2) (0, 3) (by decide) ?_ ?_ ?_
  · rintro ⟨a, b⟩ s' hI h
    dsimp only at hI ⊢
    exact step4_inv a b s' hI h
  · rintro ⟨a, b⟩ s' hI h
    dsimp only at hI
    rcases (by omega : b = 1 ∨ b = 2 ∨ 3 ≤ b) with rfl | rfl | h3
    · rw [step4_one] at h
      obtain rfl := Option.some.inj h
      refine ⟨0, ?_⟩
      show next (.C a 0) = _
      simp only [next, φ, Option.some.injEq, State.C.injEq] <;> omega
    · rw [step4_two] at h; simp at h
    · obtain ⟨s'', hs, hn⟩ := big a b h3
      rw [hs] at h
      obtain rfl := Option.some.inj h
      refine ⟨a + 1, ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, b = d + 3 := ⟨b - 3, by omega⟩
      rw [It_succ]
      have e1 : next (φ (a, d + 3)) = some (.P a 0 (d + 2)) := rfl
      rw [e1, show a + 1 = 1 + a by omega, It_add, phase_It]
      rw [show d + 3 - 1 = d + 2 by omega] at hn
      exact hn
  · rintro ⟨a, b⟩ hI h
    dsimp only at hI
    rcases (by omega : b = 1 ∨ b = 2 ∨ 3 ≤ b) with rfl | rfl | h3
    · rw [step4_one] at h; simp at h
    · exact ⟨1, rfl⟩
    · obtain ⟨s'', hs, -⟩ := big a b h3
      rw [hs] at h; simp at h

/-- **A.4, machine level.** The Turing machine `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` halts
    from the blank tape iff our macro system halts from C(0, 3). -/
theorem machine_halts_iff_run4 : IsHalt target ↔ ∃ n, run4 n (0, 3) = none := by
  rw [isHalt_iff_acceleration]
  have hs : start = φ (0, 3) := rfl
  unfold CollatzHalts
  rw [hs]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨n, hn⟩ := sim.mp ⟨m, Option.isNone_iff_eq_none.mp hm⟩
    exact ⟨n, by rw [run4_It]; exact hn⟩
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := sim.mpr ⟨n, by rw [← run4_It]; exact hn⟩
    exact ⟨m, Option.isNone_iff_eq_none.mpr hm⟩

/-- **A.4, machine level, cascade form.** The Turing machine halts iff some reachable C(m, 1)
    starts an expansion cascade with m + s + 4 = 2^(s+2), i.e. m ∈ {0, 3, 10, 25, 56, 119, …}. -/
theorem machine_halts_iff_cascade : IsHalt target ↔
    ∃ n m s, run4 n (0, 3) = some (m, 1) ∧ m + s + 4 = 2 ^ (s + 2) :=
  machine_halts_iff_run4.trans a4_halts_iff

end CryptidLink.A4

#print axioms CryptidLink.A4.machine_halts_iff_run4
#print axioms CryptidLink.A4.machine_halts_iff_cascade
