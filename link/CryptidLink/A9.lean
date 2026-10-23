import AntihydraOuroboros.A9
import BusyBeaver.Machines.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD
/-!
# A.9: from the raw Turing machine to our halting criterion

The upstream file proves, for the Turing machine `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`
run from the blank tape, `IsHalt target ↔ CollatzHalts next start`. Here we identify their
`next` with our `step9o` (hence, by `step9_enc`, with `step9`), so that

    IsHalt target ↔ ∃ n, run9 n (5, 2, 0) = none ↔ (race criterion `a9_halts_iff`).

This closes the transcription gap for A.9: the statement is about the actual machine.
-/

open BusyBeaver

namespace CryptidLink.A9

open BusyBeaver.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

/-- Their two families as our tagged states. -/
def ψ : State → Bool × ℕ × ℕ × ℕ
  | .C_0 a b c => (false, a, b, c)
  | .C_1 a b c => (true, a, b, c)

/-- Their states in our merged coordinates. -/
def φ (s : State) : ℕ × ℕ × ℕ := enc (ψ s)

theorem next_eq (s : State) : (next s).map ψ = step9o (ψ s) := by
  rcases s with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> rcases b with _ | b <;> rcases c with _ | _ | c <;> rfl

theorem step9_φ (s : State) : step9 (φ s) = (next s).map φ := by
  unfold φ
  rw [step9_enc, ← next_eq, Option.map_map]
  rfl

theorem iter_none (n : ℕ) : (fun o : Option State => o.bind next)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem iter_map (n : ℕ) : ∀ s : State,
    ((fun o : Option State => o.bind next)^[n] (some s)).map φ = run9 n (φ s) := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    show ((fun o : Option State => o.bind next)^[n] (next s)).map φ = (step9 (φ s)).bind (run9 n)
    rw [step9_φ]
    cases h : next s with
    | none => rw [iter_none]; rfl
    | some t => exact ih t

theorem collatzHalts_iff : CollatzHalts next start ↔ ∃ n, run9 n (5, 2, 0) = none := by
  unfold CollatzHalts
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have := iter_map n start
    rw [Option.isNone_iff_eq_none.mp hn] at this
    exact this.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have := iter_map n start
    have h5 : φ start = (5, 2, 0) := rfl
    rw [h5, hn, Option.map_eq_none_iff] at this
    rw [this]; rfl

/-- **A.9, machine level.** The Turing machine `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`
    halts from the blank tape iff our merged macro system halts from C(5,2,0). -/
theorem machine_halts_iff_run9 : IsHalt target ↔ ∃ n, run9 n (5, 2, 0) = none :=
  isHalt_iff_acceleration.trans collatzHalts_iff

/-- **A.9, machine level, race form.** The Turing machine halts from the blank tape iff its
    orbit reaches C(a,b,c) with b ≥ 1 and (b = c or b = c + 1). -/
theorem machine_halts_iff_race :
    IsHalt target ↔ ∃ n s, run9 n (5, 2, 0) = some s ∧ raceHalts s :=
  machine_halts_iff_run9.trans a9_halts_iff

end CryptidLink.A9

#print axioms CryptidLink.A9.machine_halts_iff_run9
#print axioms CryptidLink.A9.machine_halts_iff_race
