import CryptidLink.L17PairSweep

/-!
# E73 — a first structural first-return lemma: the 4n A-pair sweep contains no C

NoCBefore is a machine-level state-safety property for *every* exact
intermediate timestep, not merely the fixed endpoints in E66. It does
not prove the C-to-C E60 first return: the other phases need separate
C-visit and left-witness certificates.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))

/-- Every defined intermediate configuration before the given clock has
control state different from C. It is quantified over the full machine
configuration, so it does not assume a particular tape suffix. -/
def E73NoCBefore (source : Cfg (Fin 2) (Fin 6)) (clock : ℕ) : Prop :=
  ∀ t : ℕ, t < clock →
    ∀ c : Cfg (Fin 2) (Fin 6),
      ReachesIn target t source c → c.q ≠ some C

private theorem e73_noC_of_exact {source good c : Cfg (Fin 2) (Fin 6)}
    {t : ℕ} (hgood : ReachesIn target t source good)
    (hnot : good.q ≠ some C)
    (hc : ReachesIn target t source c) : c.q ≠ some C := by
  have h : some c = some good := hc.symm.trans hgood
  have heq : c = good := Option.some.inj h
  simpa [heq] using hnot

/-- Directly verify all four possible states before one A-pair transfer:
A, E, F and D. The next step restores A. -/
theorem e73_one_pair_C_free (L R : Bits) :
    E73NoCBefore
      (Cfg.headRight A (push P L) (push [1, 1] R)) 4 := by
  let s : Cfg (Fin 2) (Fin 6) :=
    Cfg.headRight A (push P L) (push [1, 1] R)
  have h0 : ReachesIn target 0 s s := ReachesIn.zero target s
  have h1 : ReachesIn target 1 s
      (Cfg.headRight E (push [0, 0, 1] L) (push [1] R)) := by
    dsimp only [s]
    l17_exact_steps
  have h2 : ReachesIn target 2 s
      (Cfg.headRight F (push [0, 1] L) (push [0, 0] R)) := by
    dsimp only [s]
    l17_exact_steps
  have h3 : ReachesIn target 3 s
      (Cfg.headRight D (push [1] L) (push [0, 1, 0] R)) := by
    dsimp only [s]
    l17_exact_steps
  intro t ht c hc
  change ReachesIn target t s c at hc
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with h | h | h | h
  · subst t
    exact e73_noC_of_exact h0 (by change (some A : Option (Fin 6)) ≠ some C; decide) hc
  · subst t
    exact e73_noC_of_exact h1 (by change (some E : Option (Fin 6)) ≠ some C; decide) hc
  · subst t
    exact e73_noC_of_exact h2 (by change (some F : Option (Fin 6)) ≠ some C; decide) hc
  · subst t
    exact e73_noC_of_exact h3 (by change (some D : Option (Fin 6)) ≠ some C; decide) hc

/-- All 4*n intermediate raw-machine steps of the E66 guarded A sweep
have control state different from C; the arbitrary exterior tapes are
retained. This is a universal safety claim, proved by induction, not by
bounded replay. -/
theorem e73_all_pair_sweeps_C_free (n : ℕ) (L R : Bits) :
    E73NoCBefore
      (Cfg.headRight A (push (P ^ n) L) (push [1, 1] R))
      (4 * n) := by
  induction n generalizing R with
  | zero =>
    intro t ht c hc
    omega
  | succ n ih =>
    intro t ht c hc
    rw [ListBlank.append_pow_succ P n L] at hc
    by_cases hsmall : t < 4
    · exact (e73_one_pair_C_free (push (P ^ n) L) R) t hsmall c hc
    · have hafter : t = 4 + (t - 4) := by omega
      have h4 := e66_A_two_ones_transfer_exact (push (P ^ n) L) R
      change multiStep target _ 4 = some _ at h4
      change multiStep target _ t = some c at hc
      rw [hafter, multiStep_add, h4, Option.bind_some] at hc
      exact ih (push Q R) (t - 4) (by omega) c hc

end CryptidLink.L17

#print axioms CryptidLink.L17.e73_one_pair_C_free
#print axioms CryptidLink.L17.e73_all_pair_sweeps_C_free
