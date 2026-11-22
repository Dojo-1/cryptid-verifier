import CryptidLink.L17NoCWindow
import CryptidLink.L17MixedBoundary

/-!
# E74 — the entire variable-length A window contains no C control state

Strengthens the exact A01 scanner by recording *every* intermediate state.
Combines this with E73's guarded four-step pair sweep to show the
entire 6*M A phase is C-free. Arbitrary ListBlank exteriors are retained.

This is a machine-level invariant, not a first blank-left C return or
a blank-tape nonhalting theorem.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))

private theorem e74_nonC_of_exact {s good c : Cfg (Fin 2) (Fin 6)}
    {t : ℕ} (hgood : ReachesIn target t s good)
    (hnot : good.q ≠ some C)
    (hc : ReachesIn target t s c) : c.q ≠ some C := by
  have h : some c = some good := hc.symm.trans hgood
  have heq : c = good := Option.some.inj h
  simpa [heq] using hnot

/-- The short 01 scanner is A at t=0, B at t=1, A again at t=2.
Both exterior tapes are arbitrary. -/
theorem e74_one_01_C_free (L R : Bits) :
    E73NoCBefore (Cfg.headRight A L (push [0, 1] R)) 2 := by
  let s : Cfg (Fin 2) (Fin 6) :=
    Cfg.headRight A L (push [0, 1] R)
  have h0 : ReachesIn target 0 s s := ReachesIn.zero target s
  have h1 : ReachesIn target 1 s
      (Cfg.headRight B (push [1] L) (push [1] R)) := by
    dsimp only [s]
    l17_exact_steps
  intro t ht c hc
  change ReachesIn target t s c at hc
  rcases (show t = 0 ∨ t = 1 by omega) with h | h
  · subst t
    exact e74_nonC_of_exact h0
      (by change (some A : Option (Fin 6)) ≠ some C; decide) hc
  · subst t
    exact e74_nonC_of_exact h1
      (by change (some B : Option (Fin 6)) ≠ some C; decide) hc

/-- A full 2*n scanner never visits control state C, including every
intermediate raw-machine step. -/
theorem e74_all_01_scans_C_free (n : ℕ) (L R : Bits) :
    E73NoCBefore
      (Cfg.headRight A L (push (P ^ n) R)) (2 * n) := by
  induction n generalizing L with
  | zero =>
    intro t ht c hc
    omega
  | succ n ih =>
    intro t ht c hc
    rw [ListBlank.append_pow_succ P n R] at hc
    by_cases hsmall : t < 2
    · exact (e74_one_01_C_free L (push (P ^ n) R)) t hsmall c hc
    · have hafter : t = 2 + (t - 2) := by omega
      have h2 := a01_exact L (push (P ^ n) R)
      change multiStep target _ 2 = some _ at h2
      change multiStep target _ t = some c at hc
      rw [hafter, multiStep_add, h2, Option.bind_some] at hc
      exact ih (push P L) (t - 2) (by omega) c hc

/-- Concatenate two C-free intervals along a certified exact state
without appealing to any arbitrary insertion simulation. -/
theorem e74_C_free_trans
    {source mid : Cfg (Fin 2) (Fin 6)} {m n : ℕ}
    (hpath : ReachesIn target m source mid)
    (hfirst : E73NoCBefore source m)
    (hsecond : E73NoCBefore mid n) :
    E73NoCBefore source (m + n) := by
  intro t ht c hc
  by_cases hleft : t < m
  · exact hfirst t hleft c hc
  · have hclock : t = m + (t - m) := by omega
    change multiStep target source m = some mid at hpath
    change multiStep target source t = some c at hc
    rw [hclock, multiStep_add, hpath, Option.bind_some] at hc
    exact hsecond (t - m) (by omega) c hc

/-- Every step in the entire 6*M A-phase is non-C:
a 2*M 01 scanner, followed by the E66 4*M guarded pair sweep.
No dependence on M, L or R beyond their explicitly typed domains. -/
theorem e74_variable_A_window_C_free (M : ℕ) (L R : Bits) :
    E73NoCBefore
      (Cfg.headRight A L (push (P ^ M) (push [1, 1] R)))
      (6 * M) := by
  have hscan := e74_all_01_scans_C_free M L (push [1, 1] R)
  have hexact := a01_sweep_exact M L (push [1, 1] R)
  have hsweep := e73_all_pair_sweeps_C_free M L R
  have h := e74_C_free_trans hexact hscan hsweep
  rw [show 2 * M + 4 * M = 6 * M by omega] at h
  exact h

end CryptidLink.L17

#print axioms CryptidLink.L17.e74_one_01_C_free
#print axioms CryptidLink.L17.e74_all_01_scans_C_free
#print axioms CryptidLink.L17.e74_C_free_trans
#print axioms CryptidLink.L17.e74_variable_A_window_C_free
