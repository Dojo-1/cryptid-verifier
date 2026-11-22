import CryptidLink.L17Window

/-!
# E66 — a guarded A-mode transfer and its exact arbitrary-length sweep

This is an independently composable small-step fact about L17. The four-step
kernel consumes a head-nearest 01 pair on the left and restores state A,
transferring one head-nearest 10 pair to the right after a 11 guard.

The theorem applies for every natural n and arbitrary exterior tapes.
No E60 C-checkpoint entry, first return, or blank-orbit nonhalting follows.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))

/-- A local four-step transfer. The read window relative to the initial
head is [-1,1]; both exterior tapes are left symbolic. -/
theorem e66_A_two_ones_transfer_exact (L R : Bits) :
    ReachesIn target 4
      (Cfg.headRight A (push P L) (push [1, 1] R))
      (Cfg.headRight A L (push [1, 1] (push Q R))) := by
  l17_exact_steps

/-- Exactly 4*n raw steps, carrying n head-nearest 01 pairs from the left
into n 10 pairs after the right-hand 11 guard. In particular the original
right exterior R remains intact. -/
theorem e66_A_two_ones_sweep_exact (n : ℕ) (L R : Bits) :
    ReachesIn target (4 * n)
      (Cfg.headRight A (push (P ^ n) L) (push [1, 1] R))
      (Cfg.headRight A L (push [1, 1] (push (Q ^ n) R))) := by
  induction n generalizing R with
  | zero =>
    simpa only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil] using
      ReachesIn.zero target (Cfg.headRight A L (push [1, 1] R))
  | succ n ih =>
    have h := e66_A_two_ones_transfer_exact (push (P ^ n) L) R
    have hh := h.trans (ih (push Q R))
    rw [← ListBlank.append_pow_succ P n L,
      ListBlank.append_pow_comm Q n R,
      ← ListBlank.append_pow_succ Q n R,
      show 4 + 4 * n = 4 * (n + 1) by omega] at hh
    exact hh

end CryptidLink.L17

#print axioms CryptidLink.L17.e66_A_two_ones_transfer_exact
#print axioms CryptidLink.L17.e66_A_two_ones_sweep_exact
