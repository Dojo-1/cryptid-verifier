import CryptidLink.L17z
/-!
# L17: exact even-11 K22 and odd-11 J1K terminal dispatch

The phase-correct \`A11;D10^2;D6^h;D10\` preludes were proved
in L17z. This module transports their directed D heads through
the complete 22-step K22 (even j=2h) and 10-step J1K (odd j=2h+1)
kernels. The two endpoints are intentionally different:

* even: raw C headRight, with the 13-cell K22 output still visible;
* odd: raw D headRight, with the seven-cell J1K output still visible.

Neither endpoint is a blank-left C return without additional outer
stack sweeps. All states, clocks, and arbitrary exterior contexts are
part of the statements. No blank-orbit reachability is asserted.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- K22 in its left-directed D input frame. The head carries the
    first zero; the following eight left bits are exactly 01010101. -/
theorem k22_headLeft_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 22
      (Cfg.headLeft D
        (ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (ListBlank.append [1, 0, 1, 0] R))
      (Cfg.headRight C L
        (ListBlank.append [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  have he :
      Cfg.headLeft D
        (ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (ListBlank.append [1, 0, 1, 0] R) =
      Cfg.headRight D
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1] L)
        (ListBlank.append [0, 1, 0, 1, 0] R) :=
    Cfg.headLeft_cons D (0 : Fin 2)
      (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1] L)
      (ListBlank.append [1, 0, 1, 0] R)
  rw [he]
  exact k22_exact L R

/-- J1K in its left-directed D frame. The head carries the
    first zero; the next four left bits are 0100. -/
theorem j1k_headLeft_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 10
      (Cfg.headLeft D
        (ListBlank.append [0, 0, 1, 0, 0] L)
        (ListBlank.append [1, 0] R))
      (Cfg.headRight D L
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0] R)) := by
  have he :
      Cfg.headLeft D (ListBlank.append [0, 0, 1, 0, 0] L)
        (ListBlank.append [1, 0] R) =
      Cfg.headRight D (ListBlank.append [0, 1, 0, 0] L)
        (ListBlank.append [0, 1, 0] R) :=
    Cfg.headLeft_cons D (0 : Fin 2)
      (ListBlank.append [0, 1, 0, 0] L)
      (ListBlank.append [1, 0] R)
  rw [he]
  exact j1k_exact L R

/-- Exact right-side remainder after the first four bits of the even
    D prelude have been consumed by the K22 input window. -/
def d11_even_tail : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, R => ListBlank.append [1, 0, 1, 0] R
  | h + 1, R =>
      ListBlank.append [1, 0, 1, 0]
        (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
          (ListBlank.append [1, 0, 1, 0, 1, 0] R))

/-- The D-prelude right tape has exactly the required 1010 prefix
    for K22, with an unmodified, explicitly retained remainder. -/
theorem d11_even_tail_factor (h : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append [1, 0]
      (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
        (ListBlank.append [1, 0, 1, 0, 1, 0] R)) =
    ListBlank.append [1, 0, 1, 0] (d11_even_tail h R) := by
  cases h with
  | zero => rfl
  | succ h =>
    rw [ListBlank.append_pow_succ
      ([1, 0, 1, 0, 1, 0] : List (Fin 2)) h
      (ListBlank.append [1, 0, 1, 0, 1, 0] R)]
    rfl

/-- Even 11 branch: after 40h+37 defined raw transitions, the full
    D-mode prelude and K22 have reached C at the precise head frame,
    retaining the 13-cell K22 output and the complete tail. -/
theorem a101_11_even_k22_exact (h : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (40 * h + 37)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0]
            (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1] L)))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h))
          (ListBlank.append [1, 1] R)))
      (Cfg.headRight C L
        (ListBlank.append [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
          (d11_even_tail h R))) := by
  have h1 := a101_11_even_dmode_exact h
    (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1] L) R
  rw [d11_even_tail_factor h R] at h1
  have h2 := k22_headLeft_exact L (d11_even_tail h R)
  convert h1.trans h2 using 1 <;> (first | rfl | omega)

/-- Odd 11 branch: the 40h+28 prelude followed by the ten-step
    J1K leads to a full D headRight in exactly 40h+38 steps. -/
theorem a101_11_odd_j1k_exact (h : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (40 * h + 38)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0] (ListBlank.append [0] L)))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
          (ListBlank.append [1, 1] R)))
      (Cfg.headRight D L
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
          (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
            (ListBlank.append [1, 0, 1, 0, 1, 0] R)))) := by
  have h1 := a101_11_odd_dmode_exact h (ListBlank.append [0] L) R
  have h2 := j1k_headLeft_exact L
    (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [1, 0, 1, 0, 1, 0] R))
  convert h1.trans h2 using 1 <;> (first | rfl | omega)

end CryptidLink.L17

#print axioms CryptidLink.L17.k22_headLeft_exact
#print axioms CryptidLink.L17.j1k_headLeft_exact
#print axioms CryptidLink.L17.d11_even_tail_factor
#print axioms CryptidLink.L17.a101_11_even_k22_exact
#print axioms CryptidLink.L17.a101_11_odd_j1k_exact
