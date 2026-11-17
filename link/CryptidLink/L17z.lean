import CryptidLink.L17y
/-!
# L17: corrected D-mode phase transport for homogeneous 11 terminals

IMPORTANT CORRECTION: the raw trace does not support the older literal
composition \`A11; D10^3; D6^h\`. Its order is instead

  A11 ; D10^2 ; D6^h ; D10

before the final K22 (even 101 count) or J1K (odd 101 count).
All three theorems below preserve exact complete framed configurations,
raw clocks, and arbitrary exterior left/right tape contexts.

The correction does not change the aggregate clock: 8+14h+4 =
12+14h. It changes WHICH cells each sweep reads, and is essential
to composing the actual raw transition relation.

No theorem here asserts a global C-return, blank-tape reachability,
or halting/non-halting.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Homogeneous 101^j then 11, followed by exactly TWO D10
    conversions, reaches the phase-correct D6 input.
    Exact time: 13j+3+8 = 13j+11. -/
theorem a101_11_d10_twice_exact (j : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (13 * j + 11)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ j)
          (ListBlank.append [1, 1] R)))
      (Cfg.headLeft D
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [0] L)))
        (ListBlank.append [1, 0, 1, 0, 1, 0] R)) := by
  let M : ListBlank (Fin 2) :=
    ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
      (ListBlank.append [0] L)
  have h1 := a101_11_terminal_exact j L R
  have h2 := d10_exact (ListBlank.append [0, 1, 0, 1] M)
    (ListBlank.append [1, 0] R)
  have h3 := d10_headLeft_exact (ListBlank.append [0, 1] M)
    (ListBlank.append [1, 0, 1, 0] R)
  convert (h1.trans h2).trans h3 using 1 <;> (first | rfl | omega)

/-- Even number j=2h of 101 tokens: the D-mode scanner first
    consumes TWO D10 pairs, then h D6 blocks and finally ONE D10 pair.
    The D head then sits on the zero to the left of the scanned gaps.
    Exact total clock: 40h+15, with the full D-right output retained. -/
theorem a101_11_even_dmode_exact (h : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (40 * h + 15)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h))
          (ListBlank.append [1, 1] R)))
      (Cfg.headLeft D (ListBlank.append [0] L)
        (ListBlank.append [1, 0]
          (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
            (ListBlank.append [1, 0, 1, 0, 1, 0] R)))) := by
  have h1 := a101_11_d10_twice_exact (2 * h) L R
  rw [c6_phase_even h L] at h1
  have h2 := d6_sweep_exact h
    (ListBlank.append [0, 1, 0] L)
    (ListBlank.append [1, 0, 1, 0, 1, 0] R)
  have h3 := d10_headLeft_exact
    (ListBlank.append [0] L)
    (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [1, 0, 1, 0, 1, 0] R))
  convert (h1.trans h2).trans h3 using 1 <;> (first | rfl | omega)

/-- Odd number j=2h+1: the phase-correct same sequence leaves
    an extra 001 block on the D-left tape, so the endpoint retains
    a four-bit [0,0,1,0] prefix. Exact total clock: 40h+28. -/
theorem a101_11_odd_dmode_exact (h : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (40 * h + 28)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
          (ListBlank.append [1, 1] R)))
      (Cfg.headLeft D (ListBlank.append [0, 0, 1, 0] L)
        (ListBlank.append [1, 0]
          (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
            (ListBlank.append [1, 0, 1, 0, 1, 0] R)))) := by
  have h1 := a101_11_d10_twice_exact (2 * h + 1) L R
  rw [c6_phase_odd h L] at h1
  rw [← ListBlank.append_pow_succ'
    ([0, 1, 0, 0, 1, 0] : List (Fin 2)) h L] at h1
  have h2 := d6_sweep_exact h
    (ListBlank.append [0, 1, 0, 0, 1, 0] L)
    (ListBlank.append [1, 0, 1, 0, 1, 0] R)
  have h3 := d10_headLeft_exact
    (ListBlank.append [0, 0, 1, 0] L)
    (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
      (ListBlank.append [1, 0, 1, 0, 1, 0] R))
  convert (h1.trans h2).trans h3 using 1 <;> (first | rfl | omega)

end CryptidLink.L17

#print axioms CryptidLink.L17.a101_11_d10_twice_exact
#print axioms CryptidLink.L17.a101_11_even_dmode_exact
#print axioms CryptidLink.L17.a101_11_odd_dmode_exact
