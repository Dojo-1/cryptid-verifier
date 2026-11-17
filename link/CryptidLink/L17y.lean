import CryptidLink.L17x
/-!
# L17: exact D-mode local kernels and arbitrary-length D10 sweeps

The two remaining homogeneous return families end in \`11\` and
initially run in D mode. The exact kernels below are transcriptions
of the source/endpoint windows in
\`analysis/l17-a-stream/kernels.json\`:

* D10: D on local -1..0, input 10, four defined steps,
  exits D at -2 with the same two-bit output;
* J1K: D on local -4..2, input 0010010, ten steps,
  exits D at -4 with output 0101010;
* K22: D on local -8..4, input 1010101001010, 22 steps,
  exits C at -8 with output 1101010101010.

The left tape lists are head-nearest-first. The arbitrary exterior
\`L\` and \`R\` are not inspected. These theorems are for the
raw L17 machine with the target's exact step relation and do not
assert blank-tape reachability or a complete section return.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Exact four-step D10 kernel; the D head starts on the right bit of
    input 10 and moves two cells left, preserving both bits. -/
theorem d10_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 4
      (Cfg.headRight D (ListBlank.append [1] L)
        (ListBlank.append [0] R))
      (Cfg.headLeft D L (ListBlank.append [1, 0] R)) := by
  l17_exact_steps

/-- Head-left presentation of D10, with its exact two-cell frame.
    This is the form suitable for composing repeated leftward sweeps. -/
theorem d10_headLeft_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 4
      (Cfg.headLeft D (ListBlank.append [0, 1] L) R)
      (Cfg.headLeft D L (ListBlank.append [1, 0] R)) := by
  have he :
      Cfg.headLeft D (ListBlank.append [0, 1] L) R =
      Cfg.headRight D (ListBlank.append [1] L)
        (ListBlank.append [0] R) :=
    Cfg.headLeft_cons D (0 : Fin 2) (ListBlank.append [1] L) R
  rw [he]
  exact d10_exact L R

/-- Every finite D10 sweep consumes n 01 left-tape pairs, writes
    n 10 right-tape pairs and requires exactly 4n defined transitions.
    The invariant retains both arbitrary exterior tapes. -/
theorem d10_sweep_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (4 * n)
      (Cfg.headLeft D
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) L) R)
      (Cfg.headLeft D L
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R)) := by
  induction n generalizing R with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, ListBlank.append_nil]
    exact ReachesIn.zero _ _
  | succ n ih =>
    have h1 : ReachesIn target 4
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 1)) L) R)
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) L)
          (ListBlank.append [1, 0] R)) := by
      rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) n L]
      exact d10_headLeft_exact _ _
    have h2 := ih (ListBlank.append [1, 0] R)
    rw [← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) n R]
    convert h1.trans h2 using 1 <;> omega

/-- J1K on [-4,2]: input 0010010, output 0101010.
    Ten defined steps, D head reaches x=-4. -/
theorem j1k_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 10
      (Cfg.headRight D (ListBlank.append [0, 1, 0, 0] L)
        (ListBlank.append [0, 1, 0] R))
      (Cfg.headRight D L
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0] R)) := by
  l17_exact_steps

/-- K22 on [-8,4]: input 1010101001010, output 1101010101010.
    Twenty-two defined steps, exits C on the leftmost output cell. -/
theorem k22_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 22
      (Cfg.headRight D
        (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1] L)
        (ListBlank.append [0, 1, 0, 1, 0] R))
      (Cfg.headRight C L
        (ListBlank.append [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 4096 in
    l17_exact_steps

end CryptidLink.L17

#print axioms CryptidLink.L17.d10_exact
#print axioms CryptidLink.L17.d10_headLeft_exact
#print axioms CryptidLink.L17.d10_sweep_exact
#print axioms CryptidLink.L17.j1k_exact
#print axioms CryptidLink.L17.k22_exact
