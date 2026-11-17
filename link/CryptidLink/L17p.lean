import CryptidLink.L17o
/-!
# L17: exact periodic left-moving C and D sweeps

The fixed, contextual C6 and D6 kernels were proved in L17m.
Here they are iterated for *all* h : Nat. The same six-cell input
block [0,1,0,0,1,0] is consumed moving left, but the written blocks
and raw clocks differ by mode:

  C: 010010 -> 111010, exactly 6*h transitions for h blocks;
  D: 010010 -> 101010, exactly 14*h transitions for h blocks.

Both conclusions preserve arbitrary unread exterior contexts and
the exact C/D head orientation. The left tape source is head-nearest-first.
These are raw finite-execution theorems, not returns to a global section
and not assertions about designated blank-tape reachability.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Every h-block C6 sweep moves left through h copies of 010010, writing
    h copies of 111010, in exactly 6*h defined machine transitions. -/
theorem c6_sweep_exact (h : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (6 * h)
      (Cfg.headLeft C
        (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ h) L)
        R)
      (Cfg.headLeft C L
        (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h) R)) := by
  induction h generalizing R with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, ListBlank.append_nil]
    exact ReachesIn.zero _ _
  | succ h ih =>
    have e : (Cfg.headLeft C
        (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ (h + 1)) L) R) =
        Cfg.headRight C
          (ListBlank.append [1, 0, 0, 1, 0]
            (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ h) L))
          (ListBlank.append [0] R) := by
      rw [ListBlank.append_pow_succ ([0, 1, 0, 0, 1, 0] : List (Fin 2)) h L]
      exact Cfg.headLeft_cons C (0 : Fin 2) _ R
    have h1 : ReachesIn target 6
        (Cfg.headLeft C
          (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ (h + 1)) L) R)
        (Cfg.headLeft C
          (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ h) L)
          (ListBlank.append [1, 1, 1, 0, 1, 0] R)) := by
      rw [e]
      exact c6_exact _ _
    have h2 := ih (ListBlank.append [1, 1, 1, 0, 1, 0] R)
    rw [← ListBlank.append_pow_succ' ([1, 1, 1, 0, 1, 0] : List (Fin 2)) h R]
    convert h1.trans h2 using 1 <;> omega

/-- Every h-block D6 sweep moves left through h copies of 010010, writing
    h copies of 101010, in exactly 14*h defined machine transitions. -/
theorem d6_sweep_exact (h : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (14 * h)
      (Cfg.headLeft D
        (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ h) L)
        R)
      (Cfg.headLeft D L
        (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h) R)) := by
  induction h generalizing R with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, ListBlank.append_nil]
    exact ReachesIn.zero _ _
  | succ h ih =>
    have e : (Cfg.headLeft D
        (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ (h + 1)) L) R) =
        Cfg.headRight D
          (ListBlank.append [1, 0, 0, 1, 0]
            (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ h) L))
          (ListBlank.append [0] R) := by
      rw [ListBlank.append_pow_succ ([0, 1, 0, 0, 1, 0] : List (Fin 2)) h L]
      exact Cfg.headLeft_cons D (0 : Fin 2) _ R
    have h1 : ReachesIn target 14
        (Cfg.headLeft D
          (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ (h + 1)) L) R)
        (Cfg.headLeft D
          (ListBlank.append (([0, 1, 0, 0, 1, 0] : List (Fin 2)) ^ h) L)
          (ListBlank.append [1, 0, 1, 0, 1, 0] R)) := by
      rw [e]
      exact d6_exact _ _
    have h2 := ih (ListBlank.append [1, 0, 1, 0, 1, 0] R)
    rw [← ListBlank.append_pow_succ' ([1, 0, 1, 0, 1, 0] : List (Fin 2)) h R]
    convert h1.trans h2 using 1 <;> omega

end CryptidLink.L17

#print axioms CryptidLink.L17.c6_sweep_exact
#print axioms CryptidLink.L17.d6_sweep_exact
