import CryptidLink.L17q
/-!
# L17: exact C01 sweeps and the short K41 bottom kernel

The local C01 two-step move has a complete head-relative frame and an exact
clock. Its n-fold induction yields a 2*n-step left-moving sweep. K41short
is the 41-step read-bounded kernel in
analysis/l17-a-stream/kernels.json, with read interval [-10,3] and declared
input interval [-11,3]. In the source below the head is at position 0;
the target head is at position -11, with full output tape preserved.

These are statements about arbitrary initial machine configurations. No
blank-orbit membership, general section-return, or nonhalting claim follows.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- C01, the local leftward two-cell conversion 01 -> 11.
    Initial C head at x=0 on a 1, exit C head at x=-2. -/
theorem c01_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 2
      (Cfg.headRight C (ListBlank.append [0] L)
        (ListBlank.append [1] R))
      (Cfg.headLeft C L (ListBlank.append [1, 1] R)) := by
  l17_exact_steps

/-- Exact C01 sweep of any number n of alternating pairs.
    Input on the left is head-nearest-first (10)^n; output right is (11)^n.
    Both exterior contexts are arbitrary and remain unchanged. -/
theorem c01_sweep_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (2 * n)
      (Cfg.headLeft C
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) L) R)
      (Cfg.headLeft C L
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) R)) := by
  induction n generalizing R with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, ListBlank.append_nil]
    exact ReachesIn.zero _ _
  | succ n ih =>
    have h1 : ReachesIn target 2
        (Cfg.headLeft C
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L) R)
        (Cfg.headLeft C
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) L)
          (ListBlank.append [1, 1] R)) := by
      rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) n L]
      have he :
          Cfg.headLeft C
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) L)) R =
          Cfg.headRight C
            (ListBlank.append [0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) L))
            (ListBlank.append [1] R) := by
        exact Cfg.headLeft_cons C (1 : Fin 2) _ R
      rw [he]
      exact c01_exact _ _
    have h2 := ih (ListBlank.append [1, 1] R)
    rw [← ListBlank.append_pow_succ' ([1, 1] : List (Fin 2)) n R]
    convert h1.trans h2 using 1 <;> omega

/-- K41short: C on the zero after six (10) pairs and three subsequent
    ones, with arbitrary untouched exterior tapes. Exactly 41 transitions
    yield C at x=-11 (leftmost cell of the window), with the full output
    word 11(01)^6 0 on the right. -/
theorem k41short_exact (L R : ListBlank (Fin 2)) :
    ReachesIn target 41
      (Cfg.headRight C
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] L)
        (ListBlank.append [0, 1, 1, 1] R))
      (Cfg.headRight C L
        (ListBlank.append [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R)) := by
  set_option maxRecDepth 4096 in
    l17_exact_steps

end CryptidLink.L17

#print axioms CryptidLink.L17.c01_exact
#print axioms CryptidLink.L17.c01_sweep_exact
#print axioms CryptidLink.L17.k41short_exact
