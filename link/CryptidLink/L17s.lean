import CryptidLink.L17r
/-!
# L17: exact K41short plus arbitrary C01 bottom-layer compositions

Two distinct, fully framed shapes are formalized:

1. A middle layer has an explicit zero separator to the next left run.
   K41short followed by n+1 C01 pairs consumes that separator and ends
   in C with the original exterior left tape L under the head.
2. The outermost layer lacks that separator. K41short followed by n C01
   pairs stops on the first 1 of L instead. These two frames MUST NOT
   be identified; that is the relevant off-by-one obstruction.

All statements have exact transition counts and arbitrary exterior L/R.
They are raw machine reachability, not a universal section-return theorem.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Tail of K41short's output after transporting the first 1 across the
    directed-head representation boundary. The trailing 0 is retained. -/
private abbrev Ktail : List (Fin 2) :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- A middle-layer K41short followed by n+1 C01 conversions.
    Source: C scanning the rightmost 0 of (10)^(n+6), with a 0 separator
    to arbitrary left context L and at least three right-side ones.
    Endpoint: C scanning the first bit of L (headLeft), with an exact
    right output (11)^(n+1) ++ Ktail ++ R.
    All right tape beyond the three entering ones is untouched. -/
theorem k41_c01_middle_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (41 + 2 * (n + 1))
      (Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 6))
          (ListBlank.append [0] L))
        (ListBlank.append [1, 1, 1] R))
      (Cfg.headLeft C L
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1))
          (ListBlank.append Ktail R))) := by
  let X := ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
    (ListBlank.append [0] L)
  have hs :
      Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 6))
          (ListBlank.append [0] L))
        (ListBlank.append [1, 1, 1] R) =
      Cfg.headRight C
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] X)
        (ListBlank.append [0, 1, 1, 1] R) := by
    rw [show n + 6 = 6 + n by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 6 n (ListBlank.append [0] L)]
    exact Cfg.headLeft_cons C (0 : Fin 2) _ _
  have hrot :
      ListBlank.append [1] X =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L := by
    dsimp [X]
    rw [rotLB n (ListBlank.append [0] L)]
    rw [← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) n L]
    rfl
  have he :
      Cfg.headRight C X
        (ListBlank.append [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R) =
      Cfg.headLeft C
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L)
        (ListBlank.append Ktail R) := by
    rw [← hrot]
    exact Cfg.headRight_cons C (1 : Fin 2) X (ListBlank.append Ktail R)
  have h1 := k41short_exact X R
  rw [← hs, he] at h1
  exact h1.trans (c01_sweep_exact (n + 1) L (ListBlank.append Ktail R))

/-- The outermost layer is different: no separator is consumed.
    The C head remains on an explicit 1 immediately before the
    arbitrary left context L. The clock is 41+2n, not 41+2(n+1). -/
theorem k41_c01_last_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (41 + 2 * n)
      (Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 6)) L)
        (ListBlank.append [1, 1, 1] R))
      (Cfg.headLeft C (ListBlank.append [1] L)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ n)
          (ListBlank.append Ktail R))) := by
  let X := ListBlank.append (([0, 1] : List (Fin 2)) ^ n) L
  have hs :
      Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 6)) L)
        (ListBlank.append [1, 1, 1] R) =
      Cfg.headRight C
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] X)
        (ListBlank.append [0, 1, 1, 1] R) := by
    rw [show n + 6 = 6 + n by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 6 n L]
    exact Cfg.headLeft_cons C (0 : Fin 2) _ _
  have hrot :
      ListBlank.append [1] X =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] L) :=
    rotLB n L
  have he :
      Cfg.headRight C X
        (ListBlank.append [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R) =
      Cfg.headLeft C
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] L))
        (ListBlank.append Ktail R) := by
    rw [← hrot]
    exact Cfg.headRight_cons C (1 : Fin 2) X (ListBlank.append Ktail R)
  have h1 := k41short_exact X R
  rw [← hs, he] at h1
  exact h1.trans (c01_sweep_exact n (ListBlank.append [1] L) (ListBlank.append Ktail R))

end CryptidLink.L17

#print axioms CryptidLink.L17.k41_c01_middle_exact
#print axioms CryptidLink.L17.k41_c01_last_exact
