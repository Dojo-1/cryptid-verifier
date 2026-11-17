import CryptidLink.L17m
/-!
# L17: arbitrary-length homogeneous 101 scanner

This proves exact defined-step execution for *every finite repetition count*.
It is a theorem about arbitrary framed A configurations, not a blank-tape
reachability statement and not a claim about what happens after the terminal
token. The repeated inserted left block [0,0,1] is the head-nearest-first
encoding of each new nonzero-width internal run plus its separator.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- For any j, the A scanner consumes (101)^j in exactly 13*j steps,
    moves its head +3*j and grows j additional runs in the represented
    left stack. No exterior context is inspected or rewritten.

    The left tape is nearest-first: the initial suffix is (01)^3 0 L,
    and its exact endpoint is (01)^3 (001)^j 0 L. -/
theorem a101_repeat_exact (j : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (13 * j)
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1] (ListBlank.append [0] L))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ j) R))
      (Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [0] L)))
        R) := by
  induction j generalizing R with
  | zero =>
    simp only [Nat.mul_zero]
    exact ReachesIn.zero _ _
  | succ j ih =>
    have h1 := ih (ListBlank.append [1, 0, 1] R)
    have h2 : ReachesIn target 13
        (Cfg.headRight A
          (ListBlank.append [0, 1, 0, 1, 0, 1]
            (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
              (ListBlank.append [0] L)))
          (ListBlank.append [1, 0, 1] R))
        (Cfg.headRight A
          (ListBlank.append [0, 1, 0, 1, 0, 1]
            (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ (j + 1))
              (ListBlank.append [0] L)))
          R) := by
      rw [ListBlank.append_pow_succ ([0, 0, 1] : List (Fin 2)) j
        (ListBlank.append [0] L)]
      exact a101_exact
        (ListBlank.append [0, 1]
          (ListBlank.append (([0, 0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append [0] L))) R
    rw [← ListBlank.append_pow_succ' ([1, 0, 1] : List (Fin 2)) j R]
    convert h1.trans h2 using 1 <;> omega

end CryptidLink.L17

#print axioms CryptidLink.L17.a101_repeat_exact
