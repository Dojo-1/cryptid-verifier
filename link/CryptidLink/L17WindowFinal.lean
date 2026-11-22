import CryptidLink.L17WindowSource

/-!
# E71 — normalize exact E60 output words

No new machine transitions: list-word identities translate E70's exact
C-to-C paths into the original E60 F1/F3 terminal expressions.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))
private abbrev I := ([1] : List (Fin 2))

/-- Pure tape algebra: move five fixed 01 pairs through the variable
    block and expose the exact six-bit E60 suffix. This is independent
    of the outer ones prefix and the variable right exterior. -/
private theorem one_pair_word (v : ℕ) (X : Bits) :
    push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
      (push (P ^ (v + 5)) (push [0, 0] X)) =
    push (P ^ (v + 8)) (push [0, 1, 0, 1, 0, 0] X) := by
  let T : Bits := push [0, 0] X
  change push (P ^ 5) (push (P ^ (v + 5)) T) =
    push (P ^ (v + 8)) (push (P ^ 2) T)
  rw [← ListBlank.append_pow_add P 5 (v + 5) T,
      ← ListBlank.append_pow_add P (v + 8) 2 T,
      show 5 + (v + 5) = (v + 8) + 2 by omega]

private theorem one_normalize (m u v : ℕ) (R : Bits) :
    push (I ^ (2 * u + 6))
      (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
        (push (P ^ (v + 5))
          (push [0, 0] (push (Q ^ 16) (push (Q ^ (m + 1)) R))))) =
      push (I ^ (2 * u + 6))
        (push (P ^ (v + 8))
          (push [0, 1, 0, 1, 0, 0]
            (push (Q ^ (16 + (m + 1))) R))) := by
  have hQ : push (Q ^ 16) (push (Q ^ (m + 1)) R) =
      push (Q ^ (16 + (m + 1))) R :=
    (ListBlank.append_pow_add Q 16 (m + 1) R).symm
  rw [hQ, one_pair_word v (push (Q ^ (16 + (m + 1))) R)]

private theorem three_normalize (m u v : ℕ) (R : Bits) :
    five_run_bottom_result u
      (push (I ^ (2 * (v + 2)))
        (push (P ^ 21) (push [0] (push (Q ^ (m + 1)) R)))) =
    push (I ^ (2 * u + 1))
      (push (Q ^ 7)
        (push (I ^ (2 * v + 4))
          (push (P ^ (21 + (m + 1))) (push [0] R)))) := by
  unfold five_run_bottom_result
  rw [one_pow_two_mul u, rotLB0 (m + 1) R]
  let T : Bits := push [0] R
  have hP : push (P ^ 21) (push (P ^ (m + 1)) T) =
      push (P ^ (21 + (m + 1))) T :=
    (ListBlank.append_pow_add P 21 (m + 1) T).symm
  rw [hP]
  let S : Bits := push (Q ^ 7)
    (push (I ^ (2 * (v + 2)))
      (push (P ^ (21 + (m + 1))) T))
  change push (I ^ 1) (push (I ^ (2 * u)) S) =
    push (I ^ (2 * u + 1))
      (push (Q ^ 7)
        (push (I ^ (2 * v + 4))
          (push (P ^ (21 + (m + 1))) T)))
  rw [← ListBlank.append_pow_add I 1 (2 * u) S,
      show 1 + 2 * u = 2 * u + 1 by omega]
  dsimp only [S]
  rw [show 2 * (v + 2) = 2 * v + 4 by omega]

/-- Canonical E60 G1(M), every M=m+1 >= 1, with exact full F1 output. -/
theorem e71_one_full_E60_exact (m u v : ℕ) (R : Bits) :
    ReachesIn target (214 + 6 * (m + 1) + 2 * u + 4 * v)
      (widthFourCutSource u v
        (push [1] (push (Q ^ 7) (push [1, 1, 0, 1]
          (push (Q ^ (m + 1)) (push [1, 1, 1] R))))))
      (Cfg.headRight C default
        (push (I ^ (2 * u + 6))
          (push (P ^ (v + 8))
            (push [0, 1, 0, 1, 0, 0]
              (push (Q ^ (16 + (m + 1))) R))))) := by
  have h := e70_one_from_widthFour_exact m u v R
  rw [one_normalize m u v R] at h
  exact h

/-- Canonical E60 G3(M), every M=m+1 >= 1, with exact full F3 output. -/
theorem e71_three_full_E60_exact (m u v : ℕ) (R : Bits) :
    ReachesIn target (268 + 6 * (m + 1) + 2 * u + 2 * v)
      (widthFourCutSource u v
        (push [1, 1, 1] (push (Q ^ 7) (push [1, 1, 0, 1]
          (push (Q ^ (m + 1)) (push [1, 1, 1] R))))))
      (Cfg.headRight C default
        (push (I ^ (2 * u + 1))
          (push (Q ^ 7)
            (push (I ^ (2 * v + 4))
              (push (P ^ (21 + (m + 1))) (push [0] R)))))) := by
  have h := e70_three_from_widthFour_exact m u v R
  rw [three_normalize m u v R] at h
  exact h

end CryptidLink.L17

#print axioms CryptidLink.L17.e71_one_full_E60_exact
#print axioms CryptidLink.L17.e71_three_full_E60_exact
