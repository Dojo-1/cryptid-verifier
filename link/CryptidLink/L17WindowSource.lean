import CryptidLink.L17WindowComplete

/-!
# E70 — restore the original width-four C-checkpoint source

The parameter m used by E65 corresponds to physical E60 width M=m+1.
These two theorems identify the original widthFourCutSource (including the
whole left tape) with the E65 input and apply the already-certified E69
C-to-C result. Canonical terminal word normalization remains separate.
-/

open BusyBeaver BusyBeaver.SixState Turing
namespace CryptidLink.L17

private abbrev Bits := ListBlank (Fin 2)
local notation "push" => @ListBlank.append (Fin 2) _
private abbrev P := ([0, 1] : List (Fin 2))
private abbrev Q := ([1, 0] : List (Fin 2))
private abbrev I := ([1] : List (Fin 2))

private abbrev G1 (m : ℕ) (R : Bits) : Bits :=
  push [1] (push (Q ^ 7) (push [1, 1, 0, 1]
    (push (Q ^ (m + 1)) (push [1, 1, 1] R))))
private abbrev G3 (m : ℕ) (R : Bits) : Bits :=
  push [1, 1, 1] (push (Q ^ 7) (push [1, 1, 0, 1]
    (push (Q ^ (m + 1)) (push [1, 1, 1] R))))

private theorem one_source_frame (m u v : ℕ) (R : Bits) :
    widthFourCutSource u v (G1 m R) =
      Cfg.headRight C
        (push [1, 0, 1, 0, 0, 1]
          (push [0] (push (P ^ (v + 7)) (push [0] (push (P ^ (u + 6)) default)))))
        (push [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
          (push (Q ^ m) (push [1, 1, 1] R))) := by
  unfold widthFourCutSource
  rw [ListBlank.append_pow_succ Q m (push [1, 1, 1] R)]
  rfl

private theorem three_source_frame (m u v : ℕ) (R : Bits) :
    widthFourCutSource u v (G3 m R) =
      Cfg.headRight C
        (push [1, 0, 1, 0, 0, 1, 0, 0, 1]
          (push (P ^ (v + 6)) (push [0] (push (P ^ (u + 6)) default))))
        (push [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]
          (push (Q ^ m) (push [1, 1, 1] R))) := by
  unfold widthFourCutSource
  rw [ListBlank.append_pow_succ Q m (push [1, 1, 1] R),
      ListBlank.append_pow_succ P (v + 6)
        (push [0] (push (P ^ (u + 6)) default))]
  rfl

/-- The one-headed E60 width-four source reaches the full E69 blank-left C tape. -/
theorem e70_one_from_widthFour_exact (m u v : ℕ) (R : Bits) :
    ReachesIn target (214 + 6 * (m + 1) + 2 * u + 4 * v)
      (widthFourCutSource u v (G1 m R))
      (Cfg.headRight C default
        (push (I ^ (2 * u + 6))
          (push [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
            (push (P ^ (v + 5))
              (push [0, 0] (push (Q ^ 16) (push (Q ^ (m + 1)) R))))))) := by
  rw [one_source_frame m u v R]
  exact e69_one_from_contextual_C_exact m u v R

/-- The three-headed E60 width-four source reaches the full E69 blank-left C tape. -/
theorem e70_three_from_widthFour_exact (m u v : ℕ) (R : Bits) :
    ReachesIn target (268 + 6 * (m + 1) + 2 * u + 2 * v)
      (widthFourCutSource u v (G3 m R))
      (Cfg.headRight C default
        (five_run_bottom_result u
          (push (I ^ (2 * (v + 2)))
            (push (P ^ 21) (push [0] (push (Q ^ (m + 1)) R)))))) := by
  rw [three_source_frame m u v R]
  exact e69_three_from_contextual_C_exact m u v R

end CryptidLink.L17

#print axioms CryptidLink.L17.e70_one_from_widthFour_exact
#print axioms CryptidLink.L17.e70_three_from_widthFour_exact
