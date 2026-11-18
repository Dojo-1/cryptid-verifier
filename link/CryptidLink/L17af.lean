import CryptidLink.L17ae
/-!
# L17: normalize the complete parametric mixed-width return word

PR #32 proved a conditional all-width raw-machine return for the
mixed token prefix 01·101·01·101·00, with p=u+4 and arbitrary c.
Its right tape was deliberately stated as a fully framed unnormalized
word, to avoid smuggling a string simplification into the machine proof.

This file proves that the resulting word *is identically equal* to
    1^(2p-6) (01)^(c+11) 0111 R
or, subtraction-free in Lean with p=u+4,
    1^(2u+2) (01)^(c+11) 0111 R.

No coordinates or tape cells are discarded; these are literal
ListBlank word equalities. The canonical execution statements follow
by rewriting the already certified machine theorem.

All exterior tapes remain symbolic. These are guarded source theorems,
not a blanket mixed-stack return, designated blank-orbit occurrence,
stack boundedness or a halting/non-halting result.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

def mixed_width2_canonical_result (u c : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 11))
      (ListBlank.append [0, 1, 1, 1] R))

private theorem mixed_ones_prefix (u : ℕ) (T : ListBlank (Fin 2)) :
    ListBlank.append [1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1] T)) =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2)) T := by
  rw [one_pow_two_mul]
  rw [show 2 * u + 2 = 1 + (2 * u + 1) by omega,
    ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * u + 1) T,
    ListBlank.append_pow_succ' ([1] : List (Fin 2)) (2 * u) T]
  rfl

private theorem mixed_ten_prefix (c : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append [1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 7))
          (ListBlank.append [1, 1, 1] R))) =
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 11))
          (ListBlank.append [0, 1, 1, 1] R)) := by
  let Tail : ListBlank (Fin 2) := ListBlank.append [1, 1, 1] R
  have hcombine :
      ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append [1, 0]
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 7)) Tail)) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 12)) Tail := by
    change
      ListBlank.append (([1, 0] : List (Fin 2)) ^ 4)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 7)) Tail)) = _
    rw [← ListBlank.append_pow_add ([1, 0] : List (Fin 2))
          1 (c + 7) Tail,
      ← ListBlank.append_pow_add ([1, 0] : List (Fin 2))
          4 (1 + (c + 7)) Tail]
    exact congrArg (fun n : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) Tail) (by omega)
  have hrotate :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 12)) Tail =
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 11))
          (ListBlank.append [0] Tail)) := by
    have hpow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 12)) Tail =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (c + 11))
          (ListBlank.append [1, 0] Tail) := by
      rw [show c + 12 = (c + 11) + 1 by omega,
        ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) (c + 11) Tail]
    exact hpow.trans (rotLB (c + 11) (ListBlank.append [0] Tail)).symm
  exact hcombine.trans hrotate

/-- Literal identity: unnormalized physical right tape equals the
    canonical exponent word for every u,c and arbitrary R. -/
theorem mixed_width2_result_normalized (u c : ℕ)
    (R : ListBlank (Fin 2)) :
    mixed_width2_result u c R =
      mixed_width2_canonical_result u c R := by
  unfold mixed_width2_result mixed_width2_canonical_result
  rw [mixed_ten_prefix c R]
  exact mixed_ones_prefix u
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 11))
      (ListBlank.append [0, 1, 1, 1] R))

/-- Exact all-width contextual mixed return, in canonical full-tape
    notation: 2u+4c+134 steps with exterior L,R unchanged. -/
theorem mixed_width2_canonical_exact (u c : ℕ)
    (L R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 4 * c + 134)
      (mixed_width2_source u c L R)
      (Cfg.headRight C L (mixed_width2_canonical_result u c R)) := by
  rw [← mixed_width2_result_normalized u c R]
  exact mixed_width2_parametric_exact u c L R

/-- Blank-left specialization with full canonical result and exact clock. -/
theorem mixed_width2_canonical_blankleft (u c : ℕ)
    (R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 4 * c + 134)
      (mixed_width2_source u c default R)
      (Cfg.headRight C default (mixed_width2_canonical_result u c R)) :=
  mixed_width2_canonical_exact u c default R

end CryptidLink.L17

#print axioms CryptidLink.L17.mixed_width2_result_normalized
#print axioms CryptidLink.L17.mixed_width2_canonical_exact
#print axioms CryptidLink.L17.mixed_width2_canonical_blankleft
