import CryptidLink.L17s
/-!
# L17: first complete, exact blank-left C return from a two-gap A state

For arbitrary u,v : Nat and right context R, set p = u+6, c = v+7.
The source left tape (spatial left-to-right) is
  (10)^p 0 (10)^c 0 (10)^3
with A scanning the cell immediately to its right and right input 00R.

Three certified paths compose:
  A00L (10 steps),
  middle K41/C01 (41 + 2*(v+2) steps),
  outer K41/C01 (41 + 2*u steps).

The full clock is 2*u + 2*v + 96 = 2*p + 2*c + 70.
The C endpoint has an *actually blank* left tape, not merely a local
C-mode return with an unconsumed left stack.

The exact right word uses two retained K41 residuals, each
T41 = 1(01)^6 0. It is not shortened by deleting the zero. The
literature-note normalized word is
  1^(2p-10) (01)^7 1^(2c-13) (01)^7 1^5 R;
that additional word normalization is a separate arithmetic identity.
This theorem certifies the complete unnormalized word as a machine
configuration. No statement about blank-orbit occurrence is made.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- The exact 14-bit remainder after the K41-directed-head rotation. -/
abbrev returnKtail : List (Fin 2) :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Guarded A source, with p=u+6 and c=v+7. Left tape is nearest-first.
    Both exterior tapes are default zeros except for explicit context R. -/
def a00_zero_source (u v : ℕ) (R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ ((v + 1) + 6))
        (ListBlank.append [0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))))
    (ListBlank.append [0, 0] R)

/-- Complete physical C right word. No zero separators are erased:
    1 (11)^u T41 1^(2v+1) T41 1^6 R. -/
def a00_zero_result (u v : ℕ) (R : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append [1]
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
      (ListBlank.append returnKtail
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 1))
          (ListBlank.append returnKtail
            (ListBlank.append [1, 1, 1, 1, 1, 1] R)))))

/-- For *all* u,v and every unread right context R, the full source
    returns in exactly 2u+2v+96 defined transitions to a blank-left C
    configuration with the exact entire right tape a00_zero_result. -/
theorem a00_zero_blankleft_exact (u v : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (2 * u + 2 * v + 96)
      (a00_zero_source u v R)
      (Cfg.headRight C default (a00_zero_result u v R)) := by
  let Lp : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default
  let TailR : ListBlank (Fin 2) := ListBlank.append [1, 1, 1, 1, 1, 1] R
  let FullTailR : ListBlank (Fin 2) := ListBlank.append returnKtail TailR
  let Rlast : ListBlank (Fin 2) :=
    ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 1)) FullTailR

  have h1 :=
    a00l_exact
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ ((v + 1) + 6))
        (ListBlank.append [0] Lp)) R
  have h2 := k41_c01_middle_exact (v + 1) Lp TailR

  have hones :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ ((v + 1) + 1)) FullTailR =
      ListBlank.append [1, 1, 1] Rlast := by
    change
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 2)) FullTailR =
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 1)) FullTailR)
    rw [one_pow_two_mul (v + 2),
      show 2 * (v + 2) = 3 + (2 * v + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (2 * v + 1) FullTailR]
    rfl

  have h12 : ReachesIn target (10 + (41 + 2 * ((v + 1) + 1)))
      (a00_zero_source u v R)
      (Cfg.headLeft C Lp (ListBlank.append [1, 1, 1] Rlast)) := by
    rw [← hones]
    exact h1.trans h2

  have h3 := k41_c01_last_exact u default Rlast
  have h123 := h12.trans h3

  have he :
      Cfg.headLeft C (ListBlank.append [1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append returnKtail Rlast)) =
      Cfg.headRight C default (a00_zero_result u v R) := by
    change
      Cfg.headLeft C (ListBlank.append [1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append returnKtail Rlast)) =
      Cfg.headRight C default
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
            (ListBlank.append returnKtail Rlast)))
    exact (Cfg.headRight_cons C (1 : Fin 2) default
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append returnKtail Rlast))).symm

  rw [he] at h123
  convert h123 using 1 <;> omega

end CryptidLink.L17

#print axioms CryptidLink.L17.a00_zero_blankleft_exact
