import CryptidLink.L17t
/-!
# L17: first nonzero-repetition homogeneous return, exact and blank-left

For u,v,h : Nat, set p=u+6 and c=v+7. Starting from A with
physical left tape (10)^p 0 (10)^c 0 (10)^3 and right input
(101)^(2h+2) 00 R, the full C return is obtained by composing:

  a101_00_even_c6_exact (clock 32h+42)
  k41_c01_middle_exact (clock 41+2(v+2))
  k41_c01_last_exact (clock 41+2u)

The resulting clock is 32h+2u+2v+128 = 2p+2c+102+32h.
The final C head has a completely blank left tape. The full right word
retains *both* K41 tails and the 010 periodic-boundary word; do not
discard an interior zero or replace the result with a substring.

These statements concern arbitrary guarded starting configurations,
not reachability from the blank tape or a global nonhalting argument.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Guarded A source with p=u+6, c=v+7 and an even positive count
    of homogeneous 101 scanner tokens. All left exterior cells are 0. -/
def a00_even_source (u v h : ℕ) (R : ListBlank (Fin 2)) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ ((v + 1) + 6))
        (ListBlank.append [0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))))
    (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 2))
      (ListBlank.append [0, 0] R))

/-- Complete physical C return tape, with the periodic suffix exactly
    010 (111010)^h 1^9 R after the two K41 residual words. -/
def a00_even_result (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank (Fin 2) :=
  ListBlank.append [1]
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
      (ListBlank.append returnKtail
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 1))
          (ListBlank.append returnKtail
            (ListBlank.append [0, 1, 0]
              (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
                (ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R)))))))

/-- For all u,v,h and any unread right context R, the raw machine reaches
    C with a genuinely blank left tape in exactly 32h+2u+2v+128 steps.
    This is the positive-even-00 guarded homogeneous return family. -/
theorem a00_even_blankleft_exact (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (32 * h + 2 * u + 2 * v + 128)
      (a00_even_source u v h R)
      (Cfg.headRight C default (a00_even_result u v h R)) := by
  let Lp : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default
  let L : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ ((v + 1) + 6))
      (ListBlank.append [0] Lp)
  let Nine : ListBlank (Fin 2) :=
    ListBlank.append [1, 1, 1, 1, 1, 1, 1, 1, 1] R
  let Rmid : ListBlank (Fin 2) :=
    ListBlank.append [0, 1, 0]
      (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h) Nine)
  let FullTailR : ListBlank (Fin 2) := ListBlank.append returnKtail Rmid
  let Rlast : ListBlank (Fin 2) :=
    ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 1)) FullTailR

  have h1 := a101_00_even_c6_exact h L R
  have hphase :
      ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ (h + 1)) Nine =
      ListBlank.append [1, 1, 1] Rmid := by
    rw [ListBlank.append_pow_succ
      ([1, 1, 1, 0, 1, 0] : List (Fin 2)) h Nine]
    rfl
  rw [hphase] at h1

  have h2 := k41_c01_middle_exact (v + 1) Lp Rmid
  have h12 := h1.trans h2

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

  rw [hones] at h12
  have h3 := k41_c01_last_exact u default Rlast
  have h123 := h12.trans h3

  have he :
      Cfg.headLeft C (ListBlank.append [1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append returnKtail Rlast)) =
      Cfg.headRight C default (a00_even_result u v h R) := by
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
  convert h123 using 1 <;> (first | rfl | omega | (simp only [a00_even_source, ListBlank.append_append]; rfl))

end CryptidLink.L17

#print axioms CryptidLink.L17.a00_even_blankleft_exact
