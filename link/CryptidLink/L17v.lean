import CryptidLink.L17u
/-!
# L17: exact odd-100 homogeneous return to a blank-left C head

For every u,v,h : Nat, p=u+6 and c=v+7, start from A with physical
left tape (10)^p 0 (10)^c 0 (10)^3, and right word (101)^(2h+1) 100 R.
The three previously proven, exact paths compose:

* a101_100_odd_c6_exact (32*h+38 steps),
* k41_c01_middle_exact (v+1) (41+2*(v+2) steps),
* k41_c01_last_exact u (41+2*u steps).

The resulting machine-level exact clock is 32*h+2*u+2*v+124,
equivalently 2*p+2*c+98+32*h. The C exit has a truly blank left tape
and complete right word
    1 (11)^u T41 1^(2v+1) T41 010 (111010)^h 1^7 R
where T41=1(01)^6 0. The 010 phase and final zeros are retained.
Exterior context R is arbitrary and unread.

This is a conditional, all-parameter execution theorem only. It does not
assert that the guarded A source occurs on the blank-tape orbit, that all
returns terminate, or that the designated machine halts/nonhalts.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- Guarded A source with p=u+6, c=v+7 and an odd count
    of homogeneous 101 scanner tokens. All left exterior cells are 0. -/
def a100_odd_source (u v h : ℕ) (R : ListBlank (Fin 2)) :
    Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1, 0]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ ((v + 1) + 6))
        (ListBlank.append [0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default))))
    (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
      (ListBlank.append [1, 0, 0] R))

/-- Complete physical C return tape, with the periodic suffix exactly
    010 (111010)^h 1^7 R after the two K41 residual words. -/
def a100_odd_result (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank (Fin 2) :=
  ListBlank.append [1]
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
      (ListBlank.append returnKtail
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 1))
          (ListBlank.append returnKtail
            (ListBlank.append [0, 1, 0]
              (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h)
                (ListBlank.append [1, 1, 1, 1, 1, 1, 1] R)))))))

/-- For all u,v,h and any unread right context R, the raw machine reaches
    C with a genuinely blank left tape in exactly 32h+2u+2v+124 steps.
    This is the odd-100 guarded homogeneous return family. -/
theorem a100_odd_blankleft_exact (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (32 * h + 2 * u + 2 * v + 124)
      (a100_odd_source u v h R)
      (Cfg.headRight C default (a100_odd_result u v h R)) := by
  let Lp : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default
  let L : ListBlank (Fin 2) :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ ((v + 1) + 6))
      (ListBlank.append [0] Lp)
  let Seven : ListBlank (Fin 2) :=
    ListBlank.append [1, 1, 1, 1, 1, 1, 1] R
  let Rmid : ListBlank (Fin 2) :=
    ListBlank.append [0, 1, 0]
      (ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ h) Seven)
  let FullTailR : ListBlank (Fin 2) := ListBlank.append returnKtail Rmid
  let Rlast : ListBlank (Fin 2) :=
    ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 1)) FullTailR

  have h1 := a101_100_odd_c6_exact h L R
  have hphase :
      ListBlank.append (([1, 1, 1, 0, 1, 0] : List (Fin 2)) ^ (h + 1)) Seven =
      ListBlank.append [1, 1, 1] Rmid := by
    rw [ListBlank.append_pow_succ
      ([1, 1, 1, 0, 1, 0] : List (Fin 2)) h Seven]
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
      Cfg.headRight C default (a100_odd_result u v h R) := by
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
  convert h123 using 1 <;> (first | rfl | omega | (simp only [a100_odd_source, ListBlank.append_append]; rfl))

end CryptidLink.L17

#print axioms CryptidLink.L17.a100_odd_blankleft_exact
