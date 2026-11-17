import CryptidLink.L17aa
/-!
# L17: complete homogeneous 11 returns, with exact clocks

For p=u+6 and c=v+7, both parity branches of
  (10)^p 0(10)^c 0(10)^3 A> (101)^j 11 R
return to C with a blank left tape. The complete right word and clock
are explicit. The proof uses the corrected D phase in L17z/L17aa,
then the outer sweeps that those modules intentionally leave open.

These are guarded configuration theorems for every natural parameter
and arbitrary right context. No blank-orbit occurrence or general
mixed-token return is asserted.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

private abbrev tail22 : List (Fin 2) :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Transport a right-directed C head through a middle-layer separator.
    The extra pair consumes that separator; the arbitrary L is retained. -/
theorem c01_middle_headRight_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (2 * (n + 1))
      (Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append [0] L))
        (ListBlank.append [1] R))
      (Cfg.headLeft C L
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1)) R)) := by
  have hrot :
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append [0] L)) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L := by
    rw [rotLB, ← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) n L]
    rfl
  have he :
      Cfg.headRight C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append [0] L))
        (ListBlank.append [1] R) =
      Cfg.headLeft C
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) L) R := by
    rw [← hrot]
    exact Cfg.headRight_cons C (1 : Fin 2) _ R
  rw [he]
  exact c01_sweep_exact (n + 1) L R

/-- Outermost K22 has no middle-layer separator to consume after its
    local path. Its n C01 pairs leave an explicit 1 before context L. -/
theorem k22_c01_last_exact (n : ℕ) (L R : ListBlank (Fin 2)) :
    ReachesIn target (22 + 2 * n)
      (Cfg.headLeft D
        (ListBlank.append [0]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 4)) L))
        (ListBlank.append [1, 0, 1, 0] R))
      (Cfg.headLeft C (ListBlank.append [1] L)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ n)
          (ListBlank.append tail22 R))) := by
  let X := ListBlank.append (([0, 1] : List (Fin 2)) ^ n) L
  have hs :
      ListBlank.append [0]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 4)) L) =
      ListBlank.append [0, 0, 1, 0, 1, 0, 1, 0, 1] X := by
    rw [show n + 4 = 4 + n by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 4 n L]
    rfl
  rw [hs]
  have h1 := k22_headLeft_exact X R
  have he :
      Cfg.headRight C X
        (ListBlank.append [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] R) =
      Cfg.headLeft C
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
          (ListBlank.append [1] L))
        (ListBlank.append tail22 R) := by
    rw [← rotLB n L]
    exact Cfg.headRight_cons C (1 : Fin 2) X (ListBlank.append tail22 R)
  rw [he] at h1
  exact h1.trans (c01_sweep_exact n (ListBlank.append [1] L)
    (ListBlank.append tail22 R))

private theorem triple10_power (h : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h) R =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * h)) R := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [ListBlank.append_pow_succ
      ([1, 0, 1, 0, 1, 0] : List (Fin 2)) h R, ih]
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ 3)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * h)) R) = _
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun n : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R) (by omega)

private theorem d11_even_tail_pairs (h : ℕ) (R : ListBlank (Fin 2)) :
    d11_even_tail h R =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * h + 2)) R := by
  cases h with
  | zero => rfl
  | succ h =>
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3) R)) = _
    rw [triple10_power, ← ListBlank.append_pow_add,
      ← ListBlank.append_pow_add]
    exact congrArg (fun n : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R) (by omega)

private theorem ten_power_right (n : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) R =
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append [0] R)) := by
  rw [rotLB, ← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) n R]
  rfl

private theorem ones_sandwich (n : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append [1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ n)
        (ListBlank.append [1] R)) =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * n + 2)) R := by
  rw [one_pow_two_mul, show 2 * n + 2 = 1 + (2 * n + 1) by omega,
    ListBlank.append_pow_add ([1] : List (Fin 2)) 1 (2 * n + 1),
    ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * n) 1]
  rfl

private theorem zero_ones_one (n : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ n) (ListBlank.append [1] R)) =
      ListBlank.append [0, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ n) R) := by
  rw [ListBlank.append_pow_succ' ([1] : List (Fin 2)) n R,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) n R]
  rfl

private theorem k41_word_normalize (u a k : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append [1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append returnKtail
          (ListBlank.append (([1] : List (Fin 2)) ^ a)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) R)))) =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
          (ListBlank.append (([1] : List (Fin 2)) ^ a)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0] R)))) := by
  change ListBlank.append [1]
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 6)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ a)
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) R)))))) = _
  rw [ones_sandwich, ten_power_right, zero_ones_one]
  rw [← ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) 6
    (ListBlank.append (([1] : List (Fin 2)) ^ a)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0] R)))]

/-- A source with physical left stack[p,c,3], p=u+6,c=v+7. -/
def a11_source (u v j : ℕ) (R : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [0, 1, 0, 1, 0, 1]
      (ListBlank.append [0]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 7))
          (ListBlank.append [0]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default)))))
    (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ j)
      (ListBlank.append [1, 1] R))

/-- Complete canonical return word for j=2h; every internal zero remains. -/
def a11_even_result (u v h : ℕ) (R : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 2))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 5))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 * h + 7))
          (ListBlank.append [0] R))))

/-- Complete canonical return word for j=2h+1. -/
def a11_odd_result (u v h : ℕ) (R : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ (2 * u + 6))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3 * h + 16))
      (ListBlank.append [0] R))

/-- Even homogeneous11 return: all parameters and arbitrary context,
    complete blank-left C endpoint, exactly40h+2u+2v+86 steps. -/
theorem a11_even_blankleft_exact (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (40 * h + 2 * u + 2 * v + 86)
      (a11_source u v (2 * h) R)
      (Cfg.headRight C default (a11_even_result u v h R)) := by
  let Lp := ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default
  let Lc := ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3))
    (ListBlank.append [0] Lp)
  let Rest := ListBlank.append tail22 (d11_even_tail h R)
  let Rlast := ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 5)) Rest
  have hs : a11_source u v (2 * h) R =
      Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0]
            (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1] Lc)))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h))
          (ListBlank.append [1, 1] R)) := by
    unfold a11_source
    rw [show v + 7 = 4 + (v + 3) by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 4 (v + 3)]
    rfl
  have h1 := a101_11_even_k22_exact h Lc R
  have h2 := c01_middle_headRight_exact (v + 3) Lp Rest
  have h12 := h1.trans h2
  have hones :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 4)) Rest =
      ListBlank.append [1, 1, 1] Rlast := by
    rw [one_pow_two_mul, show 2 * (v + 4) = 3 + (2 * v + 5) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (2 * v + 5)]
    rfl
  rw [hones] at h12
  have h3 := k41_c01_last_exact u default Rlast
  have h123 := h12.trans h3
  have hperiod : Rest =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ ((3 * h + 7) + 1)) R := by
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ 6)
      (d11_even_tail h R) = _
    rw [d11_even_tail_pairs, ← ListBlank.append_pow_add]
    exact congrArg (fun n : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R) (by omega)
  have hword :
      ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append returnKtail Rlast)) = a11_even_result u v h R := by
    change ListBlank.append [1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append returnKtail
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * v + 5)) Rest))) = _
    rw [hperiod]
    exact k41_word_normalize u (2 * v + 5) (3 * h + 7) R
  have he :
      Cfg.headLeft C (ListBlank.append [1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
          (ListBlank.append returnKtail Rlast)) =
      Cfg.headRight C default (a11_even_result u v h R) :=
    (Cfg.headLeft_cons C (1 : Fin 2) default
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
        (ListBlank.append returnKtail Rlast))).trans
      (congrArg (Cfg.headRight C default) hword)
  rw [← hs, he] at h123
  convert h123 using 1
  omega

/-- Odd homogeneous11 return: the final D sweep and outer K22
    yield the complete C word in40h+2u+4v+92 defined steps. -/
theorem a11_odd_blankleft_exact (u v h : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (40 * h + 2 * u + 4 * v + 92)
      (a11_source u v (2 * h + 1) R)
      (Cfg.headRight C default (a11_odd_result u v h R)) := by
  let Lp := ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 6)) default
  let L := ListBlank.append [1]
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 6))
      (ListBlank.append [0] Lp))
  let Rds := ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * h + 6)) R
  let Rtail := ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 3 * h + 11)) R
  have hs : a11_source u v (2 * h + 1) R =
      Cfg.headRight A
        (ListBlank.append [0, 1, 0, 1, 0, 1]
          (ListBlank.append [0] (ListBlank.append [0] L)))
        (ListBlank.append (([1, 0, 1] : List (Fin 2)) ^ (2 * h + 1))
          (ListBlank.append [1, 1] R)) := by
    unfold a11_source
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (v + 6)]
    rfl
  have h1 := a101_11_odd_j1k_exact h L R
  have hpairs :
      ListBlank.append [0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
          (ListBlank.append [1, 0, 1, 0, 1, 0] R)) =
      ListBlank.append [0] Rds := by
    change ListBlank.append [0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3)
        (ListBlank.append (([1, 0, 1, 0, 1, 0] : List (Fin 2)) ^ h)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3) R))) = _
    rw [triple10_power, ← ListBlank.append_pow_add,
      ← ListBlank.append_pow_add]
    exact congrArg (fun n : ℕ => ListBlank.append [0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R)) (by omega)
  have hleft : ListBlank.append [0] L =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 7))
        (ListBlank.append [0] Lp) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (v + 6)]
    rfl
  have heD : Cfg.headRight D L (ListBlank.append [0] Rds) =
      Cfg.headLeft D
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 7))
          (ListBlank.append [0] Lp)) Rds :=
    (Cfg.headRight_cons D (0 : Fin 2) L Rds).trans
      (congrArg (fun Z => Cfg.headLeft D Z Rds) hleft)
  rw [hpairs, heD] at h1
  have h2 := d10_sweep_exact (v + 7) (ListBlank.append [0] Lp) Rds
  have h12 := h1.trans h2
  have hright :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7)) Rds =
      ListBlank.append [1, 0, 1, 0] Rtail := by
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 7))
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * h + 6)) R) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ 2)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 3 * h + 11)) R)
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add]
    exact congrArg (fun n : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R) (by omega)
  rw [hright] at h12
  have h3 := k22_c01_last_exact (u + 2) default Rtail
  have h123 := h12.trans h3
  have hperiod : ListBlank.append tail22 Rtail =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ ((v + 3 * h + 16) + 1)) R := by
    change ListBlank.append (([1, 0] : List (Fin 2)) ^ 6)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (v + 3 * h + 11)) R) = _
    rw [← ListBlank.append_pow_add]
    exact congrArg (fun n : ℕ =>
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) R) (by omega)
  have hword :
      ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 2))
          (ListBlank.append tail22 Rtail)) = a11_odd_result u v h R := by
    rw [hperiod, ten_power_right, ones_sandwich]
    unfold a11_odd_result
    exact congrArg (fun n : ℕ =>
      ListBlank.append (([1] : List (Fin 2)) ^ n)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3 * h + 16))
          (ListBlank.append [0] R))) (by omega)
  have he :
      Cfg.headLeft C (ListBlank.append [1] default)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 2))
          (ListBlank.append tail22 Rtail)) =
      Cfg.headRight C default (a11_odd_result u v h R) :=
    (Cfg.headLeft_cons C (1 : Fin 2) default
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 2))
        (ListBlank.append tail22 Rtail))).trans
      (congrArg (Cfg.headRight C default) hword)
  rw [← hs, he] at h123
  convert h123 using 1
  omega

def a11_return_clock (u v j : ℕ) : ℕ :=
  if j % 2 = 0 then 40 * (j / 2) + 2 * u + 2 * v + 86
  else 40 * (j / 2) + 2 * u + 4 * v + 92

def a11_return_result (u v j : ℕ) (R : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  if j % 2 = 0 then a11_even_result u v (j / 2) R
  else a11_odd_result u v (j / 2) R

/-- Every homogeneous11 source in the guarded domain returns to blank-left
    C, with an exact piecewise clock and complete explicitly defined word. -/
theorem a11_homogeneous_blankleft_exact (u v j : ℕ) (R : ListBlank (Fin 2)) :
    ReachesIn target (a11_return_clock u v j)
      (a11_source u v j R)
      (Cfg.headRight C default (a11_return_result u v j R)) := by
  have hdiv := Nat.mod_add_div j 2
  have hlt : j % 2 < 2 := Nat.mod_lt j (by omega)
  by_cases he : j % 2 = 0
  · simp only [a11_return_clock, a11_return_result, ite_eq_left he]
    have hj : j = 2 * (j / 2) := by omega
    have h := a11_even_blankleft_exact u v (j / 2) R
    rw [← hj] at h
    exact h
  · simp only [a11_return_clock, a11_return_result, ite_eq_right he]
    have hj : j = 2 * (j / 2) + 1 := by omega
    have h := a11_odd_blankleft_exact u v (j / 2) R
    rw [← hj] at h
    exact h

end CryptidLink.L17

#print axioms CryptidLink.L17.c01_middle_headRight_exact
#print axioms CryptidLink.L17.k22_c01_last_exact
#print axioms CryptidLink.L17.a11_even_blankleft_exact
#print axioms CryptidLink.L17.a11_odd_blankleft_exact
#print axioms CryptidLink.L17.a11_homogeneous_blankleft_exact
