import CryptidLink.L17
/-!
# L17: the b = 1 branch for a ≡ 0 (mod 3), and the orbit to the next boundary

Write C(a, b)·X for 0^∞ C> (01)^a 1^b X, with X a right tail. The countdown rules hold with any tail.
The b = 1 branch, for a ≥ 7, is

    C(a, 1) ⊢⁺ C(0, 2a − 12)·T,   T = (01)^7 1^3,

(entry, a sweep, a fixed 60-step segment on the last 8 pairs, a sweep back). Since C(x, 0)·T = C(x + 7, 3),
for a = 3k this gives

    C(3k, 1) ⊢⁺ C(10k − 12, 3)   (k ≥ 3).

`blank_reaches_boundary2`: from the blank tape the machine reaches C(6575648756, 1), with
6575648756 ≡ 2 (mod 3), where the next unresolved case starts.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- C(a, b)·X = 0^∞ C> (01)^a 1^b X. -/
def cfgCt (a b : ℕ) (X : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C default
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append (([1] : List (Fin 2)) ^ b) X))

/-- The tail T = (01)^7 1^3. -/
def tailT : ListBlank (Fin 2) :=
  ListBlank.append (([0, 1] : List (Fin 2)) ^ 7) (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)

/-! ## Branches with a tail -/

theorem entryT (a b : ℕ) (X : ListBlank (Fin 2)) :
    ReachesPlus target (cfgCt (a + 1) b X)
      (Cfg.headRight A default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2))
        (ListBlank.append (([1] : List (Fin 2)) ^ b) X))) := by
  show ReachesPlus target
    (Cfg.headRight C default (ListBlank.append [0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append (([1] : List (Fin 2)) ^ b) X))))
    (Cfg.headRight A default (ListBlank.append [0, 1] (ListBlank.append [0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append (([1] : List (Fin 2)) ^ b) X)))))
  bb_steps

theorem branch_a0T (b : ℕ) (X : ListBlank (Fin 2)) :
    ReachesPlus target (cfgCt 0 (b + 1) X) (cfgCt 1 (b + 1) X) := by
  show ReachesPlus target
    (Cfg.headRight C default (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) X)))
    (Cfg.headRight C default (ListBlank.append [0, 1]
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) X))))
  bb_steps

theorem branch_ge2T (a b : ℕ) (X : ListBlank (Fin 2)) :
    ReachesPlus target (cfgCt (a + 1) (b + 2) X)
      (Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 5))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ b) X)))) := by
  have h1 := entryT a (b + 2) X
  have hO : ListBlank.append (([1] : List (Fin 2)) ^ (b + 2)) X =
      ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) X) := by
    rw [Nat.add_comm b 2, ListBlank.append_pow_add]; rfl
  rw [hO] at h1
  have h2 := sweepA (a + 2) default
    (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) X))
  have h3 := segAEF (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 2)) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ b) X)
  have h4 := sweepD (a + 2) default
    (ListBlank.append [1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) X))
  have hp : ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
        (ListBlank.append [1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) X)) =
      ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 1))
        (ListBlank.append [1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) X))) :=
    ListBlank.append_pow_succ _ _ _
  rw [hp] at h4
  have h5 := path10 (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 1))
    (ListBlank.append [1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) X)))
  rw [tail_eq] at h5
  exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5

theorem branch3T (a c : ℕ) (X : ListBlank (Fin 2)) (ha : 1 ≤ a) :
    ReachesPlus target (cfgCt a (c + 3) X) (cfgCt (a + 5) c X) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have h := branch_ge2T a (c + 1) X
  have e : ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 5))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) X)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1 + 5))
        (ListBlank.append (([1] : List (Fin 2)) ^ c) X) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c, show a + 1 + 5 = (a + 5) + 1 from rfl,
      ← ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) (a + 5)] <;> rfl
  rw [e] at h
  exact h

theorem countdownT (X : ListBlank (Fin 2)) (q : ℕ) : ∀ a, 1 ≤ a → ∀ r,
    ReachesStar target (cfgCt a (3 * q + r) X) (cfgCt (a + 5 * q) r X) := by
  induction q with
  | zero => intro a _ r; simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; exact ReachesStar.refl _ _
  | succ q ih =>
    intro a ha r
    have h := branch3T a (3 * q + r) X ha
    have h' := ih (a + 5) (by omega) r
    rw [show 3 * (q + 1) + r = 3 * q + r + 3 by omega, show a + 5 * (q + 1) = a + 5 + 5 * q by omega]
    exact (h.trans_star h').to_star

/-! ## The b = 1 branch -/

/-- The fixed 60-step segment: it reads only the last 8 pairs and two cells to their right. -/
theorem segR1 (L : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) L) (ListBlank.append [1] default))
      (Cfg.headLeft C (ListBlank.append [1] L)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] default)) := by
  rw [show (([0, 1] : List (Fin 2)) ^ 8) = [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] from rfl]
  bb_steps

theorem L2 (c : ℕ) :
    [1] ++ (([1, 1] : List (Fin 2)) ^ c ++ [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]) =
      ([1] : List (Fin 2)) ^ (2 * c + 2) ++ (([0, 1] : List (Fin 2)) ^ 7 ++ ([1] : List (Fin 2)) ^ 3) := by
  rw [one_pow_two_mul, show 2 * c + 2 = 1 + (2 * c + 1) by omega,
    list_pow_add ([1] : List (Fin 2)) 1 (2 * c + 1), list_pow_add ([1] : List (Fin 2)) (2 * c) 1, list_pow_one]
  simp only [List.append_assoc]
  rfl

/-- **The b = 1 branch, a ≥ 7:** C(c + 7, 1) ⊢⁺ C(0, 2c + 2)·T. -/
theorem R1 (c : ℕ) : ReachesPlus target (cfgC (c + 7) 1) (cfgCt 0 (2 * c + 2) tailT) := by
  have h1 := entry (c + 7) 1 (Or.inl (by omega))
  have e1 : cfgA (c + 7 + 1) 1 = Cfg.headRight A default
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 8)) (ListBlank.append [1] default)) := rfl
  rw [e1] at h1
  have h2 := sweepA (c + 8) default (ListBlank.append [1] default)
  have hs : ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 8)) default =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 8) (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default) := by
    rw [show c + 8 = 8 + c by omega, ListBlank.append_pow_add]
  rw [hs] at h2
  have h3 := segR1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)
  rw [rotLB] at h3
  have h4 := sweepC c (ListBlank.append [1] default)
    (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] default)
  rw [hconv] at h4
  have e2 : ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1] default)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * c + 2)) tailT) := by
    unfold tailT
    rw [list_pow_zero, ListBlank.append_nil]
    simp only [ListBlank.append_append]
    congr 1
    (try simp only [List.append_assoc])
    exact L2 c
  rw [e2] at h4
  exact ((h1.trans_star h2).trans h3).trans_star h4

/-- **C(3k, 1) ⊢⁺ C(10k − 12, 3)**, written with k = j + 3. -/
theorem C3k (j : ℕ) : ReachesPlus target (cfgC (3 * j + 9) 1) (cfgC (10 * j + 18) 3) := by
  have h1 := R1 (3 * j + 2)
  rw [show 3 * j + 2 + 7 = 3 * j + 9 by omega, show 2 * (3 * j + 2) + 2 = 6 * j + 5 + 1 by omega] at h1
  have h2 := branch_a0T (6 * j + 5) tailT
  have h3 := countdownT tailT (2 * j + 2) 1 le_rfl 0
  rw [show 3 * (2 * j + 2) + 0 = 6 * j + 5 + 1 by omega] at h3
  have e : cfgCt (1 + 5 * (2 * j + 2)) 0 tailT = cfgC (10 * j + 18) 3 := by
    unfold cfgCt cfgC tailT
    rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add,
      show 1 + 5 * (2 * j + 2) + 7 = 10 * j + 18 by omega]
  rw [e] at h3
  exact (h1.trans h2).trans_star h3

theorem stepC3k (a b j : ℕ) (ha : a = 3 * j + 9) (hb : b = 10 * j + 18) :
    ReachesPlus target (cfgC a 1) (cfgC b 3) := by
  subst ha; subst hb; exact C3k j

theorem step3b0 (a m : ℕ) (ha : 1 ≤ a) (hm : m = 2 * (a + 5) + 4) :
    ReachesPlus target (cfgC a 3) (cfgC 0 m) := by
  subst hm
  exact (branch3 a 0 ha).trans (branch_b0 (a + 5))

/-- **L17, machine level, next boundary.** From the blank tape the machine reaches C(6575648756, 1).
    6575648756 ≡ 2 (mod 3): the a ≢ 0 (mod 3) case of the b = 1 branch is the next open question. -/
theorem blank_reaches_boundary2 : ReachesPlus target (init []) (cfgC 6575648756 1) :=
  blank_reaches_boundary
    |>.trans (stepC3k 53262756 177542508 17754249 (by norm_num) (by norm_num))
    |>.trans (step3b0 177542508 355085030 (by norm_num) (by norm_num))
    |>.trans (step2 355085030 1183616774 118361676 (by norm_num) (by norm_num))
    |>.trans (step2 1183616774 3945389254 394538924 (by norm_num) (by norm_num))
    |>.trans (step1 3945389254 6575648756 1315129751 (by norm_num) (by norm_num))

end CryptidLink.L17

#print axioms CryptidLink.L17.R1
#print axioms CryptidLink.L17.C3k
#print axioms CryptidLink.L17.blank_reaches_boundary2
