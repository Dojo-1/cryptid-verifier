import BusyBeaver.Basic
import BusyBeaver.Bridge
/-!
# L17 = `1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---`: four branches, machine level

Section C(a, b) := 0^∞ C> (01)^a 1^b 0^∞. Proved against the raw Turing machine (upstream semantics):

* b = 0:          C(a, 0)     ⊢⁺ C(0, 2a + 4)
* a = 0, b ≥ 1:   C(0, b)     ⊢⁺ C(1, b)
* a ≥ 1, b = 2:   C(a, 2)     ⊢⁺ C(a + 4, 0)
* a ≥ 1, b ≥ 3:   C(a, b + 3) ⊢⁺ C(a + 5, b)

The open case is a ≥ 1, b = 1. Chaining the rules from the blank tape gives
`blank_reaches_boundary`: the machine reaches C(53262756, 1) (at raw time 1 870 497 627 040 360, by the
step counts in `analysis/leads/L17.md`; the counts are not part of this Lean statement).
Derivation from GPT's report (`analysis/leads/gpt-2026-10-20/report.md`).
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

/-- C(a, b) = 0^∞ C> (01)^a 1^b 0^∞. -/
def cfgC (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C default
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append (([1] : List (Fin 2)) ^ b) default))

/-- A(a, b) = 0^∞ A> (01)^a 1^b 0^∞. -/
def cfgA (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A default
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append (([1] : List (Fin 2)) ^ b) default))

/-! ## List identities -/

theorem rot_list (x y : Fin 2) : ∀ n : ℕ, [x] ++ ([y, x] : List (Fin 2)) ^ n = ([x, y] : List (Fin 2)) ^ n ++ [x]
  | 0 => by simp [list_pow_zero]
  | n + 1 => by
    simp only [list_pow_succ, List.append_assoc]
    rw [← rot_list x y n] <;> rfl

theorem rot2 (x y : Fin 2) : ∀ m : ℕ, ([x, y] : List (Fin 2)) ^ m ++ [x, y] = [x] ++ (([y, x] : List (Fin 2)) ^ m ++ [y])
  | 0 => rfl
  | m + 1 => by
    simp only [list_pow_succ, List.append_assoc]
    rw [rot2 x y m] <;> rfl

theorem rotLB (n : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) s) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] s) := by
  rw [ListBlank.append_append, ListBlank.append_append, rot_list]

theorem ones (a : ℕ) : [1] ++ (([1, 1] : List (Fin 2)) ^ (a + 1) ++ [1]) = ([1] : List (Fin 2)) ^ (2 * a + 4) := by
  rw [one_pow_two_mul, show 2 * a + 4 = 1 + (2 * (a + 1) + 1) by omega,
    list_pow_add ([1] : List (Fin 2)) 1 (2 * (a + 1) + 1), list_pow_add ([1] : List (Fin 2)) (2 * (a + 1)) 1,
    list_pow_one]

theorem L1 (a : ℕ) :
    ([0, 1, 0, 1, 0, 1, 0] : List (Fin 2)) ++ (([1, 0] : List (Fin 2)) ^ a ++ [1, 0]) =
      ([0, 1] : List (Fin 2)) ^ (a + 4) ++ [0] := by
  rw [rot2, show a + 4 = 4 + a by omega, list_pow_add ([0, 1] : List (Fin 2)) 4 a, List.append_assoc] <;> rfl

/-! ## Sweeps -/

/-- A sweeps right across (01)^k, turning it into (10)^k. -/
theorem sweepA (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [0, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- D sweeps left across (10)^k, leaving it unchanged (path D0 A1 E1 F0 per block). -/
theorem sweepD (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft D l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft D
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)) r)
          (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 0] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 0] r)
    have h3 := (h1.trans_star h2).to_star
    have h_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_r :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] r) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_l, h_r] at h3

/-- C sweeps left across (01)^k (read right to left as 1,0), turning it into 1^(2k). -/
theorem sweepC (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft C (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft C l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft C
            (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)) r)
          (Cfg.headLeft C (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_l :
        ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_l, h_r] at h3

/-! ## Fixed segments -/

theorem segAB (L : ListBlank (Fin 2)) :
    ReachesPlus target (Cfg.headRight A L default)
      (Cfg.headLeft C (ListBlank.append [1] L) (ListBlank.append [1] default)) := by
  bb_steps

theorem segAEF (l r : ListBlank (Fin 2)) :
    ReachesPlus target (Cfg.headRight A l (ListBlank.append [1, 1] r))
      (Cfg.headLeft D l (ListBlank.append [1, 0] r)) := by
  bb_steps

/-- The fixed ten-step path D0 A0 B1 A1 E0 B0 C0 D1 E0 B0. -/
theorem path10 (X : ListBlank (Fin 2)) :
    ReachesPlus target (Cfg.headLeft D default (ListBlank.append [1, 0] X))
      (Cfg.headRight C default (ListBlank.append [0, 1, 0, 1, 0, 1, 0] X)) := by
  bb_steps

theorem hconv (R : ListBlank (Fin 2)) :
    Cfg.headLeft C (ListBlank.append [1] default) R = Cfg.headRight C default (ListBlank.append [1] R) :=
  Cfg.headLeft_cons C 1 default R

/-! ## Branches -/

theorem init_C : ReachesPlus target (init []) (cfgC 0 2) := by
  show ReachesPlus target (init []) (Cfg.headRight C default (ListBlank.append [1, 1] default))
  bb_steps

/-- C(a, b) ⊢⁺ A(a + 1, b) when the head reads 0. -/
theorem entry (a b : ℕ) (h : 1 ≤ a ∨ b = 0) : ReachesPlus target (cfgC a b) (cfgA (a + 1) b) := by
  rcases a with _ | a
  · rcases h with h | rfl
    · omega
    · show ReachesPlus target (Cfg.headRight C default default)
        (Cfg.headRight A default (ListBlank.append [0, 1] default))
      bb_steps
  · show ReachesPlus target
      (Cfg.headRight C default (ListBlank.append [0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))
      (Cfg.headRight A default (ListBlank.append [0, 1] (ListBlank.append [0, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))))
    bb_steps

theorem branch_a0 (b : ℕ) : ReachesPlus target (cfgC 0 (b + 1)) (cfgC 1 (b + 1)) := by
  show ReachesPlus target
    (Cfg.headRight C default (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
    (Cfg.headRight C default (ListBlank.append [0, 1]
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))
  bb_steps

theorem ones_LB (a : ℕ) :
    ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) (ListBlank.append [1] default)) =
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 4)) default := by
  simp only [ListBlank.append_append]
  congr 1
  exact ones a

theorem branch_b0 (a : ℕ) : ReachesPlus target (cfgC a 0) (cfgC 0 (2 * a + 4)) := by
  have h1 := entry a 0 (Or.inr rfl)
  have h2 := sweepA (a + 1) default default
  have h3 := segAB (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default)
  rw [rotLB] at h3
  have h4 := sweepC (a + 1) (ListBlank.append [1] default) (ListBlank.append [1] default)
  rw [hconv, ones_LB] at h4
  have e1 : cfgA (a + 1) 0 =
      Cfg.headRight A default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default) := rfl
  have e2 : cfgC 0 (2 * a + 4) =
      Cfg.headRight C default (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 4)) default) := rfl
  rw [e1] at h1
  rw [e2]
  exact ((h1.trans_star h2).trans h3).trans_star h4

theorem tail_eq (a : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append [0, 1, 0, 1, 0, 1, 0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ a) (ListBlank.append [1, 0] R)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 4)) (ListBlank.append [0] R) := by
  simp only [ListBlank.append_append]
  congr 1
  exact L1 a

theorem branch_ge2 (a b : ℕ) (ha : 1 ≤ a) :
    ReachesPlus target (cfgC a (b + 2))
      (Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 4))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))) := by
  have h1 := entry a (b + 2) (Or.inl ha)
  have hO : ListBlank.append (([1] : List (Fin 2)) ^ (b + 2)) default =
      ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default) := by
    rw [Nat.add_comm b 2, ListBlank.append_pow_add]; rfl
  have e1 : cfgA (a + 1) (b + 2) = Cfg.headRight A default
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1))
        (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))) := by
    unfold cfgA; rw [hO]
  rw [e1] at h1
  have h2 := sweepA (a + 1) default
    (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
  have h3 := segAEF (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append (([1] : List (Fin 2)) ^ b) default)
  have h4 := sweepD (a + 1) default
    (ListBlank.append [1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
  rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) a] at h4
  have h5 := path10 (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
    (ListBlank.append [1, 0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
  rw [tail_eq] at h5
  exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5

theorem branch2 (a : ℕ) (ha : 1 ≤ a) : ReachesPlus target (cfgC a 2) (cfgC (a + 4) 0) := by
  have h := branch_ge2 a 0 ha
  have e : ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default) =
      (default : ListBlank (Fin 2)) := by
    show ListBlank.cons 0 default = default
    exact ListBlank.cons_zero_default
  rw [e] at h
  exact h

theorem branch3 (a c : ℕ) (ha : 1 ≤ a) : ReachesPlus target (cfgC a (c + 3)) (cfgC (a + 5) c) := by
  have h := branch_ge2 a (c + 1) ha
  have e : ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 4))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 5))
        (ListBlank.append (([1] : List (Fin 2)) ^ c) default) := by
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c, show a + 5 = (a + 4) + 1 from rfl,
      ← ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) (a + 4)] <;> rfl
  rw [e] at h
  exact h

/-! ## Countdowns and the blank orbit -/

theorem countdown (q : ℕ) : ∀ a, 1 ≤ a → ∀ r,
    ReachesStar target (cfgC a (3 * q + r)) (cfgC (a + 5 * q) r) := by
  induction q with
  | zero => intro a _ r; simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; exact ReachesStar.refl _ _
  | succ q ih =>
    intro a ha r
    have h := branch3 a (3 * q + r) ha
    have h' := ih (a + 5) (by omega) r
    rw [show 3 * (q + 1) + r = 3 * q + r + 3 by omega, show a + 5 * (q + 1) = a + 5 + 5 * q by omega]
    exact (h.trans_star h').to_star

theorem res0 (k : ℕ) (hk : 1 ≤ k) : ReachesPlus target (cfgC 0 (3 * k)) (cfgC 0 (10 * k + 6)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 := branch_a0 (3 * j + 2)
  have h2 := countdown (j + 1) 1 le_rfl 0
  have h3 := branch_b0 (1 + 5 * (j + 1))
  rw [show 3 * (j + 1) + 0 = 3 * j + 2 + 1 by omega] at h2
  rw [show 3 * (j + 1) = 3 * j + 2 + 1 by omega, show 10 * (j + 1) + 6 = 2 * (1 + 5 * (j + 1)) + 4 by omega]
  exact (h1.trans_star h2).trans h3

theorem res2 (k : ℕ) : ReachesPlus target (cfgC 0 (3 * k + 2)) (cfgC 0 (10 * k + 14)) := by
  have h1 := branch_a0 (3 * k + 1)
  have h2 := countdown k 1 le_rfl 2
  have h3 := branch2 (1 + 5 * k) (by omega)
  have h4 := branch_b0 (1 + 5 * k + 4)
  rw [show 3 * k + 1 + 1 = 3 * k + 2 by omega] at h1
  rw [show 10 * k + 14 = 2 * (1 + 5 * k + 4) + 4 by omega]
  exact ((h1.trans_star h2).trans h3).trans h4

theorem res1 (k : ℕ) : ReachesPlus target (cfgC 0 (3 * k + 1)) (cfgC (5 * k + 1) 1) := by
  have h1 := branch_a0 (3 * k)
  have h2 := countdown k 1 le_rfl 1
  rw [show 5 * k + 1 = 1 + 5 * k by omega]
  exact h1.trans_star h2

theorem step0 (n m k : ℕ) (hk : 1 ≤ k) (hn : n = 3 * k) (hm : m = 10 * k + 6) :
    ReachesPlus target (cfgC 0 n) (cfgC 0 m) := by
  subst hn; subst hm; exact res0 k hk

theorem step2 (n m k : ℕ) (hn : n = 3 * k + 2) (hm : m = 10 * k + 14) :
    ReachesPlus target (cfgC 0 n) (cfgC 0 m) := by
  subst hn; subst hm; exact res2 k

theorem step1 (n a k : ℕ) (hn : n = 3 * k + 1) (ha : a = 5 * k + 1) :
    ReachesPlus target (cfgC 0 n) (cfgC a 1) := by
  subst hn; subst ha; exact res1 k

/-- **L17, machine level.** From the blank tape the machine reaches C(53262756, 1), the first
    configuration where the open branch (a ≥ 1, b = 1) is needed. In particular it does not halt before. -/
theorem blank_reaches_boundary : ReachesPlus target (init []) (cfgC 53262756 1) :=
  init_C
    |>.trans (step2 2 14 0 (by norm_num) (by norm_num))
    |>.trans (step2 14 54 4 (by norm_num) (by norm_num))
    |>.trans (step0 54 186 18 (by norm_num) (by norm_num) (by norm_num))
    |>.trans (step0 186 626 62 (by norm_num) (by norm_num) (by norm_num))
    |>.trans (step2 626 2094 208 (by norm_num) (by norm_num))
    |>.trans (step0 2094 6986 698 (by norm_num) (by norm_num) (by norm_num))
    |>.trans (step2 6986 23294 2328 (by norm_num) (by norm_num))
    |>.trans (step2 23294 77654 7764 (by norm_num) (by norm_num))
    |>.trans (step2 77654 258854 25884 (by norm_num) (by norm_num))
    |>.trans (step2 258854 862854 86284 (by norm_num) (by norm_num))
    |>.trans (step0 862854 2876186 287618 (by norm_num) (by norm_num) (by norm_num))
    |>.trans (step2 2876186 9587294 958728 (by norm_num) (by norm_num))
    |>.trans (step2 9587294 31957654 3195764 (by norm_num) (by norm_num))
    |>.trans (step1 31957654 53262756 10652551 (by norm_num) (by norm_num))

end CryptidLink.L17

#print axioms CryptidLink.L17.branch_b0
#print axioms CryptidLink.L17.branch3
#print axioms CryptidLink.L17.blank_reaches_boundary
