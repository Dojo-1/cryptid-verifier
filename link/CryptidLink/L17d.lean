import CryptidLink.L17c
/-!
# L17: one-tail state space and macro moves

S(a, b, k, s) := 0^∞ C> (01)^a 1^b (01)^k 1^s 0^∞. Every state on the blank orbit that GPT's 2,000-rewrite
trace visits has this form (one tail at most). The moves below are corollaries of the machine-level lemmas
in `L17`, `L17b`, `L17c`, stated with explicit arithmetic side conditions, so a chain can be generated
mechanically and checked by `norm_num`.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- The tail (01)^k 1^s. -/
def W (k s : ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append (([1] : List (Fin 2)) ^ s) default)

/-- S(a, b, k, s) = 0^∞ C> (01)^a 1^b (01)^k 1^s 0^∞. -/
def S (a b k s : ℕ) : Cfg (Fin 2) (Fin 6) := cfgCt a b (W k s)

theorem S_plain (a b : ℕ) : S a b 0 0 = cfgC a b := rfl

/-- Entry then countdown from S(0, n, k, s). -/
theorem LEC (n q r a k s : ℕ) (hn : n = 3 * q + r) (h1 : 1 ≤ n) (ha : a = 1 + 5 * q) :
    ReachesPlus target (S 0 n k s) (S a r k s) :=
  stepEC n q r a (W k s) hn h1 ha

/-- Countdown with a ≥ 1 and at least one step. -/
theorem LCD (a b q r a' k s : ℕ) (ha : 1 ≤ a) (hq : 1 ≤ q) (hb : b = 3 * q + r) (ha' : a' = a + 5 * q) :
    ReachesPlus target (S a b k s) (S a' r k s) := by
  subst hb; subst ha'
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  unfold S
  rw [show 3 * (q + 1) + r = 3 * q + r + 3 by omega, show a + 5 * (q + 1) = a + 5 + 5 * q by omega]
  exact (branch3T a (3 * q + r) (W k s) ha).trans_star (countdownT (W k s) q (a + 5) (by omega) r)

/-- Two ones before a tail (01)^(m+1) 1^s: P then Z. -/
theorem LPZ (a n m k s : ℕ) (ha : 1 ≤ a) (hk : k = m + 1) (hn : n = 2 * a + 13) :
    ReachesPlus target (S a 2 k s) (S 0 n m s) := by
  subst hk
  exact stepPZ a n m (ListBlank.append (([1] : List (Fin 2)) ^ s) default) ha hn

/-- Two ones, plain: C(a, 2) ⊢⁺ C(a + 4, 0) ⊢⁺ C(0, 2a + 12). -/
theorem LB2 (a n : ℕ) (ha : 1 ≤ a) (hn : n = 2 * a + 12) :
    ReachesPlus target (S a 2 0 0) (S 0 n 0 0) := by
  subst hn
  rw [S_plain, S_plain, show 2 * a + 12 = 2 * (a + 4) + 4 by omega]
  exact (branch2 a ha).trans (branch_b0 (a + 4))

/-- No ones, plain: C(a, 0) ⊢⁺ C(0, 2a + 4). -/
theorem LB0 (a n : ℕ) (hn : n = 2 * a + 4) : ReachesPlus target (S a 0 0 0) (S 0 n 0 0) := by
  subst hn; rw [S_plain, S_plain]; exact branch_b0 a

/-- One one, plain: C(c + 7, 1) ⊢⁺ S(0, 2c + 2, 7, 3). -/
theorem LR1 (a n c : ℕ) (ha : a = c + 7) (hn : n = 2 * c + 2) :
    ReachesPlus target (S a 1 0 0) (S 0 n 7 3) := by
  rw [S_plain]; exact stepR1 a n c ha hn

/-- One one before the tail (01)^k: F100. -/
theorem LF100 (a n u k : ℕ) (ha : a = u + 7) (hn : n = 2 * u + 2) :
    ReachesPlus target (S a 1 k 0) (S 0 n 7 (2 * k + 3)) := by
  subst ha; subst hn
  have e : ListBlank.append (([1] : List (Fin 2)) ^ 1)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [0] default) := by
    rw [list_pow_zero, ListBlank.append_nil, list_pow_one, rotLB k default,
      ← ListBlank.append_pow_succ' ([1, 0] : List (Fin 2)) k]
    congr 1
    show ListBlank.cons 1 default = ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 0 default))
    simp only [ListBlank.cons_zero_default]
  have e2 : S (u + 7) 1 k 0 =
      Ccal (u + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [0] default)) := by
    unfold S W cfgCt Ccal; rw [e]
  rw [e2]
  exact F100 u k default

/-- One one before the tail (01)^(d+1) 1^(t+3): F111. -/
theorem LF111 (a n u k d t : ℕ) (ha : a = u + 5) (hk : k = d + 1) (hn : n = 2 * u + 2) :
    ReachesPlus target (S a 1 k (t + 3)) (S 0 n (k + 7) t) := by
  subst ha; subst hk; subst hn
  have h := F111 u d (ListBlank.append (([1] : List (Fin 2)) ^ (t + 1)) default)
  have es : ListBlank.append (([1] : List (Fin 2)) ^ 1)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1)) (ListBlank.append (([1] : List (Fin 2)) ^ (t + 3)) default)) =
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (t + 1)) default)) := by
    rw [list_pow_one, rotLB (d + 1) _]
    congr 1
    all_goals (rw [show t + 3 = 2 + (t + 1) by omega, ListBlank.append_pow_add]; rfl)
  have et : ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (t + 1)) default)) =
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1 + 7)) (ListBlank.append (([1] : List (Fin 2)) ^ t) default) := by
    rw [show d + 1 + 7 = (d + 7) + 1 from rfl, ← ListBlank.append_pow_succ' _ (d + 7),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) t]
    rfl
  have e2 : S (u + 5) 1 (d + 1) (t + 3) =
      Ccal (u + 5) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (t + 1)) default))) := by
    unfold S W cfgCt Ccal; rw [es]
  rw [et] at h
  rw [e2]
  exact h

/-- Merging: S(a, 0, k, s) is literally S(a + k, s, 0, 0). -/
theorem LN (a k s a' : ℕ) (ha : a' = a + k) : S a 0 k s = S a' s 0 0 := by
  subst ha
  unfold S W cfgCt
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [← ListBlank.append_pow_add]

/-- Merging ones: S(a, b, 0, s) is literally S(a, b + s, 0, 0). -/
theorem LM (a b s b' : ℕ) (hb : b' = b + s) : S a b 0 s = S a b' 0 0 := by
  subst hb
  unfold S W cfgCt
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [← ListBlank.append_pow_add]

end CryptidLink.L17
