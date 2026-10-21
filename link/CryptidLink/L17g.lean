import CryptidLink.L17f
/-!
# L17: the two-layer collapse subsystem (GPT, `analysis/l17-collapse/COLLAPSE.md`)

D(N, k, z) := 𝒞(0; 1^N (01)^k 1^(3z) T),   T = (01)^7 1^3.

Write N = 3q + r. One decision is entry and countdown, then:

* r = 0: absorb the k pairs, giving a one-tail state S;
* r = 1: F111, giving D(10q − 6, k + 7, z − 1), or S when z = 1;
* r = 2: P then Z, giving D(10q + 15, k − 1, z), or S when k = 1.

The rank k + 8z drops by one at every non-return decision, so `D_returns` holds: every D state with N ≥ 2,
k, z ≥ 1 reaches some one-tail state S. Together with `F1100`, this gives `push_returns`: a push from
S(u+7, 1, 3j+8, 1) returns to one layer. With `LF1100R` (the a ≡ 0 mod 3 case), this covers every push GPT's
continuation has observed.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- D(N, k, z) = 𝒞(0; 1^N (01)^k 1^(3z) T). -/
def Dc (N k z : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ N)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default))))

/-- r = 0: return to S. -/
theorem D_r0 (q k z : ℕ) (hq : 1 ≤ q) :
    ReachesPlus target (Dc (3 * q) k z) (S (1 + 5 * q + k) (3 * z) 7 3) := by
  have h := stepEC (3 * q) q 0 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default)))
    (by omega) (by omega) rfl
  have e : cfgCt (1 + 5 * q) 0 (ListBlank.append (([0, 1] : List (Fin 2)) ^ k)
        (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default))) =
      S (1 + 5 * q + k) (3 * z) 7 3 := by
    unfold cfgCt S W
    rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add]
    all_goals rfl
  rw [e] at h
  exact h

/-- r = 1, z ≥ 2: F111, to D(10q − 6, k + 7, z − 1) (written with q = p + 1, z = w + 2). -/
theorem D_r1 (p k w : ℕ) (hk : 1 ≤ k) :
    ReachesPlus target (Dc (3 * p + 4) k (w + 2)) (Dc (10 * p + 4) (k + 7) (w + 1)) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have h1 := stepEC (3 * p + 4) (p + 1) 1 (1 + 5 * (p + 1))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * (w + 2))) (ListBlank.append Tl default)))
    (by omega) (by omega) rfl
  have es : cfgCt (1 + 5 * (p + 1)) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ (3 * (w + 2))) (ListBlank.append Tl default))) =
      Ccal (5 * p + 1 + 5) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (3 * w + 4)) (ListBlank.append Tl default)))) := by
    unfold cfgCt Ccal
    rw [show 1 + 5 * (p + 1) = 5 * p + 1 + 5 by omega, list_pow_one, rotLB (d + 1),
      show 3 * (w + 2) = 2 + (3 * w + 4) by omega, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (3 * w + 4)]
    all_goals rfl
  rw [es] at h1
  have h2 := F111 (5 * p + 1) d (ListBlank.append (([1] : List (Fin 2)) ^ (3 * w + 4)) (ListBlank.append Tl default))
  have et : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (5 * p + 1) + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (3 * w + 4)) (ListBlank.append Tl default))))) =
      Dc (10 * p + 4) (d + 1 + 7) (w + 1) := by
    unfold Dc
    rw [show 2 * (5 * p + 1) + 2 = 10 * p + 4 by omega, show d + 1 + 7 = d + 7 + 1 from rfl,
      ← ListBlank.append_pow_succ' _ (d + 7), show 3 * (w + 1) = 3 * w + 3 by omega,
      show 3 * w + 4 = 3 * w + 3 + 1 from rfl, ListBlank.append_pow_succ ([1] : List (Fin 2)) (3 * w + 3)]
    all_goals rfl
  rw [et] at h2
  exact h1.trans h2

/-- r = 1, z = 1: F111, then the two pair blocks join into a one-tail state. -/
theorem D_r1z (p k : ℕ) (hk : 1 ≤ k) :
    ReachesPlus target (Dc (3 * p + 4) k 1) (S 0 (10 * p + 4) (k + 14) 3) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have h1 := stepEC (3 * p + 4) (p + 1) 1 (1 + 5 * (p + 1))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * 1)) (ListBlank.append Tl default)))
    (by omega) (by omega) rfl
  have es : cfgCt (1 + 5 * (p + 1)) 1 (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ (3 * 1)) (ListBlank.append Tl default))) =
      Ccal (5 * p + 1 + 5) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ 1) (ListBlank.append Tl default)))) := by
    unfold cfgCt Ccal
    rw [show 1 + 5 * (p + 1) = 5 * p + 1 + 5 by omega, list_pow_one, rotLB (d + 1)]
    all_goals rfl
  rw [es] at h1
  have h2 := F111 (5 * p + 1) d (ListBlank.append (([1] : List (Fin 2)) ^ 1) (ListBlank.append Tl default))
  have et : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (5 * p + 1) + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 7))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 1) (ListBlank.append Tl default))))) =
      S 0 (10 * p + 4) (d + 1 + 14) 3 := by
    unfold S W cfgCt Ccal
    rw [show 2 * (5 * p + 1) + 2 = 10 * p + 4 by omega, show d + 1 + 14 = (d + 7 + 1) + 7 by omega,
      ListBlank.append_pow_add ([0, 1] : List (Fin 2)) (d + 7 + 1) 7, ← ListBlank.append_pow_succ' _ (d + 7)]
    all_goals rfl
  rw [et] at h2
  exact h1.trans h2

/-- r = 2, k ≥ 2: P then Z, to D(10q + 15, k − 1, z). -/
theorem D_r2 (q m z : ℕ) :
    ReachesPlus target (Dc (3 * q + 2) (m + 2) z) (Dc (10 * q + 15) (m + 1) z) := by
  have h1 := stepEC (3 * q + 2) q 2 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 2))
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default)))
    (by omega) (by omega) rfl
  have h2 := stepPZ (1 + 5 * q) (10 * q + 15) (m + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default)) (by omega) (by omega)
  exact h1.trans h2

/-- r = 2, k = 1: P then Z, and the ones join into a one-tail state. -/
theorem D_r2k (q z : ℕ) :
    ReachesPlus target (Dc (3 * q + 2) 1 z) (S 0 (10 * q + 15 + 3 * z) 7 3) := by
  have h1 := stepEC (3 * q + 2) q 2 (1 + 5 * q)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (0 + 1))
      (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default)))
    (by omega) (by omega) rfl
  have h2 := stepPZ (1 + 5 * q) (10 * q + 15) 0
    (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default)) (by omega) (by omega)
  have e : Ccal 0 (ListBlank.append (([1] : List (Fin 2)) ^ (10 * q + 15))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
          (ListBlank.append (([1] : List (Fin 2)) ^ (3 * z)) (ListBlank.append Tl default)))) =
      S 0 (10 * q + 15 + 3 * z) 7 3 := by
    unfold S W cfgCt Ccal
    rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add]
    all_goals rfl
  rw [e] at h2
  exact h1.trans h2

/-- **Collapse:** every D(N, k, z) with N ≥ 2, k, z ≥ 1 reaches a one-tail state (rank k + 8z). -/
theorem D_returns (R : ℕ) : ∀ N k z, k + 8 * z ≤ R → 2 ≤ N → 1 ≤ k → 1 ≤ z →
    ∃ a b c s, ReachesPlus target (Dc N k z) (S a b c s) := by
  induction R with
  | zero => intro N k z hR _ hk _; omega
  | succ R ih =>
    intro N k z hR hN hk hz
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ N = 3 * q + r := ⟨N / 3, N % 3, Nat.mod_lt _ (by norm_num), by omega⟩
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
    · exact ⟨_, _, _, _, D_r0 q k z (by omega)⟩
    · obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      rw [show 3 * (p + 1) + 1 = 3 * p + 4 by omega]
      rcases (by omega : z = 1 ∨ 2 ≤ z) with rfl | hz2
      · exact ⟨_, _, _, _, D_r1z p k hk⟩
      · obtain ⟨w, rfl⟩ : ∃ w, z = w + 2 := ⟨z - 2, by omega⟩
        obtain ⟨a, b, c, s, h⟩ := ih (10 * p + 4) (k + 7) (w + 1) (by omega) (by omega) (by omega) (by omega)
        exact ⟨a, b, c, s, (D_r1 p k w hk).trans h⟩
    · rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
      · exact ⟨_, _, _, _, D_r2k q z⟩
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
        obtain ⟨a, b, c, s, h⟩ := ih (10 * q + 15) (m + 1) z (by omega) (by omega) (by omega) hz
        exact ⟨a, b, c, s, (D_r2 q m z).trans h⟩

/-- **Push and collapse:** S(u+7, 1, 3j+8, 1) reaches a one-tail state (F1100, then `D_returns`). -/
theorem push_returns (u j : ℕ) : ∃ a b c s, ReachesPlus target (S (u + 7) 1 (3 * j + 8) 1) (S a b c s) := by
  have h1 := F1100 u (3 * j + 1) default
  have es : S (u + 7) 1 (3 * j + 8) 1 =
      Ccal (u + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j + 1 + 7)) (ListBlank.append [1, 1, 0, 0] default)) := by
    unfold S W cfgCt Ccal
    rw [show 3 * j + 1 + 7 = 3 * j + 8 by omega, list_pow_one, rotLB (3 * j + 8)]
    show _ = Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u + 7))
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j + 8))
        (ListBlank.append [1, 1] (ListBlank.cons 0 (ListBlank.cons 0 default)))))
    simp only [ListBlank.cons_zero_default]
    all_goals rfl
  rw [es]
  rw [show 2 * (3 * j + 1) + 1 = 3 * (2 * j + 1) by omega] at h1
  obtain ⟨a, b, c, s, h2⟩ := D_returns (7 + 8 * (2 * j + 1)) (2 * u + 2) 7 (2 * j + 1)
    le_rfl (by omega) (by omega) (by omega)
  exact ⟨a, b, c, s, h1.trans h2⟩

end CryptidLink.L17

#print axioms CryptidLink.L17.D_returns
#print axioms CryptidLink.L17.push_returns
