import CryptidLink.L17d
import CryptidLink.L17e
/-!
# L17: the return move for two-layer excursions (GPT, `analysis/l17-return-section/`)

    S(3u+9, 1, d+7, 1) ⊢⁺ S(10u+18, 2d+1, 7, 3)

The composition is F1100, then entry and countdown, then a tape equality. The F1100 push is absorbed at once,
so the one-tail state space S is closed under this tenth move.
-/

open BusyBeaver BusyBeaver.SixState Turing

namespace CryptidLink.L17

/-- **Return move:** S(3u+9, 1, d+7, 1) ⊢⁺ S(10u+18, 2d+1, 7, 3). -/
theorem LF1100R (u d : ℕ) : ReachesPlus target (S (3 * u + 9) 1 (d + 7) 1) (S (10 * u + 18) (2 * d + 1) 7 3) := by
  have h1 := F1100 (3 * u + 2) d default
  have es : S (3 * u + 9) 1 (d + 7) 1 =
      Ccal (3 * u + 2 + 7) (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 7)) (ListBlank.append [1, 1, 0, 0] default)) := by
    unfold S W cfgCt Ccal
    rw [show 3 * u + 2 + 7 = 3 * u + 9 by omega, list_pow_one, rotLB (d + 7)]
    show _ = Cfg.headRight C default (ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 * u + 9))
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 7))
        (ListBlank.append [1, 1] (ListBlank.cons 0 (ListBlank.cons 0 default)))))
    simp only [ListBlank.cons_zero_default]
    all_goals rfl
  rw [es]
  have h2 := stepEC (2 * (3 * u + 2) + 2) (2 * u + 2) 0 (1 + 5 * (2 * u + 2))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * d + 1)) (ListBlank.append Tl default)))
    (by omega) (by omega) rfl
  have et : cfgCt (1 + 5 * (2 * u + 2)) 0
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ 7)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * d + 1)) (ListBlank.append Tl default))) =
      S (10 * u + 18) (2 * d + 1) 7 3 := by
    unfold cfgCt S W
    rw [list_pow_zero, ListBlank.append_nil, ← ListBlank.append_pow_add,
      show 1 + 5 * (2 * u + 2) + 7 = 10 * u + 18 by omega]
    all_goals rfl
  rw [et] at h2
  exact h1.trans h2

/-- The return move with explicit numbers, for generated chains. -/
theorem LRet (a k u d a' b' : ℕ) (ha : a = 3 * u + 9) (hk : k = d + 7) (ha' : a' = 10 * u + 18) (hb' : b' = 2 * d + 1) :
    ReachesPlus target (S a 1 k 1) (S a' b' 7 3) := by
  subst ha; subst hk; subst ha'; subst hb'; exact LF1100R u d

end CryptidLink.L17

#print axioms CryptidLink.L17.LF1100R
